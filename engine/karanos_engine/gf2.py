"""GF(2) kernel test for the Kaplansky program (Phase G0 spike).

The reformulation (docs/KAPLANSKY_GPU_PLAN.md): fix a left factor `a`
(a set of group-ring basis elements over F₂), restrict the right factor
to support inside a region S. Then b ↦ a·b is F₂-linear, and a zero
divisor with left factor `a` and right support ⊆ S exists iff the matrix
M_a has a nontrivial kernel — any nonzero kernel vector IS the witness b.

This module is the CPU reference implementation: rows are Python ints
used as bitsets (augmented identity in the low bits, product-class
columns in the high bits), eliminated incrementally with early exit on
the first kernel vector. It is the ground truth the GPU kernel must
agree with, and the benchmark that decides whether a GPU port is worth
building at all.

Trust boundary, same as the SAT track: a kernel hit is only a CANDIDATE
until `product_parity` (an independent from-scratch recount) and the
registry scorer confirm it; misses inherit the table-completeness caveat
(products beyond the anchored radius may be under-merged, which can only
hide cancellations, never invent them — sound merges make hits
trustworthy, misses conservative).
"""

from __future__ import annotations

from collections.abc import Callable, Iterator, Sequence
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from pathlib import Path

    from .kaplansky import GammaBall
    from .ledger import Ledger

# product(x, y) -> class id of x·y; must be total on the arguments used.
Product = Callable[[int, int], int]


def build_rows(a: Sequence[int], region: Sequence[int], product: Product) -> tuple[list[int], int]:
    """Rows of M_aᵀ as int bitsets: row j = products a·region[j].

    Bit layout: bits [0, len(region)) are the augmented identity (bit j
    set on row j), bits ≥ len(region) index distinct product classes in
    order of first appearance. Returns (rows, n_product_columns).

    Distinct elements of `a` give distinct products against a fixed s
    (left translation is injective), so a repeated column bit within one
    row means the caller passed duplicate elements or a broken product
    map — refused, never silently XOR-cancelled."""
    n_aug = len(region)
    col: dict[int, int] = {}
    rows: list[int] = []
    for j, s in enumerate(region):
        row = 1 << j
        for x in a:
            p = product(x, s)
            idx = col.setdefault(p, len(col))
            bit = 1 << (n_aug + idx)
            if row & bit:
                raise AssertionError(
                    "duplicate product within one row: duplicate elements in `a` "
                    "or a non-injective product map"
                )
            row |= bit
        rows.append(row)
    return rows, len(col)


def kernel_vector(rows: Sequence[int], n_aug: int) -> list[int] | None:
    """First kernel combination found, as sorted region indices, else None.

    Incremental Gaussian elimination over GF(2): each row is reduced
    against the pivots collected so far (pivot = leading data bit); a row
    whose data part vanishes has its augmented part as a nonzero kernel
    vector of M_a. The augmented part cannot vanish: row j carries aug
    bit j, and only rows with smaller aug indices are ever XORed in."""
    pivots: dict[int, int] = {}
    for row in rows:
        while True:
            lead = row.bit_length() - 1
            if lead < n_aug:
                return [j for j in range(n_aug) if row >> j & 1]
            piv = pivots.get(lead)
            if piv is None:
                pivots[lead] = row
                break
            row ^= piv
    return None


def zd_kernel(a: Sequence[int], region: Sequence[int], product: Product) -> list[int] | None:
    """Support of a b with a·b = 0 in F₂ (class ids from `region`), or None."""
    rows, _ = build_rows(a, region, product)
    combo = kernel_vector(rows, len(region))
    if combo is None:
        return None
    return [region[j] for j in combo]


def product_parity(a: Sequence[int], b: Sequence[int], product: Product) -> set[int]:
    """Odd-multiplicity product classes of (Σa)(Σb) — recounted from
    scratch, no linear algebra: the independent check every kernel hit
    must pass before it is called a candidate. Empty set ⟺ a·b = 0."""
    mult: dict[int, int] = {}
    for x in a:
        for y in b:
            p = product(x, y)
            mult[p] = mult.get(p, 0) + 1
    return {p for p, m in mult.items() if m % 2 == 1}


# -- shared drivers ---------------------------------------------------------


def _region_setup(
    a_radius: int, region_radius: int, out: Path, table: Path | None = None
) -> tuple[GammaBall, list[int], list[int], str, str]:
    """Guarded setup for asymmetric searches: the ball, the b-region, the
    a-pool, the trust-tier label, and a provenance label naming the table.

    The ball is built at max(a_radius, region_radius) so the a-pool is
    never silently capped by a smaller region (the 2026-07-21 slice-b6w2
    mislabeling bug). Trust tiers derive from the LOADED table's own tree
    and close radii, so deep tables get their real, larger converged
    zones. Products that could leave the built tree are refused."""
    from .kaplansky import region_ball

    ball_radius = max(a_radius, region_radius)
    ext = region_ball(ball_radius, out, table)
    tree_max = ext.quotient.tree_radius
    converged_max = ext.quotient.close_radius
    prod_max = a_radius + region_radius
    if prod_max > tree_max:
        raise SystemExit(
            f"a-radius {a_radius} + region-radius {region_radius} = {prod_max} "
            f"exceeds the built tree ({tree_max}); refuse rather than mis-walk"
        )
    tier = (
        "converged"
        if prod_max <= converged_max
        else f"SHELL (products reach {prod_max} > {converged_max}: under-merge there can hide hits)"
    )
    region = [c for c in ext.classes if len(ext.words[c]) <= region_radius]
    pool = [c for c in ext.classes if len(ext.words[c]) <= a_radius]
    label = "default" if table is None else table.stem
    return ext, region, pool, tier, label


def _audit_hit(
    ext: GammaBall, a: Sequence[int], hit: Sequence[int], ledger: Ledger, program: str, where: str
) -> None:
    """The single audit path for every kernel hit: independent recount +
    the Nielsen–Soelberg ≥16 support floor. CANDIDATE or BUG, ledgered
    and printed loudly either way — never silently trusted."""
    import json

    from .kaplansky import format_word

    recount = product_parity(a, hit, ext.product_class)
    floor_ok = len(a) + len(hit) >= 16
    verdict = (
        "CANDIDATE — recount clean, meets the |A|+|B| ≥ 16 floor; escalate to "
        "the audit + certification path, this is NOT yet a result"
        if not recount and floor_ok
        else "BUG — "
        + ("fails independent recount" if recount else "violates the ≥16 support floor")
        + "; pipeline or table is wrong, stop and investigate"
    )
    witness = {
        "A": [format_word(ext.words[c]) for c in a],
        "B": [format_word(ext.words[c]) for c in hit],
    }
    note = f"kernel at {where} (|a|={len(a)}, |b|={len(hit)}): {verdict}"
    ledger.append("kaplansky_g0_gf2", 0, program, None, witness, note)
    print(note, flush=True)
    print(json.dumps(witness), flush=True)


def extension_candidates(
    base: Sequence[int], pool: Sequence[int], max_extra: int
) -> Iterator[tuple[int, ...]]:
    """Yield base ∪ E for every E ⊆ pool with 1 ≤ |E| ≤ max_extra, in
    weight order. `pool` must be disjoint from `base` (the caller strips
    overlaps); duplicates would be refused downstream by build_rows."""
    from itertools import combinations

    base_t = tuple(base)
    for k in range(1, max_extra + 1):
        for extra in combinations(pool, k):
            yield base_t + extra


# -- controls and benchmark -------------------------------------------------


def _cyclic_controls() -> list[str]:
    """Positive controls on F₂[C_n]: the kernel test must FIND the known
    zero divisors, and every hit must pass the independent recount."""
    notes: list[str] = []
    cases: list[tuple[int, list[int]]] = [
        (2, [0, 1]),  # (1+g)(1+g) = 0 in F₂[C₂]
        (3, [0, 1, 2]),  # (1+g+g²)(1+g) = 0 in F₂[C₃]
        (3, [0, 1]),  # (1+g)(1+g+g²) = 0 in F₂[C₃]
    ]
    for n, a in cases:
        region = list(range(n))

        def product(x: int, y: int, n: int = n) -> int:
            return (x + y) % n

        b = zd_kernel(a, region, product)
        if b is None:
            raise AssertionError(f"C_{n}, a={a}: known zero divisor NOT found — pipeline is wrong")
        if product_parity(a, b, product):
            raise AssertionError(f"C_{n}, a={a}: kernel b={b} fails the independent recount")
        notes.append(f"C_{n} a={a}: found b={b}, recount clean")
    return notes


def main() -> int:
    import argparse
    import json
    import random
    import time
    from pathlib import Path

    from .kaplansky import build_gamma, format_word, score_zd_f2
    from .ledger import Ledger

    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest="cmd", required=True)
    pc = sub.add_parser("controls", help="positive (cyclic) + negative (Γ radius-5) controls")
    pc.add_argument("--samples", type=int, default=50, help="random left factors for the negative")
    pc.add_argument("--seed", type=int, default=0)
    pb = sub.add_parser("bench", help="candidates/sec versus b-region size")
    pb.add_argument("--reps", type=int, default=5)
    pb.add_argument("--weight", type=int, default=5, help="left-factor support weight")
    pb.add_argument("--seed", type=int, default=0)
    pasym = sub.add_parser("asym", help="asymmetric sweep: random small a against a large b-region")
    pasym.add_argument("--a-radius", type=int, default=2)
    pasym.add_argument("--region-radius", type=int, default=8)
    pasym.add_argument("--samples", type=int, default=100)
    pasym.add_argument("--min-weight", type=int, default=3)
    pasym.add_argument("--max-weight", type=int, default=13)
    pasym.add_argument("--seed", type=int, default=0)
    psl = sub.add_parser("slice", help="EXHAUSTIVE low-weight slice: every a of weight ≤ w")
    psl.add_argument("--a-radius", type=int, default=3)
    psl.add_argument("--region-radius", type=int, default=8)
    psl.add_argument("--max-weight", type=int, default=3)
    pw = sub.add_parser("witness", help="EXHAUSTIVE sweep of the non-u.p. witness support")
    pw.add_argument("--side", choices=("A", "B"), default="A")
    pw.add_argument("--region-radius", type=int, default=6)
    pw.add_argument("--min-weight", type=int, default=1)
    pw.add_argument("--max-weight", type=int, default=4)
    px = sub.add_parser("extend", help="EXHAUSTIVE witness SUPERSETS: W ∪ E, |E| ≤ k")
    px.add_argument("--base", choices=("A", "B"), default="A")
    px.add_argument("--extend-radius", type=int, default=6, help="E drawn from B(r) \\ W")
    px.add_argument("--max-extra", type=int, default=1, help="largest |E|")
    px.add_argument("--region-radius", type=int, default=6)
    for sp in (pasym, psl, pw, px):
        sp.add_argument("--table", type=Path, default=None, help="deep table pickle (tier2_build)")
    ap.add_argument("--out", type=Path, default=Path("runs"))
    args = ap.parse_args()

    gamma = build_gamma(args.out)
    ledger = Ledger(args.out / "kaplansky.ledger.jsonl")
    by_radius = {
        r: [c for c in gamma.classes if len(gamma.words[c]) <= r] for r in range(gamma.radius + 1)
    }
    rng = random.Random(getattr(args, "seed", 0))

    if args.cmd == "controls":
        notes = _cyclic_controls()
        for note in notes:
            print(f"positive: {note}")

        # Scorer cross-check: the parity recount must agree with the
        # registry scorer on random pairs (two code paths, one truth).
        b3 = by_radius[3]
        for _ in range(20):
            pa = rng.sample(b3, rng.randint(2, 8))
            pb_ = rng.sample(b3, rng.randint(2, 8))
            parity = product_parity(pa, pb_, gamma.product_class)
            witness = {
                "A": [format_word(gamma.words[c]) for c in pa],
                "B": [format_word(gamma.words[c]) for c in pb_],
            }
            if score_zd_f2(witness, gamma.radius) != float(len(parity)):
                raise AssertionError(f"parity recount disagrees with registry scorer on {witness}")
        print("cross-check: parity recount agrees with score_zd_f2 on 20 random pairs")

        # Negative control on Γ: any kernel here is a pipeline bug —
        # |b| = 1 is impossible (left translation is injective), and any
        # larger hit violates either the Nielsen–Soelberg |A|+|B| ≥ 16
        # floor (for |a| ≤ 13) or the radius-5 UNSAT already in the ledger.
        b5 = by_radius[5]
        t0 = time.perf_counter()
        for i in range(args.samples):
            a = rng.sample(b5, rng.randint(3, 13))
            hit = zd_kernel(a, b5, gamma.product_class)
            if hit is not None:
                raise AssertionError(
                    f"IMPOSSIBLE KERNEL at sample {i}: |a|={len(a)}, |b|={len(hit)} — "
                    "contradicts the support floor / radius-5 UNSAT; the pipeline is wrong"
                )
        dt = time.perf_counter() - t0
        note = (
            f"G0 controls PASS: {len(notes)} cyclic positives found+recounted, scorer "
            f"cross-check 20/20, negative {args.samples} random a over B(5) "
            f"({len(b5)} classes) all kernel-free in {dt:.1f}s"
        )
        ledger.append("kaplansky_g0_gf2", 0, "g0-spike controls", None, None, note)
        print(note)
        return 0

    if args.cmd == "asym":
        ext, region, pool, tier, table_label = _region_setup(
            args.a_radius, args.region_radius, args.out, args.table
        )
        print(
            f"asym: a ⊆ B({args.a_radius}) ({len(pool)} classes), "
            f"b-region B({args.region_radius}) ({len(region)} classes), "
            f"tier: {tier}, table: {table_label}",
            flush=True,
        )
        hits = 0
        t0 = time.perf_counter()
        for i in range(args.samples):
            hi = min(args.max_weight, len(pool))
            a = rng.sample(pool, rng.randint(min(args.min_weight, hi), hi))
            hit = zd_kernel(a, region, ext.product_class)
            if hit is not None:
                hits += 1
                _audit_hit(ext, a, hit, ledger, "asym-sweep", f"sample {i}")
        dt = time.perf_counter() - t0
        note = (
            f"asym sweep: {args.samples} random a ⊆ B({args.a_radius}) "
            f"(weight {args.min_weight}–{args.max_weight}) vs b-region B({args.region_radius}) "
            f"({len(region)} classes), tier {tier}, table {table_label}: {hits} kernels "
            f"in {dt:.1f}s ({args.samples / dt:.1f}/s)"
        )
        ledger.append("kaplansky_g0_gf2", 0, "asym-sweep", None, None, note)
        print(note, flush=True)
        return 2 if hits else 0

    if args.cmd == "slice":
        import math
        from itertools import combinations

        ext, region, pool, tier, table_label = _region_setup(
            args.a_radius, args.region_radius, args.out, args.table
        )
        total = sum(math.comb(len(pool), w) for w in range(1, args.max_weight + 1))
        print(
            f"slice: EXHAUSTIVE a ⊆ B({args.a_radius}) weight ≤ {args.max_weight} "
            f"({len(pool)} classes → {total} candidates) vs b-region "
            f"B({args.region_radius}) ({len(region)} classes), tier: {tier}, "
            f"table: {table_label}",
            flush=True,
        )
        hits = done = 0
        t0 = time.perf_counter()
        for w in range(1, args.max_weight + 1):
            for a_tuple in combinations(pool, w):
                hit = zd_kernel(a_tuple, region, ext.product_class)
                done += 1
                if hit is not None:
                    hits += 1
                    _audit_hit(ext, a_tuple, hit, ledger, "slice-sweep", f"candidate {done}")
                if done % 2000 == 0:
                    rate = done / (time.perf_counter() - t0)
                    eta_min = (total - done) / rate / 60
                    print(f"  {done}/{total} ({rate:.1f}/s, ETA {eta_min:.0f} min)", flush=True)
        dt = time.perf_counter() - t0
        note = (
            f"slice COMPLETE: every a ⊆ B({args.a_radius}) of weight ≤ {args.max_weight} "
            f"({total} candidates) vs b-region B({args.region_radius}) ({len(region)} classes), "
            f"tier {tier}, table {table_label}: {hits} kernels in {dt:.0f}s ({total / dt:.1f}/s)"
        )
        ledger.append("kaplansky_g0_gf2", 0, "slice-sweep", None, None, note)
        print(note, flush=True)
        return 2 if hits else 0

    if args.cmd == "witness":
        import math
        from itertools import chain, combinations

        from .kaplansky import WITNESS_NONUP_A, WITNESS_NONUP_B, parse_word

        words = WITNESS_NONUP_A if args.side == "A" else WITNESS_NONUP_B
        a_radius = max(len(parse_word(w)) for w in words)
        ext, region, _pool, tier, table_label = _region_setup(
            a_radius, args.region_radius, args.out, args.table
        )
        support = [ext.class_of(parse_word(w)) for w in words]
        if len(set(support)) != len(support):
            raise AssertionError("witness support contains duplicate classes — table is wrong")
        lo, hi = args.min_weight, min(args.max_weight, len(support))
        total = sum(math.comb(len(support), w) for w in range(lo, hi + 1)) + 1
        print(
            f"witness-{args.side}: EXHAUSTIVE subsets of the non-u.p. witness "
            f"({len(support)} elements, weight {lo}–{hi}, + the full support → {total} "
            f"candidates) vs b-region B({args.region_radius}) ({len(region)} classes), "
            f"tier: {tier}, table: {table_label}",
            flush=True,
        )
        hits = done = 0
        t0 = time.perf_counter()
        subsets = (a_tuple for w in range(lo, hi + 1) for a_tuple in combinations(support, w))
        for a_tuple in chain(subsets, [tuple(support)]):
            hit = zd_kernel(a_tuple, region, ext.product_class)
            done += 1
            if hit is not None:
                hits += 1
                _audit_hit(ext, a_tuple, hit, ledger, f"witness-{args.side}", f"candidate {done}")
            if done % 2000 == 0:
                rate = done / (time.perf_counter() - t0)
                eta_min = (total - done) / rate / 60
                print(f"  {done}/{total} ({rate:.1f}/s, ETA {eta_min:.0f} min)", flush=True)
        dt = time.perf_counter() - t0
        note = (
            f"witness-{args.side} COMPLETE: subsets weight {lo}–{hi} + full support "
            f"({total} candidates) of the non-u.p. witness vs b-region "
            f"B({args.region_radius}) ({len(region)} classes), tier {tier}, "
            f"table {table_label}: {hits} kernels in {dt:.0f}s ({total / dt:.1f}/s)"
        )
        ledger.append("kaplansky_g0_gf2", 0, f"witness-{args.side}", None, None, note)
        print(note, flush=True)
        return 2 if hits else 0

    if args.cmd == "extend":
        import math

        from .kaplansky import WITNESS_NONUP_A, WITNESS_NONUP_B, parse_word

        words = WITNESS_NONUP_A if args.base == "A" else WITNESS_NONUP_B
        a_radius = max(max(len(parse_word(w)) for w in words), args.extend_radius)
        ext, region, _pool, tier, table_label = _region_setup(
            a_radius, args.region_radius, args.out, args.table
        )
        base = [ext.class_of(parse_word(w)) for w in words]
        base_set = set(base)
        pool = [
            c for c in ext.classes if len(ext.words[c]) <= args.extend_radius and c not in base_set
        ]
        total = sum(math.comb(len(pool), k) for k in range(1, args.max_extra + 1))
        print(
            f"extend-{args.base}: witness ({len(base)} elements) ∪ E, E ⊆ "
            f"B({args.extend_radius})\\W ({len(pool)} classes), |E| = 1–{args.max_extra} "
            f"→ {total} candidates vs b-region B({args.region_radius}) "
            f"({len(region)} classes), tier: {tier}, table: {table_label}",
            flush=True,
        )
        hits = done = 0
        t0 = time.perf_counter()
        for a_tuple in extension_candidates(base, pool, args.max_extra):
            hit = zd_kernel(a_tuple, region, ext.product_class)
            done += 1
            if hit is not None:
                hits += 1
                _audit_hit(ext, a_tuple, hit, ledger, f"extend-{args.base}", f"candidate {done}")
            if done % 200 == 0:
                rate = done / (time.perf_counter() - t0)
                eta_min = (total - done) / rate / 60
                print(f"  {done}/{total} ({rate:.1f}/s, ETA {eta_min:.0f} min)", flush=True)
        dt = time.perf_counter() - t0
        note = (
            f"extend-{args.base} COMPLETE: witness ∪ E exhaustive for E ⊆ "
            f"B({args.extend_radius})\\W, |E| ≤ {args.max_extra} ({total} candidates) vs "
            f"b-region B({args.region_radius}) ({len(region)} classes), tier {tier}, "
            f"table {table_label}: {hits} kernels in {dt:.0f}s ({total / dt:.1f}/s)"
        )
        ledger.append("kaplansky_g0_gf2", 0, f"extend-{args.base}", None, None, note)
        print(note, flush=True)
        return 2 if hits else 0

    # bench: per-candidate cost as a function of the b-region size.
    results: dict[str, dict[str, float]] = {}
    for r in range(3, gamma.radius + 1):
        region = by_radius[r]
        build_s = solve_s = 0.0
        for _ in range(args.reps):
            a = rng.sample(by_radius[2], args.weight)
            t0 = time.perf_counter()
            rows, _n_cols = build_rows(a, region, gamma.product_class)
            t1 = time.perf_counter()
            kernel_vector(rows, len(region))
            t2 = time.perf_counter()
            build_s += t1 - t0
            solve_s += t2 - t1
        per = (build_s + solve_s) / args.reps
        results[f"B({r})"] = {
            "region": len(region),
            "sec_per_candidate": round(per, 4),
            "candidates_per_sec": round(1.0 / per, 2),
            "build_frac": round(build_s / (build_s + solve_s), 2),
        }
        print(f"B({r}) |S|={len(region)}: {per:.3f}s/candidate ({1.0 / per:.1f}/s)")
    note = f"G0 bench (weight={args.weight}, reps={args.reps}): {json.dumps(results)}"
    ledger.append("kaplansky_g0_gf2", 0, "g0-spike bench", None, None, note)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
