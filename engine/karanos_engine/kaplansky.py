"""Kaplansky zero-divisor program: the Γ substrate and its scorers.

Target (founder-approved 2026-07-20, see kaplansky-zd/PHASE0.md at the
workspace root): Γ = ⟨a,b | aba²b⁻¹a²b⁻², ab³ab⁴a⁻¹b⟩, the torsion-free
Ã₂-building lattice from Giles Gardam's SMRI slides (2021-10-05) — the one
concrete non-unique-product group where the zero-divisor conjecture is
open in every characteristic.

Anchor discipline: the ball table is TRUSTED ONLY after reproducing the
two published anchors — B(4) is a tree (161 elements, i.e. free) and
|B(6)| = 1311. `build_gamma()` refuses to hand out an unanchored table.

Scorers (deterministic, finite witnesses — registry rule):
- nonup: #unique products of (A, B) in Γ; 0 ⟹ (A,B) witnesses u.p. failure.
- zd_f2: #odd-multiplicity products of (A, B); 0 ⟹ Σa·Σb = 0 in F₂[Γ],
  i.e. a zero-divisor candidate (subject to certificate verification).

Witness format (JSON-safe): {"A": [word, ...], "B": [word, ...]} with
words over the letters a, A, b, B (A = a⁻¹, B = b⁻¹); "" is the identity.
"""

from __future__ import annotations

import pickle
from pathlib import Path

from .groupball import BallQuotient, free_reduce

GENERATORS = 2
# letters: 0 = a, 1 = a⁻¹, 2 = b, 3 = b⁻¹
RELATOR_1 = (0, 2, 0, 0, 3, 0, 0, 3, 3)  # a b a a b⁻¹ a a b⁻¹ b⁻¹
RELATOR_2 = (0, 2, 2, 2, 0, 2, 2, 2, 2, 1, 2)  # a b³ a b⁴ a⁻¹ b
ANCHOR_BALL4 = 161  # free ball of rank 2, radius 4 — "B(4) is a tree"
ANCHOR_BALL6 = 1311  # Gardam, SMRI slides 2021-10-05
SUPPORT_RADIUS = 6  # supports live in B(6); products then live in B(12)
TREE_RADIUS = 12
CLOSE_RADIUS = 10

_LETTER = {"a": 0, "A": 1, "b": 2, "B": 3}
_LETTER_INV = {v: k for k, v in _LETTER.items()}


def parse_word(s: str) -> tuple[int, ...]:
    try:
        return free_reduce(tuple(_LETTER[ch] for ch in s))
    except KeyError as exc:
        raise ValueError(f"bad letter in word {s!r} (alphabet aAbB)") from exc


def format_word(w: tuple[int, ...]) -> str:
    return "".join(_LETTER_INV[g] for g in w)


class GammaBall:
    """Anchored ball table for Γ: elements of B(radius) with geodesic words
    and a total multiplication map B(radius) × B(radius) → classes."""

    def __init__(self, quotient: BallQuotient, radius: int) -> None:
        ball = quotient.ball(radius)
        self.radius = radius
        self.quotient = quotient
        self.classes = sorted(ball)  # stable ids: index in this list
        self.words = {c: ball[c] for c in self.classes}
        self.index = {c: i for i, c in enumerate(self.classes)}

    def class_of(self, word: tuple[int, ...]) -> int:
        c = self.quotient.class_of_word(word)
        if c == -1:
            raise ValueError(f"word {format_word(word)!r} leaves the built ball")
        return c

    def product_class(self, x: int, y: int) -> int:
        c = self.quotient.walk(x, self.words[y])
        if c == -1:
            raise ValueError("product left the built ball (radii too small)")
        return c


_CACHE: GammaBall | None = None


def build_gamma(cache_dir: Path | None = None) -> GammaBall:
    """Build (or load) the anchored Γ table. Raises AssertionError with a
    plain message if the anchors fail — an unanchored table must never be
    used downstream, per PHASE0 discipline."""
    global _CACHE
    if _CACHE is not None:
        return _CACHE
    cache_path = (cache_dir or Path("runs")) / "gamma_ball.pickle"
    if cache_path.exists():
        with cache_path.open("rb") as fh:
            quotient: BallQuotient = pickle.load(fh)  # noqa: S301 — own artifact
    else:
        quotient = BallQuotient(GENERATORS, [RELATOR_1, RELATOR_2], TREE_RADIUS, CLOSE_RADIUS)
        cache_path.parent.mkdir(parents=True, exist_ok=True)
        with cache_path.open("wb") as fh:
            pickle.dump(quotient, fh)
    b4 = len(quotient.ball(4))
    b6 = len(quotient.ball(6))
    if b4 != ANCHOR_BALL4:
        raise AssertionError(
            f"ANCHOR FAILED: |B(4)| = {b4}, expected {ANCHOR_BALL4} (free/tree). "
            "Table is not trustworthy; do not proceed."
        )
    if b6 != ANCHOR_BALL6:
        detail = "under-merged: raise radii" if b6 > ANCHOR_BALL6 else "OVER-merged: bug"
        raise AssertionError(
            f"ANCHOR FAILED: |B(6)| = {b6}, expected {ANCHOR_BALL6} (Gardam 2021); {detail}."
        )
    _CACHE = GammaBall(quotient, SUPPORT_RADIUS)
    return _CACHE


REGION_RADIUS_MAX = 8  # default table: counts convergence-stable through r=10 (mapped 2026-07-20)
PRODUCT_TREE_MAX = TREE_RADIUS  # default-table hard bound; per-table code reads quotient radii
PRODUCT_CONVERGED_MAX = CLOSE_RADIUS  # default table: products ≤ 10 sit in the converged zone

# The reproduced non-unique-product witness for Γ (SAT + scorer-confirmed,
# ledger 2026-07-20T16:27:34Z). Frozen here so campaigns that search the
# witness's support geometry are reproducible from source, not from a log.
WITNESS_NONUP_A: tuple[str, ...] = (
    "", "a", "A", "b", "ab", "aB", "Ab", "bb", "aba", "abb", "aBB", "AbA", "Abb",
    "abaa", "abab", "abbA", "abbb", "AbAb", "Abbb", "aabaa", "abaab", "bbAA",
    "ababb", "abbAA", "abbAb", "abbbb", "AbAA", "AbAbb", "bbAAB", "abaabb",
    "abbAbb", "AbAAb",
)  # fmt: skip
WITNESS_NONUP_B: tuple[str, ...] = (
    "", "A", "b", "B", "ab", "AA", "bA", "bb", "BA", "bAA", "bbA", "bbb", "Bab",
    "BBAB", "bbAA", "abbab", "AbAA", "BAbAA", "BBAAA", "BBABA", "BBBAB",
    "abbbbb", "babbab", "bbAbAA", "BBBAAA", "BBBABA", "BBABab", "bAbAA",
)  # fmt: skip


def load_table(path: Path) -> BallQuotient:
    """Load a quotient pickle and re-verify the published anchors before
    handing it out. Deep tables (t13/t14/t15 …) were count-cross-checked
    against the primary table when built (tier2_build PASS gate); this
    load-time check re-asserts the two external anchors every time."""
    with path.open("rb") as fh:
        quotient: BallQuotient = pickle.load(fh)  # noqa: S301 — own artifact
    b4, b6 = len(quotient.ball(4)), len(quotient.ball(6))
    if b4 != ANCHOR_BALL4 or b6 != ANCHOR_BALL6:
        raise AssertionError(
            f"ANCHOR FAILED loading {path}: B(4)={b4} (want {ANCHOR_BALL4}), "
            f"B(6)={b6} (want {ANCHOR_BALL6}) — table untrustworthy, do not proceed."
        )
    return quotient


def max_region_radius(quotient: BallQuotient) -> int:
    """Largest element-region radius a table supports: two inside its
    close radius, matching the Tier-1 decision on the default table
    (close 10 → regions ≤ 8) and scaling with deeper builds."""
    return quotient.close_radius - 2


def region_ball(radius: int, cache_dir: Path | None = None, table: Path | None = None) -> GammaBall:
    """A GammaBall with an element region of the given radius, for
    asymmetric kernel searches (small a, large b).

    With `table` unset, the region extends the default anchored table
    (radius ≤ 8) with a prefix-consistency check against the anchored
    B(6). With `table` set (a deep pickle from tier2_build), the region
    may extend to that table's own limit; anchors are re-checked at load.

    Trust tiers are decided by the TABLE's radii, not constants: products
    ≤ close_radius are merge-converged; up to tree_radius they reach the
    built-but-unconverged shell (under-merge can hide hits, never invent
    them); beyond tree_radius walks could leave the tree — refused."""
    if table is not None:
        quotient = load_table(table)
        limit = max_region_radius(quotient)
        if not 0 <= radius <= limit:
            raise ValueError(f"region radius {radius} outside [0, {limit}] for table {table}")
        return GammaBall(quotient, radius)
    if not 0 <= radius <= REGION_RADIUS_MAX:
        raise ValueError(f"region radius {radius} outside [0, {REGION_RADIUS_MAX}]")
    anchored = build_gamma(cache_dir)
    if radius <= anchored.radius:
        return GammaBall(anchored.quotient, radius)
    extended = GammaBall(anchored.quotient, radius)
    # Prefix consistency: the extended enumeration must agree with the
    # anchored B(6) exactly — same classes, same geodesic lengths.
    core = {c for c in extended.classes if len(extended.words[c]) <= anchored.radius}
    if core != set(anchored.classes):
        raise AssertionError(
            f"extended B({radius}) is not a superset-extension of anchored "
            f"B({anchored.radius}): enumeration inconsistent, do not proceed"
        )
    return extended


def _parse_witness(witness: object) -> tuple[list[int], list[int], GammaBall]:
    if not (
        isinstance(witness, dict)
        and isinstance(witness.get("A"), list)
        and isinstance(witness.get("B"), list)
    ):
        raise ValueError('witness must be {"A": [words], "B": [words]}')
    gamma = build_gamma()
    sides: list[list[int]] = []
    for key in ("A", "B"):
        classes: list[int] = []
        for w in witness[key]:
            if not isinstance(w, str):
                raise ValueError("words must be strings over aAbB")
            classes.append(gamma.class_of(parse_word(w)))
        if not classes:
            raise ValueError(f"{key} is empty")
        if len(set(classes)) != len(classes):
            raise ValueError(f"{key} contains duplicate group elements")
        for c in classes:
            if c not in gamma.index:
                raise ValueError(f"{key} element outside B({gamma.radius})")
        sides.append(classes)
    return sides[0], sides[1], gamma


def _product_multiplicities(a: list[int], b: list[int], gamma: GammaBall) -> dict[int, int]:
    mult: dict[int, int] = {}
    for x in a:
        for y in b:
            p = gamma.product_class(x, y)
            mult[p] = mult.get(p, 0) + 1
    return mult


def score_nonup(witness: object, size: int) -> float:
    """#unique products of (A,B) in Γ, supports within B(size≤6).

    0 means (A,B) is a non-unique-product witness pair — reproducing
    Gardam's announced theorem. Every product having ≥2 representations is
    the necessary condition any zero-divisor support pair must meet."""
    a, b, gamma = _parse_witness(witness)
    if size > gamma.radius:
        raise ValueError(f"size beyond built radius {gamma.radius}")
    return float(sum(1 for m in _product_multiplicities(a, b, gamma).values() if m == 1))


def score_zd_f2(witness: object, size: int) -> float:
    """#odd-multiplicity products of (A,B) in Γ — the F₂ obstruction.

    0 means (Σa)(Σb) = 0 in F₂[Γ] with a,b ≠ 0: a zero-divisor
    counterexample CANDIDATE (a discovery only after the Lean certificate
    path confirms it; a sandbox score is never a result)."""
    a, b, gamma = _parse_witness(witness)
    if size > gamma.radius:
        raise ValueError(f"size beyond built radius {gamma.radius}")
    return float(sum(1 for m in _product_multiplicities(a, b, gamma).values() if m % 2 == 1))


# -- SAT encodings ---------------------------------------------------------
# Variables 1..n (A-membership), n+1..2n (B-membership) for n ball classes;
# pair variables z(i,j) Tseytin-defined as x_i ∧ y_j. CNF as int-lists,
# solver-agnostic (pysat if installed, else DIMACS export).


def _pair_layout(n: int) -> tuple[int, int]:
    return n, 2 * n  # x-block end, y-block end (z-block starts after)


def encode_common(
    gamma: GammaBall, radius: int
) -> tuple[list[list[int]], dict[tuple[int, int], int], list[list[tuple[int, int]]], int]:
    """Shared skeleton: z-definitions + product-class pair grouping.

    Returns (clauses, zvar, groups, top). groups[k] = list of (i,j) pairs
    sharing product class k (indices into the restricted ball)."""
    classes = [c for c in gamma.classes if len(gamma.words[c]) <= radius]
    n = len(classes)
    _, y_end = _pair_layout(n)
    clauses: list[list[int]] = []
    zvar: dict[tuple[int, int], int] = {}
    by_product: dict[int, list[tuple[int, int]]] = {}
    top = y_end
    for i, x in enumerate(classes):
        for j, y in enumerate(classes):
            top += 1
            z = top
            zvar[(i, j)] = z
            xi, yj = i + 1, n + j + 1
            clauses += [[-z, xi], [-z, yj], [z, -xi, -yj]]
            by_product.setdefault(gamma.product_class(x, y), []).append((i, j))
    groups = list(by_product.values())
    return clauses, zvar, groups, top


def _normalize_identity(
    clauses: list[list[int]], gamma: GammaBall, radius: int, normalize: bool
) -> int:
    """1 ∈ A and 1 ∈ B (translation normalization). Sound for EXISTENCE
    searches (any witness pair translates to one containing the identity),
    but the translate may need a larger ball — so an UNSAT obtained WITH
    normalization only excludes witness pairs containing 1. Exclusion runs
    that want the unconditional statement pass normalize=False. Returns
    the class count."""
    classes = [c for c in gamma.classes if len(gamma.words[c]) <= radius]
    n_classes = len(classes)
    if normalize:
        identity_index = next(i for i, c in enumerate(classes) if gamma.words[c] == ())
        clauses.append([identity_index + 1])  # 1 ∈ A
        clauses.append([n_classes + identity_index + 1])  # 1 ∈ B
    else:
        clauses.append(list(range(1, n_classes + 1)))  # A nonempty
        clauses.append(list(range(n_classes + 1, 2 * n_classes + 1)))  # B nonempty
    return n_classes


def encode_nonup(
    gamma: GammaBall, radius: int, normalize: bool = True
) -> tuple[list[list[int]], int, int]:
    """SAT model ⟺ a pair (A,B) in B(radius) with NO unique product.

    Constraint per pair (i,j): z(i,j) → some OTHER pair in the same
    product group is selected."""
    clauses, zvar, groups, top = encode_common(gamma, radius)
    for group in groups:
        for i, j in group:
            others = [zvar[p] for p in group if p != (i, j)]
            clauses.append([-zvar[(i, j)], *others])
    n_classes = _normalize_identity(clauses, gamma, radius, normalize)
    return clauses, top, n_classes


def encode_zd_f2(
    gamma: GammaBall,
    radius: int,
    min_side: int,
    min_sum: int,
    normalize: bool = True,
) -> tuple[list[list[int]], int, int]:
    """SAT model ⟺ supports (A,B) in B(radius) with EVERY product class hit
    an even number of times, i.e. (Σa)(Σb) = 0 in F₂[Γ]. UNSAT at given
    caps ⟹ exclusion bound. Parity per product group via XOR ladders; the
    floor |A|+|B| ≥ 16 is theorem-backed (Nielsen–Soelberg 2024), so
    passing min_sum=16 is sound pruning, not an assumption."""
    clauses, zvar, groups, top = encode_common(gamma, radius)
    for group in groups:
        # XOR ladder: acc ⟺ parity of the pair-vars so far; force even.
        acc = 0  # 0 encodes "no accumulator yet"
        for idx, p in enumerate(group):
            z = zvar[p]
            if idx == 0:
                acc = z
                continue
            top += 1
            new = top
            # new ⟺ acc ⊕ z (full Tseytin, both directions)
            clauses += [
                [-new, acc, z],
                [-new, -acc, -z],
                [new, -acc, z],
                [new, acc, -z],
            ]
            acc = new
        if acc:
            clauses.append([-acc])  # even multiplicity (zero included)
    n_classes = _normalize_identity(clauses, gamma, radius, normalize)
    top = _at_least(clauses, list(range(1, n_classes + 1)), min_side, top)
    top = _at_least(clauses, list(range(n_classes + 1, 2 * n_classes + 1)), min_side, top)
    top = _at_least(clauses, list(range(1, 2 * n_classes + 1)), min_sum, top)
    return clauses, top, n_classes


def _at_least(clauses: list[list[int]], lits: list[int], k: int, top: int) -> int:
    """≥k over lits, encoded as Sinz sequential ≤(n−k) over the negations.

    One-directional register clauses are sound for ≤ (registers over-set
    only tighten the cap); encoding ≥ directly that way is NOT sound — it
    was the bug this function replaces."""
    n = len(lits)
    if k <= 0:
        return top
    if k > n:
        clauses.append([])  # unsatisfiable by construction
        return top
    r = n - k
    if r == 0:
        for lit in lits:
            clauses.append([lit])
        return top
    neg = [-lit for lit in lits]
    # registers: reg[i][j] ⟺ ≥ j+1 of neg[0..i] are true; cap at r.
    prev: list[int] = []
    for i in range(n):
        width = min(i + 1, r)
        row = [top + 1 + j for j in range(width)]
        top += width
        clauses.append([-neg[i], row[0]])
        if prev:
            for j in range(min(len(prev), width)):
                clauses.append([-prev[j], row[j]])
            for j in range(1, width):
                if j - 1 < len(prev):
                    clauses.append([-neg[i], -prev[j - 1], row[j]])
            if len(prev) >= r:
                clauses.append([-neg[i], -prev[r - 1]])  # never exceed r
        prev = row
    return top


def decode_pair(
    model: list[int], n_classes: int, gamma: GammaBall, radius: int
) -> dict[str, list[str]]:
    classes = [c for c in gamma.classes if len(gamma.words[c]) <= radius]
    pos = {v for v in model if v > 0}
    a = [format_word(gamma.words[classes[i]]) for i in range(n_classes) if i + 1 in pos]
    b = [format_word(gamma.words[classes[j]]) for j in range(n_classes) if n_classes + j + 1 in pos]
    return {"A": a, "B": b}


# -- driver ----------------------------------------------------------------


def _solve(
    clauses: list[list[int]], top: int, timeout_s: float | None, dimacs_path: Path
) -> tuple[str, list[int] | None]:
    """Solve with pysat if importable; otherwise export DIMACS and report.
    Returns (status, model): status ∈ sat | unsat | unknown | exported."""
    try:
        from pysat.solvers import Cadical195  # type: ignore[import-untyped]
    except ImportError:
        with dimacs_path.open("w", encoding="ascii") as fh:
            fh.write(f"p cnf {top} {len(clauses)}\n")
            for cl in clauses:
                fh.write(" ".join(map(str, cl)) + " 0\n")
        return "exported", None
    with Cadical195(bootstrap_with=clauses) as solver:
        if timeout_s is not None:
            # interrupt-based budget: portable across pysat versions
            from threading import Timer

            timer = Timer(timeout_s, solver.interrupt)
            timer.start()
            try:
                res = solver.solve_limited(expect_interrupt=True)
            finally:
                timer.cancel()
        else:
            res = solver.solve()
        if res is True:
            return "sat", solver.get_model()
        if res is False:
            return "unsat", None
        return "unknown", None


def main() -> int:
    import argparse
    import json

    from .ledger import Ledger

    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("anchors", help="build the Γ table and print anchored ball sizes")
    for name in ("nonup", "zd"):
        p = sub.add_parser(name)
        p.add_argument("--radius", type=int, default=SUPPORT_RADIUS)
        p.add_argument("--timeout", type=float, default=None, help="seconds")
        p.add_argument("--no-normalize", action="store_true")
        if name == "zd":
            p.add_argument("--min-side", type=int, default=3)
            p.add_argument("--min-sum", type=int, default=16)
    ap.add_argument("--out", type=Path, default=Path("runs"))
    args = ap.parse_args()

    gamma = build_gamma(args.out)
    if args.cmd == "anchors":
        counts = {r: len(gamma.quotient.ball(r)) for r in range(SUPPORT_RADIUS + 1)}
        print(f"anchored: B(4)={counts[4]} (tree), B(6)={counts[6]} — {counts}")
        print(f"merge witnesses recorded: {len(gamma.quotient.witnesses)}")
        return 0

    normalize = not args.no_normalize
    if args.cmd == "nonup":
        key = "kaplansky_nonup_gamma"
        clauses, top, n_classes = encode_nonup(gamma, args.radius, normalize)
        caps = f"radius={args.radius} normalize={normalize}"
    else:
        key = "kaplansky_zd_f2_gamma"
        clauses, top, n_classes = encode_zd_f2(
            gamma, args.radius, args.min_side, args.min_sum, normalize
        )
        caps = (
            f"radius={args.radius} min_side={args.min_side} "
            f"min_sum={args.min_sum} normalize={normalize}"
        )

    ledger = Ledger(args.out / "kaplansky.ledger.jsonl")
    print(f"{key}: {top} vars, {len(clauses)} clauses ({caps})")
    status, model = _solve(clauses, top, args.timeout, args.out / f"{key}_r{args.radius}.cnf")
    if status == "sat" and model is not None:
        witness = decode_pair(model, n_classes, gamma, args.radius)
        # Independent re-check: the scorer recomputes the product multiset
        # from scratch, sharing no code path with the SAT encoding.
        scorer = {"kaplansky_nonup_gamma": score_nonup, "kaplansky_zd_f2_gamma": score_zd_f2}[key]
        score = scorer(witness, args.radius)
        note = f"SAT ({caps}); scorer confirms {score:.0f}" + (
            " — WITNESS" if score == 0 else " — SOLVER/SCORER MISMATCH, investigate"
        )
        ledger.append(key, 0, f"sat-driver {caps}", score, witness, note)
        print(note)
        print(json.dumps(witness))
        return 0 if score == 0 else 2
    note = {
        "unsat": f"UNSAT ({caps}) — exclusion bound, table-completeness caveat applies",
        "unknown": f"UNKNOWN/timeout ({caps})",
        "exported": f"no pysat; DIMACS exported ({caps})",
    }[status]
    ledger.append(key, 0, f"sat-driver {caps}", None, None, note)
    print(note)
    return 0 if status != "unknown" else 3


if __name__ == "__main__":
    raise SystemExit(main())
