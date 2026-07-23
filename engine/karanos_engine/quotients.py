"""Finite-quotient search for Γ — the distinctness half of the P2
certificate (docs/KAPLANSKY_PLAN.md).

The Lean certificate needs the 32 elements of the non-u.p. witness side A
(and the 28 of side B) pairwise distinct in Γ. Inequalities cannot come
from relators; they come from homomorphisms onto finite groups: a pair of
images (â, b̂) killing both relators induces φ: Γ → G, and φ(u) ≠ φ(v)
proves u ≠ v. Each unordered pair needs only ONE quotient that separates
it, so several small quotients may share the load.

Search plan, cheapest first:
1. The abelianization: relator exponent sums give the matrix [[5,-2],[1,8]]
   with |det| = 42, so Γᵃᵇ ≅ ℤ/42 (Smith form; gcd of entries is 1). The
   induced map sends a word to its exponent-sum pair — separation is a
   modular-arithmetic check, no search at all.
2. Symmetric groups: sweep â over conjugacy-class representatives of Sₙ
   (conjugating a hom gives an equivalent hom, so one representative per
   class suffices for â) and b̂ over all of Sₙ, keeping pairs that kill
   both relators; score each hom by how many required pairs it separates;
   greedily cover the remainder.

Everything here is UNTRUSTED search — the Lean side re-verifies every hom
(relators by decide) and every separation (image inequality by decide).
This module only has to FIND them and honestly report coverage.
"""

from __future__ import annotations

from itertools import combinations, permutations

from .kaplansky import (
    RELATOR_1,
    RELATOR_2,
    WITNESS_NONUP_A,
    WITNESS_NONUP_B,
    parse_word,
)

Perm = tuple[int, ...]

# Exponent sums of (a, b) in a letter word: letters 0/1 are a/a⁻¹, 2/3 are b/b⁻¹.


def exponent_sums(word: tuple[int, ...]) -> tuple[int, int]:
    ea = sum(1 if g == 0 else -1 if g == 1 else 0 for g in word)
    eb = sum(1 if g == 2 else -1 if g == 3 else 0 for g in word)
    return ea, eb


ABELIAN_ORDER = 42  # |det [[5,-2],[1,8]]| = 42, gcd of entries 1 ⟹ Γᵃᵇ ≅ ℤ/42


def abelian_image(word: tuple[int, ...]) -> int:
    """Image of a word in Γᵃᵇ ≅ ℤ/42, via the Smith-form change of basis.

    With relations 5a − 2b ≡ 0 and a + 8b ≡ 0, eliminate a = −8b to get
    42b ≡ 0; then a word with exponent sums (ea, eb) maps to
    (eb − 8·ea) mod 42 in the ℤ/42 coordinate."""
    ea, eb = exponent_sums(word)
    return (eb - 8 * ea) % ABELIAN_ORDER


# -- permutation machinery (0-indexed images as tuples) ---------------------


def p_mul(p: Perm, q: Perm) -> Perm:
    """(p∘q)(x) = p(q(x)) — apply q first."""
    return tuple(p[q[x]] for x in range(len(p)))


def p_inv(p: Perm) -> Perm:
    out = [0] * len(p)
    for i, v in enumerate(p):
        out[v] = i
    return tuple(out)


def p_eval(word: tuple[int, ...], a: Perm, b: Perm) -> Perm:
    """Image of a letter word under a ↦ a, b ↦ b (letters 0,1,2,3)."""
    imgs = {0: a, 1: p_inv(a), 2: b, 3: p_inv(b)}
    acc = tuple(range(len(a)))
    for g in word:
        acc = p_mul(acc, imgs[g])
    return acc


def kills_relators(a: Perm, b: Perm) -> bool:
    ident = tuple(range(len(a)))
    return p_eval(RELATOR_1, a, b) == ident and p_eval(RELATOR_2, a, b) == ident


def cycle_type_reps(n: int) -> list[Perm]:
    """One representative per conjugacy class of Sₙ (i.e. per cycle type),
    built by laying out cycles over 0..n-1 in partition order."""
    reps: list[Perm] = []

    def partitions(rest: int, cap: int) -> list[list[int]]:
        if rest == 0:
            return [[]]
        return [
            [k, *tail] for k in range(min(rest, cap), 0, -1) for tail in partitions(rest - k, k)
        ]

    for part in partitions(n, n):
        perm = list(range(n))
        pos = 0
        for k in part:
            for i in range(k):
                perm[pos + i] = pos + (i + 1) % k
            pos += k
        reps.append(tuple(perm))
    return reps


# -- separation bookkeeping -------------------------------------------------


def required_pairs() -> list[tuple[tuple[int, ...], tuple[int, ...]]]:
    """All unordered word pairs that the certificate must separate:
    within-A (496) and within-B (378) — 874 in total."""
    words_a = [parse_word(w) for w in WITNESS_NONUP_A]
    words_b = [parse_word(w) for w in WITNESS_NONUP_B]
    return list(combinations(words_a, 2)) + list(combinations(words_b, 2))


def separated_by_abelian(
    pairs: list[tuple[tuple[int, ...], tuple[int, ...]]],
) -> set[int]:
    return {i for i, (u, v) in enumerate(pairs) if abelian_image(u) != abelian_image(v)}


def separated_by_hom(
    pairs: list[tuple[tuple[int, ...], tuple[int, ...]]], a: Perm, b: Perm
) -> set[int]:
    return {i for i, (u, v) in enumerate(pairs) if p_eval(u, a, b) != p_eval(v, a, b)}


def search(max_n: int = 8, verbose: bool = True) -> dict[str, object]:
    """Greedy cover of the 874 required pairs by finite quotients.

    Returns a JSON-safe report: the abelian coverage, the homs found
    (as one-line cycle images), the greedy cover, and — the gate — the
    number of pairs left unseparated (0 = G-a PASS)."""
    pairs = required_pairs()
    remaining = set(range(len(pairs)))
    cover: list[dict[str, object]] = []

    ab = separated_by_abelian(pairs)
    cover.append({"quotient": f"Z/{ABELIAN_ORDER} (abelianization)", "separates": len(ab)})
    remaining -= ab
    if verbose:
        print(f"Z/42 separates {len(ab)}/{len(pairs)}; remaining {len(remaining)}", flush=True)

    homs: list[tuple[int, Perm, Perm, set[int]]] = []
    for n in range(4, max_n + 1):
        if not remaining:
            break
        reps = cycle_type_reps(n)
        found = 0
        for a in reps:
            for b in permutations(range(n)):
                if not kills_relators(a, b):
                    continue
                sep = separated_by_hom(pairs, a, b)
                if sep & remaining:
                    homs.append((n, a, b, sep))
                found += 1
        if verbose:
            print(f"S_{n}: {found} relator-killing homs (up to conj of a)", flush=True)

    # Greedy set cover over the collected homs.
    while remaining and homs:
        n, a, b, sep = max(homs, key=lambda h: len(h[3] & remaining))
        gain = len(sep & remaining)
        if gain == 0:
            break
        cover.append({"quotient": f"S_{n}", "a": a, "b": b, "separates_new": gain})
        remaining -= sep
        if verbose:
            print(f"greedy: S_{n} hom covers {gain} more; remaining {len(remaining)}", flush=True)

    report: dict[str, object] = {
        "pairs_total": len(pairs),
        "cover": cover,
        "unseparated": len(remaining),
        "gate_G_a": "PASS" if not remaining else "FAIL",
    }
    return report


def main() -> int:
    import argparse
    import json
    from pathlib import Path

    from .ledger import Ledger

    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--max-n", type=int, default=8)
    ap.add_argument("--out", type=Path, default=Path("runs"))
    args = ap.parse_args()

    report = search(args.max_n)
    (args.out / "p2_quotients.json").write_text(json.dumps(report, indent=2, default=list) + "\n")
    cover_obj = report["cover"]
    assert isinstance(cover_obj, list)
    cover_names = [str(c.get("quotient")) for c in cover_obj if isinstance(c, dict)]
    note = (
        f"P2 gate G-a: quotient search max_n={args.max_n}: "
        f"{report['gate_G_a']} — {report['unseparated']} of {report['pairs_total']} "
        f"pairs unseparated; cover {cover_names}"
    )
    Ledger(args.out / "kaplansky.ledger.jsonl").append(
        "kaplansky_p2_quotients", 0, f"quotient-search max_n={args.max_n}", None, None, note
    )
    print(note)
    return 0 if report["gate_G_a"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
