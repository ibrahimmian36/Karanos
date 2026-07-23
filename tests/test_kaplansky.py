"""Tests for the Kaplansky program substrate: ball quotients anchored
against independent ground truth, encodings checked pointwise (a given
(A,B) extends to a satisfying assignment iff the property really holds),
and the calibration scorers on known zero divisors."""

from __future__ import annotations

from karanos_engine.groupball import BallQuotient, free_reduce, rotations_with_inverses
from karanos_engine.kaplansky import (
    RELATOR_1,
    RELATOR_2,
    GammaBall,
    encode_nonup,
    encode_zd_f2,
    format_word,
    parse_word,
)

# -- groupball -------------------------------------------------------------


def test_free_reduce() -> None:
    assert free_reduce((0, 1, 2)) == (2,)
    assert free_reduce((0, 2, 3, 1)) == ()
    assert parse_word("aAbB") == ()
    assert format_word(parse_word("abAB")) == "abAB"


def test_rotations_include_inverses() -> None:
    rots = rotations_with_inverses((0, 2))
    assert (2, 0) in rots and (3, 1) in rots


def test_free_group_balls_are_trees() -> None:
    free = BallQuotient(2, [(0, 0, 0, 0, 0, 0, 0, 0)], tree_radius=4, close_radius=0)
    # close_radius 0 still traces from the root; a⁸ needs radius ≥ 4 to
    # close, so nothing merges and counts are free: 1, 5, 17, 53, 161.
    assert [len(free.ball(r)) for r in range(5)] == [1, 5, 17, 53, 161]


def test_z2_ball_sizes() -> None:
    z2 = BallQuotient(2, [(0, 2, 1, 3)], tree_radius=8, close_radius=6)
    assert [len(z2.ball(r)) for r in range(5)] == [1, 5, 13, 25, 41]


def test_z2_multiplication_commutes() -> None:
    z2 = BallQuotient(2, [(0, 2, 1, 3)], tree_radius=8, close_radius=6)
    ab = z2.class_of_word((0, 2))
    ba = z2.class_of_word((2, 0))
    assert ab == ba != -1


def test_gamma_smoke_anchors() -> None:
    """The published anchors at reduced radii: B(4) free (161), |B(6)| =
    1311 (Gardam, SMRI slides 2021-10-05). The full-depth build in
    kaplansky.build_gamma re-checks the same anchors at radius 12/10."""
    gam = BallQuotient(2, [RELATOR_1, RELATOR_2], tree_radius=8, close_radius=7)
    sizes = [len(gam.ball(r)) for r in range(7)]
    assert sizes[:5] == [1, 5, 17, 53, 161]
    assert sizes[6] == 1311


# -- encodings, checked pointwise -----------------------------------------


def _extend_and_check(
    clauses: list[list[int]], n_classes: int, a_idx: set[int], b_idx: set[int]
) -> bool:
    """Try to satisfy the CNF with x/y fixed by (a_idx, b_idx), extending
    aux variables greedily by unit propagation; returns True iff a total
    satisfying assignment is found. Sound for these encodings because
    every aux variable is definitionally forced once x/y are fixed."""
    assign: dict[int, bool] = {}
    for i in range(n_classes):
        assign[i + 1] = i in a_idx
        assign[n_classes + i + 1] = i in b_idx

    def value(lit: int) -> bool | None:
        v = assign.get(abs(lit))
        if v is None:
            return None
        return v if lit > 0 else not v

    changed = True
    while changed:
        changed = False
        for cl in clauses:
            vals = [value(lit) for lit in cl]
            if any(v is True for v in vals):
                continue
            unknown = [lit for lit, v in zip(cl, vals, strict=True) if v is None]
            if not unknown:
                return False  # clause falsified
            if len(unknown) == 1:
                lit = unknown[0]
                assign[abs(lit)] = lit > 0
                changed = True
    # Aux vars not forced by propagation are only capped from above in
    # these encodings (Sinz registers), so "false" is always safe for them.
    for cl in clauses:
        for lit in cl:
            if abs(lit) not in assign:
                assign[abs(lit)] = False
    return all(any(value(lit) is True for lit in cl) for cl in clauses)


def _tiny_gamma() -> GammaBall:
    """A GammaBall over ℤ² — small, orderable (every pair HAS a unique
    product), perfect negative control for the encodings."""
    return GammaBall(BallQuotient(2, [(0, 2, 1, 3)], tree_radius=6, close_radius=4), 1)


def test_encode_nonup_rejects_up_pairs_in_z2() -> None:
    tiny = _tiny_gamma()
    clauses, _top, n = encode_nonup(tiny, 1, normalize=False)
    # ℤ² is orderable: no (A,B) can satisfy the no-unique-product CNF.
    idx = range(n)
    for a_mask in range(1, 2**n):
        for b_mask in range(1, 2**n):
            a = {i for i in idx if a_mask >> i & 1}
            b = {i for i in idx if b_mask >> i & 1}
            assert not _extend_and_check(clauses, n, a, b)


def test_encode_zd_parity_matches_scorer_logic() -> None:
    tiny = _tiny_gamma()
    clauses, _top, n = encode_zd_f2(tiny, 1, min_side=1, min_sum=2, normalize=False)
    classes = [c for c in tiny.classes if len(tiny.words[c]) <= 1]
    for a_mask in range(1, 2**n):
        for b_mask in range(1, 2**n):
            a = {i for i in idx_set(a_mask, n)}
            b = {i for i in idx_set(b_mask, n)}
            mult: dict[int, int] = {}
            for i in a:
                for j in b:
                    p = tiny.product_class(classes[i], classes[j])
                    mult[p] = mult.get(p, 0) + 1
            all_even = all(m % 2 == 0 for m in mult.values())
            meets_floor = len(a) + len(b) >= 2
            expected = all_even and meets_floor
            assert _extend_and_check(clauses, n, a, b) == expected


def idx_set(mask: int, n: int) -> set[int]:
    return {i for i in range(n) if mask >> i & 1}


# -- calibration note ------------------------------------------------------
# The calibration zero divisors (F₂[C₂], ℚ[C₃]) and their Lean certificates
# were validated through the search engine's problem registry during Phase 1
# and are recorded in runs/kaplansky.ledger.jsonl. The mathematical content
# they cover — that the kernel test finds known zero divisors — is tested
# directly and more thoroughly in test_gf2.py, so nothing is lost here.
