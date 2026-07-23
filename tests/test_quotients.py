"""Tests for the P2 finite-quotient search: the abelianization arithmetic
is checked against first principles, the permutation machinery against
hand values, and every hom the search reports must genuinely kill the
relators (the searcher is untrusted, but it must not lie to itself)."""

from __future__ import annotations

from karanos_engine.kaplansky import RELATOR_1, RELATOR_2, parse_word
from karanos_engine.quotients import (
    ABELIAN_ORDER,
    abelian_image,
    cycle_type_reps,
    exponent_sums,
    kills_relators,
    p_eval,
    p_inv,
    p_mul,
    required_pairs,
    separated_by_abelian,
)


def test_exponent_sums_of_relators() -> None:
    assert exponent_sums(RELATOR_1) == (5, -2)
    assert exponent_sums(RELATOR_2) == (1, 8)


def test_relators_die_in_the_abelianization() -> None:
    assert abelian_image(RELATOR_1) == 0
    assert abelian_image(RELATOR_2) == 0


def test_abelian_image_is_a_homomorphism_on_samples() -> None:
    u, v = parse_word("abAB"), parse_word("bbaB")
    concat = tuple(list(u) + list(v))
    assert abelian_image(concat) == (abelian_image(u) + abelian_image(v)) % ABELIAN_ORDER


def test_perm_mul_inv() -> None:
    p = (1, 2, 0)
    assert p_mul(p, p_inv(p)) == (0, 1, 2)
    assert p_eval((0, 1), p, (0, 1, 2)) == (0, 1, 2)  # a·a⁻¹ = e


def test_cycle_type_reps_count() -> None:
    # #cycle types of S_n = #partitions of n: 5 for n=4, 7 for n=5.
    assert len(cycle_type_reps(4)) == 5
    assert len(cycle_type_reps(5)) == 7
    for rep in cycle_type_reps(5):
        assert sorted(rep) == list(range(5))


def test_trivial_hom_kills_relators_and_separates_nothing() -> None:
    e4 = (0, 1, 2, 3)
    assert kills_relators(e4, e4)
    pairs = required_pairs()
    from karanos_engine.quotients import separated_by_hom

    assert separated_by_hom(pairs, e4, e4) == set()


def test_required_pairs_count() -> None:
    assert len(required_pairs()) == 32 * 31 // 2 + 28 * 27 // 2  # 496 + 378 = 874


def test_abelianization_separates_something() -> None:
    pairs = required_pairs()
    got = separated_by_abelian(pairs)
    assert 0 < len(got) < len(pairs)  # useful but not everything
