"""Tests for the GF(2) kernel test (Phase G0): the linear-algebra route
must find every known zero divisor (positive controls), must agree with
brute-force enumeration wherever brute force is affordable, and every
hit must survive the independent parity recount."""

from __future__ import annotations

import random
from itertools import combinations

import pytest

from karanos_engine.gf2 import build_rows, kernel_vector, product_parity, zd_kernel
from karanos_engine.groupball import BallQuotient
from karanos_engine.kaplansky import RELATOR_1, RELATOR_2


def cyclic(n: int):
    def product(x: int, y: int) -> int:
        return (x + y) % n

    return product


# -- positive controls: known zero divisors must be FOUND ------------------


@pytest.mark.parametrize(
    ("n", "a"),
    [(2, [0, 1]), (3, [0, 1, 2]), (3, [0, 1]), (4, [0, 2]), (6, [0, 3])],
)
def test_cyclic_zero_divisors_found(n: int, a: list[int]) -> None:
    region = list(range(n))
    b = zd_kernel(a, region, cyclic(n))
    assert b is not None, f"known zero divisor in F2[C_{n}] not found"
    assert product_parity(a, b, cyclic(n)) == set()


def test_kernel_vector_is_a_witness_not_just_a_flag() -> None:
    # C_4, a = 1 + g^2: kernel must decode to an explicit b with a·b = 0.
    b = zd_kernel([0, 2], [0, 1, 2, 3], cyclic(4))
    assert b is not None and len(b) >= 2
    assert product_parity([0, 2], b, cyclic(4)) == set()


# -- agreement with brute force where brute force is affordable ------------


@pytest.mark.parametrize("n", [2, 3, 4, 5, 6])
def test_matches_brute_force_on_cyclic_groups(n: int) -> None:
    """For every nonzero a in F2[C_n]: kernel test says a is a left zero
    divisor iff brute force over all nonzero b finds one."""
    region = list(range(n))
    product = cyclic(n)
    for r in range(1, n + 1):
        for a in combinations(region, r):
            kernel = zd_kernel(list(a), region, product)
            brute = any(
                not product_parity(list(a), list(b), product)
                for s in range(1, n + 1)
                for b in combinations(region, s)
            )
            assert (kernel is not None) == brute
            if kernel is not None:
                assert product_parity(list(a), kernel, product) == set()


def test_torsion_free_z2_has_no_kernel_in_small_ball() -> None:
    """F2[Z^2] has no zero divisors at all (torsion-free abelian), so no
    a over B(2) may have a kernel with b ranging over B(3)."""
    z2 = BallQuotient(2, [(0, 2, 1, 3)], tree_radius=8, close_radius=6)
    b2 = sorted(z2.ball(2))
    b3 = sorted(z2.ball(3))
    words = z2.ball(3)

    def product(x: int, y: int) -> int:
        c = z2.walk(x, words[y])
        assert c != -1
        return c

    rng = random.Random(0)
    for _ in range(30):
        a = rng.sample(b2, rng.randint(1, 6))
        assert zd_kernel(a, b3, product) is None


# -- Γ at small radius: kernel test vs the parity recount ------------------


def test_gamma_small_radius_agreement() -> None:
    """On Γ at radius 2 (affordable), the kernel verdict must match brute
    force over subsets of B(2) up to size 3, for random small a."""
    gam = BallQuotient(2, [RELATOR_1, RELATOR_2], tree_radius=6, close_radius=5)
    b2 = sorted(gam.ball(2))
    words = gam.ball(3) | gam.ball(2)

    def product(x: int, y: int) -> int:
        c = gam.walk(x, words[y] if y in words else gam.ball(2)[y])
        assert c != -1
        return c

    region = b2
    rng = random.Random(1)
    for _ in range(10):
        a = rng.sample(b2, rng.randint(2, 4))
        kernel = zd_kernel(a, region, product)
        brute = any(
            not product_parity(a, list(b), product)
            for s in range(1, 4)
            for b in combinations(region, s)
        )
        if kernel is not None:
            assert product_parity(a, kernel, product) == set()
        if brute:
            assert kernel is not None  # kernel search is complete over the region
        # note: kernel may exist with |b| > 3, which brute (capped at 3) misses.


# -- extended-region guards (cheap: must reject before any table work) -----


@pytest.mark.parametrize("radius", [-1, 9, 100])
def test_region_ball_rejects_out_of_range_radius(radius: int) -> None:
    from karanos_engine.kaplansky import region_ball

    with pytest.raises(ValueError, match="region radius"):
        region_ball(radius)


# -- custom tables and the a-pool regression -------------------------------


def _small_table(tmp_path, tree: int, close: int):
    import pickle

    quotient = BallQuotient(2, [RELATOR_1, RELATOR_2], tree_radius=tree, close_radius=close)
    path = tmp_path / f"t{tree}c{close}.pickle"
    with path.open("wb") as fh:
        pickle.dump(quotient, fh)
    return path


def test_region_setup_pool_not_capped_by_region(tmp_path) -> None:
    """Regression for the 2026-07-21 slice-b6w2 mislabeling: with
    a_radius > region_radius the a-pool must span its full radius, not
    get silently truncated to the region ball."""
    from karanos_engine.gf2 import _region_setup

    table = _small_table(tmp_path, tree=8, close=7)
    ext, region, pool, tier, label = _region_setup(4, 2, tmp_path, table)
    assert len(pool) == 161  # full B(4), NOT capped to B(2)
    assert len(region) == 17  # B(2)
    assert tier == "converged"  # 4 + 2 = 6 ≤ close 7, judged from the table's own radii
    assert label == "t8c7"
    assert ext.quotient.tree_radius == 8


def test_load_table_rejects_unanchored_table(tmp_path) -> None:
    """A table too shallow to reproduce the published anchors must be
    refused at load, not trusted downstream."""
    from karanos_engine.kaplansky import load_table

    bad = _small_table(tmp_path, tree=6, close=4)
    with pytest.raises(AssertionError, match="ANCHOR FAILED"):
        load_table(bad)


def test_max_region_radius_scales_with_close_radius(tmp_path) -> None:
    from karanos_engine.kaplansky import load_table, max_region_radius

    table = _small_table(tmp_path, tree=8, close=7)
    assert max_region_radius(load_table(table)) == 5


def test_witness_constants_are_the_ledgered_pair() -> None:
    from karanos_engine.kaplansky import WITNESS_NONUP_A, WITNESS_NONUP_B, parse_word

    assert len(WITNESS_NONUP_A) == 32 and len(WITNESS_NONUP_B) == 28
    for words in (WITNESS_NONUP_A, WITNESS_NONUP_B):
        parsed = [parse_word(w) for w in words]
        assert len(set(parsed)) == len(parsed)  # no duplicate elements
        assert max(len(p) for p in parsed) == 6  # radius-6 supports


# -- extension candidates (witness-superset campaign) ----------------------


def test_extension_candidates_counts_and_shape() -> None:
    from math import comb

    from karanos_engine.gf2 import extension_candidates

    base, pool = [10, 20, 30], [1, 2, 3, 4]
    got = list(extension_candidates(base, pool, 2))
    assert len(got) == comb(4, 1) + comb(4, 2)
    assert all(c[:3] == (10, 20, 30) for c in got)  # every candidate contains the base
    assert all(len(c) == len(set(c)) for c in got)  # no duplicates within a candidate
    assert len(set(got)) == len(got)  # no duplicate candidates
    assert {len(c) for c in got} == {4, 5}  # weights base+1 and base+2


def test_extension_candidates_zero_extra_is_empty() -> None:
    from karanos_engine.gf2 import extension_candidates

    assert list(extension_candidates([1], [2, 3], 0)) == []


# -- mechanics -------------------------------------------------------------


def test_build_rows_refuses_duplicate_elements() -> None:
    with pytest.raises(AssertionError):
        build_rows([0, 0], [0, 1], cyclic(3))


def test_kernel_vector_none_on_independent_rows() -> None:
    rows, n_cols = build_rows([0], [0, 1, 2], cyclic(3))
    assert n_cols == 3
    assert kernel_vector(rows, 3) is None


def test_kernel_early_exit_returns_nonempty_support() -> None:
    rows, _ = build_rows([0, 1], [0, 1], cyclic(2))
    combo = kernel_vector(rows, 2)
    assert combo == [0, 1]
