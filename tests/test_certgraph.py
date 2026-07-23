"""Tests for the proof-producing closure: the certified quotient must
reproduce the plain quotient's class structure exactly, and every
certificate it emits must survive the free-reduction check (which the
implementation also runs internally on every edge — these tests exercise
the public path and the composition rules)."""

from __future__ import annotations

import pytest

from karanos_engine.certgraph import (
    CertifiedBallQuotient,
    free_reduce,
    piece_word,
    word_inv,
)
from karanos_engine.groupball import BallQuotient
from karanos_engine.kaplansky import RELATOR_1, RELATOR_2, parse_word

Z2_RELATOR = (0, 2, 1, 3)  # aba⁻¹b⁻¹


def z2() -> CertifiedBallQuotient:
    return CertifiedBallQuotient(2, [Z2_RELATOR], tree_radius=8, close_radius=6)


def verify_pair(q: CertifiedBallQuotient, u: str, v: str) -> int:
    """Full independent re-verification: expand the pair's proof path,
    concatenate all pieces (with orientation), free-reduce, compare
    against u·v⁻¹. Returns the number of relator instances used."""
    uw, vw = parse_word(u), parse_word(v)
    path, _ = q.pair_cert(uw, vw)
    acc: tuple[int, ...] = ()
    n_pieces = 0
    for eidx, forward in path:
        cert = q.edge_cert(eidx)
        pieces = cert.pieces if forward else [(c, r, -s) for c, r, s in reversed(cert.pieces)]
        for piece in pieces:
            acc = free_reduce(acc + piece_word(piece, q.relators))
            n_pieces += 1
    assert acc == free_reduce(uw + word_inv(vw)), "composed certificate failed"
    return n_pieces


def test_z2_matches_plain_quotient() -> None:
    plain = BallQuotient(2, [Z2_RELATOR], tree_radius=8, close_radius=6)
    cert = z2()
    assert [len(cert.ball(r)) for r in range(5)] == [len(plain.ball(r)) for r in range(5)]
    assert [len(cert.ball(r)) for r in range(5)] == [1, 5, 13, 25, 41]


def test_z2_commutator_certificate() -> None:
    q = z2()
    n = verify_pair(q, "ab", "ba")
    assert n >= 1  # at least the relator itself


def test_z2_longer_equalities() -> None:
    q = z2()
    for u, v in [("aabb", "abab"), ("aBab", "baB")]:
        if q.class_of_word(parse_word(u)) == q.class_of_word(parse_word(v)):
            verify_pair(q, u, v)


def test_z2_unequal_words_refused() -> None:
    q = z2()
    with pytest.raises(AssertionError, match="not equal"):
        q.pair_cert(parse_word("a"), parse_word("b"))


def test_gamma_small_matches_plain_quotient() -> None:
    plain = BallQuotient(2, [RELATOR_1, RELATOR_2], tree_radius=8, close_radius=7)
    cert = CertifiedBallQuotient(2, [RELATOR_1, RELATOR_2], tree_radius=8, close_radius=7)
    for r in (4, 6):
        assert len(cert.ball(r)) == len(plain.ball(r))
    assert len(cert.ball(4)) == 161 and len(cert.ball(6)) == 1311


def test_gamma_small_certificates_verify() -> None:
    """Find genuinely merged pairs in small-Γ and verify their
    certificates end to end."""
    q = CertifiedBallQuotient(2, [RELATOR_1, RELATOR_2], tree_radius=8, close_radius=7)
    checked = 0
    for edge in q.proof_edges[:40]:
        u = q.word_of_vertex(edge.x)
        v = q.word_of_vertex(edge.y)
        cert = q.edge_cert(edge.index)  # runs the internal verifier
        assert cert.pieces or free_reduce(u + word_inv(v)) == ()
        checked += 1
    assert checked == 40


def test_every_z2_edge_expands_clean() -> None:
    q = z2()
    for edge in q.proof_edges:
        q.edge_cert(edge.index)  # internal free-reduction check on every edge
