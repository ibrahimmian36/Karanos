"""Proof-producing ball closure — the equality half of the P2 certificate.

For words u, v with u = v in Γ, the Lean certificate needs the free-group
identity  u·v⁻¹ = ∏ gᵢ rᵢ^{±1} gᵢ⁻¹  (rᵢ a relator), checkable by word
reduction alone. This module rebuilds the BallQuotient closure with
bookkeeping that makes those identities extractable:

- every edge of the quotient graph remembers the TREE edge it descends
  from (tree edges are free equalities: word(t) = reduce(word(p)·g), so
  they cost nothing in a certificate);
- every merge adds an edge to a PROOF FOREST labeled with its reason: a
  relator trace contributes exactly one conjugated relator plus
  normalization sub-certificates; a cascade merge contributes zero
  relators (its conjugations cancel freely: (Xs)(Ys)⁻¹ = XY⁻¹).

Certificates compose along proof-forest paths; expansion references only
strictly earlier merges, so the recursion is well-founded. Output is a
DAG — one lemma per used proof edge, compositions per needed pair — the
anti-blowup measure and the natural Lean shape at once. Every edge
lemma is self-verified here by free reduction BEFORE Lean ever sees it;
compositions then telescope by construction.

This class duplicates the parent's closure loop deliberately: the
production BallQuotient stays byte-for-byte untouched (it anchors the
running search), and the certified rebuild re-verifies the anchors
itself before anything downstream trusts it.
"""

from __future__ import annotations

from array import array
from collections import deque
from dataclasses import dataclass, field

from .groupball import free_reduce, inv, rotations_with_inverses

Word = tuple[int, ...]
# A certificate piece: (conjugator word, relator index 0/1, sign +1/-1).
Piece = tuple[Word, int, int]


def word_inv(w: Word) -> Word:
    return tuple(inv(g) for g in reversed(w))


def piece_word(piece: Piece, relators: list[Word]) -> Word:
    conj, ridx, sign = piece
    rel = relators[ridx] if sign > 0 else word_inv(relators[ridx])
    return free_reduce(conj + rel + word_inv(conj))


@dataclass
class TraceReason:
    """Merge from tracing `rotation` (a cyclic rotation of a relator or
    its inverse) from vertex `start`: the path used tree edges
    (source_vertex, target_vertex) per letter, entering each step at
    source_vertex which is class-equal to the previous target."""

    start: int
    rotation: Word
    rel_index: int
    rel_sign: int
    prefix: Word  # rotation = prefix⁻¹ · r^sign · prefix (freely)
    steps: list[tuple[int, int]]  # (source_vertex, target_vertex) per letter


@dataclass
class CascadeReason:
    """Merge forced by an edge clash during a union: vertices p1, p2 were
    already class-equal and both carry tree edges via the same letter to
    the two endpoints — whose equality certificate is explain(p1, p2)
    verbatim (right-conjugation cancels freely)."""

    p1: int
    p2: int


@dataclass
class ProofEdge:
    x: int  # vertex
    y: int  # vertex
    reason: TraceReason | CascadeReason
    index: int  # creation order; expansions reference strictly smaller indices


@dataclass
class EdgeCert:
    """Expanded, self-verified certificate for one proof edge:
    word(x)·word(y)⁻¹ = ∏ pieces (as free words)."""

    pieces: list[Piece] = field(default_factory=list)
    letters: int = 0  # total letter count over pieces (the size measure)


class CertifiedBallQuotient:
    """BallQuotient's algorithm with proof production. Kept structurally
    parallel to groupball.BallQuotient (same tree, same closure order) so
    the class partition it computes is checked against expectations by
    callers via ball counts."""

    def __init__(
        self,
        n_generators: int,
        relators: list[Word],
        tree_radius: int,
        close_radius: int,
    ) -> None:
        if close_radius > tree_radius:
            raise ValueError("close_radius cannot exceed tree_radius")
        self.n_letters = 2 * n_generators
        self.relators = [free_reduce(r) for r in relators]
        self.tree_radius = tree_radius
        self.close_radius = close_radius
        # rotation -> (rel_index, sign, prefix) with rotation = p⁻¹ r^s p
        self._rot_info: dict[Word, tuple[int, int, Word]] = {}
        for ridx, rel in enumerate(self.relators):
            for sign, base in ((1, rel), (-1, word_inv(rel))):
                for i in range(len(base)):
                    rot = base[i:] + base[:i]
                    self._rot_info.setdefault(rot, (ridx, sign, base[:i]))
        self.proof_edges: list[ProofEdge] = []
        self._proof_adj: dict[int, list[tuple[int, int]]] = {}  # vertex -> [(other, edge_idx)]
        self._edge_cert_memo: dict[int, EdgeCert] = {}
        self._build_tree()
        self._close()

    # -- free tree (identical layout to groupball) ---------------------------

    def _build_tree(self) -> None:
        letters = self.n_letters
        parent = array("i", [-1])
        letter = array("i", [-1])
        dist = array("i", [0])
        children: dict[int, int] = {}
        frontier = [0]
        n = 1
        for d in range(1, self.tree_radius + 1):
            nxt: list[int] = []
            for v in frontier:
                banned = inv(letter[v]) if v else -1
                for g in range(letters):
                    if g == banned:
                        continue
                    children[v * letters + g] = n
                    parent.append(v)
                    letter.append(g)
                    dist.append(d)
                    nxt.append(n)
                    n += 1
            frontier = nxt
        self.n_vertices = n
        self._parent = parent
        self._letter = letter
        self._dist = dist
        self._children = children
        self._uf = array("i", range(n))
        self._size = array("i", [1] * n)
        # class edge maps: letter -> (target_vertex, source_vertex); the
        # source is the vertex whose TREE edge this entry descends from.
        self._patched: dict[int, dict[int, tuple[int, int]]] = {}

    def find(self, v: int) -> int:
        uf = self._uf
        while uf[v] != v:
            uf[v] = uf[uf[v]]
            v = uf[v]
        return v

    def word_of_vertex(self, v: int) -> Word:
        out: list[int] = []
        while v:
            out.append(self._letter[v])
            v = self._parent[v]
        return tuple(reversed(out))

    def vertex_of_word(self, word: Word) -> int:
        w = free_reduce(word)
        if len(w) > self.tree_radius:
            raise ValueError("word longer than the built tree")
        v = 0
        for g in w:
            v = self._children[v * self.n_letters + g]
        return v

    def _tree_neighbor(self, v: int, g: int) -> int:
        if v and inv(self._letter[v]) == g:
            return self._parent[v]
        return self._children.get(v * self.n_letters + g, -1)

    def _edge(self, c: int, g: int) -> tuple[int, int]:
        """(target_vertex, source_vertex) for class-rep c via g; (-1, -1)
        if outside the ball. Target is NOT normalized."""
        patched = self._patched.get(c)
        if patched is not None:
            return patched.get(g, (-1, -1))
        t = self._tree_neighbor(c, g)
        return (t, c) if t != -1 else (-1, -1)

    def _materialize(self, c: int) -> dict[int, tuple[int, int]]:
        patched = self._patched.get(c)
        if patched is None:
            patched = {}
            for g in range(self.n_letters):
                t = self._tree_neighbor(c, g)
                if t != -1:
                    patched[g] = (t, c)
            self._patched[c] = patched
        return patched

    # -- proof forest --------------------------------------------------------

    def _add_proof_edge(self, x: int, y: int, reason: TraceReason | CascadeReason) -> None:
        edge = ProofEdge(x, y, reason, len(self.proof_edges))
        self.proof_edges.append(edge)
        self._proof_adj.setdefault(x, []).append((y, edge.index))
        self._proof_adj.setdefault(y, []).append((x, edge.index))

    def explain(self, u: int, v: int, limit: int | None = None) -> list[tuple[int, bool]]:
        """Path from vertex u to vertex v in the proof forest, as
        (edge_index, forward) steps, using only edges with index < limit
        (an edge's reason may only cite strictly earlier merges — such a
        path always exists, since the cited pair was class-equal before
        the edge was created). BFS — paths are short in practice and
        correctness beats cleverness here."""
        if u == v:
            return []
        cap = len(self.proof_edges) if limit is None else limit
        prev: dict[int, tuple[int, int, bool]] = {u: (-1, -1, True)}
        queue = deque([u])
        while queue:
            x = queue.popleft()
            for y, eidx in self._proof_adj.get(x, ()):
                if y in prev or eidx >= cap:
                    continue
                prev[y] = (x, eidx, self.proof_edges[eidx].x == x)
                if y == v:
                    path: list[tuple[int, bool]] = []
                    cur = v
                    while cur != u:
                        px, eidx2, fwd = prev[cur]
                        path.append((eidx2, fwd))
                        cur = px
                    path.reverse()
                    return path
                queue.append(y)
        raise AssertionError(f"vertices {u} and {v} are not connected in the proof forest")

    # -- closure with proof production --------------------------------------

    def _union(
        self,
        a: int,
        b: int,
        pending: deque[tuple[int, int, CascadeReason]],
    ) -> bool:
        ra, rb = self.find(a), self.find(b)
        if ra == rb:
            return False
        if self._size[ra] < self._size[rb]:
            ra, rb = rb, ra
        ea, eb = self._materialize(ra), self._materialize(rb)
        self._uf[rb] = ra
        self._size[ra] += self._size[rb]
        del self._patched[rb]
        for g, (t2, p2) in eb.items():
            got = ea.get(g)
            if got is None:
                ea[g] = (t2, p2)
            else:
                t1, p1 = got
                if self.find(t1) != self.find(t2):
                    pending.append((t1, t2, CascadeReason(p1, p2)))
        return True

    def _close(self) -> None:
        rots = [rot for rel in self.relators for rot in rotations_with_inverses(rel)]
        close_vertices = [v for v in range(self.n_vertices) if self._dist[v] <= self.close_radius]
        pending: deque[tuple[int, int, CascadeReason]] = deque()
        changed = True
        while changed:
            changed = False
            for v in close_vertices:
                for rot in rots:
                    c = self.find(v)
                    steps: list[tuple[int, int]] = []
                    ok = True
                    for g in rot:
                        t, src = self._edge(c, g)
                        if t == -1:
                            ok = False
                            break
                        steps.append((src, t))
                        c = self.find(t)
                    if ok and c != self.find(v):
                        ridx, sign, prefix = self._rot_info[rot]
                        end_vertex = steps[-1][1]
                        self._add_proof_edge(
                            v,
                            end_vertex,
                            TraceReason(v, rot, ridx, sign, prefix, steps),
                        )
                        if self._union(v, end_vertex, pending):
                            changed = True
                        while pending:
                            x, y, why = pending.popleft()
                            if self.find(x) != self.find(y):
                                self._add_proof_edge(x, y, why)
                                if self._union(x, y, pending):
                                    changed = True

    # -- queries (parallel to groupball) ------------------------------------

    def ball(self, radius: int) -> dict[int, Word]:
        root = self.find(0)
        out: dict[int, Word] = {root: ()}
        frontier = [root]
        for _ in range(radius):
            nxt: list[int] = []
            for c in frontier:
                for g in range(self.n_letters):
                    t, _src = self._edge(c, g)
                    if t == -1:
                        continue
                    rt = self.find(t)
                    if rt not in out:
                        out[rt] = out[c] + (g,)
                        nxt.append(rt)
            frontier = nxt
        return out

    def class_of_word(self, word: Word) -> int:
        c = self.find(0)
        for g in free_reduce(word):
            t, _src = self._edge(c, g)
            if t == -1:
                return -1
            c = self.find(t)
        return c

    # -- certificate expansion ----------------------------------------------

    def edge_cert(self, eidx: int, _memo: dict[int, EdgeCert] | None = None) -> EdgeCert:
        """Certificate for proof edge eidx: word(x)·word(y)⁻¹ = ∏ pieces,
        self-verified by free reduction. Memoized; recursion touches only
        strictly earlier edges."""
        if _memo is None:
            _memo = self._edge_cert_memo
        cached = _memo.get(eidx)
        if cached is not None:
            return cached
        edge = self.proof_edges[eidx]
        pieces: list[Piece] = []
        if isinstance(edge.reason, CascadeReason):
            pieces = self._pair_pieces(edge.reason.p1, edge.reason.p2, eidx, _memo)
        else:
            tr = edge.reason
            w0 = self.word_of_vertex(tr.start)
            # word(v0) ~ word(v0)·rot: one conjugated relator, with the
            # rotation folded into the conjugator via rot = p⁻¹ r^s p.
            conj = free_reduce(w0 + word_inv(tr.prefix))
            # word(v0)·word(v0·rot)⁻¹ = v0·rot⁻¹·v0⁻¹ — the INVERSE of the
            # traced rotation, hence the flipped sign.
            pieces.append((conj, tr.rel_index, -tr.rel_sign))
            # Rewrite word(v0)·rot to word(end): per letter, jump to the
            # tree-edge source (class-equal, cert conjugation cancels on
            # the right), then the tree edge itself is free.
            at = tr.start
            for src, tgt in tr.steps:
                pieces.extend(self._pair_pieces(at, src, eidx, _memo))
                at = tgt
        cert = EdgeCert(pieces, sum(2 * len(c) + len(self.relators[r]) for c, r, _ in pieces))
        self._verify_edge(edge, cert)
        _memo[eidx] = cert
        return cert

    def _pair_pieces(self, u: int, v: int, limit: int, memo: dict[int, EdgeCert]) -> list[Piece]:
        """Pieces for word(u)·word(v)⁻¹ via the proof forest, using only
        edges with index < limit (well-foundedness guard)."""
        out: list[Piece] = []
        for eidx, forward in self.explain(u, v, limit):
            sub = self.edge_cert(eidx, memo).pieces
            if forward:
                out.extend(sub)
            else:
                out.extend((c, r, -s) for c, r, s in reversed(sub))
        return out

    def _verify_edge(self, edge: ProofEdge, cert: EdgeCert) -> None:
        acc: Word = ()
        for piece in cert.pieces:
            acc = free_reduce(acc + piece_word(piece, self.relators))
        want = free_reduce(self.word_of_vertex(edge.x) + word_inv(self.word_of_vertex(edge.y)))
        if acc != want:
            raise AssertionError(f"edge {edge.index} certificate FAILED free-reduction check")

    def flat_pieces(self, u_word: Word, v_word: Word) -> list[Piece]:
        """Flattened, oriented pieces certifying u = v directly (composing
        the proof-forest path), re-verified here by free reduction before
        being handed to any emitter."""
        path, _ = self.pair_cert(u_word, v_word)
        pieces: list[Piece] = []
        for eidx, forward in path:
            cert = self.edge_cert(eidx).pieces
            pieces.extend(cert if forward else [(c, r, -s) for c, r, s in reversed(cert)])
        acc: Word = ()
        for piece in pieces:
            acc = free_reduce(acc + piece_word(piece, self.relators))
        want = free_reduce(tuple(u_word) + word_inv(tuple(v_word)))
        if acc != want:
            raise AssertionError("flattened certificate failed free-reduction check")
        return pieces

    def pair_cert(self, u_word: Word, v_word: Word) -> tuple[list[tuple[int, bool]], int]:
        """Certificate for u = v in Γ as a proof-forest path (edge DAG
        references), with every referenced edge expanded and verified.
        Returns (path, total_new_letters_expanded)."""
        u, v = self.vertex_of_word(u_word), self.vertex_of_word(v_word)
        if self.find(u) != self.find(v):
            raise AssertionError("words are not equal in the quotient — no certificate exists")
        before = sum(c.letters for c in self._edge_cert_memo.values())
        path = self.explain(u, v)
        for eidx, _fwd in path:
            self.edge_cert(eidx)
        after = sum(c.letters for c in self._edge_cert_memo.values())
        return path, after - before
