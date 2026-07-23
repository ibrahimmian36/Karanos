"""Cayley-ball arithmetic for finitely presented groups, merge-witnessed.

Purpose: given ⟨generators | relators⟩, build the radius-R ball of the
Cayley graph well enough to (a) enumerate B(r) exactly, (b) multiply ball
elements, and (c) later extract kernel-checkable equality derivations.

Method: start from the free-group ball (a tree — trivially correct), then
close under the relators by partial Todd–Coxeter: trace every cyclic
rotation of every relator (and inverses) from every vertex; a trace that
completes inside the ball and lands elsewhere forces a merge. Coincidence
cascades are processed to fixpoint.

Soundness/completeness split, stated honestly:
- SOUND by construction: every merge is witnessed by a relator path (the
  witness is recorded), so distinct classes are never merged wrongly.
- COMPLETE only up to the chosen radii: an equality provable only via a
  long excursion can be missed, which INFLATES ball counts. Callers must
  anchor counts against independent data before trusting the table
  (kaplansky.py anchors against Gardam's published |B(4)|=161-tree and
  |B(6)|=1311). Never skip the anchor step.
"""

from __future__ import annotations

from array import array
from collections import deque
from dataclasses import dataclass


def inv(g: int) -> int:
    """Generator involution: letters are 0,1 (a, a⁻¹), 2,3 (b, b⁻¹), ..."""
    return g ^ 1


def free_reduce(word: tuple[int, ...]) -> tuple[int, ...]:
    out: list[int] = []
    for g in word:
        if out and out[-1] == inv(g):
            out.pop()
        else:
            out.append(g)
    return tuple(out)


def rotations_with_inverses(relator: tuple[int, ...]) -> list[tuple[int, ...]]:
    """All cyclic rotations of the relator and of its inverse, deduplicated."""
    seen: set[tuple[int, ...]] = set()
    inverse = tuple(inv(g) for g in reversed(relator))
    for base in (relator, inverse):
        for i in range(len(base)):
            seen.add(base[i:] + base[:i])
    return sorted(seen)


@dataclass(frozen=True)
class MergeWitness:
    """One recorded identification: tracing `relator_rotation` from (the
    class of) vertex `start` ended at a different class, so start ~ end.
    Vertex ids refer to free-tree vertices; their tree words reconstruct
    explicit group words for certificate extraction later."""

    start: int
    end: int
    relator_rotation: tuple[int, ...]
    via_determinism: bool  # True for cascade merges forced by edge clashes


class BallQuotient:
    """Quotient of the free ball of radius `tree_radius` by relator closure
    (relators traced from every vertex of distance ≤ close_radius)."""

    def __init__(
        self,
        n_generators: int,
        relators: list[tuple[int, ...]],
        tree_radius: int,
        close_radius: int,
    ) -> None:
        if close_radius > tree_radius:
            raise ValueError("close_radius cannot exceed tree_radius")
        self.n_letters = 2 * n_generators
        self.relators = [free_reduce(r) for r in relators]
        if any(not r for r in self.relators):
            raise ValueError("trivial relator")
        self.tree_radius = tree_radius
        self.close_radius = close_radius
        self.witnesses: list[MergeWitness] = []
        self._build_tree()
        self._close()

    # -- free tree ---------------------------------------------------------

    def _build_tree(self) -> None:
        letters = self.n_letters
        parent = array("i", [-1])
        letter = array("i", [-1])
        dist = array("i", [0])
        children: dict[int, int] = {}  # key = vertex * n_letters + g
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
        # union-find (path-halving), size-weighted
        self._uf = array("i", range(n))
        self._size = array("i", [1] * n)
        # classes whose edge map differs from the pristine tree
        self._patched: dict[int, dict[int, int]] = {}

    def find(self, v: int) -> int:
        uf = self._uf
        while uf[v] != v:
            uf[v] = uf[uf[v]]
            v = uf[v]
        return v

    def _tree_neighbor(self, v: int, g: int) -> int:
        if v and inv(self._letter[v]) == g:
            return self._parent[v]
        return self._children.get(v * self.n_letters + g, -1)

    def neighbor(self, c: int, g: int) -> int:
        """Edge from class-representative c along letter g; -1 if outside
        the built ball. Result is NOT normalized; callers find() it."""
        patched = self._patched.get(c)
        if patched is not None:
            return patched.get(g, -1)
        return self._tree_neighbor(c, g)

    # -- relator closure ---------------------------------------------------

    def _materialize(self, c: int) -> dict[int, int]:
        patched = self._patched.get(c)
        if patched is None:
            patched = {
                g: t for g in range(self.n_letters) if (t := self._tree_neighbor(c, g)) != -1
            }
            self._patched[c] = patched
        return patched

    def _union(
        self, a: int, b: int, witness: MergeWitness, pending: deque[tuple[int, int, MergeWitness]]
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
        self.witnesses.append(witness)
        for g, t in eb.items():
            cur = ea.get(g)
            if cur is None:
                ea[g] = t
            elif self.find(cur) != self.find(t):
                cascade = MergeWitness(cur, t, (g,), via_determinism=True)
                pending.append((cur, t, cascade))
        return True

    def _close(self) -> None:
        rots = [rot for rel in self.relators for rot in rotations_with_inverses(rel)]
        close_vertices = [v for v in range(self.n_vertices) if self._dist[v] <= self.close_radius]
        pending: deque[tuple[int, int, MergeWitness]] = deque()
        changed = True
        while changed:
            changed = False
            for v in close_vertices:
                for rot in rots:
                    c = self.find(v)
                    ok = True
                    for g in rot:
                        nxt = self.neighbor(c, g)
                        if nxt == -1:
                            ok = False
                            break
                        c = self.find(nxt)
                    if ok and c != self.find(v):
                        pending.append((v, c, MergeWitness(v, c, rot, via_determinism=False)))
                        while pending:
                            x, y, w = pending.popleft()
                            if self._union(x, y, w, pending):
                                changed = True

    # -- queries -----------------------------------------------------------

    def ball(self, radius: int) -> dict[int, tuple[int, ...]]:
        """Class-representative -> geodesic word, for the Cayley ball B(radius).

        Distances are graph distances in the QUOTIENT, which can only be
        ≤ tree distance; radius must leave room for products, enforced by
        callers."""
        root = self.find(0)
        out: dict[int, tuple[int, ...]] = {root: ()}
        frontier = [root]
        for _ in range(radius):
            nxt: list[int] = []
            for c in frontier:
                for g in range(self.n_letters):
                    t = self.neighbor(c, g)
                    if t == -1:
                        continue
                    rt = self.find(t)
                    if rt not in out:
                        out[rt] = out[c] + (g,)
                        nxt.append(rt)
            frontier = nxt
        return out

    def walk(self, start_class: int, word: tuple[int, ...]) -> int:
        """Class of start·word, or -1 if the path leaves the built ball."""
        c = self.find(start_class)
        for g in word:
            t = self.neighbor(c, g)
            if t == -1:
                return -1
            c = self.find(t)
        return c

    def class_of_word(self, word: tuple[int, ...]) -> int:
        return self.walk(self.find(0), free_reduce(word))
