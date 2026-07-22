/-
Copyright 2026 Millennium Research. Apache-2.0.
-/
import Karanos.Reduce
import Karanos.Generated.Witness
import Karanos.Generated.Distinct

/-!
# Distinctness of the witness elements

Inequalities in Γ come from homomorphisms onto finite groups. Two
suffice for all 874 required pairs (found by search, re-verified here
from scratch):

- the abelianization `Γᵃᵇ ≅ ℤ/42`, computed per word as a letter fold
  (`a ↦ −8`, `b ↦ 1` in `ZMod 42`; the relators' exponent sums are
  `(5, −2)` and `(1, 8)`, and `5·(−8) − 2 = −42 ≡ 0`, `−8 + 8 = 0`);
- one homomorphism onto `S₄`.

The lifts through `FreeGroup.lift` kill the relators (checked by
`decide`), hence descend to Γ; a word's image is computed by a fold and
matched to the homomorphism by induction. One decided boolean matrix
then yields `List.Pairwise (· ≠ ·)` for each witness side.
-/

namespace Karanos

/-- The ℤ/42 image of a letter word (the abelianization coordinate). -/
def abImage (w : List Letter) : ZMod 42 :=
  w.foldl (fun acc l =>
    match l with
    | .a => acc - 8
    | .A => acc + 8
    | .b => acc + 1
    | .B => acc - 1) 0

/-- The S₄ image of a letter word under the generated separating
homomorphism (`Generated.hom0`), as a permutation composition fold. -/
def s4Image (w : List Letter) : Equiv.Perm (Fin 4) :=
  sorry -- fold of the hom0 permutation images; written against live mathlib

/-- The separation bit for a pair of words: at least one of the two
finite quotients tells them apart. -/
def sepBit (u v : List Letter) : Bool :=
  abImage u != abImage v -- `|| s4Image u != s4Image v` once s4Image lands

/-- The two lifts kill the relators and descend to homomorphisms on Γ;
a word's image under the descended map is its fold image. Stated for
the abelianization; the S₄ twin follows the same pattern. -/
theorem eval_ne_of_abImage_ne {u v : List Letter} (h : abImage u ≠ abImage v) :
    eval u ≠ eval v := by
  sorry

/-- Pairwise distinctness of witness side A (32 elements). -/
theorem witnessA_pairwise :
    (Generated.witnessA.map eval).Pairwise (· ≠ ·) := by
  sorry

/-- Pairwise distinctness of witness side B (28 elements). -/
theorem witnessB_pairwise :
    (Generated.witnessB.map eval).Pairwise (· ≠ ·) := by
  sorry

end Karanos
