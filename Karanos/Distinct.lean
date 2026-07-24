/-
Copyright (c) 2026 Millennium Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Millennium Research (Ibby Mian), with Claude
-/
import Karanos.Reduce
import Karanos.Generated.Witness

/-!
# Distinctness of the witness elements

Inequalities in Γ come from homomorphisms onto finite groups; two
suffice for all 874 required pairs (found by search, re-verified here
from scratch):

- the abelianization coordinate `Γ → ℤ/42` (per letter: `a ↦ −8`,
  `b ↦ +1`; the relators' images are `5·(−8) − 2 = −42 ≡ 0` and
  `−8 + 8 = 0`);
- one homomorphism onto `S₄` (as permutations of `Fin 4`).

Each lift kills the relators (checked by `decide` after case-splitting
the two-element relator set), so it descends to Γ by
`PresentedGroup.toGroup`; a word's image under the descent is its
letter-fold image, by list induction. One decided `Pairwise` over each
witness list then gives pairwise distinctness in Γ.
-/

namespace Karanos

/-! ## The abelianization coordinate ℤ/42 -/

/-- Per-letter value in `ℤ/42`. -/
def Letter.abVal : Letter → ZMod 42
  | .a => -8 | .A => 8 | .b => 1 | .B => -1

/-- The ℤ/42 image of a letter word. -/
def abImage (w : List Letter) : ZMod 42 :=
  (w.map Letter.abVal).sum

/-- Generator images for the abelianization lift. -/
def abGen : Gen → Multiplicative (ZMod 42)
  | .ga => Multiplicative.ofAdd (-8)
  | .gb => Multiplicative.ofAdd 1

theorem abGen_kills : ∀ r ∈ relators, FreeGroup.lift abGen r = 1 := by
  intro r hr
  simp only [relators, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with h | h <;> subst h <;>
    simp only [map_mul, map_pow, map_inv, FreeGroup.lift_apply_of] <;> decide

/-- The abelianization homomorphism on Γ. -/
noncomputable def abHom : Gamma →* Multiplicative (ZMod 42) :=
  PresentedGroup.toGroup abGen_kills

/-- The descent agrees with the free lift on `mk` (definitional). -/
theorem abHom_mk (x : FreeGroup Gen) :
    abHom (PresentedGroup.mk relators x) = FreeGroup.lift abGen x := rfl

/-- Letter-level compatibility of the free lift. -/
theorem lift_abGen_toFree (l : Letter) :
    FreeGroup.lift abGen l.toFree = Multiplicative.ofAdd l.abVal := by
  cases l <;> simp [Letter.toFree, Letter.abVal, FreeGroup.lift_apply_of, abGen]

/-- Word-level compatibility: the descent computes the letter fold. -/
theorem abHom_eval (w : List Letter) :
    abHom (eval w) = Multiplicative.ofAdd (abImage w) := by
  rw [eval, abHom_mk]
  induction w with
  | nil => rfl
  | cons l w ih =>
      rw [wordToFree_cons, map_mul, ih, lift_abGen_toFree]
      simp [abImage, ofAdd_add]

/-- ℤ/42 separation implies inequality in Γ. -/
theorem eval_ne_of_abImage_ne {u v : List Letter} (h : abImage u ≠ abImage v) :
    eval u ≠ eval v := fun he =>
  h (by
    have := congrArg abHom he
    rw [abHom_eval, abHom_eval] at this
    exact Multiplicative.ofAdd.injective this)

/-! ## The S₄ homomorphism -/

/-- Image of `a`: the permutation `0↦1, 1↦2, 2↦0, 3↦3`. -/
def s4a : Equiv.Perm (Fin 4) :=
  ⟨![1, 2, 0, 3], ![2, 0, 1, 3], by decide, by decide⟩

/-- Image of `b`: the permutation `0↦0, 1↦3, 2↦1, 3↦2`. -/
def s4b : Equiv.Perm (Fin 4) :=
  ⟨![0, 3, 1, 2], ![0, 2, 3, 1], by decide, by decide⟩

/-- Generator images for the S₄ lift. -/
def s4Gen : Gen → Equiv.Perm (Fin 4)
  | .ga => s4a
  | .gb => s4b

theorem s4Gen_kills : ∀ r ∈ relators, FreeGroup.lift s4Gen r = 1 := by
  intro r hr
  simp only [relators, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with h | h <;> subst h <;>
    simp only [map_mul, map_pow, map_inv, FreeGroup.lift_apply_of] <;> decide

/-- The S₄ homomorphism on Γ. -/
noncomputable def s4Hom : Gamma →* Equiv.Perm (Fin 4) :=
  PresentedGroup.toGroup s4Gen_kills

/-- Per-letter S₄ value. -/
def Letter.s4Val : Letter → Equiv.Perm (Fin 4)
  | .a => s4a | .A => s4a⁻¹ | .b => s4b | .B => s4b⁻¹

/-- The S₄ image of a letter word. -/
def s4Image (w : List Letter) : Equiv.Perm (Fin 4) :=
  (w.map Letter.s4Val).prod

/-- The descent agrees with the free lift on `mk` (definitional). -/
theorem s4Hom_mk (x : FreeGroup Gen) :
    s4Hom (PresentedGroup.mk relators x) = FreeGroup.lift s4Gen x := rfl

theorem lift_s4Gen_toFree (l : Letter) :
    FreeGroup.lift s4Gen l.toFree = l.s4Val := by
  cases l <;> simp [Letter.toFree, Letter.s4Val, FreeGroup.lift_apply_of, s4Gen]

theorem s4Hom_eval (w : List Letter) :
    s4Hom (eval w) = s4Image w := by
  rw [eval, s4Hom_mk]
  induction w with
  | nil => rfl
  | cons l w ih =>
      rw [wordToFree_cons, map_mul, ih, lift_s4Gen_toFree]
      simp [s4Image]

/-- S₄ separation implies inequality in Γ. -/
theorem eval_ne_of_s4Image_ne {u v : List Letter} (h : s4Image u ≠ s4Image v) :
    eval u ≠ eval v := fun he =>
  h (by have := congrArg s4Hom he; rwa [s4Hom_eval, s4Hom_eval] at this)

/-! ## Pairwise distinctness -/

/-- The separation bit: one of the two quotients tells the words apart. -/
def sepBit (u v : List Letter) : Bool :=
  abImage u != abImage v || s4Image u != s4Image v

theorem eval_ne_of_sepBit {u v : List Letter} (h : sepBit u v = true) :
    eval u ≠ eval v := by
  rcases Bool.or_eq_true_iff.mp h with h' | h'
  · exact eval_ne_of_abImage_ne (by simpa using h')
  · exact eval_ne_of_s4Image_ne (by simpa using h')

/-- Pairwise distinctness of witness side A (32 elements). -/
theorem witnessA_pairwise :
    (Generated.witnessA.map eval).Pairwise (· ≠ ·) := by
  rw [List.pairwise_map]
  have hbit : Generated.witnessA.Pairwise (fun u v => sepBit u v = true) := by decide
  exact hbit.imp fun h => eval_ne_of_sepBit h

/-- Pairwise distinctness of witness side B (28 elements). -/
theorem witnessB_pairwise :
    (Generated.witnessB.map eval).Pairwise (· ≠ ·) := by
  rw [List.pairwise_map]
  have hbit : Generated.witnessB.Pairwise (fun u v => sepBit u v = true) := by decide
  exact hbit.imp fun h => eval_ne_of_sepBit h

end Karanos
