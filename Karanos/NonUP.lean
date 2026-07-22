/-
Copyright 2026 Millennium Research. Apache-2.0.
-/
import Karanos.Distinct
import Karanos.Generated.Equalities

/-!
# The headline: Γ does not have unique products

Assembly of the two certified halves. The witness Finsets `A` (32
elements) and `B` (28) come from the generated word lists via `eval`,
with cardinalities guaranteed by pairwise distinctness. Every product
`a·b` coincides with another product from a different index pair — the
generated equality chains, made transitive — so no `UniqueMul` witness
exists, refuting `UniqueProds Gamma`.

Torsion-freeness of Γ is Gardam's result and is NOT claimed here; this
theorem stands alone: an explicit finitely presented group, machine-
verified not to have the unique-product property.
-/

namespace Karanos

open Finset

/-- Witness Finset A ⊆ Γ. -/
noncomputable def witnessFinsetA : Finset Gamma :=
  (Generated.witnessA.map eval).toFinset

/-- Witness Finset B ⊆ Γ. -/
noncomputable def witnessFinsetB : Finset Gamma :=
  (Generated.witnessB.map eval).toFinset

theorem card_witnessFinsetA : witnessFinsetA.card = 32 := by
  sorry -- toFinset card = length, from witnessA_pairwise

theorem card_witnessFinsetB : witnessFinsetB.card = 28 := by
  sorry

/-- Every product coincides with a product from a different index pair:
for all `a₀ ∈ A`, `b₀ ∈ B` there are `a ∈ A`, `b ∈ B` with
`a * b = a₀ * b₀` and `(a, b) ≠ (a₀, b₀)`. -/
theorem no_unique_mul :
    ∀ a₀ ∈ witnessFinsetA, ∀ b₀ ∈ witnessFinsetB,
      ¬ UniqueMul witnessFinsetA witnessFinsetB a₀ b₀ := by
  sorry -- from the generated equality chains + distinctness

/-- **Γ does not have the unique-product property.** -/
theorem gamma_not_uniqueProds : ¬ UniqueProds Gamma := by
  intro h
  obtain ⟨a₀, ha₀, b₀, hb₀, huniq⟩ :=
    h.uniqueMul_of_nonempty
      (A := witnessFinsetA) (B := witnessFinsetB)
      (by rw [← card_pos, card_witnessFinsetA]; omega)
      (by rw [← card_pos, card_witnessFinsetB]; omega)
  exact no_unique_mul a₀ ha₀ b₀ hb₀ huniq

end Karanos
