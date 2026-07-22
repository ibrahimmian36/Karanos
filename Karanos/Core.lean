/-
Copyright 2026 Millennium Research. Apache-2.0.
-/
import Mathlib

/-!
# Karanos core: Γ, free words, and the certificate types

Γ = ⟨a, b | a b a² b⁻¹ a² b⁻², a b³ a b⁴ a⁻¹ b⟩ — Gardam's Ã₂-building
lattice, the concrete torsion-free non-unique-product group on which the
zero-divisor form of Kaplansky's conjecture is open (SMRI slides, 2021).

This module fixes the group as a `PresentedGroup`, defines the free
alphabet and the map from letter-words into Γ, and states the data
types the generated certificates populate. The mathematical content —
that the emitted certificates actually prove what they claim — lives in
`Karanos.Reduce` (free-reduction soundness) and `Karanos.NonUP`
(assembly into `¬ UniqueProds Γ`). Nothing here is axiomatic beyond
mathlib's own base; the publication gate (`scripts/axiom_gate.sh`)
enforces that across the whole library.
-/

namespace Karanos

/-- The four letters: `a`, `a⁻¹`, `b`, `b⁻¹`. -/
inductive Letter
  | a | A | b | B
deriving DecidableEq, Repr

namespace Letter

/-- The formal inverse of a letter. -/
def inv : Letter → Letter
  | a => A | A => a | b => B | B => b

@[simp] theorem inv_inv (l : Letter) : l.inv.inv = l := by cases l <;> rfl

end Letter

/-- The two generators of the free group `F₂`, indexed for `PresentedGroup`. -/
inductive Gen
  | ga | gb
deriving DecidableEq

open PresentedGroup in
/-- The relators of Γ as elements of the free group on `Gen`, written in
the letters `a := .of .ga`, `b := .of .gb`. -/
noncomputable def relators : Set (FreeGroup Gen) :=
  let a := FreeGroup.of Gen.ga
  let b := FreeGroup.of Gen.gb
  { a * b * a^2 * b⁻¹ * a^2 * b⁻¹^2,
    a * b^3 * a * b^4 * a⁻¹ * b }

/-- Γ itself. -/
noncomputable def Gamma : Type := PresentedGroup relators

noncomputable instance : Group Gamma := by unfold Gamma; infer_instance

/-- A letter's image in the free group on `Gen`. -/
def Letter.toFree : Letter → FreeGroup Gen
  | .a => FreeGroup.of Gen.ga
  | .A => (FreeGroup.of Gen.ga)⁻¹
  | .b => FreeGroup.of Gen.gb
  | .B => (FreeGroup.of Gen.gb)⁻¹

/-- A letter-word's image in the free group. -/
def wordToFree (w : List Letter) : FreeGroup Gen :=
  (w.map Letter.toFree).prod

/-- A letter-word's image in Γ. -/
noncomputable def eval (w : List Letter) : Gamma :=
  PresentedGroup.mk relators (wordToFree w)

/-- A product-coincidence certificate: two words claimed equal in Γ,
together with the conjugated-relator pieces witnessing the equality of
their images in the free group modulo the relators. Emitted by the
Python proof-forest extractor; checked in `Karanos.Reduce`. -/
structure ProductEquality where
  lhs : List Letter
  rhs : List Letter
  pieces : List (List Letter × Nat × Bool)

/-- A separating homomorphism to a symmetric group `S_deg`, given by the
images of the two generators as one-line permutations. Emitted for the
non-abelian pairs the ℤ/42 abelianization does not separate. -/
structure SepHom where
  deg : Nat
  imA : Array Nat
  imB : Array Nat

/-- One product pair `(u, v)` of the witness together with its partner
pair `(pu, pv)` and the conjugated-relator pieces certifying
`u ++ v = pu ++ pv` in Γ. Emitted in canonical A-major order so that
coverage of the full product grid is a plain list equality. -/
structure PartnerCert where
  u : List Letter
  v : List Letter
  pu : List Letter
  pv : List Letter
  pieces : List (List Letter × Nat × Bool)

end Karanos
