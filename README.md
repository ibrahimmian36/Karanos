# Karanos

A machine-checked proof that Γ, the torsion-free Ã₂-building lattice

    Γ = ⟨a, b | a b a² b⁻¹ a² b⁻², a b³ a b⁴ a⁻¹ b⟩,

does **not** have the unique-product property — `¬ UniqueProds Γ`, stated
against mathlib's own `UniqueProds` class, kernel-checked, with a
publication gate that rejects any theorem depending on an axiom beyond
Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`), any
`sorry`, or any `native_decide`.

Γ is the concrete group on which the zero-divisor form of Kaplansky's
conjecture is open in every characteristic (Gardam, SMRI 2021). Its
failure of unique products is the first step of that landscape; this
development certifies it. Torsion-freeness of Γ is a separate result of
Gardam's and is **not** claimed here — the theorem stands on its own.

## What is proved

The witness is an explicit pair of finite sets `A` (32 elements) and `B`
(28 elements) of Γ. Unique-product failure means: every product `a·b`
with `a ∈ A`, `b ∈ B` coincides with at least one other such product.
The certificate has two mechanically-checked halves:

- **Equalities** — the product coincidences, each certified by an
  explicit free-group identity (a product of conjugated relators) that
  Lean verifies by word reduction. Extracted from a proof-producing
  Todd–Coxeter closure and self-verified in Python before transcription.
- **Distinctness** — that the elements of `A` (and of `B`) are pairwise
  distinct in Γ, via homomorphisms onto finite groups: the abelianization
  `Γᵃᵇ ≅ ℤ/42` separates all but six pairs, and one homomorphism onto
  `S₄` separates the rest. Each is checked in Lean by `decide`.

## Layout

- `Karanos/Core.lean` — Γ as a `PresentedGroup`, the letter alphabet, the
  word-to-Γ map, and the certificate data types.
- `Karanos/Reduce.lean` — free reduction and the soundness lemma: a
  certificate that reduces to `lhs · rhs⁻¹` proves `eval lhs = eval rhs`.
- `Karanos/Distinct.lean` — the finite-quotient separation argument.
- `Karanos/NonUP.lean` — assembly: the certified equalities and
  distinctness give `¬ UniqueProds Γ`.
- `Karanos/Generated/` — the certificate data, emitted by
  `scripts/p2_codegen.py` from the Python proof-forest
  extractor. Generated, never hand-edited; the Lean side re-checks it
  from scratch, so the generator is not a trusted component.
- `scripts/axiom_gate.sh` — the publication gate.

## Provenance

The certificate data is produced and independently self-verified by the
search engine in `engine/` — the finite-quotient cover in
`quotients.py` (gate G-a) and the proof-forest certificate DAG in
`certgraph.py` (gate G-b). The numbers behind this development: 874
distinctness pairs separated by two quotients; 896 product pairs, each
with a flat partner certificate re-verified by free reduction in Python
before transcription and re-checked from scratch by the Lean kernel.

## Verifying

```
lake exe cache get
lake build
scripts/axiom_gate.sh
```

The gate re-checks every theorem in the library (122 at last count)
against the allowed axiom set and fails on any `sorry`, any
`native_decide`, or any axiom beyond the standard three. CI runs it on
every push. The headline:

```
'Karanos.gamma_not_uniqueProds' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

## Repository layout

Everything for this problem lives here: the search that found the witness,
the extraction that turned it into certificates, the Lean proof, the
evidence trail, and the write-up.

    Karanos/          the Lean development (the theorem)
      Core.lean         Γ as a PresentedGroup, the certificate vocabulary
      Reduce.lean       word reduction + certificate-checker soundness
      Distinct.lean     the ℤ/42 and S₄ descents, pairwise distinctness
      NonUP.lean        assembly → gamma_not_uniqueProds
      Generated/        emitted certificate data (do not hand-edit)
      AxiomCheck.lean   publication manifest
      AxiomAudit.lean   mechanical whole-library axiom audit
    engine/           the search + extraction pipeline (Python)
      kaplansky.py      Γ substrate, SAT encodings, scorers
      groupball.py      merge-witnessed Todd–Coxeter ball quotients
      certgraph.py      proof-producing closure → equality certificates
      quotients.py      finite-quotient search → distinctness
      gf2.py            the F₂ kernel test and its campaign drivers
    scripts/          drivers: axiom_gate.sh, codegen, table builds, runs
    tests/            48 tests over the engine
    docs/             plan, GPU/scale analysis, run book, arXiv note
    runs/             the append-only ledger — every search verdict, dated

The Python side is untrusted by construction: it searches, extracts, and
self-verifies, then emits data that Lean re-checks from scratch. Nothing
it produces is believed because it produced it.

## Running the search

    python -m pytest                      # engine tests
    PYTHONPATH=engine python -m karanos_engine.gf2 controls
    PYTHONPATH=engine python scripts/p2_codegen.py    # regenerate certificates
