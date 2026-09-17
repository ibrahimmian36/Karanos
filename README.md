# Karanos

A machine-checked proof that Γ, the torsion-free Ã₂-building lattice

    Γ = ⟨a, b | a b a² b⁻¹ a² b⁻², a b³ a b⁴ a⁻¹ b⟩,

does **not** have the unique-product property — `¬ UniqueProds Γ`, stated
against mathlib's own `UniqueProds` class, kernel-checked, with a
publication gate that rejects any theorem depending on an axiom beyond
Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`), any
`sorry`, or any `native_decide`.

That Γ fails unique products is a theorem announced by Giles Gardam in
lectures in 2021, where he proposed Γ as a candidate for Kaplansky's
zero-divisor conjecture; no proof or witness has been published. This
repository supplies a kernel-checked proof with an explicit witness found
by our own search. The mathematical statement is Gardam's.

Being an Ã₂ lattice, Γ has property (T), so it admits no proper action on
a CAT(0) cube complex (Niblo–Reeves) and lies outside the reach of the
methods that settle the conjecture for virtually compact special groups.
Torsion-freeness of Γ and its description as a lattice are Gardam's and
are **not** formalized here — the theorem is about the presented group and
stands on its own.

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
  distinct in Γ, via homomorphisms to finite groups: the map onto
  `ℤ/42` (the abelianization) separates all but six pairs, and one
  homomorphism into `S₄`, with image `A₄`, separates the rest. Each is
  checked in Lean by `decide`.

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

The certificates can also be checked without Lean:

```
python3 scripts/recheck_certificates.py
```

reads the generated files directly and re-verifies every equality
certificate by free reduction and every distinctness fact through the two
quotients (standard library only, under a second). Of the 896 product
coincidences, 658 already hold in the free group; the other 238 use 970
conjugated relators in all.

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
the extraction that turned it into certificates, the Lean proof, and the
evidence trail.

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
    docs/             plan, GPU/scale analysis, run book
    runs/             the append-only ledger — every search verdict, dated

The Python side is untrusted by construction: it searches, extracts, and
self-verifies, then emits data that Lean re-checks from scratch. Nothing
it produces is believed because it produced it.

## Running the search

    python -m pytest                      # engine tests
    PYTHONPATH=engine python -m karanos_engine.gf2 controls
    PYTHONPATH=engine python scripts/p2_codegen.py    # regenerate certificates
