# PLAN_v2 — Forward Roadmap for Extraction Phase 3+

**Companion to:** [PLAN.md](PLAN.md) (historical Phase 0–Phase 1
detail), [AUDIT.md](AUDIT.md), [ARCHITECTURE.md](ARCHITECTURE.md),
[RISKS.md](RISKS.md), [README.md](README.md).
**Created:** 2026-04-24.
**Last updated:** 2026-04-24.
**Status:** picking up from current state — Phase 1 complete (10
realizers, 9 theorems extract end-to-end via `#extract_to_c`),
Phase 3a/b user-land prototypes complete (term-content extraction
via `#extract_def`, `Nonempty.some` realizer, ℕ/ℤ canonical
inhabitants, 12/12 byte-equivalent), mechanized completeness and
the optional toolchain track pending.

---

## Document purpose

This is the authoritative forward-looking roadmap. Every entry here
is either open, in flight, or a near-term deliverable. Historical
context (Phase 0 runtime, Phase 1 walker construction, the
Pass A–H sequence, the audit findings, the architectural decisions
ratified during the prototype phase) lives in PLAN.md and AUDIT.md
verbatim and is not reproduced here.

PLAN.md should be treated as the immutable record of how the
prototype was built. PLAN_v2.md (this file) is the mutable
forward plan — update freely as work lands and priorities shift.

When a task in this file lands, mark it ✅ here and add a one-line
"completed" entry under the appropriate completed-work block. Do
not delete entries; the running diff is part of the record.

---

## Executive summary

The extraction prototype has validated the structural thesis: a
single decomposing Expr walker plus a small per-constant realizer
table extracts classical Mathlib theorems and noncomputable defs
to bit-exact C, without rewriting either the theorem or the
underlying Mathlib definition. Twelve realizers cover nine
structurally distinct theorems and three term-content defs;
all twelve outputs pass `make diff` byte-equivalence against
hand-validated reference C.

The forward work splits cleanly into four tracks. **Track A**
finishes the user-land prototype: the remaining derived classical
constants (`Classical.dec`, `Classical.em`, `Classical.propDecidable`,
`Exists.choose`, `Quot.lift`), an empirical regression harness, and
retiring the per-theorem command in favor of attribute-driven batch
extraction. **Track B** builds the type-indexed canonical-selector
machinery — exposing the prime-atom picking rule already proved in
Decomposition.lean as a public API, extending `TypeTheoryConstructible`
with the four constructors that close the inhabitation gap (`list`,
`subtype`, `sigma_nat`, `inductive_wf`), and providing the
`canonicalInhabitant` extractor. **Track C** mechanizes the
composition meta-theorem in three components — Rota-backed
compositional soundness, Shannon-backed choice substitution, and
per-realizer numerical lemmas. **Track D** is an optional Lean
compiler fork addressing one specific scenario (`#eval` /
`native_decide` over extracted defs) that isn't required for the
extraction-to-standalone-C use case; it is deferred until a
concrete user request demands it.

Tracks A and B are on the critical path for any release beyond the
current prototype. Track C is required for publication-grade
mechanized completeness claims; Track A/B can ship before Track C
with empirical-regression as the soundness witness. Track D is
deferred indefinitely.

Total estimated effort, all tracks: ~10 weeks for engineering +
mechanization (excluding Track D), with per-realizer numerical
work continuing beyond that.

---

## Architectural rulings carried forward

These have been ratified across iterations and are not re-litigated
in forward work:

**R1 — The realizer registry is the central abstraction.** Per-constant
realizers keyed by constant name (and, for type-indexed entries like
`Classical.choice`, by the implicit type argument). Coverage is
honest: no realizer → static error at extraction time listing the
exact missing constant. No silent fallback, no runtime panic.

**R2 — Cardinality and inhabitation are orthogonal.**
`AbadirCompletenessTheorem` proves cardinality equality
(`Cardinal.mk α = Cardinal.mk (Nat_L n)`); the extraction registry
needs canonical inhabitation. A type can escape the finite Beth
staircase in cardinality terms while still admitting a constructive
canonical element via the ℕ-indexed constructor chain bottoming at
`EntropyNat.zero`. Track B exploits this orthogonality: the four new
inductive constructors (`list`, `subtype`, `sigma_nat`, `inductive_wf`)
extend inhabitation coverage without extending cardinality coverage,
which keeps the GCH/CH theorems (Hilbert #1) restricted to the
finite staircase as proved.

**R3 — `Inhabited` typeclass synthesis is the engineering primary;
`TypeTheoryConstructible` is the theoretical secondary.** At the
realizer dispatch site, first attempt `synthInstance (Inhabited α)`.
On success, emit the synthesized default. On failure, fall through
to the type-indexed canonical-inhabitant lookup via
`TypeTheoryConstructible`. Both produce sound inhabitants by the
Pass E argument (any inhabitant of a Nonempty type preserves
choice-invariant propositions). The ordering matters: `Inhabited`
synthesis is fast and covers the common case; `TypeTheoryConstructible`
is the axiom-backed route used by the mechanized completeness proof.

**R4 — The prime-atom picking rule is universal.** Every nat factors
uniquely (FTA), every type at level `n` is equivalent to `Nat_L n`,
the composition gives every element a prime-indexed address, and the
canonical element is the one whose prime address is minimal. This is
already proved in Decomposition.lean (`literalAtom`,
`assignmentCompositePrime`, `fta_via_information`) — Track B exposes
it as a `primeAddress` / `canonicalAtLevel` API outside the SAT
context.

**R5 — "Rigidity of 0" dispatches the empty-box edge cases.**
`IsEntropyZeroOnEmpty` + `IsEntropyZeroInvariant` (proven Rota
axioms; instances on `shannonEntropyNNReal` are sorry-free) handle
degenerate cases uniformly: types with no information content
(empty domains, zero-probability extensions) collapse to the same
realizer regardless of type-level structural distinctions. This is
the same mechanism P=NP uses for UNSAT detection
(`unsat_detected_by_prime_structure`) and ports unchanged into the
extraction completeness story.

**R6 — Quotient handling is per-type, not universal.** No general
`Quotient r → TypeTheoryConstructible` constructor is pursued, because
no canonical-representative function exists for arbitrary `Setoid r`
without `Classical.choice`. The per-type bridge pattern
(`EntropyRat ≃ ℚ` via `entropyRatEquivRat`, `EntropyReal ≃ ℝ` via
`entropyRealEquivReal`, one EntropyX per target Mathlib quotient
type) is the level of generality that matches what the theory can
actually prove. ZMod n is fine via Fin n; Cauchy-sequence-based ℝ
is handled via the existing EntropyReal bridge.

**R7 — The Lean compiler fork is optional.** Phase 1's nine
theorems and Phase 3a/b's three defs all extract via user-land
elaborator commands without any modification to `Lean/Compiler/`
sources. The default Phase 3 path is library-only; the toolchain
fork (Track D) is reserved for the specific scenario where
extracted defs need to be callable from compiled Lean code
(`#eval`, `native_decide`, downstream Lean modules), which isn't
the extraction-to-standalone-C use case. When/if Track D is
pursued, the fork is small: 2 files added, 1–2 surgical
modifications to stable areas of the Lean codebase.

**R8 — Composition correctness decomposes into three components.**
Component 1 (compositional soundness through Expr trees) is
discharged structurally by the Rota axioms, by direct analogy with
how Decomposition.lean's `cnfSharesFactor_iff_zero_conditional_cnf_entropy`
discharges SAT decidability. Component 2 (`Classical.choice`
substitution soundness) decomposes into a Shannon half (zero
differential information, backed by RECT + `programToEntropy`) and
a logical half (parametricity over choice-invariant propositions,
new lemma). Component 3 (per-realizer numerical soundness) is
orthogonal to the theory stack and requires per-constant analytic
inequalities. Track C addresses all three.

---

## Completed work (carried forward as baseline)

The detail for each completed phase is in PLAN.md and the prototype
directory; only the running tally is here.

**Phase 0 — runtime substrate.** ✅
`egpt_num` C ABI shim on FRAQTL `feat/egpt-num-cffi` (`f4ba38b`).
Bit-exact BigInt rationals, JS-parity tested. 50+ FFI symbols
(`egpt_from_i64`, `egpt_add`, `egpt_sub`, `egpt_mul`, `egpt_div`,
`egpt_cmp`, `egpt_free`, etc.).

**Phase 1 Pass A–H — decomposing walker + 12 realizers + 9 theorems.** ✅
EGPT-research commits `54165e2` (A, retired) through `0497796` (H).
Final scoreboard (all green):
- Walker: `realizeReal` + `realizeProp` with `CMode` discriminator
  for expression-vs-block emission.
- Realizers: `LT`, `Eq`, `And`, `Or`, `Exists`, `forallE` over
  `Fin N`, `HAdd`, `HSub`, `HMul`, `OfNat`, `Real.exp`, `Real.sqrt`,
  `Classical.choice`, `Fin.val` pass-through.
- 9/9 theorems byte-equivalent: `exp_one_gt_two`, `exp_one_lt_three`,
  `one_lt_sqrt_two`, `two_lt_one_plus_sqrt_two`,
  `classical_choice_mul_zero_lt_one`, `exists_sq_eq_four`,
  `exp_one_between_two_and_three`, `exp_one_lt_three_or_huge`,
  `forall_fin_three_val_lt_three`.
- 8/9 axiom closures `{propext, Classical.choice, Quot.sound}`;
  the ninth depends on no axioms.

**Phase 2 — Phase 1 documentation.** ✅
[AUDIT.md](AUDIT.md), [ARCHITECTURE.md](ARCHITECTURE.md),
[RISKS.md](RISKS.md), [README.md](README.md), [PLAN.md](PLAN.md)
(historical PLAN doc).

**Phase 3a user-land prototype — `#extract_def` for term content.** ✅
`#extract_def <name>` mirrors `#extract_to_c` for noncomputable defs:
walks the def's value via the same `realizeReal` pipeline, emits a
C function returning the realized inhabitant. Validation target:
`noncomputable def Extraction.classical_choice_real : ℝ := Classical.choice ⟨(0:ℝ)⟩`
extracts to `EgptNumber *Extraction_classical_choice_real(void) { return egpt_from_i64(0); }`.
Same Pass E realizer carries from theorem-statement extraction to
term-content extraction.

**Phase 3b user-land prototype — derived classical (partial).** ✅
- `Nonempty.some` realizer added (same type-indexed dispatch as
  `Classical.choice`).
- ℕ and ℤ added to canonical-inhabitant dispatch (both → 0).
- Two new defs: `Extraction.classical_choice_nat`,
  `Extraction.nonempty_some_real`.
- 12/12 byte-equivalent (9 theorems + 3 defs).

---

## Track A — Complete the user-land prototype (zero fork)

Estimated effort: ~3 weeks total. No Lean compiler modifications.
Direct continuation of Phase 1 + Phase 3a/b user-land work.

### A.1 — Remaining derived classical constants (~1 week)

Add realizers for the constants that show up in real Mathlib
`noncomputable def`s once we widen the test corpus beyond the
current prototype targets:

| Constant | Realizer strategy |
|---|---|
| `Classical.dec p` | `decide p` via `synthInstance (Decidable p)`; fall through to `Classical.propDecidable` realizer if synth fails |
| `Classical.em p` | same as `Classical.dec` (returns the chosen disjunct) |
| `Classical.propDecidable p` | type-indexed: dispatch on `p`'s structure to existing `LT`/`Eq`/`And`/`Or` realizers |
| `Exists.choose h` | registered witness-search strategy per predicate shape (sqrt-search for `∃ x, x*x=k`, linear search for bounded existentials, miss-error for unrecognized) |
| `Quot.lift f h q` | `f (Quot.unquot q)` — strip the quotient at runtime; q's representative is its runtime value |
| `Quotient.lift f h q` | same, via `Quotient.mk`'s representative |

Each entry is a single arm in `realizeProp` / `realizeReal` plus a
target def + theorem to validate it. Pattern is identical to
Pass E's `Classical.choice` arm.

Validation: a Mathlib `noncomputable def` exercising each constant
extracts to bit-exact C. Suggested targets: `Nat.find_spec` (uses
`Classical.dec` transitively), `Quotient.mk` ↦ `Quotient.lift`
round-trip on `EntropyRat`.

### A.2 — Empirical regression harness (~1 week)

Closes the soundness-empirical-validation gap before Track C
mechanizes it. Needed regardless of whether Track C lands.

- For each extraction target, the harness runs:
  - `lake env lean extraction/ExtractionCommand.lean` — does Lean
    elaborate + emit C without error?
  - `cd extraction/prototype && make diff` — does emitted C match
    the reference?
  - For theorems: does the binary print `true`?
  - For defs: does the emitted C function return the value Lean's
    `#eval` (or `decide`) would return when reducible?
- Target oracle: `native_decide` on the original term where Lean
  can reduce it; `decide` comparison where the proposition has a
  `Decidable` instance; hand-audited fixtures for transcendental
  inequalities (Pass B/C/D/E targets).
- Output: a single command (`make regression`) that fails CI on
  any divergence.

### A.3 — Attribute-driven batch extraction (~3 days)

`@[extract_safe]` attribute that drives the walker over all
attributed decls during module elaboration. Replaces the
per-target `#extract_to_c <name>` / `#extract_def <name>` invocations
with a single `lake build` that processes the whole batch.

Implementation: `PersistentEnvExtension` for the attribute, an
elaboration extension that hooks the attribute's `add` event, runs
the existing walker on the attributed decl's elaborated `Expr`,
writes the C output. No compiler patch; pure user-land.

### A.4 — `#extract_to_c` / `#extract_def` retire as primary surface (~2 days)

Once A.3 lands, the per-theorem commands become the manual
single-target backup for ad-hoc extraction. The primary user surface
is `@[extract_safe]`. Documentation sweep of README.md to reflect
the new entry point.

### A.5 — Test corpus widening (~1 week)

Bring in a set of Mathlib theorems beyond the current nine that
exercise:
- More Real-valued transcendentals (Real.log, Real.sin, Real.cos —
  see Component 3 dependency).
- Quotient types (via Quot.lift, EntropyRat round-trip).
- Subtypes (via the canonical-form pattern).
- Compound classical constants (Classical.choice + Classical.em in
  the same theorem).

Goal: raise the registry coverage from "validates the thesis" to
"covers a representative slice of Mathlib's classical surface."
Each corpus entry that fails because of a missing realizer surfaces
as a static error pointing at the missing constant — Add Realizer →
Re-run pattern.

---

## Track B — TypeTheoryConstructible canonical-selector machinery

Estimated effort: ~3 weeks. Lean library only, no compiler
modifications.

### B.1 — Prime-atom canonical selector API (~3 days, **critical path**)

Expose existing Decomposition.lean machinery as a public API
outside the SAT context:

```lean
namespace InformationTheory.PrimeAtom

/-- Encode a nat as its prime factorization signature. Already proved
constructively via FTA in Decomposition.lean / RotaEntropy.lean. -/
def primeAddress : ℕ → List (ℕ × ℕ)

/-- Decode the canonical element at level n in the Beth hierarchy
for the smallest valid prime address. -/
def canonicalAtLevel : (n : ℕ) → Nat_L n

/-- Zero-prime-address → bottom inhabitant. Composes through the
Nat_L recursion to give a deterministic canonical element at every
level, independent of Classical.choice. -/
theorem canonicalAtLevel_zero_eq_bottom :
  ∀ n, canonicalAtLevel n = (Nat_L.bottom n)

end InformationTheory.PrimeAtom
```

This sub-block is the conceptual hinge for Track B and Component 2
of Track C. With it exposed, every other Track B item is mechanical.

### B.2 — `TypeTheoryConstructible.list` constructor (~2 days)

Add to the inductive in
[ContinuumHypothesis.lean](../InformationTheory/EntropyNumber/ContinuumHypothesis.lean):

```lean
| list {α : Type} :
    TypeTheoryConstructible α →
    TypeTheoryConstructible (List α)
```

Cardinality side: `|List α| = |α|^<ω` absorbs to `max(ℵ₀, |α|)`. For
α at level `n`, this is `max(beth_0, beth_n) = beth_n`. Direct
cardinal-absorption proof, ports the pattern from the existing
`prod`/`sum` cases in `AbadirCompletenessTheorem`.

Inhabitation side: canonical element of `List α` is `[]`. Always
trivially inhabited.

### B.3 — `TypeTheoryConstructible.subtype` constructor (~3 days)

```lean
| subtype {α : Type} {p : α → Prop} [DecidablePred p] :
    TypeTheoryConstructible α →
    (∃ x, p x) →                      -- inhabitation witness
    TypeTheoryConstructible { x : α // p x }
```

Cardinality side: `|{x // p x}| ≤ |α|`. Equality holds when p has
infinitely many witnesses (which is the case for `IsCanonical` on
`List Bool`). Cardinal arithmetic: existing pattern in
`AbadirCompletenessTheorem` extends, requires a "predicate is
infinite" auxiliary lemma — straight cardinal-absorption.

Inhabitation side: the inhabitation witness in the constructor IS
the canonical element. `canonicalInhabitant` returns `⟨witness, h⟩`.

### B.4 — `TypeTheoryConstructible.sigma_nat` constructor (~2 days, inhabitation only)

```lean
| sigma_nat {F : ℕ → Type} :
    (∀ n : ℕ, TypeTheoryConstructible (F n)) →
    TypeTheoryConstructible (Σ n : ℕ, F n)
```

Cardinality side: deliberately **not** added to
`AbadirCompletenessTheorem`. ℕ-indexed sigma types have cardinality
`beth_ω`, outside the finite staircase. The cardinality theorem
stays restricted to the finite-index constructors; this constructor
is for inhabitation only.

Inhabitation side: canonical element is `⟨0, canonicalInhabitant (F 0)⟩`.
Justified by `IsEntropyCondAddSigma` applied to a Dirac-at-0 prior:
the joint entropy reduces to the level-0 slice's entropy, finite.

### B.5 — `TypeTheoryConstructible.inductive_wf` constructor (~4 days)

```lean
| inductive_wf {α : Type} (base : α) (well_founded : ...) :
    TypeTheoryConstructible α
```

Generic constructor for any inhabited inductive type with a
designated base case. Canonical element is the base. Covers `List`,
`Tree`, `Finset`, `Multiset`, and any user-defined inductive that
has a non-recursive constructor.

The `well_founded` field encodes the WF-recursion structure that
ensures `canonicalInhabitant` terminates: for non-recursive
constructors, terminate immediately; for recursive constructors,
fold through canonical elements of the non-recursive arg types.

Cardinality side: not added to `AbadirCompletenessTheorem`. WF-recursive
inductive cardinalities can vary widely (List α might be beth_n
for a beth_n α; user-defined might escape). Inhabitation only.

### B.6 — ℚ and ℝ corollaries (~1 day each, ~2 days total)

```lean
theorem rat_is_constructible : TypeTheoryConstructible ℚ :=
  .equiv (.subtype (.list .base)
            EntropyRat.IsCanonical_decidable
            EntropyRat.IsCanonical_inhabited)
         entropyRatEquivRat

theorem real_is_constructible : TypeTheoryConstructible ℝ :=
  .equiv (.powerset .base) entropyRealEquivReal
```

Both immediate once B.2/B.3 land. ℝ already works without B.2/B.3
because it threads through the existing `powerset` constructor —
this corollary just makes the chain explicit.

### B.7 — `canonicalInhabitant` extractor + soundness (~1 week)

```lean
noncomputable def canonicalInhabitant {α : Type} :
    TypeTheoryConstructible α → α
  | .base => EntropyNat.zero
  | .powerset _ => fun _ => false
  | .arrow _ ih_β => fun _ => canonicalInhabitant ih_β
  | .prod ih_α ih_β => (canonicalInhabitant ih_α, canonicalInhabitant ih_β)
  | .sum ih_α _ => Sum.inl (canonicalInhabitant ih_α)
  | .sigma ih => ⟨0, canonicalInhabitant (ih 0)⟩
  | .equiv ih e => e (canonicalInhabitant ih)
  | .list _ => []
  | .subtype _ ⟨w, h⟩ => ⟨w, h⟩
  | .sigma_nat ih => ⟨0, canonicalInhabitant (ih 0)⟩
  | .inductive_wf base _ => base

theorem canonicalInhabitant_sound_for_choice :
    ∀ {α} (h_c : TypeTheoryConstructible α) [h_ne : Nonempty α]
      (P : α → Prop) (h_inv : ∀ x y : α, P x ↔ P y),
    P (Classical.choice h_ne) ↔ P (canonicalInhabitant h_c)
```

Mechanical case-analysis on the inductive. ~200 LOC including the
soundness theorem.

---

## Track C — Mechanized completeness meta-theorem

Estimated effort: ~5 weeks for Components 1+2 (Component 3 is
ongoing per-realizer). Lean library only, no compiler modifications.

### C.1 — Component 1: compositional soundness via Rota (~1.5 weeks)

Files: `Lean/EGPT/extraction/Completeness/RealizerEntropy.lean`,
`Lean/EGPT/extraction/Completeness/Composition.lean`.

The structural composition theorem says: realizer substitution
commutes with Expr decomposition; the emitted C's operational
semantics is the compositional contraction of the per-constant
semantics.

Discharged structurally by Rota. Define
`RealizerEntropy : Expr → NNReal` as the information mass of a
sub-Expr under the walker's match distribution. Prove the 7 Rota
axioms for it. Apply `rota_all_entropy_scaled_shannon` for
canonicity. Prove the bridge:

```lean
theorem expr_realizes_iff_zero_residual_entropy :
    ∀ e, (∃ c, realizeProp e = some c) ↔
         RealizerResidualEntropy e = 0
```

Direct analog of `cnfSharesFactor_iff_zero_conditional_cnf_entropy`
in Decomposition.lean. The pattern ports from the P=NP chain: the
Rota chain rule covers the walker's additive decomposition,
`IsEntropyZeroOnEmpty` covers leaf closure, `IsEntropyZeroInvariant`
covers ignored type-class args, Rota uniqueness pins the cost
measure as canonical, `fta_via_information` supplies the arithmetic
shadow.

Output theorem:

```lean
theorem realizer_composition_sound :
    ∀ e, (∃ c, realizeProp e = some c) →
         SemanticEquiv (emittedC e) (Decidable.decide ⟦e⟧)
```

### C.2 — Component 2: Classical.choice substitution soundness (~1.5 weeks)

File: `Lean/EGPT/extraction/Completeness/ChoiceSubstitution.lean`.

Two halves composed.

**Shannon half (~3 days).** Backed by RECT (`exists_program_of_entropy`)
+ `programToEntropy`. Both `Classical.choice α h` and
`canonicalInhabitant h` have zero differential information content
given the `Nonempty α` proof — the Shannon programs realizing them
are of equal complexity.

```lean
theorem choice_and_canonical_have_zero_differential_entropy :
    ∀ {α} [Nonempty α] (h_c : TypeTheoryConstructible α),
    programToEntropy (programOf (Classical.choice ‹Nonempty α›)) =
    programToEntropy (programOf (canonicalInhabitant h_c))
```

**Logical half (~1 week).** The parametricity lemma — choice-invariant
propositions are unchanged under substitution. New material, not in
existing files.

```lean
theorem choice_invariant_substitution :
    ∀ {α : Type} [Nonempty α] (P : α → Prop)
      (h_inv : ∀ x y : α, P x ↔ P y) (x : α),
    P (Classical.choice ⟨x⟩) ↔ P x
```

Straight case analysis on the `Nonempty` unfolding plus invocation
of `h_inv`. Soundness threads through the canonical-inhabitant
extractor (Track B.7) to give the final form.

Output theorem:

```lean
theorem classical_choice_to_canonical_sound :
    ∀ {α} [h_ne : Nonempty α] (h_c : TypeTheoryConstructible α)
      (P : α → Prop) (h_inv : ∀ x y, P x ↔ P y),
    P (Classical.choice h_ne) ↔ P (canonicalInhabitant h_c)
```

### C.3 — Component 3: per-realizer numerical soundness (~3 days/realizer, ongoing)

File: `Lean/EGPT/extraction/Completeness/Numerical.lean`.

Per-realizer analytic inequalities that tie each numerical realizer
to its Mathlib counterpart with explicit slack. Not dischargeable
by the theory stack — this is straight numerical analysis.

```lean
theorem exp_partial_sum_le_exp :
    ∀ x : ℝ, 0 ≤ x → ∀ N : ℕ, exp_partial_sum x N ≤ Real.exp x

theorem exp_partial_sum_residual_bound :
    ∀ x : ℝ, 0 ≤ x → ∀ N : ℕ,
    Real.exp x - exp_partial_sum x N < x^(N+1) / (N+1)!

theorem sqrt_partial_newton_ge_sqrt :
    ∀ x : ℝ, 0 ≤ x → ∀ N : ℕ, Real.sqrt x ≤ sqrt_partial_newton x N

theorem sqrt_partial_newton_residual_bound :
    ∀ x : ℝ, 0 ≤ x → ∀ N : ℕ,
    sqrt_partial_newton x N - Real.sqrt x < (sqrt_init x - Real.sqrt x) / 2^N
```

Each lemma is a Mathlib-style proof; unblocks corresponding theorem
extractions to ship with mechanized soundness rather than empirical
validation.

Initial set: `exp`, `sqrt`. Add per realizer as Track A.5 widens
the test corpus.

### C.4 — Final composition (~3 days)

```lean
theorem extraction_soundness :
    ∀ (thm : Name) (e : Expr),
      realizerRegistryCovers e →
      numericalPrecisionAdequate e →
      emittedC(e).evaluate = Decidable.decide ⟦thm⟧
  := by
    apply realizer_composition_sound       -- C.1 Component 1 (Rota)
      <;> apply classical_choice_to_canonical_sound  -- C.2 Component 2
      <;> apply per_realizer_soundness     -- C.3 Component 3
```

This is the publication-grade mechanized correctness theorem. With
it, the extraction prototype graduates from "validated on nine
theorems" to "provably sound on every theorem in the realizer
registry's coverage."

---

## Track D — Optional Lean compiler fork (deferred)

Reserved for the specific scenario: making `@[extract_safe]`-decorated
`noncomputable def`s callable from compiled Lean code (`#eval`,
`native_decide`, downstream Lean modules). Not required for the
extraction-to-standalone-C use case.

If pursued, the fork is small. Lean source impact:

| Item | Source impact |
|---|---|
| LCNF substitution pass | 1 new file in `Lean/Compiler/LCNF/` |
| LCNF pass manager registration | 1 line added to `Lean/Compiler/LCNF/PassManager.lean` |
| Relax `compileDecl` noncomputable gate for `@[extract_safe]` | 1 conditional in `Lean/Elab/Definition.lean` (or equivalent) |

Total: 2 files added, 1–2 files modified (small surgical changes).
Maintenance burden against upstream Lean ~1 hour per major release
to rebase. Touched code is in stable areas of the Lean codebase
that haven't seen breaking changes in years.

A larger fork (Option 2: upstream `@[realizer_for]` as a first-class
compiler attribute alongside `@[extern]` and `@[implemented_by]`)
is RFC territory — ~5 files modified across `Lean/Elab/Attributes`,
`Lean/Compiler/LCNF/`, `Lean/Compiler/IR/EmitC.lean`. This is a
contribution-PR scope, not a long-lived divergent fork.

**Decision rule:** Track D is unblocked only by a concrete user
request that demands `#eval foo` for noncomputable `foo`, or by an
appetite for Lean upstream contribution. Until then, Tracks A/B/C
ship without it.

---

## Critical path

Dependency-ordered sequence for landing the full Phase 3 stack:

1. **B.1 prime-atom canonical selector API** (3d) — unblocks B.7
   `canonicalInhabitant` and Component 2 of Track C.
2. **B.2 + B.3 list + subtype constructors** (5d) — unblocks B.6
   ℚ/ℝ corollaries.
3. **A.3 attribute-driven batch extraction** (3d) — required for
   A.5 corpus widening at scale.
4. **B.6 ℚ/ℝ corollaries** (2d) — depends on B.1 + B.2 + B.3.
5. **B.7 canonicalInhabitant + soundness** (1w) — depends on
   B.1–B.6.
6. **A.1 derived classical constants** (1w) — independent of B; can
   run in parallel.
7. **A.2 empirical regression harness** (1w) — independent; can run
   in parallel; required before any release ship.
8. **C.1 Component 1 compositional soundness** (1.5w) — depends on
   nothing in B; can start immediately on top of Phase 1 walker.
9. **B.4 + B.5 sigma_nat + inductive_wf** (6d) — extends coverage
   but not on critical path for ℚ/ℝ shipping.
10. **C.2 Component 2 choice substitution** (1.5w) — depends on
    B.7 canonicalInhabitant.
11. **A.4 retire `#extract_to_c` as primary** (2d) — depends on
    A.3 landing.
12. **A.5 test corpus widening** (1w) — depends on A.1 + A.3.
13. **C.3 numerical lemmas** (ongoing per realizer) — depends on
    A.5 identifying the realizers that need formal soundness.
14. **C.4 final composition theorem** (3d) — depends on C.1 + C.2
    landing; corpus-validated by C.3.

Critical path through to "Track A + B done, Track C Component 1
landed, ready for empirical-soundness ship": ~5 weeks.

Critical path through to "all tracks done excluding D, mechanized
soundness ship": ~10 weeks.

Track D adds 1–2 weeks if pursued.

---

## Estimates and milestones

**Milestone M1 — Empirical-soundness release (~5 weeks).** Tracks A
+ B complete, Component 1 of Track C landed, Component 3 numerical
lemmas for the existing realizers (`exp`, `sqrt`). Empirical
regression harness green on widened corpus. Suitable for prototype
release / Zulip handoff response.

**Milestone M2 — Mechanized-soundness release (~10 weeks).** All of
Tracks A + B + C complete. The `extraction_soundness` meta-theorem
is proved. Suitable for publication-grade claims; the 'I have a
constructive P=NP that compiles to bit-exact C' assertion is now
backed by a mechanized soundness theorem rather than empirical
validation.

**Milestone M3 — Lean-callable extracted defs (Track D, optional, +1–2 weeks).**
Only pursued on concrete user demand or upstream-contribution
appetite.

---

## Open questions

The following remain open and need a ruling before the affected
tasks start:

**Q1 — Should `canonicalInhabitant` be `noncomputable`?** The
extractor function in B.7 is structural recursion on the
`TypeTheoryConstructible` proof, but several arms invoke functions
that Mathlib marks as `noncomputable` (e.g., `entropyRatEquivRat`).
Two options: (a) keep `canonicalInhabitant` as `noncomputable def`
and accept that it lives in the proof layer only; (b) define a
parallel `canonicalInhabitant_compute` that bypasses Mathlib's
noncomputable bridges using the EGPT-side `EntropyX` representation
directly. Option (b) is more work but unblocks `#eval`
canonicalInhabitant for testing.

**Q2 — Should `RealizerEntropy` be defined over the user-land walker
or a hypothetical LCNF-level walker?** Component 1 of Track C
requires `RealizerEntropy : Expr → NNReal`. The current walker is
user-land; an LCNF-level walker would need Track D to exist. Option
(a): define `RealizerEntropy` over the user-land walker, which
covers the user-land extraction case completely. Option (b): define
it abstractly over any walker satisfying a refinement-relation
predicate, so the same proof carries to both user-land and LCNF
walkers. Option (b) is more work but more general; option (a) is
sufficient for the extraction-to-C use case.

**Q3 — Should we register `Quot.lift` as a runtime pass-through
even though it's noncomputable in Mathlib?** The extracted C uses
the quotient's representative directly (since `egpt_num` rationals
are already in canonical reduced form via `EntropyRat.IsCanonical`).
The realizer is sound; the question is whether to expose this as a
public realizer or document it as an internal implementation detail.

**Q4 — Coverage manifest scope.** The `Inhabited` synthesis path
means the set of extractable theorems drifts with the Mathlib
version (a new `Inhabited` instance upstream silently broadens
coverage). For reproducibility, do we pin a Mathlib commit per
extraction release? Add a coverage-manifest CI check that asserts
the set of extractable theorems hasn't changed shape unexpectedly?

---

## File map

Files that exist in the prototype (do not modify Phase 1/2 outputs
without coordinating):

```
Lean/EGPT/extraction/
├── README.md                    -- index + quick start
├── PLAN.md                      -- historical record (Phase 0/1/2/3a/3b detail)
├── PLAN_v2.md                   -- this file (forward plan)
├── AUDIT.md                     -- 2026-04-24 audit findings
├── ARCHITECTURE.md              -- walker architecture + extension procedures
├── RISKS.md                     -- gap register
├── ExtractionCommand.lean       -- the walker + #extract_to_c + #extract_def commands
├── prototype/
│   ├── Makefile                 -- build + diff harness
│   └── Extraction_<name>/       -- per-target output dirs (12 currently)
│       ├── extracted.c
│       ├── expected_output.txt
│       └── extracted_bin
```

Files to add (per track):

```
Lean/EGPT/extraction/
├── Attribute.lean               -- A.3: @[extract_safe] PersistentEnvExtension
├── BatchElaborator.lean         -- A.3: hooks attribute, drives walker
├── Regression.lean              -- A.2: empirical regression harness
├── Completeness/
│   ├── RealizerEntropy.lean     -- C.1
│   ├── Composition.lean         -- C.1
│   ├── ChoiceSubstitution.lean  -- C.2
│   └── Numerical.lean           -- C.3
└── Registry/
    ├── PrimeAtom.lean                    -- B.1: prime-atom canonical selector
    ├── TypeTheoryConstructibleExt.lean   -- B.2–B.5
    ├── CanonicalInhabitant.lean          -- B.7
    └── MathlibCorollaries.lean           -- B.6
```

Files in adjacent components (read but do not modify without
coordination):

- [`InformationTheory/EntropyNumber/Hierarchy.lean`](../InformationTheory/EntropyNumber/Hierarchy.lean)
  — `Nat_L`, the Beth staircase
- [`InformationTheory/EntropyNumber/ContinuumHypothesis.lean`](../InformationTheory/EntropyNumber/ContinuumHypothesis.lean)
  — `TypeTheoryConstructible`, `AbadirCompletenessTheorem`
- [`InformationTheory/EntropyNumber/Rat.lean`](../InformationTheory/EntropyNumber/Rat.lean)
  — `entropyRatEquivRat`
- [`InformationTheory/EntropyNumber/Real.lean`](../InformationTheory/EntropyNumber/Real.lean)
  — `entropyRealEquivReal`
- [`InformationTheory/EntropyNumber/RotaEntropy.lean`](../InformationTheory/EntropyNumber/RotaEntropy.lean)
  — `rota_all_entropy_scaled_shannon`, `fta_via_information`
- [`InformationTheory/Entropy/Axioms.lean`](../InformationTheory/Entropy/Axioms.lean)
  — the 7 Rota axioms
- [`InformationTheory/Entropy/SourceCoding.lean`](../InformationTheory/Entropy/SourceCoding.lean),
  [`Program.lean`](../InformationTheory/Entropy/Program.lean),
  [`Shannon.lean`](../InformationTheory/Entropy/Shannon.lean)
  — RECT + `programToEntropy` + Shannon entropy formalism
- [`InformationTheory/Complexity/Decomposition.lean`](../InformationTheory/Complexity/Decomposition.lean)
  — the prime-atom + conditional-entropy bridge that B.1 exposes
- [`InformationTheory/Complexity/PPNP.lean`](../InformationTheory/Complexity/PPNP.lean),
  [`SetRFL.lean`](../InformationTheory/Complexity/SetRFL.lean)
  — P=NP proof chain (template for Component 1 structure)

External:

- [`FRAQTL/fat/crates/egpt_num/`](../../../../Unkamon/FRAQTL/fat/crates/egpt_num/)
  — runtime ABI (`feat/egpt-num-cffi`)

---

## References

- [PLAN.md](PLAN.md) — Phase 0/1/2/3a/3b detail, including the
  per-pass commit history and the original Phase 3 elaboration that
  this document supersedes.
- [AUDIT.md](AUDIT.md) — what the EntropyReal tower audit found on
  2026-04-24, the divergences from the original Zulip handoff, and
  the session decisions that shaped the prototype.
- [ARCHITECTURE.md](ARCHITECTURE.md) — how the walker works,
  realizer dispatch, runtime ABI, extension procedures.
- [RISKS.md](RISKS.md) — gap register: approximation soundness,
  bounded search, walker limitations, what a correctness
  meta-theorem still needs to prove.
- [README.md](README.md) — index + quick start for the prototype.
- [`EGPT-research/PRIVATE/Zulip_Clean_Forward_Boundary.md`](../../../PRIVATE/Zulip_Clean_Forward_Boundary.md)
  — original handoff brief; the §1–2 framing was superseded by the
  realizer-registry reframing in AUDIT.md.

---

## Update protocol

When work lands:

1. Mark the corresponding task ✅ in this file in-place.
2. Append a one-line entry under "Completed work" with a date and a
   brief description.
3. If the task uncovered a new architectural ruling, add it to the
   "Architectural rulings carried forward" section (numbered
   continuation: R9, R10, ...).
4. If the task surfaces a new open question, add it under "Open
   questions" (numbered continuation: Q5, Q6, ...).
5. If the task was on the critical path, re-evaluate the ordering
   and update milestone estimates.
6. Do not delete tasks; the running diff is part of the record.
