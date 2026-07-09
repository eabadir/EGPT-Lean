# AUDIT — Constructive Extraction for EGPT Mathlib4 Fork

**Date opened:** 2026-04-24
**Status:** Steps 1–4 of handoff Investigation Order complete. Phase 0 (runtime-first prototype) starting.
**Author:** Claude Code (session-opened under `/Users/essam/Code/Unkamon/FRAQTL`)

This document is the authoritative cold-start brief. A future agent picking up this work should read this file, then [PLAN.md](PLAN.md), then the handoff at [`EGPT-research/PRIVATE/Zulip_Clean_Forward_Boundary.md`](../../../PRIVATE/Zulip_Clean_Forward_Boundary.md) §"Agent Handoff" for original framing.

---

## 1. Mission (as reframed 2026-04-24)

Modify the Lean compiler's extraction pipeline so that classical Mathlib theorems (using `Classical.choice` / `Classical.em` / `noncomputable def`) compile to working C, by registering **per-constant realizers** backed by the EGPT `EntropyReal` tower's computable types. This is **engineering**, not a new theorem-proving burden.

### What the original handoff proposed
A universal Beth-collapse meta-theorem under which *every* Mathlib type admits a constructive enumeration, giving `Classical.choice` a uniform realizer: return the canonical inhabitant.

### What we actually use (session reframing, user direction)
A **realizer registry** — Coq's `Extract Constant` pattern. Coverage = what we register. Types outside the registry → static error at extract time, not runtime panic. `EntropyNat`, `EntropyReal`, and `Nat_L` are computable type constructors (no Classical in their *data*); they are the template for canonical inhabitants. The `entropyRealEquivReal` bijection theorem (which uses `Classical.choice` in its *proof*) serves as the **correctness bridge** for real-valued computation — it's the warrant, not the program.

### What we deliberately dropped
- Universal Beth-collapse requirement.
- Need to extend `TypeTheoryConstructible` to cover subtypes/quotients/WF-inductives.
- Need for `evaluate_binary_sequence` to be Classical.choice-free (it's a proof artifact, not runtime code — see §3.5).

---

## 2. Environment (verified 2026-04-24)

| Item | Value |
|---|---|
| Repo (Lean extraction deliverables) | [`EGPT-research/Lean/EGPT/`](..) — Lake project `egpt-pr` |
| Repo (FFI runtime deliverables) | [`FRAQTL/fat/crates/egpt_num/`](../../../../../Unkamon/FRAQTL/fat/crates/egpt_num/) |
| Mathlib fork | [`~/Lean/mathlib4`](../../../../../../Lean/mathlib4) @ `feat/information-theory` |
| Lean toolchain | `leanprover/lean4:v4.29.0` |
| Lake dependency | `require mathlib from "../../../../Lean/mathlib4"` (path) |
| Starting branch in EGPT-research | `refactor/ppf-canonical-expansion-EGPT-research` (had uncommitted work — do not commit extraction deliverables here) |
| New branch for Lean work | `feat/extraction-prototype` in EGPT-research |
| New branch for FFI work | `feat/egpt-num-cffi` in FRAQTL |
| Build health | `lake build InformationTheory.EntropyNumber.ContinuumHypothesis` green after `lake exe cache get` |

---

## 3. Audit findings (Steps 1–3)

### 3.1 Tower location

All tower files under [`InformationTheory/EntropyNumber/`](../InformationTheory/EntropyNumber/):

| File | Defines |
|---|---|
| `Basic.lean` | `EntropyNat` (subtype of all-true `List Bool`), `entropyNatEquivNat`, `EntropyNat.toNat/ofNat/add/mul` |
| `Int.lean` | `EntropyInt := EntropyNat × Bool`, `entropyIntEquivInt` (noncomputable) |
| `Rat.lean` | `EntropyRat` subtype with `IsCanonical` predicate, `entropyRatEquivRat` (noncomputable) |
| `Real.lean` | `EntropyReal := EntropyNat → Bool`, `evaluate_binary_sequence`, `entropyRealEquivReal` (noncomputable, only tower `Classical.choice` site) |
| `Hierarchy.lean` | `Nat_L n` recursion on ℕ, `Real_L`, `Rat_L` aliases, `cardinal_of_level` theorem |
| `ContinuumHypothesis.lean` | `cardinality_is_beth`, `abadirContinuumHypothesis`, `generalizedContinuumHypothesis`, `TypeTheoryConstructible` inductive, `AbadirCompletenessTheorem` |
| `Polynomial.lean`, `PrimeAtoms.lean`, `RotaEntropy.lean` | Downstream uses (not on the critical path) |

### 3.2 Axiom build report (verbatim output of [AxiomProbe.lean](../AxiomProbe.lean))

```
EntropyNat                               : (no axioms)
EntropyNat.toNat                         : (no axioms)
Nat_L                                    : (no axioms)
EntropyReal                              : (no axioms)
TypeTheoryConstructible                  : [propext]

entropyNatEquivNat                       : [propext]
EntropyNat.ofNat / toNat_add / toNat_mul : [propext]

evaluate_binary_sequence                 : [propext, Classical.choice, Quot.sound]
cardinal_of_level                        : [propext, Classical.choice, Quot.sound]
cardinal_entropyReal                     : [propext, Classical.choice, Quot.sound]
entropyRealEquivReal                     : [propext, Classical.choice, Quot.sound]

entropyIntEquivInt                       : [propext, Quot.sound]           ← no Classical!
entropyRatEquivRat                       : [propext, Classical.choice, Quot.sound]

cardinality_is_beth                      : [propext, Classical.choice, Quot.sound]
abadirContinuumHypothesis                : [propext, Classical.choice, Quot.sound]
generalizedContinuumHypothesis           : [propext, Classical.choice, Quot.sound]
all_infinities_indexed_by_Nat            : [propext, Classical.choice, Quot.sound]
AbadirCompletenessTheorem                : [propext, Classical.choice, Quot.sound]
```

Produced by `lake env lean AxiomProbe.lean` in [Lean/EGPT/](..).

### 3.3 Matches with Zulip handoff's MVP claims

- ✅ `entropyNatEquivNat` is propext-only. The Clean Forward MVP claim holds at the base.
- ✅ `entropyRealEquivReal` has exactly `{propext, Classical.choice, Quot.sound}` — matches the handoff's claimed return-trip axiom closure.

### 3.4 Divergences from Zulip handoff

**3.4.a [`evaluate_binary_sequence`](../InformationTheory/EntropyNumber/Real.lean#L69) is NOT Classical.choice-free.**

Its docstring says "constructive surjection… without invoking `Classical.choice`" — but it uses `tsum` (infinite series summation), whose Mathlib closure pulls in `Classical.choice`. The forward map *as written* is classical. Impact downgraded from "blocker" to "docstring overstates" under the realizer-registry reframing: the forward map is a proof artifact, not runtime code. Docstring should be updated when convenient.

**3.4.b Beth-collapse theorem is scope-restricted.**

[`AbadirCompletenessTheorem`](../InformationTheory/EntropyNumber/ContinuumHypothesis.lean#L402) is a real proven theorem — but only for [`TypeTheoryConstructible`](../InformationTheory/EntropyNumber/ContinuumHypothesis.lean#L218), a **restricted** inductive class: `EntropyNat`, powerset, arrow, prod, sum, *finite sigma (`Fin N` with `[NeZero N]`)*, equiv. It does **not** cover infinite sigma, quotients, general subtypes, `Prop`-types, or WF-recursive inductives. The explicit comment at `ContinuumHypothesis.lean:200` calls out `Σ n : ℕ, Nat_L n` (cardinality `beth_ω`) as intentionally excluded. Impact: under realizer-registry reframing, this is **no longer a blocker** — we don't need universal coverage; we only need realizers for the constants that actually appear in target theorems.

**3.4.c `entropyIntEquivInt` is noncomputable but Classical.choice-*free*.**

Axiom closure `[propext, Quot.sound]`. Implication: a computable `EntropyInt ≃ ℤ` is trivially reachable if we avoid the Mathlib-side `Equiv.intEquivNatSumNat` import chain. Minor engineering item; flag for the Int realizer.

**3.4.d `entropyRatEquivRat` does drag in Classical.choice.**

Via `Rat.mkRat` / `Rat.divInt` lemmas. Rat realizer path needs to either side-step Mathlib's classical rational API or accept the dependency (fine under the reframing).

### 3.5 How we interpret the divergences under the new framing

- **3.4.a** — don't fix the docstring yet, flag in ARCHITECTURE.md. The forward map is not executed; the bijection theorem `entropyRealEquivReal` is what backs correctness.
- **3.4.b** — `AbadirCompletenessTheorem` is not load-bearing. Keep it as a theorem of the fork; don't extend it. The realizer registry does the coverage work instead.
- **3.4.c/d** — affects which realizers are "clean" vs "classical" internally. Documentation item, not a blocker.

---

## 4. Runtime substrate inventory (Phase 0 target)

### 4.1 `egpt_num` Rust crate ([FRAQTL/fat/crates/egpt_num/](../../../../../Unkamon/FRAQTL/fat/crates/egpt_num/))

- `EgptNumber`: exact rational `{num: BigInt, den: BigInt}`, reduced canonical form, sign in numerator, positive denominator, coprime.
- Arithmetic: `add`, `sub`, `mul`, `div`, `neg`, `compare` (total order via cross-multiply) — all bit-exact via `num-bigint`.
- PPF projection via `ppf_view()` for dyadic values.
- JS-parity tested bit-for-bit against `EGPTNumber` JS via `tests/js_parity.rs` fixture.
- **No FFI yet** — no `extern "C"`, no `cbindgen` config.

### 4.2 JS reference for transcendentals ([EGPTMath/js/model/core/EGPTranscendental.js](../../../../../Unkamon/FRAQTL/egpt/EGPTMath/js/model/core/EGPTranscendental.js))

`cos`, `sin`, `exp`, `log2`, `exp2`, `factorial`. 157/157 tests green. Reference implementation for future Rust ports when realizers grow beyond the prototype.

### 4.3 Minimum viable realizer set for `Real.exp 1 > 2`

The target theorem does **not** require a full `exp` implementation. Forward Taylor for `x = 1` is monotone in N:

```
S_0 = 1
S_1 = 1 + 1 = 2
S_2 = 2 + 1/2 = 5/2
```

Since `exp(1) > S_N(1)` for all N (positive terms), `S_2 = 5/2 > 2` suffices as a bit-exact rational dominance witness. The minimum Phase 0 surface is: `egpt_from_i64`, `egpt_add`, `egpt_mul`, `egpt_div`, `egpt_cmp`, `egpt_free`, `egpt_print`. ~50 lines of `#[no_mangle]` shim.

---

## 5. Decisions made this session (2026-04-24)

Recorded here so a cold-start agent does not re-litigate them.

| # | Decision | Rationale |
|---|---|---|
| D1 | Target theorem = `Real.exp 1 > 2` | Simplest classical-over-ℝ theorem with a bit-exact rational witness. Verifiable by hand. |
| D2 | Realizer registry (Coq `Extract Constant`) — NOT universal Beth-collapse | `AbadirCompletenessTheorem` is scope-restricted and not load-bearing for per-constant realizers. User preference: engineering over theorem-proving. |
| D3 | C runtime = roll our own on top of `egpt_num` | Bit-exact, BigInt-backed, JS-parity-tested. No iRRAM/MPFR dependency. |
| D4 | FFI lives in public FRAQTL `egpt_num` crate | Additive `#[no_mangle]` shim; no private math logic exposed. |
| D5 | Branch for FFI work = `feat/egpt-num-cffi` in FRAQTL | Independent from Lean extraction branch so C-ABI can ship separately. |
| D6 | Branch for Lean extraction = `feat/extraction-prototype` in EGPT-research | Keeps Lean-side deliverables private per user instruction. |
| D7 | Phase 0 first (runtime alone, ~1–2 hrs), Phase 1 second (Lean meta-program) | Prove runtime half standalone before wiring extraction on top. |
| D8 | Cloud KB not required for this session's work | FFI is additive; user waived C. |
| D9 | `evaluate_binary_sequence` docstring is known overstated — do not fix this session | Note in ARCHITECTURE.md when written. |
| D10 | Option A for `Classical.choice` realizer = registry lookup returning canonical inhabitant; fallback = static error at extract time | Matches Coq semantics. No runtime panics. |

---

## 6. Files produced this session

- [AxiomProbe.lean](../AxiomProbe.lean) — consolidated `#print axioms` probe. Keep in repo for reproducibility.
- [AUDIT.md](AUDIT.md) — this file.
- [PLAN.md](PLAN.md) — Phase 0/1 steps; see companion document.

---

## 7. Open questions for a future session

Surface before any architectural next step:

1. **Precision threading for transcendentals beyond `exp(1) > 2`.** Once we target theorems where the inequality is *tight* (e.g., `Real.exp 1 < 3`), Taylor partial sums don't immediately witness. Do we (a) alternate upper/lower-bound series, (b) thread a precision budget through extracted C, or (c) accept "inconclusive within budget" as a valid extraction output? Deferred until a tight-inequality target appears.
2. **Subtype/Quotient realizers.** Mathlib `noncomputable def` often hides behind quotient lifts. The sketch answer — register a `CanonicalRepresentative` realizer per target quotient — is untested. Deferred until a target theorem exercises it.
3. **Correctness meta-theorem.** We claim "extracted C output corresponds to the theorem's ℝ-valued statement" because `entropyRealEquivReal` is a proven bijection. A formal proof that the realizer output composes correctly with the bijection is deferred — acceptable for a prototype, must be written before production.
4. **Sharing extracted C runtime across multiple theorems.** Phase 0/1 will emit per-theorem C files that each link against `libegpt_num`. When we scale to multiple theorems, do they share a single runtime TU or bundle it each time? Engineering detail, deferred.

---

## 8. Pointers for a cold-start agent

- Handoff brief: [`EGPT-research/PRIVATE/Zulip_Clean_Forward_Boundary.md`](../../../PRIVATE/Zulip_Clean_Forward_Boundary.md) — original framing; read §"Agent Handoff" onward. Note that §1–2 framing is superseded by this AUDIT under the realizer-registry reframing.
- Tower entry point: [`InformationTheory/EntropyNumber/Basic.lean`](../InformationTheory/EntropyNumber/Basic.lean).
- Beth-collapse scope boundary: [`ContinuumHypothesis.lean:218–244`](../InformationTheory/EntropyNumber/ContinuumHypothesis.lean#L218) (`TypeTheoryConstructible` inductive). Do not assume it covers an arbitrary Mathlib type.
- Runtime entry point: [`fat/crates/egpt_num/src/lib.rs`](../../../../../Unkamon/FRAQTL/fat/crates/egpt_num/src/lib.rs).
- JS reference for transcendentals: [`EGPTranscendental.js`](../../../../../Unkamon/FRAQTL/egpt/EGPTMath/js/model/core/EGPTranscendental.js).
- To reproduce the axiom report: from `Lean/EGPT/`, run `lake build InformationTheory.EntropyNumber.ContinuumHypothesis && lake env lean AxiomProbe.lean`.
- To cold-start without replaying this session: read AUDIT.md → PLAN.md → open the relevant branch (`feat/extraction-prototype` in EGPT-research for Lean work, `feat/egpt-num-cffi` in FRAQTL for FFI work).
