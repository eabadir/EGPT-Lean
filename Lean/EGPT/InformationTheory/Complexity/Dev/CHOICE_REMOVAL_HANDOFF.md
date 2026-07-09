# Choice-Removal in RotaEntropy.lean — Agent Handoff

> **Mission in one line.** Extend the `{propext, Quot.sound}`-closure group of theorems in `Lean/EGPT/InformationTheory/` by removing `Classical.choice` from the Rota / FTA / Shannon-entropy cluster, group by group, prioritising the load-bearing chain anchored at `RotaEntropy.lean`.
>
> **Where we are.** We have successfully eliminated `Classical.choice` from the Fundamental Theorem of Arithmetic (Information Form) by building the "Constructive Logarithms Bijective Chain" (`fta_via_information_C`), and we have established the direct, choice-free, purely integer hook between `InformationSource` and `EntropyNat` (`sourceToEntropyNat`).
>
> **Last commit on file changes:** The Bijective Chain architecture has been cleanly separated and compiled. The codebase is green and ready for the next wave of targets.

---

## 1. Context the cold-start agent must absorb first

Before doing anything, the agent must:

1. **Read this whole doc.**
2. **Read [`CLAUDE.md`](CLAUDE.md)** (Lean/EGPT-local), which establishes the proof discipline R1–R10.
3. **Read [`PROOF_CHAINS.md`](../PROOF_CHAINS.md)** (top-level `Lean/`), which lists the three P=NP chains and their capstones.
4. **Skim [`EGPT_PROOFS_VALIDATION.md`](../EGPT_PROOFS_VALIDATION.md)** for the current axiom inventory by theorem.
5. **Run [`build_report.lean`](build_report.lean)** locally to get fresh axiom data:
   ```bash
   cd Lean/EGPT && lake env lean build_report.lean > /tmp/run.txt 2>&1
   ```
   Takes ~10 s on a warm cache. Look for `depends on axioms: [propext, Classical.choice, Quot.sound]` rows — those are the remaining targets.
6. **Query the EGPT KB** (cloud-brain) at session start with `--new` on `unk-cos` and a topical `--app egpt` query — this is mandatory per the org's CLAUDE.md classification.

The discipline R3 / R4 / R5 in [`CLAUDE.md`](../EGPT/extraction/CLAUDE.md) is **non-negotiable**: never paraphrase Lean facts; always cite `file:line`. Never claim a theorem fails without a specific `lake build` error.

---

## 2. The Architecture We Built (The Bijective Chain)

Lean 4 has three built-in axioms: `propext`, `Quot.sound`, and `Classical.choice`. The entire Translation1–7 / CNF / polynomial chain was already choice-free. We have now extended this to include the extraction of logarithms and Source Coding.

### A. Constructive Logarithms (`InformationTheory/EntropyNumber/LogarithmBijective.lean`)
We could not globally equivalence `EntropyReal ≃ EntropyNat` due to Cantor's theorem ($\beth_1 > \beth_0$). Instead, we built a computable extraction of the base-2 logarithm bit-stream directly from integer arithmetic:
1. `logb_C` extracts the exact fractional and integer bits natively.
2. `ConstructibleLog` is the subset of `EntropyReal` bundled with its `PNat` source.
3. **The Engine:** `logEquivPNat` forms the rigorous bijection `ConstructibleLog ≃ PNat`.
4. **Additivity Without Limits:** By pulling back integer multiplication, we defined `log_add` structurally. The identity $\log(x \times y) = \log x + \log y$ comes for free without doing infinite series real analysis.

### B. Choice-Free Factorisation (`InformationTheory/EntropyNumber/Factorization.lean`)
Mathlib's `Nat.factorization` carries `Classical.choice` deep in its dependency tree. We moved the purely structural, fuel-bounded `factorListAux` and `factorListC` into their own foundational file so both the `Translation6` rational matrix reduction and `RotaEntropy` can access them without creating circular dependencies.

### C. The Choice-Free SCT Bridge (`InformationTheory/Entropy/SourceCoding.lean`)
We added the direct hook connecting Shannon Source Coding directly to the EGPT number-system bijection.
Instead of relying on analytical `Real.log` limits for Shannon entropy, we created `computableEntropyCeil`. Since $H_{total} = \log_2(A/B)$ for purely integer $A$ and $B$, we use a `Nat.log2` bit-length extraction. `sourceToEntropyNat` relies ONLY on `[propext]`.

---

## 3. State of the World (verified `file:line`)

### Choice-free building blocks (verified `does not depend on any axioms` or `{propext, Quot.sound}`)

| Primitive | File | Closure | Purpose |
|---|---|---|---|
| `factorListC` | `EntropyNumber/Factorization.lean` | **no axioms** | Choice-free factoriser replacing `Nat.factorization`. |
| `nthPrimeC` / `nthOddPrimeC` | `Complexity/CNF/Prime.lean` | **no axioms** | Choice-free prime sequence. |
| `evaluate_binary_sequence` | `EntropyNumber/Real.lean:95` | `noncomputable` but choice-free | "Clean Forward Trip" — constructive `EntropyReal → ℝ` surjection. |
| `logb_C` | `EntropyNumber/LogarithmBijective.lean` | `{propext}` | Computable base-2 log bit-stream generator. |
| `ConstructibleLog`, `log_add_list` | `EntropyNumber/LogarithmBijective.lean` | `{propext}` | Bijective subtype and its purely structural additive map. |
| `sourceToEntropyNat` | `Entropy/SourceCoding.lean` | `{propext}` | The SCT → EGPT-number boundary, purely in ℕ. |
| `fta_via_information_C` | `EntropyNumber/RotaEntropy.lean:534` | `{propext, Quot.sound}` | **The choice-free FTA.** |

### Remaining Choice-Using Targets (The Frontier)

The remaining `[Classical.choice]` targets in the Rota / Shannon cluster are:

| Theorem | File:line | Primary Culprit / Note |
|---|---|---|
| `rota_all_entropy_scaled_shannon` | `RotaEntropy.lean:110` | Transitive via `Real.toNNReal`, Mathlib's Jensen/BinaryEntropy chain |
| `entropy_of_fair_coin_is_one_bit` | `RotaEntropy.lean:307` | Uses `Real.log 2` natively |
| `fta_via_information` | `RotaEntropy.lean:494` | The legacy FTA statement using `Real.logb 2`. |
| `fta_via_entropy_bits` | `RotaEntropy.lean:507` | Same as above. |
| `total_entropy_from_classes_eq_shannon_formula` | `RotaEntropy.lean:772` | `Real.logb` expansions. |
| `PrimeAtoms.factorial_information_*` | `EntropyNumber/PrimeAtoms.lean` | `Real.logb` |

---

## 4. Anti-Patterns and Traps (learnt the hard way)

1. **Do not trust `Nat.*` Mathlib lemmas' choice-freeness on faith.** Always `#print axioms`. The whole `Nat.factorization` / `Nat.primeFactorsList` / `Nat.minFac` tree pulls `Classical.choice` via `Nat.find`.
2. **Do NOT use `Classical.choose` on `evaluate_binary_sequence`:** `evaluate_binary_sequence` is surjective, meaning a bit-stream exists for every real. Do not extract it using choice. Use an explicitly computable extractor (like `logb_C`).
3. **Do NOT attempt `EntropyReal ≃ EntropyNat` globally:** Cantor's theorem ($\beth_1 > \beth_0$) forbids this. The bijective chain must operate specifically on discrete subsets (like `ConstructibleLog`).
4. **Assume what you need is already proved and DO NOT reinvent the wheel:** Anything we might think needs to be proved is likely to have already been proved. If you get stuck or find yourself building complex real analysis from scratch, **STOP** and ask the user for help or pointers. For example, `rota_uniqueness` (`Uniqueness.lean:942-953`) already proves that the logarithm is derived directly from discrete probability (including continuity via the `HasRotaEntropyAxioms`). 
5. **Do not modify the three P=NP capstones.** They are already `{propext, Quot.sound}`-closed and externally cited.

---

## 5. Next Actions for the Cold-Start Agent

1. Open this file end-to-end. Open [`CLAUDE.md`](CLAUDE.md).
2. Run `cd Lean/EGPT && lake env lean build_report.lean > /tmp/run.txt 2>&1`. Verify exit 0. Look at the `depends on axioms:` output to orient yourself.
3. Review `InformationTheory/EntropyNumber/LogarithmBijective.lean` and `InformationTheory/Entropy/SourceCoding.lean` (specifically `computableEntropyCeil`) to understand how we achieved the last wave of removals without doing real-valued limits.
4. **Ask the user what to target next.** The legacy `Real.logb` formulations in `PrimeAtoms.lean` and `RotaEntropy.lean` can likely be replaced by `logb_C` and folded cleanly.

---

## 6. Build Invocation Reference

| Task | Command | Time |
|---|---|---|
| Full build | `cd Lean/EGPT && lake build` | ~15 s warm, several min cold |
| Run build_report | `cd Lean/EGPT && lake env lean build_report.lean` | ~10 s |
| Check one theorem's axioms | Create temp `.lean` with `import InformationTheory; #print axioms <full.namespace.Name>` then `lake env lean /tmp/check.lean` | ~5 s |

All commands run from a shell with `bash -c 'cd ... && ...'` because the harness does not persist `cd` between invocations.