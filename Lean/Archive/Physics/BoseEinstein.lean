import Mathlib.Data.Sym.Card

import Archive.Core
import Archive.Entropy.Common
import Archive.Physics.Common
import Archive.Entropy.RET
import Archive.Physics.UniformSystems

namespace EGPT.Physics.BE

open Multiset NNReal Finset Function -- Added Function for comp_apply

open EGPT.Entropy.RET

open Multiset NNReal
open EGPT
open EGPT.Entropy.Common
open EGPT.Physics.Common
open EGPT.Physics.UniformSystems


/-!
## Phase 1: Combinatorial Structure (Uniform Distribution Statespace & Equivalence to Multisets)

Defines the standard BE state space to be uniform `OmegaUD` over the microstates (occupancy vectors summing to M) and shows it is equivalent to `SymFin N M` (multisets of size M over Fin N).
-/
noncomputable def p_BE (N M : ℕ) : OmegaUD N M → NNReal :=
   p_UD N M


/-!
## Bose Einstein: Cardinality and Iteration
With the equivalence established, we can now define a `Fintype` instance for `OmegaUD`.
-/


/--
Calculates the cardinality of the Bose-Einstein state space `OmegaUD N M`.
This is the number of ways to distribute `M` indistinguishable particles into `N`
distinguishable energy states, which is given by the multichoose function `Nat.multichoose N M`.
This corresponds to the "stars and bars" formula `(N + M - 1) choose M`.
The proof relies on the equivalence `mbStateEquivMultiset` between `OmegaUD N M`
and `SymFin N M` (multisets of size `M` over `Fin N`), and the known cardinality
of `SymFin N M` from Mathlib (`Sym.card_fintype`).
-/
lemma card_omega_be (N M : ℕ) :
    Fintype.card (OmegaUD N M) = Nat.multichoose N M := by
  rw [Fintype.card_congr (udStateEquivMultiset N M)]
  -- Goal is now: Fintype.card (SymFin N M) = Nat.multichoose N M
  -- SymFin N M is defined as Sym (Fin N) M.
  -- Sym.card_fintype states: Fintype.card (Sym α k) = Nat.multichoose (Fintype.card α) k
  rw [Sym.card_sym_eq_multichoose (Fin N) M]
  -- Goal is now: Nat.multichoose (Fintype.card (Fin N)) M = Nat.multichoose N M
  rw [Fintype.card_fin N]
  -- Goal is now: Nat.multichoose N M = Nat.multichoose N M, which is true by reflexivity.


/-- `Nat.multichoose` is positive exactly when we can really place
    `k` indistinguishable balls into `n` labelled boxes – i.e.
    either we have at least one box (`n ≠ 0`) or there is nothing
    to place (`k = 0`). -/
lemma multichoose_pos_iff (n k : ℕ) :
    0 < Nat.multichoose n k ↔ (n ≠ 0 ∨ k = 0) := by
  -- split on the trivial `k = 0` case
  by_cases hk : k = 0
  · subst hk
    simp [Nat.multichoose_zero_right]  -- `1 > 0`
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    -- now analyse `n`
    cases n with
    | zero =>
        -- `n = 0`, `k > 0`  ⇒  multichoose vanishes
        have h0 : Nat.multichoose 0 k = 0 := by
          -- stars‑&‑bars gives a too‑large binomial coefficient
          have hlt : k - 1 < k := Nat.pred_lt (Nat.ne_of_gt hkpos)
          rw [Nat.multichoose_eq]
          rw [Nat.zero_add]
          exact (Nat.choose_eq_zero_of_lt hlt)
        simp [h0, hk]
    | succ n' =>
        -- `n = n'.succ`, `k > 0`  ⇒  multichoose positive
        have hle : k ≤ n' + k := by
          simpa [add_comm] using Nat.le_add_left k n'
        have : 0 < (n' + k).choose k := Nat.choose_pos hle
        simpa [Nat.multichoose_eq, Nat.succ_eq_add_one,
               add_comm, add_left_comm, add_assoc, hk] using this

/-- Proves that the cardinality of the Bose-Einstein state space OmegaUD N M is positive
under the condition that either the number of states N is non-zero or the number of
particles M is zero. This condition is necessary and sufficient for Nat.multichoose N M
to be positive. This lemma is important for defining probabilities, as it ensures the
denominator (total number of states) is not zero. -/
lemma card_omega_BE_pos (N M : ℕ) (h : N ≠ 0 ∨ M = 0) :
    0 < Fintype.card (OmegaUD N M) := by
  -- the heavy lifting is `multichoose_pos_iff`
  simpa [card_omega_be, multichoose_pos_iff] using h

/-!
## Phase 3: Probability Distribution
With cardinality established, we can define the Bose-Einstein probability distribution.
We assume equiprobability of all microstates (configurations).
-/


lemma p_BE_sums_to_one (N M : ℕ) (h_domain_valid : N ≠ 0 ∨ M = 0) :
    ∑ q : OmegaUD N M, (p_UD N M q) = 1 := by
  let card_val := Fintype.card (OmegaUD N M)
  have h_card_pos : card_val > 0 := card_omega_BE_pos N M h_domain_valid

  -- Substitute the definition of p_UD and simplify using h_card_pos
  -- p_UD N M q simplifies to uniformProb card_val,
  -- which simplifies to (card_val : NNReal)⁻¹ because card_val > 0.
  -- Step 1: Substitute the definition of p_UD
  simp_rw [p_UD]
  -- After this, p_UD N M q becomes uniformProb card_val q

  -- Step 2: Substitute the definition of uniformProb
  -- This will introduce an if-then-else expression:
  -- (if card_val > 0 then fun _ => (card_val : NNReal)⁻¹ else fun _ => 0) q
  -- which simplifies to: if card_val > 0 then (card_val : NNReal)⁻¹ else 0
  simp_rw [uniformProb]

  -- Step 3: Simplify the if-then-else expression using h_card_pos (which states card_val > 0)
  -- This should rewrite (if card_val > 0 then (card_val : NNReal)⁻¹ else 0) to (card_val : NNReal)⁻¹
  rw [dif_pos h_card_pos]

  -- The sum is now of a constant term (card_val : NNReal)⁻¹ over all elements in OmegaUD N M.
  -- Finset.sum_const: ∑ _x ∈ s, c = Finset.card s • c
  -- Finset.card_univ for a Fintype is Fintype.card
  rw [Finset.sum_const, Finset.card_univ]
  -- The sum is now (Fintype.card (OmegaUD N M)) • (card_val : NNReal)⁻¹
  -- which is card_val • (card_val : NNReal)⁻¹

  -- Convert nsmul (ℕ • NNReal) to multiplication (NNReal * NNReal)
  rw [nsmul_eq_mul]
  -- The sum is now (↑card_val : NNReal) * (↑card_val : NNReal)⁻¹

  -- To use mul_inv_cancel₀, we need to show (card_val : NNReal) ≠ 0.
  have h_card_nnreal_ne_zero : (card_val : NNReal) ≠ 0 := by
    -- For a natural number n, (n : NNReal) = 0 if and only if n = 0.
    -- So, (n : NNReal) ≠ 0 if and only if n ≠ 0.
    -- We have h_card_pos : card_val > 0, which implies card_val ≠ 0.

    -- Step 1: Use `norm_cast` to simplify the coercion.
    -- This tactic applies `@[norm_cast]` lemmas like `NNReal.coe_ne_zero {n : ℕ}`.
    -- It should change the goal from `(↑card_val : NNReal) ≠ 0` to `card_val ≠ 0`.
    norm_cast
    -- The previous `simp only [NNReal.coe_ne_zero]` might have issues if the
    -- wrong `coe_ne_zero` lemma was being considered or if matching failed.

    -- Step 2: Prove `card_val ≠ 0` using `h_card_pos`.
    -- `h_card_pos` states `card_val > 0` (which is `0 < card_val`).
    -- `Nat.pos_iff_ne_zero.mp` is the implication `(0 < n) → (n ≠ 0)`.
    -- Thus, `Nat.pos_iff_ne_zero.mp h_card_pos` is a proof of `card_val ≠ 0`.
    exact Nat.pos_iff_ne_zero.mp h_card_pos
    -- This replaces the previous two steps:
    -- rw [←Nat.pos_iff_ne_zero]
    -- assumption

  -- Apply mul_inv_cancel₀
  rw [mul_inv_cancel₀ h_card_nnreal_ne_zero]
  -- The goal is now 1 = 1, which is true by reflexivity.


/--
Proves that the adapted Bose-Einstein probability distribution `p_BE_fin N M`
(which is uniform over `Fin (Fintype.card (OmegaUD N M))`) sums to 1.
This confirms it's a valid probability distribution.
Requires the domain to be valid (`N ≠ 0 ∨ M = 0`) to ensure positive cardinality.
-/
lemma p_BE_fin_sums_to_one (N M : ℕ) (h_domain_valid : N ≠ 0 ∨ M = 0) :
    ∑ i : Fin (Fintype.card (OmegaUD N M)), (p_UD_fin N M i) = 1 := by
  let k := Fintype.card (OmegaUD N M)
  have hk_pos : k > 0 := card_omega_BE_pos N M h_domain_valid

  -- By definition, p_BE_fin N M i is uniformProb k.
  -- So the sum becomes ∑ (i : Fin k), uniformProb k.
  -- This can be simplified by rewriting the summand using the definition of p_BE_fin.
  simp_rw [p_UD_fin]

  -- The goal is now ∑ (_ : Fin k), uniformProb k = 1.
  -- This is exactly the statement of `sum_uniform_eq_one` with k and hk_pos.
  exact sum_uniform_eq_one hk_pos



/--
Helper lemma to show that `p_UD_fin N M` (which is `uniformProb k_card` for each entry)
is pointwise equal to `uniformDist` on `Fin k_card`.
This version uses a micro-lemma `Fintype_card_fin_pos` for clarity in the positivity argument.
-/
lemma p_BE_fin_is_uniformDist (N M : ℕ) (h_domain_valid : N ≠ 0 ∨ M = 0) :
    let k_card := Fintype.card (OmegaUD N M)
    have hk_card_pos : k_card > 0 := card_omega_BE_pos N M h_domain_valid
    -- The RHS now uses the clean Fintype_card_fin_pos lemma for its argument
    p_UD_fin N M = uniformDist (Fintype_card_fin_pos hk_card_pos) := by
  let k_card := Fintype.card (OmegaUD N M)
  have hk_card_pos : k_card > 0 := card_omega_BE_pos N M h_domain_valid

  -- Prove by functional extensionality: show they are equal for any input `i`.
  funext i

  -- LHS processing:
  -- Unfold p_BE_fin. The definition of p_BE_fin is:
  --   noncomputable def p_BE_fin (N M : ℕ) : Fin (Fintype.card (OmegaUD N M)) → NNReal :=
  --     fun _i => uniformProb (Fintype.card (OmegaUD N M))
  -- So, (p_BE_fin N M i) becomes (uniformProb k_card).
  -- Unfold uniformProb. The definition is:
  --   noncomputable def uniformProb (n : ℕ) : NNReal :=
  --     if _hn : n > 0 then (n⁻¹ : NNReal) else 0
  -- So, (uniformProb k_card) becomes (if _hn : k_card > 0 then (k_card⁻¹ : NNReal) else 0).
  -- Since we have `hk_card_pos : k_card > 0`, this simplifies to (k_card⁻¹ : NNReal).

  -- RHS processing:
  -- Unfold uniformDist. The definition is:
  --   noncomputable def uniformDist {α : Type*} [Fintype α]
  --       (_h_card_pos : 0 < Fintype.card α) : α → NNReal :=
  --   λ _ ↦ (Fintype.card α : NNReal)⁻¹
  -- Here, α is `Fin k_card`.
  -- The argument `_h_card_pos` is `Fintype_card_fin_pos hk_card_pos`.
  -- So, (uniformDist (Fintype_card_fin_pos hk_card_pos) i) becomes
  --   (Fintype.card (Fin k_card) : NNReal)⁻¹.
  -- Since `Fintype.card (Fin k_card)` is `k_card` (from `Fintype.card_fin`),
  -- this becomes `(k_card : NNReal)⁻¹`.

  -- The simp tactic should handle these unfoldings.
  -- The crucial part is that the `if` on the LHS (from uniformProb) needs to be resolved.
  simp only [p_UD_fin, uniformProb, uniformDist, Fintype.card_fin]
  -- After this, the goal becomes:
  -- `(if hk_card_pos' : k_card > 0 then (k_card : NNReal)⁻¹ else 0) = (k_card : NNReal)⁻¹`
  -- where `hk_card_pos'` is the `_hn` from `uniformProb`.
  -- We have `hk_card_pos : k_card > 0` in the context.
  -- We need to tell Lean that `hk_card_pos'` is true because of `hk_card_pos`.
  rw [dif_pos hk_card_pos]

/--
Helper lemma to show that applying an entropy function `H_func` to `p_BE_fin N M`
(coerced to `Real`) is equivalent to evaluating `f0 H_func k_card` (coerced to `Real`),
where `k_card` is the cardinality of the state space.
-/
lemma H_p_BE_fin_eq_f_H_card (N M : ℕ) (h_domain_valid : N ≠ 0 ∨ M = 0)
    (H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal)
    (hH_axioms : HasRotaEntropyProperties H_func) :
    (H_func (p_UD_fin N M) : ℝ) = (f0 hH_axioms (Fintype.card (OmegaUD N M)) : ℝ) := by
  let k_card := Fintype.card (OmegaUD N M)
  have hk_card_pos : k_card > 0 := card_omega_BE_pos N M h_domain_valid

  -- Step 1: Rewrite LHS using p_BE_fin_is_uniformDist
  -- This changes H_func(p_BE_fin N M) to H_func(uniformDist (Fintype_card_fin_pos hk_card_pos))
  rw [p_BE_fin_is_uniformDist N M h_domain_valid]

  -- Step 2: Simplify the RHS.
  -- We want to show: (f0 hH_axioms k_card : ℝ) = (H_func (uniformDist (Fintype_card_fin_pos hk_card_pos)) : ℝ)
  -- First, unfold f0.
  simp only [f0]
  -- The RHS's NNReal part is now `if _hn : k_card > 0 then f hH_axioms _hn else 0`.
  -- The coercion to Real distributes over the if: `if _hn : k_card > 0 then ↑(f hH_axioms _hn) else ↑0`.
  -- Now, simplify the if using hk_card_pos.
  rw [dif_pos hk_card_pos]
  -- Now RHS is `↑(f hH_axioms hk_card_pos)`.

  -- Step 3: Unfold f on the RHS.
  -- The term `f hH_axioms hk_card_pos` is defined as:
  -- `let α_k_card := Fin k_card;
  --  have h_card_pos_f_def : 0 < Fintype.card α_k_card := Fintype_card_fin_pos hk_card_pos;
  --  H_func (uniformDist h_card_pos_f_def)`
  -- This `uniformDist` uses `h_card_pos_f_def`, which is `Fintype_card_fin_pos hk_card_pos`.
  -- The `uniformDist` on the LHS also uses `Fintype_card_fin_pos hk_card_pos`.
  -- So, the arguments to H_func should be identical.
  simp only [f]
  -- After this, both sides should be `(H_func (uniformDist (Fintype_card_fin_pos hk_card_pos)) : ℝ)`.
  -- Therefore, reflexivity should close the goal.


theorem H_BE_from_Multiset_eq_C_shannon (N M : ℕ) (h_domain_valid : N ≠ 0 ∨ M = 0) :
    (EGPT.Physics.Common.H_physical_system (p_UD_fin N M) : ℝ) =
      (EGPT.Physics.Common.C_physical_NNReal : ℝ) *
      stdShannonEntropyLn (p_UD_fin N M) := by
  -- The proof is exactly what H_physical_system_is_rota_uniform does.
  exact H_physical_system_is_rota_uniform N M h_domain_valid
