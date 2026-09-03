import Mathlib.Data.Sym.Card
import Archive.Basic
import Archive.Core
import Archive.Entropy.RET
import Archive.Entropy.Common
import Archive.Physics.Common


namespace EGPT.Physics.UniformSystems



open Multiset NNReal
open EGPT EGPT.Basic
open EGPT.Entropy.Common EGPT.Entropy.RET
open EGPT.Physics.Common



open Fin Real NNReal Nat Multiset Finset



/--
Proof that `canonicalUniformDist k hk_pos` sums to 1.
This directly uses `sum_uniformDist` with the appropriate proof of positivity
for `Fintype.card (Fin k)`.
-/
lemma sum_canonicalUniformDist_eq_one (k : ℕ) (hk_pos : k > 0) :
    (∑ i, canonicalUniformDist k hk_pos i) = 1 := by
  simp only [canonicalUniformDist] -- Unfold to uniformDist (Fintype_card_fin_pos hk_pos)
  exact sum_uniformDist (Fintype_card_fin_pos hk_pos)

/--
Symmetry of `stdShannonEntropyLn`: `stdShannonEntropyLn (p ∘ e) = stdShannonEntropyLn p`
for an `Equiv e : α ≃ β` between two Fintypes `α` and `β`,
and a target distribution `p_target : β → NNReal`.
The sum `∑ x:α, negMulLog(p_target(e x))` is transformed to `∑ y:β, negMulLog(p_target y)`.
-/
theorem stdShannonEntropyLn_comp_equiv {α β : Type*} [Fintype α] [Fintype β]
    (p_target : β → NNReal) (e : α ≃ β) :
    stdShannonEntropyLn (p_target ∘ e) = stdShannonEntropyLn p_target := by
  -- Unfold stdShannonEntropyLn on both sides to expose the sums.
  unfold stdShannonEntropyLn
  -- LHS: ∑ (x : α), negMulLog ((p_target (e x)) : ℝ)
  -- RHS: ∑ (y : β), negMulLog ((p_target y) : ℝ)
  -- Apply Function.comp_apply to the term inside the sum on the LHS.
  simp_rw [Function.comp_apply]
  -- LHS is now: ∑ (x : α), negMulLog ((p_target (e x)) : ℝ)
  -- Let g(y) := negMulLog ((p_target y) : ℝ).
  -- LHS is ∑ (x : α), g (e x).
  -- Equiv.sum_comp states: (∑ x, g (e x)) = (∑ y, g y).
  exact Equiv.sum_comp e (fun (y : β) => negMulLog ((p_target y) : ℝ))

-- We'll continue with `stdShannonEntropyLn_canonicalUniform_eq_log_k` and the main theorem
-- `H_uniform_mapped_dist_eq_C_shannon` once this part is verified.


theorem H_canonical_uniform_eq_C_shannon
    (H_func : ∀ {α_aux : Type} [Fintype α_aux], (α_aux → NNReal) → NNReal)
    (hH_axioms : HasRotaEntropyProperties H_func)
    (k : ℕ) (hk_pos : k > 0) :
    -- Removed 'let p_unif_k := canonicalUniformDist k hk_pos' from the statement
    (H_func (canonicalUniformDist k hk_pos) : ℝ) = (C_constant_real hH_axioms) * stdShannonEntropyLn (canonicalUniformDist k hk_pos) := by
  let p_unif_k := canonicalUniformDist k hk_pos

  -- Explicitly show that (H_func p_unif_k : ℝ) is equivalent to (f0 hH_axioms k : ℝ)
  have h_lhs_eq_f0_val : (H_func p_unif_k : ℝ) = (f0 hH_axioms k : ℝ) := by
    -- Unfold definitions to show both sides are definitionally equal to
    -- (H_func (uniformDist (Fintype_card_fin_pos hk_pos)) : ℝ)
    simp only [p_unif_k, canonicalUniformDist, uniformDist, Fintype_card_fin_pos,
               f0, f, dif_pos hk_pos]
    -- At this point, both sides should be identical after simp.

  -- Rewrite the LHS of the main goal using this equality
  rw [h_lhs_eq_f0_val]
  -- Now the goal is: (f0 hH_axioms k : ℝ) = (C_constant_real hH_axioms) * stdShannonEntropyLn p_unif_k

  -- Now use RotaUniformTheorem, which applies to (f0 hH_axioms k : ℝ)
  rw [(RotaUniformTheorem_formula_with_C_constant hH_axioms).right k hk_pos]
  -- Goal: C_constant_real hH_axioms * Real.log k = C_constant_real hH_axioms * stdShannonEntropyLn p_unif_k
  -- Need stdShannonEntropyLn p_unif_k = Real.log k
  rw [stdShannonEntropyLn_canonicalUniform_eq_log_k k hk_pos]
  -- Goal is now an identity: C * log k = C * log k

/--
Helper Lemma: Shows that a system distribution `p_sys`, if uniform on `Ω_sys` with cardinality `k`,
is equivalent to the canonical uniform distribution on `Fin k` composed with the equivalence
`e_sys_to_fin_k : Ω_sys ≃ Fin k`.
-/
lemma p_sys_eq_canonical_comp_equiv
    {Ω_sys : Type} [Fintype Ω_sys]
    (p_sys : Ω_sys → NNReal)
    (k : ℕ) (hk_pos : k > 0)
    (hp_sys_is_uniform : p_sys = fun (_ : Ω_sys) => (k : NNReal)⁻¹)
    (e_sys_to_fin_k : Ω_sys ≃ Fin k) :
    p_sys = (canonicalUniformDist k hk_pos) ∘ e_sys_to_fin_k := by
  let p_unif_k := canonicalUniformDist k hk_pos
  funext ω_sys
  rw [hp_sys_is_uniform] -- LHS is k⁻¹
  simp [p_unif_k, canonicalUniformDist, uniformDist, Function.comp_apply, Fintype_card_fin_pos, hk_pos] -- RHS is k⁻¹

lemma H_sys_eq_H_canonical_nnreal_of_comp
    {Ω_sys : Type} [Fintype Ω_sys]
    (H_func : ∀ {α_aux : Type} [Fintype α_aux], (α_aux → NNReal) → NNReal)
    (hH_axioms : HasRotaEntropyProperties H_func)
    (p_sys_arg : Ω_sys → NNReal)
    (k : ℕ) (hk_pos : k > 0)
    (e_sys_to_fin_k : Ω_sys ≃ Fin k)
    (h_p_sys_is_comp : p_sys_arg = (canonicalUniformDist k hk_pos) ∘ e_sys_to_fin_k) :
    H_func p_sys_arg = H_func (canonicalUniformDist k hk_pos) := by
  let p_unif_k := canonicalUniformDist k hk_pos
  rw [h_p_sys_is_comp]
  -- Goal is now H_func (p_unif_k ∘ e_sys_to_fin_k) = H_func p_unif_k
  -- Axiom: symmetry {α} {β} (p_target : β → NNReal) (sum_proof) (e : α ≃ β) : H (p_target ∘ e) = H p_target
  -- Here: α is Ω_sys, β is Fin k, p_target is p_unif_k, e is e_sys_to_fin_k
  exact hH_axioms.symmetry p_unif_k (sum_canonicalUniformDist_eq_one k hk_pos) e_sys_to_fin_k



/--
Helper Lemma: Shows that `stdShannonEntropyLn` of `p_sys`
is equal to `stdShannonEntropyLn` of `canonicalUniformDist k hk_pos`,
given that `p_sys` is the composition of `canonicalUniformDist` with the equivalence `e_sys_to_fin_k`.
-/
lemma stdShannon_sys_eq_stdShannon_canonical
    {Ω_sys : Type} [Fintype Ω_sys]
    (p_sys : Ω_sys → NNReal)
    (k : ℕ) (hk_pos : k > 0)
    (e_sys_to_fin_k : Ω_sys ≃ Fin k)
    (h_p_sys_is_comp : p_sys = (canonicalUniformDist k hk_pos) ∘ e_sys_to_fin_k) :
    stdShannonEntropyLn p_sys = stdShannonEntropyLn (canonicalUniformDist k hk_pos) := by
  let p_unif_k := canonicalUniformDist k hk_pos
  rw [h_p_sys_is_comp] -- LHS becomes stdShannonEntropyLn (p_unif_k ∘ e_sys_to_fin_k)
  -- Goal: stdShannonEntropyLn (p_unif_k ∘ e_sys_to_fin_k) = stdShannonEntropyLn p_unif_k
  -- This is precisely what stdShannonEntropyLn_comp_equiv states.
  -- stdShannonEntropyLn_comp_equiv arguments: p_target (p_unif_k), equiv (e_sys_to_fin_k)
  exact stdShannonEntropyLn_comp_equiv p_unif_k e_sys_to_fin_k

theorem H_physical_dist_eq_C_shannon_if_uniform_and_equiv
    {Ω_sys : Type} [Fintype Ω_sys]
    (H_func : ∀ {α_aux : Type} [Fintype α_aux], (α_aux → NNReal) → NNReal)
    (hH_axioms : HasRotaEntropyProperties H_func)
    (p_sys : Ω_sys → NNReal)
    -- Condition 1: Ω_sys has a known cardinality k > 0
    (k : ℕ) (hk_pos : k > 0) (_h_card_Ω_eq_k : Fintype.card Ω_sys = k)
    -- Condition 2: p_sys is uniform on Ω_sys with this cardinality k
    (hp_sys_is_uniform : p_sys = fun (_ : Ω_sys) => (k : NNReal)⁻¹)
    -- Condition 3: Ω_sys is equivalent to Fin k
    (e_sys_to_fin_k : Ω_sys ≃ Fin k)
    :
    (H_func p_sys : ℝ) = (C_constant_real hH_axioms) * stdShannonEntropyLn p_sys := by

  let p_unif_k := canonicalUniformDist k hk_pos

  -- Prove p_sys is composition (Micro-lemma 1 application)
  have h_psys_is_comp_val : p_sys = p_unif_k ∘ e_sys_to_fin_k :=
    p_sys_eq_canonical_comp_equiv p_sys k hk_pos hp_sys_is_uniform e_sys_to_fin_k

  -- Step 1: Show (H_func p_sys : ℝ) = (H_func p_unif_k : ℝ)
  have h_H_sys_eq_H_unif_k_real : (H_func p_sys : ℝ) = (H_func p_unif_k : ℝ) := by
    have h_nnreal_eq : H_func p_sys = H_func p_unif_k :=
      H_sys_eq_H_canonical_nnreal_of_comp H_func hH_axioms p_sys k hk_pos e_sys_to_fin_k h_psys_is_comp_val
    rw [h_nnreal_eq]

  -- Step 2: Use H_canonical_uniform_eq_C_shannon
  rw [h_H_sys_eq_H_unif_k_real]
  -- Goal is now: (H_func p_unif_k : ℝ) = C_constant_real hH_axioms * stdShannonEntropyLn p_sys
  rw [H_canonical_uniform_eq_C_shannon H_func hH_axioms k hk_pos]
  -- Goal is now: C_constant_real hH_axioms * stdShannonEntropyLn p_unif_k = C_constant_real hH_axioms * stdShannonEntropyLn p_sys

  -- Step 3: Show stdShannonEntropyLn p_sys = stdShannonEntropyLn p_unif_k
  have h_shannon_sys_eq_canon : stdShannonEntropyLn p_sys = stdShannonEntropyLn p_unif_k :=
    stdShannon_sys_eq_stdShannon_canonical p_sys k hk_pos e_sys_to_fin_k h_psys_is_comp_val

  rw [h_shannon_sys_eq_canon] -- Rewrites RHS: C * stdShannon p_unif_k = C * stdShannon p_unif_k
  -- Goal should be reflexive.


/-! # Multiset to Uniform Distribution State Space Mapping by Vectorization
-/
@[reducible] def OmegaUD (N M : ℕ) := MBMacrostate N M


-- Map a uinform distribution state (occupancy vector) to the corresponding multiset of occupied states
-- Example: N=3, M=4, q = (i=0 ↦ 2, i=1 ↦ 1, i=2 ↦ 1) -> {0, 0, 1, 2}
def udStateToMultiset {N M : ℕ} (q : OmegaUD N M) : Multiset (Fin N) :=
  Finset.univ.sum (fun i => replicate (q.val i) i)

-- First provable lemma: The card of the generated multiset is M
lemma card_udStateToMultiset {N M : ℕ} (q : OmegaUD N M) :
    Multiset.card (udStateToMultiset q) = M := by
  -- Unfold the definition of the map
  simp only [udStateToMultiset]
  -- Use the property that card distributes over sum of multisets
  rw [Multiset.card_sum]
  -- Use the property that card of (replicate k a) is k
  simp_rw [Multiset.card_replicate]
  -- The remaining goal is ∑ i in Finset.univ, q.val i = M,
  -- which is exactly the property bundled in the OmegaUD subtype.
  exact q.property

-- Define the map from a multiset of states to an occupancy vector function
-- Example: {0, 0, 1, 2} -> (i=0 ↦ 2, i=1 ↦ 1, i=2 ↦ 1)
def multisetToUDState {N : ℕ} (s : Multiset (Fin N)) : Fin N → ℕ :=
  fun i => Multiset.count i s




/-!
Helper lemma for `left_inv_beState_multiset`.
Shows that counting element `i` in a multiset created by replicating element `j`
yields zero if `i` and `j` are different.
-/
lemma count_replicate_term_zero {N : ℕ} {q : Fin N → ℕ} (i j : Fin N) (hij : i ≠ j) :
    Multiset.count i (Multiset.replicate (q j) j) = 0 := by
  -- Apply the general lemma for counting in a replicated multiset and simplify using hij
  -- We use Ne.symm hij to match the condition `j = i` in `Multiset.count_replicate`.
  simp [Multiset.count_replicate, Ne.symm hij]

/-!
Helper lemma for `left_inv_beState_multiset`.
Shows that counting element `i` in a multiset created by replicating `i` itself
yields the number of replications.
-/
lemma count_replicate_term_eq {N : ℕ} {q : Fin N → ℕ} (i : Fin N) :
    Multiset.count i (Multiset.replicate (q i) i) = q i := by
  -- Apply the specific Mathlib lemma for counting the replicated element itself
  rw [Multiset.count_replicate_self]

/-!
Helper lemma for `left_inv_beState_multiset`.
Shows that the sum of counts over all `j` simplifies to the single term where `j = i`.
-/
lemma sum_count_replicate_eq_single_term {N : ℕ} {q : Fin N → ℕ} (i : Fin N) :
    ∑ j ∈ Finset.univ, Multiset.count i (Multiset.replicate (q j) j) = q i := by
  -- Use Finset.sum_eq_single to isolate the term where j = i
  -- We need to provide:
  -- 1. The index `a` we want to single out (which is `i`).
  -- 2. Proof that for all other indices `b` in the set (`j ∈ Finset.univ`), if `b ≠ a` (`j ≠ i`), the term `f b` is zero.
  -- 3. Proof that if `a` is *not* in the set, then `f a` is zero (this is usually handled by `simp` or trivial for `Finset.univ`).
  rw [Finset.sum_eq_single i]
  -- Prove the main goal after simplification: f i = q i
  · -- The term f i is `Multiset.count i (Multiset.replicate (q i) i)`
    -- Use the previous lemma `count_replicate_term_eq`
    exact count_replicate_term_eq i
  -- Prove side condition 1: ∀ j ∈ Finset.univ, j ≠ i → f j = 0
  · intro j _ hij_ne -- Assume j ∈ Finset.univ and j ≠ i
    -- The term f j is `Multiset.count i (Multiset.replicate (q j) j)`
    -- Use the first lemma `count_replicate_term_zero` with the hypothesis hij_ne
    -- We need Ne.symm because count_replicate_term_zero expects i ≠ j, but hij_ne is j ≠ i.
    exact count_replicate_term_zero i j (Ne.symm hij_ne)
  -- Prove side condition 2: i ∉ Finset.univ → f i = 0
  · intro h_not_mem -- Assume i is not in Finset.univ
    -- This case is impossible for `Fin N` as `i` is always in `Finset.univ`.
    -- `simp` should resolve this, as `i ∈ Finset.univ` is true.
    simp only [Finset.mem_univ, not_true_eq_false] at h_not_mem
    -- Alternatively, directly use the fact that i is always in univ.
    --have : i ∈ Finset.univ := Finset.mem_univ i
    --contradiction -- The assumption h_not_mem contradicts this fact.

-- Make sure this or an equivalent Mathlib lemma is available/imported
-- @[simp] lemma Multiset.count_finset_sum ... (from previous interaction)

/-!
Helper lemma for `left_inv_beState_multiset`.
Applies the distributivity of `Multiset.count` over `Finset.sum`
to the definition of `mbStateToMultiset`.
-/
lemma count_udStateToMultiset_eq_sum_count_replicate {N M : ℕ} (q : OmegaUD N M) (i : Fin N) :
    Multiset.count i (udStateToMultiset q) =
      ∑ j ∈ Finset.univ, Multiset.count i (Multiset.replicate (q.val j) j) := by
  -- Unfold the definition of mbStateToMultiset
  simp only [udStateToMultiset]
  -- Goal: count i (∑ j in Finset.univ, Multiset.replicate (q.val j) j) = ...
  -- Apply the lemma that distributes count over finset sum
  -- (Assuming the lemma Multiset.count_finset_sum provided earlier or similar exists)
  rw [Multiset.count_finset_sum]
  -- The goal should now be definitionally equal, so rfl or simp closes it.



-- Define the map from a multiset known to have card M back to a BE state
-- This bundles the function `multisetToMBState` with the proof that its components sum to M
def multisetToUDStateSubtype {N M : ℕ} (s : SymFin N M) : OmegaUD N M :=
  ⟨ multisetToUDState s.val , -- The function (Fin N → ℕ)
    by
      -- Proof that the sum is M:
      have h_sum := sum_count_eq_card s.val -- ∑ (count i s.val) = card s.val
      simp only [multisetToUDState] -- Unfold definition in the goal
      -- Goal is now ∑ i, count i ↑s = M
      rw [h_sum] -- Rewrite using the sum_count_eq_card lemma result
      -- Goal is now card s.val = M
      exact s.property -- The property bundled with s is card s.val = M
  ⟩

/-!
Lemma: `mbStateToMultiset` and `multisetToMBStateSubtype` are inverses (left inverse).
This proof uses the previously defined micro-lemmas.
-/
lemma left_inv_udState_multiset {N M : ℕ} (q : OmegaUD N M) :
    multisetToUDStateSubtype ⟨udStateToMultiset q, card_udStateToMultiset q⟩ = q := by
  apply Subtype.ext
  -- Instead of using `simp only [multisetToMBStateSubtype, Subtype.mk_val]`,
  -- we use dsimp to reveal the underlying definition.
  dsimp [multisetToUDStateSubtype]
  -- Now the goal is: multisetToMBState (mbStateToMultiset q) = q.val
  funext i
  simp only [multisetToUDState]
  rw [count_udStateToMultiset_eq_sum_count_replicate]
  rw [sum_count_replicate_eq_single_term]
  -- Goal: q.val i = q.val i, which holds.


/-!
Helper lemma for `right_inv_beState_multiset`.
Shows that summing the `replicate (count i s) i` terms over `univ`
equals the sum over just the elements present in the multiset `s` (`s.toFinset`),
because terms for elements not in `s` are the empty multiset (zero).
Uses Finset.sum_subset focusing on the required zero condition.
-/

lemma sum_replicate_count_univ_eq_sum_toFinset {α : Type*} [DecidableEq α] (s : Multiset α) (univ : Finset α) (h_univ : ∀ x : α, x ∈ univ) :
    ∑ i ∈ univ, Multiset.replicate (Multiset.count i s) i = ∑ i ∈ s.toFinset, Multiset.replicate (Multiset.count i s) i := by
  -- Use symmetry to match the structure of Finset.sum_subset conclusion: ∑ s = ∑ t
  apply Eq.symm
  -- Goal: ∑ i in s.toFinset, replicate... = ∑ i in univ, replicate...

  -- Apply Finset.sum_subset {s t} (h_sub : s ⊆ t) (h_zero : ∀ x ∈ t, x ∉ s → f x = 0) : ∑ x in s, f x = ∑ x in t, f x
  apply Finset.sum_subset
  · -- Goal 1: Prove s ⊆ t, i.e., s.toFinset ⊆ univ
    intro x _hx_mem_toFinset -- Assume x ∈ s.toFinset
    -- Prove x ∈ univ using the hypothesis h_univ
    exact h_univ x
  · -- Goal 2: Prove ∀ x ∈ t, x ∉ s → f x = 0
    -- i.e., ∀ x ∈ univ, x ∉ s.toFinset → replicate (count x s) x = 0
    intro x _hx_in_univ hx_not_in_s_toFinset -- Assume x ∈ univ and x ∉ s.toFinset

    -- Derive `x ∉ s` from `x ∉ s.toFinset` explicitly
    have hx_not_mem_s : x ∉ s := by
      -- Multiset.mem_toFinset is an iff `a ∈ s.toFinset ↔ a ∈ s`
      -- We can use its negation. `mt` (modus tollens) might work, or prove by contradiction.
      contrapose! hx_not_in_s_toFinset -- Changes goal to proving `x ∈ s.toFinset` from `x ∈ s`
      rwa [Multiset.mem_toFinset] -- Apply the iff lemma

    -- Apply the lemma showing replicate count is zero when element is not present, using the derived `x ∉ s`
    exact replicate_count_zero_of_not_mem hx_not_mem_s

/-! ## Micro–micro lemmas for the “`a ∈ s`” branch -/

/-- 2.6 (a).  Split the sum over `insert a t` into the
    part without `a` plus the `i = a` summand. -/
lemma sum_insert_split
    {α β} [DecidableEq α] [AddCommMonoid β]
    {a : α} {t : Finset α} (f : α → β) (ha : a ∈ insert a t) :
  (∑ i ∈ insert a t, f i)
    = (∑ i ∈ (insert a t).erase a, f i) + f a :=
by
  -- Apply the lemma that splits the sum
  rw [Finset.sum_eq_sum_diff_singleton_add ha f]
  -- The goal might now be `∑ i in insert a t \ {a}, f i + f a = ∑ i in (insert a t).erase a, f i + f a`
  -- We need to show `insert a t \ {a}` is the same as `(insert a t).erase a`
  -- This should hold definitionally or via a simp lemma like Finset.sdiff_singleton_eq_erase
  -- Let's try simp first, as it might handle this.
  simp only [Finset.sdiff_singleton_eq_erase]
  -- If simp worked, the goal is now trivial (α = α).

/-- 2.6 (b).  `count` for every *other* element is unchanged
    after consing `a`. -/
lemma count_cons_ne'
    {α} [DecidableEq α] {a i : α} (h : i ≠ a) {s : Multiset α} :
  Multiset.count i (a ::ₘ s) = Multiset.count i s :=
by
  --simpa [h] using Multiset.count_cons_of_ne h _   -- already proven in § 2.3
  exact count_cons_ne h s

/-- 2.6 (c).  `replicate` respects (b). -/
lemma replicate_cons_ne'
    {α} [DecidableEq α] {a i : α} (h : i ≠ a) {s : Multiset α} :
  Multiset.replicate (Multiset.count i (a ::ₘ s)) i =
    Multiset.replicate (Multiset.count i s) i :=
by
  simp [count_cons_ne' h]

/-- 2.6 (d).  Rewrite the *tail* of the split sum
    using (c).  -/
lemma tail_sum_cons
    {α} [DecidableEq α] {a : α} {s : Multiset α} :
  (∑ i ∈ (insert a s.toFinset).erase a,
      Multiset.replicate (Multiset.count i (a ::ₘ s)) i)
    =
  (∑ i ∈ s.toFinset.erase a,
      Multiset.replicate (Multiset.count i s) i) :=
by
  -- First, show the summation domains are equal
  rw [Finset.erase_insert_eq_erase]
  -- Now the goal is:
  -- ∑ i in s.toFinset.erase a, Multiset.replicate (Multiset.count i (a ::ₘ s)) i =
  --   ∑ i in s.toFinset.erase a, Multiset.replicate (Multiset.count i s) i
  -- Apply the sum congruence lemma (using Finset.sum_congr directly is often clearer)
  apply Finset.sum_congr rfl -- The domains now match (rfl), need to prove equality of terms
  intro i hi
  -- `i ∈ s.toFinset.erase a` implies `i ≠ a` and `i ∈ s.toFinset`
  simp only [Finset.mem_erase] at hi
  -- hi is now a pair: ⟨i ≠ a, i ∈ s.toFinset⟩
  have hia : i ≠ a := hi.1 -- Corrected: Use hi.1 for the inequality
  -- Use replicate_cons_ne' which requires i ≠ a
  simp [replicate_cons_ne' hia]

/-- 2.6 (e).  The *head* replicate for `a`. -/
lemma head_replicate_cons
    {α} [DecidableEq α] {a : α} {s : Multiset α} :
  Multiset.replicate (Multiset.count a (a ::ₘ s)) a =
    Multiset.replicate 1 a + Multiset.replicate (Multiset.count a s) a :=
by
  simp [Multiset.count_cons_self, replicate_split]

variable {α β : Type*} [DecidableEq α] [AddCommMonoid β]


lemma sum_eq_add_sum_erase {s : Finset α} {a : α} (f : α → β) (h : a ∈ s) :
  ∑ x ∈ s, f x = f a + ∑ x ∈ s.erase a, f x :=
by
   rw [←Finset.sum_insert (Finset.notMem_erase a s)]
   congr
   exact Eq.symm (Finset.insert_erase h)


/-- Final streamlined version of the “`a ∈ s`” inductive step. -/
lemma step_mem
    {α} [DecidableEq α] {a : α} {s : Multiset α}
    (hmem : a ∈ s.toFinset)
    (IH : ∑ i ∈ s.toFinset, Multiset.replicate (Multiset.count i s) i = s) :
  ∑ i ∈ insert a s.toFinset, Multiset.replicate (Multiset.count i (a ::ₘ s)) i
      = a ::ₘ s := by
  -- 1.  Since `a ∈ s.toFinset`, `insert` does nothing.
  have h_insert : insert a s.toFinset = s.toFinset :=
    Finset.insert_eq_of_mem hmem
  simp [h_insert] at IH ⊢                           -- rewrites the goal & IH

-- 2.  Split the sum into the `i = a` part and the tail.
  have h_split :
      (∑ i ∈ s.toFinset, Multiset.replicate (Multiset.count i (a ::ₘ s)) i) =
        Multiset.replicate (Multiset.count a (a ::ₘ s)) a +
        ∑ i ∈ s.toFinset.erase a,
            Multiset.replicate (Multiset.count i (a ::ₘ s)) i := by
    -- Apply the lemma directly, providing the function first, then the membership proof
    exact sum_eq_add_sum_erase
            (fun i ↦ Multiset.replicate (Multiset.count i (a ::ₘ s)) i)
            hmem

  -- 3.  The tail counts are unchanged when `i ≠ a`.
  have h_tail :
      ∑ i ∈ s.toFinset.erase a,
          Multiset.replicate (Multiset.count i (a ::ₘ s)) i =
      ∑ i ∈ s.toFinset.erase a,
          Multiset.replicate (Multiset.count i s) i := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi_ne : i ≠ a := (Finset.mem_erase.1 hi).1
    simp [Multiset.count_cons_of_ne hi_ne]          -- counts coincide

  -- 4.  The head term adds exactly one copy of `a`.
  have h_head :
      Multiset.replicate (Multiset.count a (a ::ₘ s)) a =
        {a} + Multiset.replicate (Multiset.count a s) a := by
    simp [Multiset.count_cons_self, replicate_split]

-- 5.  Assemble:  `lhs = {a} + (∑ over s)` and use the induction hypothesis.
  calc
    (∑ i ∈ s.toFinset, Multiset.replicate (Multiset.count i (a ::ₘ s)) i)
        = {a} + ∑ i ∈ s.toFinset,
            Multiset.replicate (Multiset.count i s) i := by
          rw [h_split]
          rw [h_head]
          rw [h_tail]
          rw [Multiset.add_assoc]
          rw [←sum_eq_add_sum_erase (fun i ↦ Multiset.replicate (Multiset.count i s) i) hmem]
    _ = {a} + s := by
          simp only [IH] -- Changed simpa to simp only
    _ = a ::ₘ s := by
          simp only [Multiset.singleton_add] -- Changed simpa to simp only

/-! ## Micro–micro lemmas for the “`a ∉ s`” branch -/

/-- 2.6 (g).  When `a ∉ s`, its count in `s` is zero. -/
lemma count_not_mem_zero
    {α} [DecidableEq α] {a : α} {s : Multiset α} (h_not_mem : a ∉ s) :
  Multiset.count a s = 0 :=
by
  -- Apply the relevant direction of the iff lemma `Multiset.count_eq_zero`
  exact Multiset.count_eq_zero.mpr h_not_mem

/-- 2.6 (h).  The head replicate collapses to `{a}` if `a ∉ s`. -/
lemma head_replicate_not_mem
    {α} [DecidableEq α] {a : α} {s : Multiset α} (h_not_mem : a ∉ s) :
  Multiset.replicate (Multiset.count a (a ::ₘ s)) a = {a} :=
by
  -- Use count_cons_self: count a (a ::ₘ s) = count a s + 1
  rw [Multiset.count_cons_self]
  -- Use count_not_mem_zero: count a s = 0 since a ∉ s
  rw [count_not_mem_zero h_not_mem]
  -- Simplify the expression: replicate (0 + 1) a = replicate 1 a
  simp only [Nat.zero_add]
  -- Use replicate_one: replicate 1 a = {a}
  rw [Multiset.replicate_one] -- Use the standard Mathlib lemma

/-- 2.6 (i).  Tail sum unchanged when `a ∉ s`. -/
lemma tail_sum_not_mem
    {α} [DecidableEq α] {a : α} {s : Multiset α} (h_not_mem : a ∉ s) :
  (∑ i ∈ s.toFinset,
      Multiset.replicate (Multiset.count i (a ::ₘ s)) i) =
  (∑ i ∈ s.toFinset,
      Multiset.replicate (Multiset.count i s) i) :=
by
  -- Apply sum congruence: need to show terms are equal for i ∈ s.toFinset
  apply Finset.sum_congr rfl -- Domains are the same (rfl)
  intro i hi_mem_finset -- Assume i ∈ s.toFinset (renamed for clarity)
  -- Need to show: replicate (count i (a ::ₘ s)) i = replicate (count i s) i
  -- This holds if i ≠ a. We need to prove i ≠ a from i ∈ s.toFinset and a ∉ s.
  have hi_ne_a : i ≠ a := by
    intro h_eq -- Assume i = a for contradiction
    subst h_eq -- Substitute a for i
    -- Now hi_mem_finset is a hypothesis: a ∈ s.toFinset
    -- We also have the main lemma hypothesis h_not_mem: a ∉ s
    -- Use Multiset.mem_toFinset to show a ∈ s.toFinset implies a ∈ s
    rw [Multiset.mem_toFinset] at hi_mem_finset -- Now hi_mem_finset is: a ∈ s
    -- This contradicts the hypothesis h_not_mem (a ∉ s).
    exact h_not_mem hi_mem_finset
  -- Now apply replicate_cons_ne' which requires i ≠ a
  rw [replicate_cons_ne' hi_ne_a] -- Uses lemma 2.6(c)


/-- 2.6 (j).  Assemble the pieces for `a ∉ s`. -/
lemma step_not_mem
    {α} [DecidableEq α] {a : α} {s : Multiset α}
    (h_not_mem_finset : a ∉ s.toFinset)
    (IH : ∑ i ∈ s.toFinset, Multiset.replicate (Multiset.count i s) i = s) :
  ∑ i ∈ insert a s.toFinset,
      Multiset.replicate (Multiset.count i (a ::ₘ s)) i = a ::ₘ s :=
by
  -- 1. Derive `a ∉ s` from `a ∉ s.toFinset`
  have h_not_mem : a ∉ s := by
    -- `a ∈ s.toFinset ↔ a ∈ s`. We prove the contrapositive.
    contrapose! h_not_mem_finset -- Goal: a ∈ s → a ∈ s.toFinset
    rwa [Multiset.mem_toFinset] -- Apply the iff lemma

  -- 2. Split the sum over `insert a s.toFinset` using `Finset.sum_insert`
  --    Requires `a ∉ s.toFinset`, which is given by `h_not_mem_finset`.
  rw [Finset.sum_insert h_not_mem_finset]
  -- Goal: f a + ∑ i ∈ s.toFinset, f i = a ::ₘ s
  -- where f i = Multiset.replicate (Multiset.count i (a ::ₘ s)) i

  -- 3. Rewrite the head term `f a` using `head_replicate_not_mem`
  --    Requires `a ∉ s`, which we proved as `h_not_mem`.
  rw [head_replicate_not_mem h_not_mem]
  -- Goal: {a} + ∑ i ∈ s.toFinset, f i = a ::ₘ s

  -- 4. Rewrite the sum term `∑ i ∈ s.toFinset, f i` using `tail_sum_not_mem`
  --    Requires `a ∉ s`, which we proved as `h_not_mem`.
  rw [tail_sum_not_mem h_not_mem]
  -- Goal: {a} + ∑ i ∈ s.toFinset, Multiset.replicate (Multiset.count i s) i = a ::ₘ s

  -- 5. Apply the induction hypothesis (IH)
  rw [IH]
  -- Goal: {a} + s = a ::ₘ s

  -- 6. Use the definition of cons `a ::ₘ s = {a} + s`
  rw [Multiset.singleton_add]
  -- Goal is now `a ::ₘ s = a ::ₘ s`, which is true by reflexivity.

@[simp]
theorem sum_replicate_count_toFinset_eq_self {α : Type*} [DecidableEq α] (s : Multiset α) :
    ∑ i ∈ s.toFinset, Multiset.replicate (Multiset.count i s) i = s := by
  -- Prove by induction on the multiset s
  induction s using Multiset.induction
  case empty =>
    -- Base case: s = 0
    simp -- Uses sum_replicate_count_nil or simplifies directly: toFinset 0 = ∅, sum over ∅ is 0. Goal 0 = 0.
  case cons a s ih =>
    -- Inductive step: Assume property holds for s, prove for a :: s
    -- Goal: ∑ i in (a :: s).toFinset, replicate (count i (a :: s)) i = a :: s
    rw [Multiset.toFinset_cons] -- (a :: s).toFinset = insert a s.toFinset
    -- Goal: ∑ i in insert a s.toFinset, replicate (count i (a :: s)) i = a :: s

    -- Split the proof based on whether 'a' was already in the finset 's.toFinset'
    by_cases ha_mem_finset : a ∈ s.toFinset
    · -- Case 1: a ∈ s.toFinset
      exact step_mem ha_mem_finset ih
    · -- Case 2: a ∉ s.toFinset
      exact step_not_mem ha_mem_finset ih

/-!
Lemma: `mbStateToMultiset` and `multisetToMBStateSubtype` are inverses (right inverse).
Shows applying the conversion to multiset then back to state map yields the original multiset.
-/
lemma right_inv_beState_multiset {N M : ℕ} (s : SymFin N M) :
    udStateToMultiset (multisetToUDStateSubtype s) = s.val := by
  -- Unfold the definitions step-by-step
  -- 1. Unfold mbStateToMultiset
  dsimp only [udStateToMultiset]
  -- Goal: ∑ i ∈ Finset.univ, replicate ((multisetToMBStateSubtype s).val i) i = s.val

  -- 2. Unfold the .val part of multisetToMBStateSubtype
  --    (multisetToMBStateSubtype s).val = multisetToMBState s.val
  simp only [multisetToUDStateSubtype] -- Use simp to handle the subtype projection
  -- Goal: ∑ i ∈ Finset.univ, replicate (multisetToMBState s.val i) i = s.val

  -- 3. Unfold multisetToMBState
  simp only [multisetToUDState]
  -- Goal: ∑ i ∈ Finset.univ, replicate (Multiset.count i s.val) i = s.val

  -- 4. Use the lemma linking sum over univ to sum over toFinset
  --    Need `Finset.univ` for Fin N and the proof `Finset.mem_univ`
  rw [sum_replicate_count_univ_eq_sum_toFinset s.val Finset.univ (Finset.mem_univ)]
  -- Goal: ∑ i ∈ s.val.toFinset, replicate (Multiset.count i s.val) i = s.val

  -- 5. Apply the key identity proven by induction
  rw [sum_replicate_count_toFinset_eq_self s.val]
  -- Goal is now s.val = s.val, which is true by reflexivity.

/-!
## Phase 1: Combinatorial Equivalence (Completed)
We have established the maps and proven they are inverses. Now we bundle them into a formal `Equiv`.
-/

/--
Formal `Equiv` (bijection) between the `OmegaUD` representation (occupancy vectors)
and the `SymFin` representation (multisets of a fixed size).
This equivalence is crucial for transferring properties (like cardinality and `Fintype` instances)
from the well-understood `SymFin` type to `OmegaUD`.
-/
def udStateEquivMultiset (N M : ℕ) : OmegaUD N M ≃ SymFin N M where
  toFun q := ⟨udStateToMultiset q, card_udStateToMultiset q⟩
  invFun s := multisetToUDStateSubtype s
  left_inv q := left_inv_udState_multiset q
  right_inv s := by
    -- The goal is: toFun (invFun s) = s
    -- which expands to:
    -- ⟨mbStateToMultiset (multisetToMBStateSubtype s), card_udStateToMultiset (multisetToMBStateSubtype s)⟩ = s
    -- For subtypes, equality `⟨v₁, p₁⟩ = ⟨v₂, p₂⟩` is equivalent to `v₁ = v₂` due to proof irrelevance for the property `p`.
    -- Here, `s.val` is the multiset part of `s : SymFin N M`, and `s.property` is the proof `card s.val = M`.
    -- The first component of `toFun (invFun s)` is `mbStateToMultiset (multisetToMBStateSubtype s)`.
    -- So, we need to show `mbStateToMultiset (multisetToMBStateSubtype s) = s.val`.
    -- This is precisely what `right_inv_beState_multiset s` states.
    apply Subtype.eq
    exact right_inv_beState_multiset s

/--
`Fintype` instance for `OmegaUD N M`.
This instance is derived from the `Fintype` instance of `SymFin N M`
(which is `Sym (Fin N) M`) via the equivalence `mbStateEquivMultiset`.
This allows us to treat `OmegaUD N M` as a finite type, enabling enumeration
and summation over all Bose-Einstein states, which is crucial for defining
probabilities and calculating entropy.
Mathlib provides `Sym.fintype` for `Sym α n` when `α` is a `Fintype` with `DecidableEq`.
`Fin N` meets these criteria.
-/
instance fintypeOmegaUD (N M : ℕ) : Fintype (OmegaUD N M) :=
  Fintype.ofEquiv (SymFin N M) (udStateEquivMultiset N M).symm

/--
Defines the Bose-Einstein probability distribution `p_BE` over the state space `OmegaUD N M`.
This is a uniform distribution, where each state `q : OmegaUD N M` has probability
`1 / Fintype.card (OmegaUD N M)`.
The probability is given as an `NNReal` (non-negative real number).
This definition relies on `uniformProb` from `EGPT.Entropy.Common`, which handles
the case where the number of outcomes might be zero (though `card_omega_be_pos`
ensures the cardinality is positive under typical physical conditions `N ≠ 0 ∨ M = 0`).
-/
noncomputable def p_UD (N M : ℕ) : OmegaUD N M → NNReal :=
  fun _q => uniformProb (Fintype.card (OmegaUD N M))


noncomputable def p_UD_fin (N M : ℕ) : Fin (Fintype.card (OmegaUD N M)) → NNReal :=
  fun _i => uniformProb (Fintype.card (OmegaUD N M))


-- Helper lemma: the uniform distribution sums to 1
lemma sum_uniform_eq_one {n : ℕ} (hn : n > 0) :
  ∑ _i : Fin n, uniformProb n = 1 := by
  simp only [uniformProb, dif_pos hn]
  rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  rw [mul_inv_cancel₀]
  apply Nat.cast_ne_zero.mpr
  exact Nat.pos_iff_ne_zero.mp hn





/-- Product of two uniform distributions is uniform on the product space. -/
lemma uniformProb_product_uniformProb_is_uniformProb
    {n m : ℕ} (hn : n > 0) (hm : m > 0) :
    product_dist
        (fun _ : Fin n     => uniformProb n)
        (fun _ : Fin m     => uniformProb m)
      = (fun _ : Fin (n*m) => uniformProb (n * m)) := by
  -- point‑wise equality of functions on `Fin (n*m)`
  funext k
  /- 1 ▸ reduce to an identity in `NNReal` -/
  simp [product_dist, uniformProb, mul_pos hn hm]  -- goal: ↑n⁻¹ * ↑m⁻¹ = ↑(n*m)⁻¹

  /- 2 ▸ build the `≠ 0` hypotheses in `NNReal` via `exact_mod_cast` -/
  have hn_ne_zero : n ≠ 0 := (Nat.pos_iff_ne_zero).1 hn
  have hm_ne_zero : m ≠ 0 := (Nat.pos_iff_ne_zero).1 hm
  have h_n : (n : NNReal) ≠ 0 := by exact_mod_cast hn_ne_zero  -- `norm_cast` trick :contentReference[oaicite:0]{index=0}
  have h_m : (m : NNReal) ≠ 0 := by exact_mod_cast hm_ne_zero

  /- 3 ▸ convert the product of inverses to the inverse of a product -/
  -- The left factor is `↑m⁻¹ * ↑n⁻¹`, so we use the lemma with arguments in that order.
  rw [nnreal_inv_mul_inv_eq_inv_mul h_m h_n]

  /- 4 ▸ finish by rewriting inside the inverse and using commutativity -/
  rw [mul_comm] --`mul_comm` is a lemma that rewrites `a * b = b * a`
  simp [hn, hm, mul_comm, nnreal_coe_nat_mul n m]  -- evaluates the `if`s and rewrites `↑n * ↑m`



lemma stdShannon_of_p_UD_fin_when_k_is_1 (N M : ℕ) (h_k_is_1 : Fintype.card (OmegaUD N M) = 1) :
    stdShannonEntropyLn (p_UD_fin N M) = 0 := by
  -- Let k_card_ be Fintype.card (OmegaUD N M). We know k_card_ = 1 by h_k_is_1.
  -- The type of p_UD_fin N M is Fin k_card_ → NNReal.
  -- We want to show that for any x in its domain, (p_UD_fin N M x) is 1.
  -- Since k_card_ = 1, the domain Fin k_card_ is Fin 1.
  -- There's only one element in Fin 1, let's call it ` एकमात्र_el : Fin k_card_` (the unique element).
  -- (More formally, ` एकमात्र_el := (0 : Fin 1).cast (by rw ←h_k_is_1)` or similar if needed)

  -- Unfold stdShannonEntropyLn
  unfold stdShannonEntropyLn
  -- Goal: ∑ (x : Fin (Fintype.card (OmegaUD N M))), negMulLog ((p_UD_fin N M x) : ℝ) = 0

  -- Since Fintype.card (OmegaUD N M) = 1, the sum is over a singleton set (Fin 1).
  -- Use Finset.sum_eq_single_of_mem or rewrite the sum over Fin 1 directly.
  -- Fintype.card (Fin 1) = 1. Finset.univ for Fin 1 is {(0 : Fin 1)}.
  conv_lhs =>
    arg 1 -- The sum itself
    simp [h_k_is_1] -- Replace Fintype.card (OmegaUD N M) with 1 in the type
    -- Now summation is over Finset.univ (α := Fin 1)

  -- Goal is now: negMulLog ((p_UD_fin N M (0 : Fin 1)) : ℝ) = 0
  -- (The (0 : Fin 1) is the default element picked by Finset.sum_singleton if not specified)
  -- We need to evaluate p_UD_fin N M (0 : Fin 1)
  -- p_UD_fin N M is (fun _ => uniformProb (Fintype.card (OmegaUD N M)))
  -- Substitute h_k_is_1 for Fintype.card (OmegaUD N M)
  simp [p_UD_fin, h_k_is_1, uniformProb, inv_one, NNReal.coe_one, Real.negMulLog_one]
  -- uniformProb 1 simplifies to 1.
  -- Then negMulLog ((1 : NNReal) : ℝ) is negMulLog 1.0 which is 0.

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

lemma card_omega_BE_pos (N M : ℕ) (h : N ≠ 0 ∨ M = 0) :
    0 < Fintype.card (OmegaUD N M) := by
  -- the heavy lifting is `multichoose_pos_iff`
  simpa [card_omega_be, multichoose_pos_iff] using h


lemma p_BE_fin_is_H_physical_system_uniform_input (N M : ℕ) (h_domain_valid : N ≠ 0 ∨ M = 0) :
    -- The let bindings for k_card_, hk_card_pos_, and H_sys_internal_pos_proof are moved into the proof block.
    -- The lemma statement now directly uses their definitions.
    p_UD_fin N M = uniformDist (α := Fin (Fintype.card (OmegaUD N M))) (by {
      simp only [Fintype.card_fin]
      exact card_omega_BE_pos N M h_domain_valid -- This was the definition of hk_card_pos_
    }) := by
  let k_card_ := Fintype.card (OmegaUD N M)
  have hk_card_pos_ : k_card_ > 0 := card_omega_BE_pos N M h_domain_valid
  funext i
  simp [p_UD_fin, uniformProb, uniformDist, Fintype.card_fin, k_card_, if_pos hk_card_pos_]



lemma eval_H_physical_system_on_p_UD_fin (N M : ℕ) (h_domain_valid : N ≠ 0 ∨ M = 0) :
    H_physical_system (p_UD_fin N M) =
      H_physical_system_uniform_only_calc
        (Fintype.card (OmegaUD N M))
        (Nat.one_le_of_lt (card_omega_BE_pos N M h_domain_valid)) := by
  let k_card_ := Fintype.card (OmegaUD N M)
  have hk_card_pos_ : k_card_ > 0 := card_omega_BE_pos N M h_domain_valid
  -- have _hk_card_ge1_ : k_card_ ≥ 1 := Nat.one_le_of_lt hk_card_pos_ -- For the target RHS

  -- Unfold H_physical_system and simplify Fintype.card (Fin n) to n generally.
  simp only [H_physical_system, Fintype.card_fin]

  -- First `if` condition in H_physical_system: k_alpha = 0 (which became k_card_ = 0 after Fintype.card_fin)
  -- We use hk_card_pos_ (0 < k_card_) to show k_card_ ≠ 0.
  rw [dif_neg (Nat.ne_of_gt hk_card_pos_)]

  -- Now in the 'else' branch of the first 'if'.
  -- The expression involves a second 'if' checking if p_UD_fin is the uniformDist.
  -- Use p_BE_fin_is_H_physical_system_uniform_input to resolve this.
  -- This lemma states: p_UD_fin N M = uniformDist (α := Fin k_card_) (proof of 0 < k_card_)
  -- The simp will substitute p_UD_fin N M and simplify the equality condition of the if.
  -- The proofs of 0 < k_card_ will be definitionally equal due to proof irrelevance.
  simp only [p_BE_fin_is_H_physical_system_uniform_input N M h_domain_valid]

  -- The expression should now be:
  -- H_physical_system_uniform_only_calc k_card_ (Nat.one_le_of_lt P_internal) = H_physical_system_uniform_only_calc k_card_ (Nat.one_le_of_lt hk_card_pos_)
  -- This holds by definitional equality because `P_internal` (which is `Nat.pos_of_ne_zero (Nat.ne_of_gt hk_card_pos_)`) is definitionally equal to `hk_card_pos_`.
  -- `simp only []` or `rfl` should close this. Using `simp only []` for robustness.
  rfl



theorem H_physical_system_is_rota_uniform (N M : ℕ) (h_domain_valid : N ≠ 0 ∨ M = 0) :
    (H_physical_system (p_UD_fin N M) : ℝ) =
      (C_physical_NNReal : ℝ) * stdShannonEntropyLn (p_UD_fin N M) := by
  let k_card_ := Fintype.card (OmegaUD N M)
  have hk_card_ge1_ : k_card_ ≥ 1 := Nat.one_le_of_lt (card_omega_BE_pos N M h_domain_valid)

  rw [eval_H_physical_system_on_p_UD_fin N M h_domain_valid]
  rw [H_physical_system_uniform_only_calc]

  if hk_eq_1 : k_card_ = 1 then
    rw [dif_pos hk_eq_1]
    simp only [NNReal.coe_zero] -- LHS is (0 : ℝ)
    -- Use the new helper lemma for the RHS
    rw [stdShannon_of_p_UD_fin_when_k_is_1 N M hk_eq_1]
    simp only [mul_zero]
  else
    rw [dif_neg hk_eq_1]
    simp only [RealLogNatToNNReal, NNReal.coe_mul, (Real.log_nonneg (Nat.one_le_cast.mpr hk_card_ge1_))]
    have h_shannon_eq_log_k : stdShannonEntropyLn (p_UD_fin N M) = Real.log (k_card_ : ℝ) := by
      rw [p_BE_fin_is_H_physical_system_uniform_input N M h_domain_valid]
      rw [stdShannonEntropyLn_uniform_eq_log_card]
      simp only [Fintype.card_fin]
      rfl
    rw [h_shannon_eq_log_k]
    rfl
