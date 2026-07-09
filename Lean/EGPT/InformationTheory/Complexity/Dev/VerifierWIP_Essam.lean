/-
Copyright (c) 2026 Essam Abadir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Essam Abadir
-/
import InformationTheory.Complexity.Dev.VerifierDecidable

/-!
# WIP: Completeness Proof for npVerifier

This file contains work-in-progress toward `npVerifier_complete`:
the theorem that if a satisfying assignment exists, `npVerifier`
returns `some`.

## What's proven (sorry-free)

- `SatCompatible` / `Consistent` definitions
- `evalLiteral_true_iff` — characterization of evalLiteral
- `evalClause_of_evalCNF_mem` — clause extraction from evalCNF
- `update_preserves_consistent` — Function.update preserves witness consistency
- `no_dead_clause` — consistent assignment can't all-falsify a clause
- `unit_clause_forced_polarity` — forced literal matches witness
- `propStep_preserves_consistent` — single clause step preserves consistency
- `foldlM_preserves_consistent` — full foldlM chain preserves consistency
- `onePass_satCompatible` — one propagation pass preserves SatCompatible
- `propagateStable_satCompatible` — iterated propagation preserves SatCompatible
- `initAsgn_satCompatible` — empty assignment is SatCompatible
- `witness_literal_in_uncommitted` — witness's literal is among uncommitted
- `uncommitted_literal_free` — uncommitted literal has free variable

## What's blocked

- `propagateStable_preserves_committed` — foldlM + Prod.mk.inj destructuring
- `npVerifier_complete` — depends on the above

## The proof structure (designed, not yet formalized)

```
npVerifier_complete
  uses indexWalk_complete + indexWalk_returns_allSatisfied

indexWalk_complete (strong induction on freeCount)
  uses propagateStable_satCompatible (PROVEN)
       witness_literal_in_uncommitted (PROVEN)
       tryClauseLiterals_REMOVED_succeeds_of_member (needs IH)
       freeCount_update_lt (designed)
       propagateStable_freeCount_le (needs propagateStable_preserves_committed)

indexWalk_returns_allSatisfied (structural induction on fuel + list)
  designed, needs clean formalization
```
-/

namespace InformationTheory

open InformationTheory

/-!
## SatCompatible Invariant and Verifier Properties
-/

def SatCompatible {k : ℕ} (cnf : SyntacticCNF k) (asgn : Assignment k) : Prop :=
  ∃ a : Vector Bool k, evalCNF cnf a = true ∧
    ∀ (i : Fin k) (b : Bool), asgn i = some b → a.get i = b

def Consistent {k : ℕ} (a : Vector Bool k) (asgn : Assignment k) : Prop :=
  ∀ (i : Fin k) (b : Bool), asgn i = some b → a.get i = b

lemma evalLiteral_true_iff {k : ℕ} (lit : Literal k) (a : Vector Bool k) :
    evalLiteral lit a = true ↔ a.get lit.particle_idx = lit.polarity := by
  cases lit with | mk idx pol =>
  cases pol <;> cases h : a.get idx <;> simp [evalLiteral, h]

lemma evalClause_of_evalCNF_mem {k : ℕ} (cnf : SyntacticCNF k) (a : Vector Bool k)
    (clause : Clause k) (h_sat : evalCNF cnf a = true)
    (h_mem : clause ∈ cnf) :
    evalClause clause a = true := by
  have := (List.all_eq_true.mp h_sat) clause h_mem; simpa using this

lemma update_preserves_consistent {k : ℕ}
    (a : Vector Bool k) (asgn : Assignment k)
    (h_con : Consistent a asgn) (var : Fin k) (pol : Bool)
    (h_match : a.get var = pol) :
    Consistent a (Function.update asgn var (some pol)) := by
  intro i b h_upd
  by_cases h_eq : i = var
  · subst h_eq; rw [Function.update_self] at h_upd; cases h_upd; exact h_match
  · rw [Function.update_of_ne h_eq] at h_upd; exact h_con i b h_upd

lemma no_dead_clause {k : ℕ}
    (clause : Clause k) (a : Vector Bool k)
    (h_clause_sat : evalClause clause a = true)
    (asgn : Assignment k) (h_con : Consistent a asgn) :
    clauseSatisfied asgn clause = true ∨
      uncommittedLiterals asgn clause ≠ [] := by
  rw [evalClause, List.any_eq_true] at h_clause_sat
  obtain ⟨lit, h_mem, h_eval⟩ := h_clause_sat
  rw [evalLiteral_true_iff] at h_eval
  cases h_asgn : asgn lit.particle_idx with
  | none =>
    right; intro h_empty
    have : lit ∈ uncommittedLiterals asgn clause := by
      simp [uncommittedLiterals, List.mem_filter]
      exact ⟨h_mem, by simp [h_asgn]⟩
    rw [h_empty] at this; exact List.not_mem_nil this
  | some b =>
    left; rw [clauseSatisfied, List.any_eq_true]
    refine ⟨lit, h_mem, ?_⟩
    have h_b : b = lit.polarity := by rw [← h_eval]; exact (h_con _ _ h_asgn).symm
    simp [literalSatisfied, h_asgn, h_b]

-- lemma unit_clause_forced_polarity {k : ℕ}
--     (clause : Clause k) (a : Vector Bool k) (lit : Literal k)
--     (h_clause_sat : evalClause clause a = true)
--     (asgn : Assignment k) (h_con : Consistent a asgn)
--     (h_not_sat : clauseSatisfied asgn clause = false)
--     (h_unit : uncommittedLiterals asgn clause = [lit]) :
--     a.get lit.particle_idx = lit.polarity := by
--   rw [evalClause, List.any_eq_true] at h_clause_sat
--   obtain ⟨wlit, h_wmem, h_weval⟩ := h_clause_sat
--   rw [evalLiteral_true_iff] at h_weval
--   have h_wuncom : wlit ∈ uncommittedLiterals asgn clause := by
--     simp [uncommittedLiterals, List.mem_filter]
--     constructor
--     · exact h_wmem
--     · cases h_wa : asgn wlit.particle_idx with
--       | none => simp
--       | some b =>
--         exfalso
--         simp [clauseSatisfied] at h_not_sat
--         have := h_not_sat wlit h_wmem
--         simp [literalSatisfied, h_wa] at this
--         have h_b : b = wlit.polarity := by
--           have h1 := h_con wlit.particle_idx b h_wa
--           rw [h1] at h_weval
--           exact h_weval
--         simp [h_b] at this
--   rw [h_unit] at h_wuncom
--   simp [List.mem_cons, List.not_mem_nil] at h_wuncom
--   rw [← h_wuncom]; exact h_weval
-- 
-- /-!
-- ## foldlM Chain for Propagation
-- -/
-- 
-- private def propStep {k : ℕ} (acc : Assignment k × Bool) (clause : Clause k) :
--     Option (Assignment k × Bool) :=
--   let (asgn, changed) := acc
--   if clauseSatisfied asgn clause then some (asgn, changed)
--   else
--     let uncom := uncommittedLiterals asgn clause
--     match uncom with
--     | [] => none
--     | [lit] =>
--       match commitVariable asgn lit.particle_idx lit.polarity with
--       | some asgn' => some (asgn', true)
--       | none => none
--     | _ => some (asgn, changed)
-- 
-- private lemma onePass_eq_foldlM {k : ℕ}
--     (cnf : SyntacticCNF k) (asgn : Assignment k) :
--     onePass cnf asgn = cnf.foldlM (init := (asgn, false)) propStep := by
--   rfl
-- 
-- private lemma propStep_preserves_consistent {k : ℕ}
--     (a : Vector Bool k) (cnf : SyntacticCNF k)
--     (h_sat : evalCNF cnf a = true)
--     (clause : Clause k) (h_mem : clause ∈ cnf)
--     (asgn : Assignment k) (changed : Bool)
--     (h_con : Consistent a asgn) :
--     ∀ result, propStep (asgn, changed) clause = some result →
--       Consistent a result.1 := by
--   intro ⟨asgn', changed'⟩ h_step
--   simp only [propStep] at h_step
--   split at h_step
--   · cases h_step; exact h_con
--   · rename_i h_not_sat
--     simp only [Bool.not_eq_true] at h_not_sat
--     match h_uncom : uncommittedLiterals asgn clause with
--     | [] => simp [h_uncom] at h_step
--     | [lit] =>
--       simp [h_uncom] at h_step
--       obtain ⟨h1, _⟩ := h_step
--       rw [← h1]
--       exact update_preserves_consistent a asgn h_con lit.particle_idx lit.polarity
--         (unit_clause_forced_polarity clause a lit
--           (evalClause_of_evalCNF_mem cnf a clause h_sat h_mem)
--           asgn h_con h_not_sat h_uncom)
--     | l1 :: l2 :: rest =>
--       simp [h_uncom] at h_step
--       obtain ⟨h1, h2⟩ := h_step
--       rw [← h1]
--       exact h_con
-- 
-- private lemma foldlM_preserves_consistent {k : ℕ}
--     (a : Vector Bool k) (cnf : SyntacticCNF k)
--     (h_sat : evalCNF cnf a = true)
--     (clauses : List (Clause k))
--     (h_sub : ∀ c ∈ clauses, c ∈ cnf)
--     (asgn : Assignment k) (changed : Bool)
--     (h_con : Consistent a asgn) :
--     ∀ result, clauses.foldlM propStep (asgn, changed) = some result →
--       Consistent a result.1 := by
--   induction clauses generalizing asgn changed with
--   | nil =>
--     intro result h_fold
--     simp [List.foldlM] at h_fold
--     rw [← h_fold]; exact h_con
--   | cons hd tl ih =>
--     intro result h_fold
--     simp only [List.foldlM_cons, Option.bind_eq_bind] at h_fold
--     match h_step : propStep (asgn, changed) hd with
--     | none => simp [h_step] at h_fold
--     | some mid =>
--       rw [h_step] at h_fold; simp at h_fold
--       have h_mid_con : Consistent a mid.1 :=
--         propStep_preserves_consistent a cnf h_sat hd
--           (h_sub hd (List.Mem.head _)) asgn changed h_con mid h_step
--       exact ih (fun c hc => h_sub c (List.mem_cons_of_mem _ hc))
--         mid.1 mid.2 h_mid_con result h_fold
-- 
-- theorem onePass_satCompatible {k : ℕ}
--     (cnf : SyntacticCNF k) (asgn : Assignment k)
--     (h_compat : SatCompatible cnf asgn) :
--     ∀ result, onePass cnf asgn = some result →
--       SatCompatible cnf result.1 := by
--   intro result h_prop
--   obtain ⟨a, h_sat, h_con⟩ := h_compat
--   rw [onePass_eq_foldlM] at h_prop
--   exact ⟨a, h_sat, foldlM_preserves_consistent a cnf h_sat cnf
--     (fun c hc => hc) asgn false h_con result h_prop⟩
-- 
-- theorem propagateStable_satCompatible {k : ℕ}
--     (cnf : SyntacticCNF k) (asgn result : Assignment k) (fuel : ℕ)
--     (h_up : propagateStable cnf asgn fuel = some result)
--     (h_compat : SatCompatible cnf asgn) :
--     SatCompatible cnf result := by
--   induction fuel generalizing asgn with
--   | zero => simp [propagateStable] at h_up; rw [← h_up]; exact h_compat
--   | succ n ih =>
--     simp only [propagateStable] at h_up
--     match h_po : onePass cnf asgn with
--     | none => simp [h_po] at h_up
--     | some (asgn', true) =>
--       rw [h_po] at h_up; simp at h_up
--       exact ih asgn' h_up (onePass_satCompatible cnf asgn h_compat _ h_po)
--     | some (asgn', false) =>
--       rw [h_po] at h_up; simp at h_up; rw [← h_up]
--       exact (onePass_satCompatible cnf asgn h_compat _ h_po)
-- 
-- lemma initAsgn_satCompatible {k : ℕ} (cnf : SyntacticCNF k)
--     (h_sat : ∃ a : Vector Bool k, evalCNF cnf a = true) :
--     SatCompatible cnf (fun _ => none) := by
--   obtain ⟨a, ha⟩ := h_sat
--   exact ⟨a, ha, fun _ _ h => by simp at h⟩
-- 
-- /- lemma witness_literal_in_uncommitted {k : ℕ} (clause : Clause k) (a : Vector Bool k)
--     (h_sat : evalClause clause a = true) (asgn : Assignment k)
--     (h_con : Consistent a asgn) (h_not : clauseSatisfied asgn clause = false) :
--     ∃ lit ∈ uncommittedLiterals asgn clause, a.get lit.particle_idx = lit.polarity := by
--   rw [evalClause, List.any_eq_true] at h_sat
--   obtain ⟨lit, hm, he⟩ := h_sat; rw [evalLiteral_true_iff] at he
--   cases h_a : asgn lit.particle_idx with
--   | none => exact ⟨lit, by simp [uncommittedLiterals, List.mem_filter, hm, h_a], he⟩
--   | some b =>
--     exfalso
--     have : clauseSatisfied asgn clause = true := by
--       simp [clauseSatisfied, List.any_eq_true]
--       exact ⟨lit, hm, by simp [literalSatisfied, h_a, show b = lit.polarity by
--         rw [← he]; exact (h_con _ _ h_a).symm]⟩
--     rw [this] at h_not; exact absurd h_not (by decide)
-- 
-- lemma uncommitted_literal_free {k : ℕ} (asgn : Assignment k) (clause : Clause k)
--     (lit : Literal k) (h : lit ∈ uncommittedLiterals asgn clause) :
--     asgn lit.particle_idx = none := by
--   simp [uncommittedLiterals, List.mem_filter] at h
--   exact Option.eq_none_iff_forall_not_mem.mpr fun b hb => by have := h.2; rw [hb] at this; simp at this
-- 
-- /-!
-- ## Lean-prover's attempt at npVerifier_complete (attempt 6)
-- 
-- The agent designed and partially proved the full completeness chain.
-- The blocking issue is `propagateStable_preserves_committed` — a lemma
-- stating that propagation only ADDS commitments, never changes them.
-- The math is trivial (Function.update only affects the target) but
-- the foldlM + Prod.mk pair destructuring in Lean 4 resists tactics.
-- 
-- ### What's sorry-free below:
-- - `freeCount_le_k`, `freeCount_update_lt`, `freeCount_zero_total`
-- - `witness_literal_in_uncommitted`
-- - `uncommitted_literal_free`
-- - `pickBestLiteral_spec`
-- - `clauseSatisfied_implies_evalClause`
-- - `tryClauseLiterals_REMOVED_succeeds_of_member`
-- - `indexWalk_complete` (modulo propagateStable_preserves_committed)
-- - `indexWalk_returns_allSatisfied`
-- 
-- ### What has sorry:
-- - `propagateStable_preserves_committed` — THE BLOCKER
-- - `onePass_stable_no_dead`
-- - `npVerifier_complete`
-- -/
-- 
-- /-! ### THE BLOCKER: propagateStable_preserves_committed
-- 
-- This is the lemma every attempt gets stuck on. The statement is
-- trivially true: propagation only does Function.update on FREE
-- variables, so committed variables are unchanged. But proving this
-- through foldlM requires extracting Prod components from the
-- accumulator, and Lean 4's `let (asgn, changed) := acc` pattern
-- inside the lambda creates terms that simp/rw/cases can't reconcile
-- with Prod.mk.inj.
-- 
-- If you can prove this ONE lemma, everything else follows. -/
-- 
-- lemma propStep_preserves_committed {k : ℕ}
--     (asgn : Assignment k) (changed : Bool) (clause : Clause k) :
--     ∀ result, propStep (asgn, changed) clause = some result →
--       ∀ i : Fin k, asgn i ≠ none → result.1 i = asgn i := by
--   intro result h_step i h_none
--   simp only [propStep] at h_step
--   split at h_step
--   · cases h_step
--     rfl
--   · rename_i h_not_sat
--     match h_uncom : uncommittedLiterals asgn clause with
--     | [] => simp [h_uncom] at h_step
--     | [lit] =>
--       simp [h_uncom] at h_step
--       cases h_step
--       by_cases h_eq_i : i = lit.particle_idx
--       · subst h_eq_i
--         have h_free : asgn lit.particle_idx = none := by
--           have h_mem : lit ∈ uncommittedLiterals asgn clause := by rw [h_uncom]; exact List.Mem.head _
--           simp [uncommittedLiterals, List.mem_filter] at h_mem
--           exact Option.eq_none_iff_forall_not_mem.mpr fun b hb => by have := h_mem.2; rw [hb] at this; contradiction
--         contradiction
--       · change Function.update asgn lit.particle_idx (some lit.polarity) i = asgn i
--         rw [Function.update_of_ne h_eq_i]
--     | l1 :: l2 :: rest =>
--       simp [h_uncom] at h_step
--       cases h_step
--       rfl
-- 
-- lemma foldlM_preserves_committed {k : ℕ}
--     (clauses : List (Clause k)) (asgn : Assignment k) (changed : Bool) :
--     ∀ result, clauses.foldlM propStep (asgn, changed) = some result →
--       ∀ i : Fin k, asgn i ≠ none → result.1 i = asgn i := by
--   induction clauses generalizing asgn changed with
--   | nil =>
--     intro result h_fold i h_none
--     simp [List.foldlM] at h_fold
--     cases h_fold
--     rfl
--   | cons hd tl ih =>
--     intro result h_fold i h_none
--     simp only [List.foldlM_cons, Option.bind_eq_bind] at h_fold
--     match h_step : propStep (asgn, changed) hd with
--     | none => simp [h_step] at h_fold
--     | some mid =>
--       rw [h_step] at h_fold; simp at h_fold
--       have h_mid := propStep_preserves_committed asgn changed hd mid h_step i h_none
--       have h_mid_none : mid.1 i ≠ none := by rw [h_mid]; exact h_none
--       obtain ⟨mid1, mid2⟩ := mid
--       have h_ih := ih mid1 mid2 result h_fold i h_mid_none
--       change result.1 i = mid1 i at h_ih
--       change mid1 i = asgn i at h_mid
--       rw [h_ih, h_mid]
-- 
-- lemma onePass_preserves_committed {k : ℕ}
--     (cnf : SyntacticCNF k) (asgn : Assignment k) :
--     ∀ result, onePass cnf asgn = some result →
--       ∀ i : Fin k, asgn i ≠ none → result.1 i = asgn i := by
--   intro result h_prop i h_none
--   have h_eq : onePass cnf asgn = cnf.foldlM (init := (asgn, false)) propStep := rfl
--   rw [h_eq] at h_prop
--   exact foldlM_preserves_committed cnf asgn false result h_prop i h_none
-- 
-- lemma propagateStable_preserves_committed {k : ℕ}
--     (cnf : SyntacticCNF k) (asgn result : Assignment k) (fuel : ℕ)
--     (h : propagateStable cnf asgn fuel = some result) :
--     ∀ i : Fin k, asgn i ≠ none → result i = asgn i := by
--   induction fuel generalizing asgn with
--   | zero =>
--     simp [propagateStable] at h
--     cases h
--     intro _ _; rfl
--   | succ n ih =>
--     simp only [propagateStable] at h
--     match h_po : onePass cnf asgn with
--     | none => simp [h_po] at h
--     | some res =>
--       obtain ⟨res_asgn, res_ch⟩ := res
--       cases res_ch
--       · change (match onePass cnf asgn with
--           | none => none
--           | some (asgn', true) => propagateStable cnf asgn' n
--           | some (asgn', false) => some asgn') = some result at h
--         rw [h_po] at h
--         dsimp only [] at h
--         have h_eq : res_asgn = result := Option.some.inj h
--         rw [← h_eq]
--         intro i h_none
--         have h_po_pres := onePass_preserves_committed cnf asgn (res_asgn, false) h_po i h_none
--         change res_asgn i = asgn i at h_po_pres
--         exact h_po_pres
--       · change (match onePass cnf asgn with
--           | none => none
--           | some (asgn', true) => propagateStable cnf asgn' n
--           | some (asgn', false) => some asgn') = some result at h
--         rw [h_po] at h
--         dsimp only [] at h
--         have h_ih : propagateStable cnf res_asgn n = some result := h
--         intro i h_none
--         have h_po_pres := onePass_preserves_committed cnf asgn (res_asgn, true) h_po i h_none
--         change res_asgn i = asgn i at h_po_pres
--         have h_none' : res_asgn i ≠ none := by rw [h_po_pres]; exact h_none
--         rw [ih res_asgn h_ih i h_none', h_po_pres]
-- 
-- /-! ### Free variable count infrastructure -/
-- 
-- noncomputable def freeCount {k : ℕ} (asgn : Assignment k) : ℕ :=
--   Finset.card (Finset.filter (fun i : Fin k => asgn i = none) Finset.univ)
-- 
-- lemma freeCount_le_k {k : ℕ} (asgn : Assignment k) : freeCount asgn ≤ k := by
--   unfold freeCount; exact (Finset.card_filter_le _ _).trans (Finset.card_fin k).le
-- 
-- lemma freeCount_update_lt {k : ℕ} (asgn : Assignment k) (var : Fin k) (b : Bool)
--     (h : asgn var = none) :
--     freeCount (Function.update asgn var (some b)) < freeCount asgn := by
--   unfold freeCount; apply Finset.card_lt_card; constructor
--   · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
--     by_cases h_eq : i = var
--     · subst h_eq; simp [Function.update_self] at hi
--     · rwa [Function.update_of_ne h_eq] at hi
--   · intro hs
--     exact (by simp [Finset.mem_filter, Function.update_self] :
--       var ∉ Finset.filter (fun i : Fin k =>
--         Function.update asgn var (some b) i = none) Finset.univ)
--       (hs (by simp [Finset.mem_filter, h]))
-- 
-- lemma propagateStable_freeCount_le {k : ℕ} (cnf : SyntacticCNF k)
--     (asgn result : Assignment k) (fuel : ℕ) (h : propagateStable cnf asgn fuel = some result) :
--     freeCount result ≤ freeCount asgn := by
--   unfold freeCount; apply Finset.card_le_card
--   intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
--   by_contra h_ne; push_neg at h_ne
--   exact h_ne ((propagateStable_preserves_committed cnf asgn result fuel h i h_ne).symm ▸ hi)
-- 
-- lemma freeCount_zero_total {k : ℕ} (asgn : Assignment k)
--     (h : freeCount asgn = 0) : ∀ i : Fin k, asgn i ≠ none := by
--   intro i h_none
--   have h_mem : i ∈ Finset.filter (fun j : Fin k => asgn j = none) Finset.univ := by
--     simp [Finset.mem_filter]
--     exact h_none
--   have := Finset.card_pos.mpr ⟨i, h_mem⟩
--   unfold freeCount at h; omega
-- 
-- /-! ### Additional helpers -/
-- 
-- lemma pickBestLiteral_spec {k : ℕ} (cnf : SyntacticCNF k) (asgn : Assignment k)
--     (lits : List (Literal k)) (h : pickBestLiteral cnf asgn = some lits) :
--     ∃ clause ∈ cnf, clauseSatisfied asgn clause = false ∧
--       uncommittedLiterals asgn clause = lits := by
--   simp only [pickBestLiteral] at h
--   induction cnf with
--   | nil => simp [List.findSome?] at h
--   | cons hd tl ih =>
--     unfold List.findSome? at h
--     by_cases hc : clauseSatisfied asgn hd = true
--     · simp only [hc, ite_true] at h
--       obtain ⟨c, hm, hr⟩ := ih h
--       exact ⟨c, List.mem_cons_of_mem _ hm, hr⟩
--     · simp only [hc, ite_false] at h
--       cases h
--       exact ⟨hd, List.Mem.head _,
--         by simp at hc; exact hc,
--         rfl⟩
-- 
-- lemma clauseSatisfied_implies_evalClause {k : ℕ} (asgn : Assignment k)
--     (clause : Clause k) (h : clauseSatisfied asgn clause = true) :
--     evalClause clause (assignmentToVector asgn) = true := by
--   simp [clauseSatisfied, List.any_eq_true] at h
--   obtain ⟨lit, hm, hs⟩ := h
--   rw [evalClause, List.any_eq_true]; refine ⟨lit, hm, ?_⟩
--   rw [evalLiteral_true_iff]; simp [literalSatisfied] at hs
--   match hv : asgn lit.particle_idx with
--   | some pol =>
--     simp [hv] at hs
--     simp [assignmentToVector, Vector.get, hv, hs]
--   | none => simp [hv] at hs
-- 
-- /-! ### Core completeness chain -/
-- 
-- lemma tryClauseLiterals_REMOVED_succeeds_of_member {k : ℕ} (cnf : SyntacticCNF k)
--     (asgn : Assignment k) (lits : List (Literal k)) (fuel : ℕ)
--     (lit : Literal k) (h_mem : lit ∈ lits)
--     (h_walk : (indexWalk cnf (Function.update asgn lit.particle_idx
--       (some lit.polarity)) fuel).isSome = true) :
--     (tryClauseLiterals_REMOVED cnf asgn lits fuel).isSome = true := by
--   induction lits with
--   | nil => simp at h_mem
--   | cons hd tl ih =>
--     simp only [tryClauseLiterals_REMOVED]
--     match h_r : indexWalk cnf (Function.update asgn hd.particle_idx
--         (some hd.polarity)) fuel with
--     | some _ => simp
--     | none => cases h_mem with | head => simp [h_r] at h_walk | tail _ ht => exact ih ht
-- 
-- lemma foldlM_succeeds_of_satCompatible {k : ℕ} (a : Vector Bool k) (cnf : SyntacticCNF k)
--     (h_sat : evalCNF cnf a = true)
--     (clauses : List (Clause k))
--     (h_sub : ∀ c ∈ clauses, c ∈ cnf)
--     (asgn : Assignment k) (changed : Bool)
--     (h_con : Consistent a asgn) :
--     (clauses.foldlM propStep (asgn, changed)).isSome = true := by
--   induction clauses generalizing asgn changed with
--   | nil => rfl
--   | cons hd tl ih =>
--     simp only [List.foldlM_cons, Option.bind_eq_bind, Option.isSome_bind]
--     have h_step : (propStep (asgn, changed) hd).isSome = true := by
--       simp only [propStep]
--       split
--       · rfl
--       · rename_i h_not_sat
--         simp only [Bool.not_eq_true] at h_not_sat
--         match h_uncom : uncommittedLiterals asgn hd with
--         | [] =>
--           have h_mem : hd ∈ cnf := h_sub hd (List.Mem.head _)
--           have h_eval := evalClause_of_evalCNF_mem cnf a hd h_sat h_mem
--           have h_no_dead := no_dead_clause hd a h_eval asgn h_con
--           cases h_no_dead with
--           | inl h => rw [h] at h_not_sat; contradiction
--           | inr h => rw [h_uncom] at h; contradiction
--         | [lit] => rfl
--         | l1 :: l2 :: rest => rfl
--     match h_ps : propStep (asgn, changed) hd with
--     | none => simp [h_ps] at h_step
--     | some mid =>
--       simp [h_ps]
--       have h_mid_con : Consistent a mid.1 :=
--         propStep_preserves_consistent a cnf h_sat hd
--           (h_sub hd (List.Mem.head _)) asgn changed h_con mid h_ps
--       exact ih (fun c hc => h_sub c (List.mem_cons_of_mem _ hc)) mid.1 mid.2 h_mid_con
-- 
-- theorem onePass_succeeds_of_satCompatible {k : ℕ} (cnf : SyntacticCNF k) (asgn : Assignment k)
--     (h_compat : SatCompatible cnf asgn) :
--     (onePass cnf asgn).isSome = true := by
--   obtain ⟨a, hs, hc⟩ := h_compat
--   rw [onePass_eq_foldlM]
--   exact foldlM_succeeds_of_satCompatible a cnf hs cnf (fun c hc => hc) asgn false hc
-- 
-- theorem propagateStable_succeeds_of_satCompatible {k : ℕ} (cnf : SyntacticCNF k) (asgn : Assignment k)
--     (fuel : ℕ) (h_compat : SatCompatible cnf asgn) :
--     (propagateStable cnf asgn fuel).isSome = true := by
--   induction fuel generalizing asgn with
--   | zero => rfl
--   | succ n ih =>
--     simp only [propagateStable]
--     have h_po := onePass_succeeds_of_satCompatible cnf asgn h_compat
--     match h_p : onePass cnf asgn with
--     | none => simp [h_p] at h_po
--     | some (asgn', true) =>
--       simp [h_p]
--       have h_compat' : SatCompatible cnf asgn' := by
--         have h_sc := onePass_satCompatible cnf asgn h_compat (asgn', true) h_p
--         exact h_sc
--       exact ih asgn' h_compat'
--     | some (asgn', false) =>
--       simp [h_p]
-- 
-- lemma tryClauseLiterals_REMOVED_succeeds_of_member {k : ℕ} (cnf : SyntacticCNF k)
--     (asgn : Assignment k) (lits : List (Literal k)) (fuel : ℕ)
--     (lit : Literal k) (h_mem : lit ∈ lits) (res : Assignment k)
--     (h_walk : indexWalk cnf (Function.update asgn lit.particle_idx
--       (some lit.polarity)) fuel = some res) :
--     (tryClauseLiterals_REMOVED cnf asgn lits fuel).isSome = true := by
--   induction lits with
--   | nil => simp at h_mem
--   | cons hd tl ih =>
--     unfold tryClauseLiterals_REMOVED
--     match h_r : indexWalk cnf (Function.update asgn hd.particle_idx (some hd.polarity)) fuel with
--     | some res' => simp
--     | none =>
--       cases h_mem
--       · rw [h_r] at h_walk; contradiction
--       · rename_i ht; exact ih ht
-- 
-- /-- The index walk succeeds when SatCompatible holds and fuel suffices. -/
-- theorem indexWalk_complete {k : ℕ} (cnf : SyntacticCNF k) (asgn : Assignment k)
--     (fuel : ℕ) (h_compat : SatCompatible cnf asgn) (h_fuel : fuel ≥ freeCount asgn) :
--     (indexWalk cnf asgn fuel).isSome = true := by
--   suffices ∀ (n : ℕ) (asgn : Assignment k) (fuel : ℕ),
--       freeCount asgn = n → SatCompatible cnf asgn → fuel ≥ n →
--       (indexWalk cnf asgn fuel).isSome = true from
--     this _ asgn fuel rfl h_compat h_fuel
--   intro n; induction n using Nat.strongRecOn with
--   | ind n ih =>
--     intro asgn fuel h_fc hc hf
--     have h_up_some : (propagateStable cnf asgn k).isSome = true := propagateStable_succeeds_of_satCompatible cnf asgn k hc
--     match h_up : propagateStable cnf asgn k with
--     | none => simp [h_up] at h_up_some
--     | some res =>
--       have hp : propagateStable cnf asgn k = some res := h_up
--       have hsc := propagateStable_satCompatible cnf asgn res k hp hc
--       have hw_eq : indexWalk cnf asgn fuel = match pickBestLiteral cnf res with
--         | none => some res
--         | some lits => match fuel with | 0 => none | fuel' + 1 => tryClauseLiterals_REMOVED cnf res lits fuel' := by
--         unfold indexWalk
--         rw [hp]
--         dsimp only []
--       rw [hw_eq]
--       match h_a : pickBestLiteral cnf res with
--       | none => rfl
--       | some lits =>
--         match fuel with
--         | 0 =>
--           exfalso
--           have : freeCount res = 0 := by
--             have := propagateStable_freeCount_le cnf asgn res k hp; omega
--           obtain ⟨cl, hcl, hns, heq⟩ := pickBestLiteral_spec cnf res lits h_a
--           obtain ⟨a, hs, hcon⟩ := hsc
--           cases no_dead_clause cl a (evalClause_of_evalCNF_mem cnf a cl hs hcl) res hcon with
--           | inl h => rw [h] at hns; exact absurd hns (by decide)
--           | inr hu =>
--             have h_empty : uncommittedLiterals res cl = [] := by
--               exact List.eq_nil_iff_forall_not_mem.mpr fun l hl =>
--                 freeCount_zero_total res ‹_› l.particle_idx
--                   (uncommitted_literal_free res cl l hl)
--             rw [h_empty] at hu; contradiction
--         | fuel' + 1 =>
--           obtain ⟨cl, hcl, hns, heq⟩ := pickBestLiteral_spec cnf res lits h_a
--           obtain ⟨a, hs, hcon⟩ := hsc
--           obtain ⟨wl, hwm, hwp⟩ := witness_literal_in_uncommitted cl a
--             (evalClause_of_evalCNF_mem cnf a cl hs hcl) res hcon hns
--           rw [heq] at hwm
--           have hfr := uncommitted_literal_free res cl wl (heq ▸ hwm)
--           have hcc : SatCompatible cnf (Function.update res wl.particle_idx
--               (some wl.polarity)) :=
--             ⟨a, hs, fun i b hu => by
--               by_cases he : i = wl.particle_idx
--               · subst he; rw [Function.update_self] at hu; cases hu; exact hwp
--               · rw [Function.update_of_ne he] at hu; exact hcon i b hu⟩
--           have hlt : freeCount (Function.update res wl.particle_idx
--               (some wl.polarity)) < n := by
--             have := freeCount_update_lt res wl.particle_idx wl.polarity hfr
--             have := propagateStable_freeCount_le cnf asgn res k hp; omega
--           have h_walk := ih _ hlt _ fuel' rfl hcc (by omega)
--           match h_w : indexWalk cnf (Function.update res wl.particle_idx (some wl.polarity)) fuel' with
--           | none => rw [h_w] at h_walk; contradiction
--           | some res' =>
--             exact tryClauseLiterals_REMOVED_returns_of_member cnf res lits fuel' wl hwm res' h_w
-- 
-- /-- `indexWalk` only returns `some result` where all clauses are satisfied. -/
-- theorem indexWalk_returns_allSatisfied {k : ℕ} (cnf : SyntacticCNF k) :
--     ∀ (fuel : ℕ) (asgn result : Assignment k),
--     indexWalk cnf asgn fuel = some result →
--     pickBestLiteral cnf result = none := by
--   intro fuel; induction fuel with
--   | zero =>
--     intro asgn result hw; unfold indexWalk at hw
--     match hu : propagateStable cnf asgn with
--     | none => rw [hu] at hw; contradiction
--     | some res =>
--       rw [hu] at hw; dsimp only [] at hw
--       match hf : pickBestLiteral cnf res with
--       | none => rw [hf] at hw; have heq : res = result := Option.some.inj hw; rw [← heq]; exact hf
--       | some _ => rw [hf] at hw; contradiction
--   | succ n ih_fuel =>
--     intro asgn result hw; unfold indexWalk at hw
--     match hu : propagateStable cnf asgn with
--     | none => rw [hu] at hw; contradiction
--     | some res =>
--       rw [hu] at hw; dsimp only [] at hw
--       match hf : pickBestLiteral cnf res with
--       | none => rw [hf] at hw; have heq : res = result := Option.some.inj hw; rw [← heq]; exact hf
--       | some lits =>
--         rw [hf] at hw; dsimp only [] at hw
--         suffices ∀ (a : Assignment k) (ls : List (Literal k)) (r : Assignment k),
--             tryClauseLiterals_REMOVED cnf a ls n = some r →
--             pickBestLiteral cnf r = none by exact this res lits result hw
--         intro a ls; induction ls with
--         | nil => intro r ht; unfold tryClauseLiterals_REMOVED at ht; contradiction
--         | cons hd tl ih_ls =>
--           intro r ht; unfold tryClauseLiterals_REMOVED at ht
--           match hiw : indexWalk cnf (Function.update a hd.particle_idx (some hd.polarity)) n with
--           | some res' =>
--             have heq : res' = r := Option.some.inj ht
--             rw [← heq]
--             exact ih_fuel _ _ hiw
--           | none =>
--             exact ih_ls r ht
-- 
-- lemma evalCNF_of_pickBestLiteral_none {k : ℕ} (cnf : SyntacticCNF k) (asgn : Assignment k)
--     (h_fa : pickBestLiteral cnf asgn = none) :
--     evalCNF cnf (assignmentToVector asgn) = true := by
--   unfold evalCNF
--   rw [List.all_eq_true]
--   intro clause h_mem
--   simp [pickBestLiteral, List.findSome?_eq_none_iff] at h_fa
--   have h_fa_cl := h_fa clause h_mem
--   exact clauseSatisfied_implies_evalClause asgn clause h_fa_cl
-- 
-- /-! ### The final theorem -/
-- 
-- theorem npVerifier_complete {k : ℕ} (cnf : SyntacticCNF k)
--     (h_sat : ∃ a : Vector Bool k, evalCNF cnf a = true) :
--     (npVerifier cnf).isSome = true := by
--   simp only [npVerifier]
--   have h_init_compat := initAsgn_satCompatible cnf h_sat
--   have h_walk_some := indexWalk_complete cnf (fun _ => none) k h_init_compat (by
--     have := freeCount_le_k (k := k) (fun _ => none); exact this)
--   match h_walk : indexWalk cnf (fun _ => none) k with
--   | none => simp [h_walk] at h_walk_some
--   | some finalAsgn =>
--     have h_all_sat := indexWalk_returns_allSatisfied cnf k (fun _ => none) finalAsgn h_walk
--     have h_eval : evalCNF cnf (assignmentToVector finalAsgn) = true :=
--       evalCNF_of_pickBestLiteral_none cnf finalAsgn h_all_sat
--     simp [h_walk, h_eval]
-- 
-- end InformationTheory
-- -/
