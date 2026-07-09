import InformationTheory.EntropyNumber.Real
import InformationTheory.Complexity.Dev.InverseAxioms
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Order.Filter.Basic

open Filter

namespace InformationTheory

lemma streamInfo_true (n : ℕ) : streamInfo (fun _ => true) n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : streamInfo (fun _ => true) (n + 1) = streamInfo (fun _ => true) n + 1 := rfl
    rw [h, ih]

lemma no_real_limit : ¬ ∃ R : ℝ, Filter.Tendsto (fun n => (streamInfo (fun _ => true) n : ℝ)) Filter.atTop (nhds R) := by
  intro h
  rcases h with ⟨R, hR⟩
  have h_eq : (fun n => (streamInfo (fun _ => true) n : ℝ)) = (fun (n : ℕ) => (n : ℝ)) := by
    ext n
    rw [streamInfo_true n]
  rw [h_eq] at hR
  have h_top := tendsto_natCast_atTop_atTop
  have h_disj : Disjoint (atTop : Filter ℝ) (nhds R) := atTop_disjoint_nhds R
  exact (tendsto_nhds_unique' h_top hR h_disj)

end InformationTheory
