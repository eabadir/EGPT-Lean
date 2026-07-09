import InformationTheory.EntropyNumber.Real
import Mathlib.Order.LiminfLimsup

open Filter

example (H : ℝ) (f : ℕ → ℝ) (h : ∃ M, ∀ k ≥ M, f k = H) :
    liminf f Filter.atTop = H := by
  have h_eventually : ∀ᶠ k in atTop, f k = H := by
    obtain ⟨M, hM⟩ := h
    rw [eventually_atTop]
    exact ⟨M, hM⟩
  have h_eq : f =ᶠ[atTop] (fun _ => H) := h_eventually
  rw [liminf_congr h_eq]
  exact liminf_const H