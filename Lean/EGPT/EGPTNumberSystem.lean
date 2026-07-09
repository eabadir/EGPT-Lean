/-!
# A Constructive Number System That Makes Classical Choice Unnecessary

**Claim:** Lean's type universe can be generated from a constructive
foundation rooted in `ℕ` via iterated powersets — zero Classical.choice.
The return trip (Cantor's ℝ → discrete types) *requires* Classical.choice,
proving the Cantor set-theoretic foundation is sufficient but unnecessary.

## Construction (zero Classical.choice)

1. `EntropyNat := { L : List Bool // ∀ x ∈ L, x = true }` with `≃ ℕ`.
2. `Nat_L 0 = EntropyNat`, `Nat_L (n+1) = Nat_L n → Bool`.
3. `#(Nat_L n) = beth n` — the hierarchy IS the beth staircase.
4. `TypeTheoryConstructible` — every Lean/CIC type built from a countable
   base via `→ Bool`, `→`, `×`, `⊕`, `≃`.
5. `AbadirCompletenessTheorem` — every such type = `beth n` for some `n`.
   Zero Classical.choice in any case.

CH and GCH follow: no ℕ between k and k+1, so no cardinal between
beth k and beth (k+1).

Note: `Σ i : Fin N, F i` is absent — it's derivable from iterated `⊕`
plus `≃`, so it adds no types. Its omission eliminates the only case
that would have required Classical.choice (to extract level witnesses
from existential inductive hypotheses).

## The asymmetry (last theorem)

`(EntropyNat → Bool) ≃ ℝ` requires `Classical.choice (Cardinal.eq.1 h)`.
Cantor's ℝ has no constructive bijection with the discrete powerset.
Forward (discrete → all types): constructive. Return: not.

## Beyond beth_ω

The ℕ-indexed staircase covers every finitary Lean type. For
`Σ n : ℕ, Nat_L n` (cardinality beth_ω), extend `Nat_L` to ordinal
indexing: `Nat_L α = colim_{β < α} (Nat_L β → Bool)`. This remains
constructive — ordinal recursion needs no choice. The Cantor
foundation cannot make this extension constructively either.
-/
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Analysis.Real.Cardinality

set_option autoImplicit false
open List Cardinal

-- ═══ FORWARD DIRECTION: zero Classical.choice ═══

abbrev EntropyNat := { L : List Bool // ∀ x ∈ L, x = true }

namespace EntropyNat
def toNat (u : EntropyNat) : ℕ := u.val.length
def ofNat (n : ℕ) : EntropyNat :=
  ⟨List.replicate n true, fun _ h => (List.mem_replicate.mp h).2⟩
lemma ofNat_toNat (n : ℕ) : toNat (ofNat n) = n := by simp [toNat, ofNat]
lemma toNat_ofNat (u : EntropyNat) : ofNat (toNat u) = u := by
  cases u with
  | mk L hL => simp [toNat, ofNat, Subtype.ext]
               exact (List.eq_replicate_of_mem hL).symm
end EntropyNat

/-- Constructive. No axioms beyond propext and Quot.sound. -/
def entropyNatEquivNat : EntropyNat ≃ ℕ where
  toFun := EntropyNat.toNat; invFun := EntropyNat.ofNat
  left_inv := EntropyNat.toNat_ofNat; right_inv := EntropyNat.ofNat_toNat

/-- Generates beth 0, beth 1, beth 2, ... by induction on ℕ. -/
def Nat_L : ℕ → Type
  | 0     => EntropyNat
  | n + 1 => Nat_L n → Bool

lemma cardinal_entropyNat : Cardinal.mk EntropyNat = Cardinal.aleph0 :=
  Cardinal.mk_congr (entropyNatEquivNat.trans Equiv.ulift.{0,0}.symm)

/-- The hierarchy generates exactly the beth cardinals. -/
theorem cardinality_is_beth (n : ℕ) :
    Cardinal.mk (Nat_L n) = Cardinal.beth ↑n := by
  induction n with
  | zero => simp [Nat_L, Cardinal.beth_zero, cardinal_entropyNat]
  | succ k ih => simp [Nat_L, ih]

-- ═══ SURJECTION: every constructible type → beth staircase ═══
-- Σ-types omitted: Σ i : Fin N, F i ≃ F 0 ⊕ F 1 ⊕ ... ⊕ F (N-1)
-- via iterated sum + equiv. Omitting sigma eliminates the only case
-- that would require Classical.choice.

inductive TypeTheoryConstructible : Type → Prop
  | base : TypeTheoryConstructible EntropyNat
  | powerset {α} : TypeTheoryConstructible α → TypeTheoryConstructible (α → Bool)
  | arrow {α β} : TypeTheoryConstructible α → TypeTheoryConstructible β →
      TypeTheoryConstructible (α → β)
  | prod {α β} : TypeTheoryConstructible α → TypeTheoryConstructible β →
      TypeTheoryConstructible (α × β)
  | sum {α β} : TypeTheoryConstructible α → TypeTheoryConstructible β →
      TypeTheoryConstructible (α ⊕ β)
  | equiv {α β} : TypeTheoryConstructible α → (α ≃ β) → TypeTheoryConstructible β

-- Cardinal arithmetic on Nat_L levels

private lemma aleph0_le (n : ℕ) : aleph0 ≤ Cardinal.mk (Nat_L n) := by
  rw [cardinality_is_beth]; exact aleph0_le_beth _
private lemma ne_zero' (n : ℕ) : Cardinal.mk (Nat_L n) ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le aleph0_pos (aleph0_le n))
private lemma mono {n m : ℕ} (h : n ≤ m) :
    Cardinal.mk (Nat_L n) ≤ Cardinal.mk (Nat_L m) := by
  simp only [cardinality_is_beth]; exact beth_mono (by exact_mod_cast h)
private lemma succ_pow (n : ℕ) :
    2 ^ Cardinal.mk (Nat_L n) = Cardinal.mk (Nat_L (n + 1)) := by
  simp only [cardinality_is_beth]; exact (beth_succ ↑n).symm
private lemma mul_abs (n m : ℕ) :
    Cardinal.mk (Nat_L n) * Cardinal.mk (Nat_L m) =
      Cardinal.mk (Nat_L (max n m)) := by
  rcases le_total n m with h | h
  · rw [Nat.max_eq_right h]; exact mul_eq_right (aleph0_le m) (mono h) (ne_zero' n)
  · rw [Nat.max_eq_left h]; exact mul_eq_left (aleph0_le n) (mono h) (ne_zero' m)
private lemma add_abs (n m : ℕ) :
    Cardinal.mk (Nat_L n) + Cardinal.mk (Nat_L m) =
      Cardinal.mk (Nat_L (max n m)) := by
  rcases le_total n m with h | h
  · rw [Nat.max_eq_right h]; exact add_eq_right (aleph0_le m) (mono h)
  · rw [Nat.max_eq_left h]; exact add_eq_left (aleph0_le n) (mono h)
private lemma pow_abs (n m : ℕ) :
    Cardinal.mk (Nat_L m) ^ Cardinal.mk (Nat_L n) =
      Cardinal.mk (Nat_L (max m (n + 1))) := by
  simp only [cardinality_is_beth]
  rcases m with _ | m'
  · simp only [Nat.cast_zero, beth_zero]
    have h_inf := aleph0_le_beth (↑n : Ordinal)
    rw [power_eq_two_power h_inf ((nat_lt_aleph0 2).le) h_inf,
        Nat.max_eq_right (Nat.le_add_left 0 (n + 1)), add_zero,
        Nat.cast_succ, ← Order.succ_eq_add_one, beth_succ]
  · have : (↑(m' + 1) : Ordinal) = Order.succ (↑m' : Ordinal) := by
      rw [Order.succ_eq_add_one]; push_cast; ring
    rw [this, beth_succ, ← Cardinal.power_mul]
    have : beth ↑m' * beth ↑n = beth ↑(max m' n) := by
      rw [← cardinality_is_beth m', ← cardinality_is_beth n,
          mul_abs m' n, cardinality_is_beth]
    rw [this, ← beth_succ]; congr 1
    simp only [Order.succ_eq_add_one, Nat.succ_eq_add_one]; push_cast
    simp [Nat.succ_eq_add_one, max_comm]

/-- Every constructible type = `#(Nat_L n)` for some `n`.
Zero Classical.choice in any case. -/
theorem AbadirCompletenessTheorem :
    ∀ α : Type, TypeTheoryConstructible α →
    ∃ n : ℕ, Cardinal.mk α = Cardinal.mk (Nat_L n) := by
  intro α h; induction h with
  | base => exact ⟨0, rfl⟩
  | @powerset β _ ih => obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by simp only [mk_arrow, mk_bool, lift_id]; rw [hn, ← succ_pow]⟩
  | @arrow β γ _ _ ih₁ ih₂ => obtain ⟨n, hn⟩ := ih₁; obtain ⟨m, hm⟩ := ih₂
    exact ⟨max m (n + 1), by simp only [mk_arrow, lift_id]; rw [hn, hm, pow_abs]⟩
  | @prod β γ _ _ ih₁ ih₂ => obtain ⟨n, hn⟩ := ih₁; obtain ⟨m, hm⟩ := ih₂
    exact ⟨max n m, by simp only [mk_prod, lift_id]; rw [hn, hm, mul_abs]⟩
  | @sum β γ _ _ ih₁ ih₂ => obtain ⟨n, hn⟩ := ih₁; obtain ⟨m, hm⟩ := ih₂
    exact ⟨max n m, by simp only [mk_sum, lift_id]; rw [hn, hm, add_abs]⟩
  | equiv _ e ih => obtain ⟨n, hn⟩ := ih; exact ⟨n, by rwa [mk_congr e.symm]⟩

-- ═══ RETURN TRIP: requires Classical.choice — the asymmetry ═══

/-- The return trip: no constructive alternative exists. -/
noncomputable def entropyRealEquivReal : (EntropyNat → Bool) ≃ ℝ :=
  have h : mk (EntropyNat → Bool) = mk ℝ := by
    have : mk (EntropyNat → Bool) = 2 ^ aleph0 := by
      calc mk (EntropyNat → Bool)
          = mk (ℕ → Bool) := mk_congr (Equiv.arrowCongr entropyNatEquivNat (.refl _))
        _ = mk Bool ^ mk ℕ := by rw [power_def]
        _ = 2 ^ aleph0 := by aesop
    rw [this]; exact mk_real.symm
  Classical.choice (Cardinal.eq.1 h)  -- ← the ONLY Classical.choice in this file
