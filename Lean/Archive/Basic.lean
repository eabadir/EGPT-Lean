import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog -- For negMulLog, Real.log
import Mathlib.Data.NNReal.Basic -- For NNReal
import Mathlib.Topology.Basic -- For ContinuousOn (placeholder)
import Mathlib.Order.Monotone.Basic -- For Monotone
import Mathlib.Algebra.BigOperators.Fin -- For sum over Fin n
import Mathlib.Data.Fin.Basic -- Basic Fin definitions and lemmas
import Mathlib.Data.Fintype.Fin -- Instances for Fin n
import Mathlib.Algebra.Order.Field.Basic -- For inv_one etc.
import Mathlib.Algebra.GroupWithZero.Units.Basic -- Provides mul_inv_cancel₀
import Mathlib.Analysis.SpecialFunctions.Log.Base -- Real.logb
import Mathlib.Analysis.SpecialFunctions.Pow.Real -- Real.rpow
import Mathlib.Data.Complex.Basic -- For Complex.exp_re if needed
import Mathlib.Analysis.SpecificLimits.Basic -- tendsto_one_div_atTop_zero
import Mathlib.Data.Real.Basic -- Basic Real properties
import Mathlib.Order.Filter.Basic -- Filter bases etc.
import Mathlib.Topology.Order.Basic -- OrderTopology
import Mathlib.Data.Nat.Basic -- Basic Nat properties
import Mathlib.Data.Nat.Log -- Nat.log
import Mathlib.Algebra.Order.Floor.Defs -- Floor definitions
import Mathlib.Tactic.Linarith -- Inequality solver
import Mathlib.Algebra.Ring.Nat -- For Nat.cast_pow
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.GroupTheory.Congruence.Basic

-- Import previous definitions and theorems


namespace EGPT.Basic

open BigOperators Fin Real Topology NNReal Filter Nat Set






/-- Coercing `ℕ` to `NNReal` with `↑` is enough in Lean 4. -/
lemma nnreal_coe_nat_mul (n m : ℕ) :
    ((n : NNReal) * m) = (n * m : NNReal) := by
  -- Step 1: reduce the goal to a statement about `ℝ`
  apply NNReal.eq          -- turns it into a goal about `Nat.cast`
  -- Step 2: rewrite with the coercion lemmas that ship with mathlib4
  simp [NNReal.coe_mul, Nat.cast_mul]   -- both sides become `↑n * ↑m` in `ℝ`


/-- Replacement for Mathlib3 NNReal.nat_cast_ne_zero -/
lemma nnreal_nat_cast_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (n : NNReal) ≠ 0 := by
  -- The goal is `↑n ≠ 0` in `NNReal`
  -- Use the fact that `↑n = 0` iff `n = 0`
  simp [hn] -- This is the negation of the `Nat.cast` lemma

/--
Ensures `NNReal.coe_nat_ne_zero_iff_ne_zero` is available.
The coercion of a natural number to `NNReal` is non-zero if and only if the natural number itself is non-zero.
This relies on `NNReal.nat_cast_eq_zero` which states `(↑n : ℝ≥0) = 0 ↔ n = 0`.
-/
@[simp] lemma NNReal.coe_nat_ne_zero_iff_ne_zero {n : ℕ} : (n : NNReal) ≠ 0 ↔ n ≠ 0 := by
  simp[natCast_eq_zero]



/-- Shows that the product `(a * a⁻¹) * (b * b⁻¹)` equals `1 * 1`, given `a` and `b` are non-zero. -/
lemma nnreal_prod_inv_self_eq_one_prod {a b : NNReal} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * a⁻¹) * (b * b⁻¹) = 1 * 1 := by
  rw [mul_inv_cancel₀ ha] -- Finds lemma mul_inv_cancel, sees it needs a ≠ 0, finds ha in context. Goal: 1 * (b * b⁻¹) = 1 * 1
  rw [mul_inv_cancel₀ hb] -- Finds lemma mul_inv_cancel, sees it needs b ≠ 0, finds hb in context. Goal: 1 * 1 = 1 * 1
  -- The goal is now true by reflexivity, rw finishes.



/-- Rearranges `(a * b) * (a⁻¹ * b⁻¹)` so that matching factors are adjacent. -/
lemma nnreal_mul_prod_inv_prod_rearrange (a b : NNReal) :
    (a * b) * (a⁻¹ * b⁻¹) = (a * a⁻¹) * (b * b⁻¹) := by
  -- `ring` works in commutative semirings like `NNReal`:
  ring

/-- Inverse of a product equals the product of inverses in `NNReal`. -/
lemma nnreal_inv_mul_inv_eq_inv_mul
    {a b : NNReal} (ha : a ≠ 0) (hb : b ≠ 0) :
    a⁻¹ * b⁻¹ = (a * b)⁻¹ := by
  -- Reduce to proving `(a⁻¹ * b⁻¹) * (a * b) = 1`.
  apply eq_inv_of_mul_eq_one_left
  -- Rearrange terms using associativity and commutativity
  rw [mul_assoc] -- a⁻¹ * (b⁻¹ * (a * b)) = 1
  rw [mul_left_comm b⁻¹ a b] -- a⁻¹ * (a * (b⁻¹ * b)) = 1
  rw [←mul_assoc] -- (a⁻¹ * a) * (b⁻¹ * b) = 1
  -- Apply inverse cancellation using the non-zero hypotheses
  rw [inv_mul_cancel₀ ha] -- 1 * (b⁻¹ * b) = 1
  rw [inv_mul_cancel₀ hb] -- 1 * 1 = 1
  -- Simplify the final expression
  rw [one_mul] -- 1 = 1
  -- Goal is now `1 = 1`, which is true by reflexivity (handled implicitly)



/-- Cast a successor into a sum: `↑(m + 1) = ↑m + 1`. -/
lemma cast_add_one_real (m : ℕ) : ↑(m + 1) = ↑m + 1 :=
  Nat.cast_add_one m

lemma add_mul_right (m : ℕ) (c : ℝ) :
    ↑m * c + c = (m + 1 : ℝ) * c := by
  ring          -- ← one line, succeeds


/-- Helper lemma: `1 < b` for `b ≥ 2` -/
lemma one_lt_cast_of_ge_two {b : ℕ} (hb : b ≥ 2) : 1 < (b : ℝ) :=
  Nat.one_lt_cast.mpr (Nat.lt_of_succ_le hb)

/-- Helper lemma: `0 < b` for `b ≥ 2` -/
lemma cast_pos_of_ge_two {b : ℕ} (hb : b ≥ 2) : 0 < (b : ℝ) :=
  Nat.cast_pos.mpr (Nat.lt_of_succ_le (by linarith [hb] : 1 ≤ b))

/-- Lemma: floor of `Real.logb b x` is at most `Real.logb b x`. -/
lemma floor_logb_le {b : ℕ} {x : ℝ} (hb : b ≥ 2) (hx : x ≥ 1) :
  (Nat.floor (Real.logb b x) : ℝ) ≤ Real.logb b x := -- Cast floor to Real
by
  have hb_gt_one_real : 1 < (b : ℝ) := one_lt_cast_of_ge_two hb
  exact Nat.floor_le (Real.logb_nonneg hb_gt_one_real hx)

/-- Lemma: `log b > 0` for `b ≥ 2`. -/
lemma log_b_pos {b : ℕ} (hb : b ≥ 2) : Real.log b > 0 := by
  apply Real.log_pos -- Changes goal to `↑b > 1`
  -- Explicitly show the cast is greater than 1
  have hb_gt_one_real : (b : ℝ) > 1 := by
    -- Convert Nat inequality `b ≥ 2` to Real inequality `↑b ≥ 2`
    have hb_ge_2_real : (b : ℝ) ≥ (2 : ℝ) := Nat.cast_le.mpr hb
    -- Use linarith: `↑b ≥ 2` implies `↑b > 1` because `2 > 1`
    linarith [hb_ge_2_real]
  exact hb_gt_one_real



/-- Lemma: `Real.logb b x * Real.log b = Real.log x`. Needs `b > 0`, `b ≠ 1`, `x > 0`. -/
lemma logb_mul_log_eq_log {b : ℕ} {x : ℝ} (hb : b ≥ 2) (hx : x ≥ 1) :
  Real.logb b x * Real.log b = Real.log x :=
by
  -- Need b ≠ 1 for logb definition
  have b_ne_one : (b : ℝ) ≠ 1 := ne_of_gt (one_lt_cast_of_ge_two hb)
  -- Need b > 0 for logb definition
  have b_pos : 0 < (b : ℝ) := cast_pos_of_ge_two hb
  -- Need x > 0 for logb definition
  have x_pos : 0 < x := by linarith [hx]

  -- Use the definition: Real.logb b x = Real.log x / Real.log b
  rw [Real.logb] -- Unfolds the definition

  -- Simplify (log x / log b) * log b = log x
  -- Use div_mul_cancel₀ which requires log b ≠ 0
  rw [div_mul_cancel₀]
  -- Prove log b ≠ 0
  exact Real.log_ne_zero_of_pos_of_ne_one b_pos b_ne_one

/-- Intermediate Lemma: `k * log b ≤ log x` where `k = floor(logb b x)`. -/
lemma floor_logb_mul_log_le_log {b : ℕ} {x : ℝ} (hb : b ≥ 2) (hx : x ≥ 1) :
  (Nat.floor (Real.logb b x) : ℝ) * Real.log b ≤ Real.log x :=
by
  have h_floor_le_logb_real : (Nat.floor (Real.logb b x) : ℝ) ≤ Real.logb b x :=
    floor_logb_le hb hx
  have h_log_b_nonneg : 0 ≤ Real.log b := le_of_lt (log_b_pos hb)
  have h_mul_log : (Nat.floor (Real.logb b x) : ℝ) * Real.log b ≤ Real.logb b x * Real.log b :=
    mul_le_mul_of_nonneg_right h_floor_le_logb_real h_log_b_nonneg
  rw [logb_mul_log_eq_log hb hx] at h_mul_log
  exact h_mul_log

/-- Intermediate Lemma: From `y * log b ≤ log x`, prove `b ^ y ≤ x`. Uses `rpow`. -/
lemma rpow_le_of_mul_log_le_log {b : ℕ} {x y : ℝ} (hb : b ≥ 2) (hx_pos : 0 < x)
    (h_mul_log : y * Real.log b ≤ Real.log x) :
    (b : ℝ) ^ y ≤ x :=
by
  have hb_pos_real : 0 < (b : ℝ) := cast_pos_of_ge_two hb
  -- Apply exp to both sides (exp is strictly monotone)
  have h_exp_le_exp : Real.exp (y * Real.log b) ≤ Real.exp (Real.log x) :=
    Real.exp_le_exp.mpr h_mul_log
  -- Simplify LHS using x ^ y = exp(y * log x)
  rw [mul_comm y (Real.log b)] at h_exp_le_exp -- Commute for rpow_def_of_pos
  rw [← Real.rpow_def_of_pos hb_pos_real] at h_exp_le_exp -- LHS is now (b : ℝ) ^ y
  -- Simplify RHS using exp(log x) = x
  rw [Real.exp_log hx_pos] at h_exp_le_exp -- RHS is now x
  exact h_exp_le_exp


/-- Lemma: `(b : ℝ) ^ (Nat.floor (Real.logb b x) : ℝ) ≤ x` for `b ≥ 2` and `x ≥ 1`. -/
lemma rpow_floor_logb_le_x {b : ℕ} {x : ℝ} (hb : b ≥ 2) (hx : x ≥ 1) :
  (b : ℝ) ^ (Nat.floor (Real.logb b x) : ℝ) ≤ x := -- Exponent is Real cast
by
  have h_mul_log : (Nat.floor (Real.logb b x) : ℝ) * Real.log b ≤ Real.log x :=
    floor_logb_mul_log_le_log hb hx
  have hx_pos : 0 < x := by linarith [hx]
  exact rpow_le_of_mul_log_le_log hb hx_pos h_mul_log

/-- Helper Lemma: `(b : ℝ) ^ k ≤ x` where `k = Nat.floor (Real.logb b x)`. Uses Nat exponent. -/
lemma pow_nat_floor_logb_le_x {b : ℕ} {x : ℝ} (hb : b ≥ 2) (hx : x ≥ 1) :
  (b : ℝ) ^ (Nat.floor (Real.logb b x)) ≤ x :=
by
  let k := Nat.floor (Real.logb b x)
  -- Get the inequality with Real exponent from the existing lemma
  have h_le_real_exp : (b : ℝ) ^ (k : ℝ) ≤ x := rpow_floor_logb_le_x hb hx
  -- Need b ≥ 0 to use rpow_natCast
  have hb_nonneg : 0 ≤ (b : ℝ) := le_of_lt (cast_pos_of_ge_two hb)
  -- Rewrite the inequality using rpow_natCast (forward direction) to match the goal (Nat exponent)
  rw [Real.rpow_natCast (b : ℝ) k] at h_le_real_exp
  -- The hypothesis now matches the goal
  exact h_le_real_exp

/-- Helper Lemma: `x < (b : ℝ) ^ (k + 1)` where `k = Nat.floor (Real.logb b x)`. Uses Nat exponent. -/
lemma x_lt_pow_succ_floor_logb {b : ℕ} {x : ℝ} (hb : b ≥ 2) (hx : x ≥ 1) :
  x < (b : ℝ) ^ (Nat.floor (Real.logb b x) + 1) :=
by
  let k := Nat.floor (Real.logb b x)
  have hb_pos : 0 < (b : ℝ) := cast_pos_of_ge_two hb
  have hx_pos : 0 < x := by linarith [hx]
  have log_b_pos' : 0 < Real.log b := log_b_pos hb

  -- Start from Nat.lt_floor_add_one
  have lt_floor_add_one : Real.logb b x < (k : ℝ) + 1 :=
    Nat.lt_floor_add_one (Real.logb b x)

  -- Multiply by log b (positive)
  have h_mul_log_lt : Real.logb b x * Real.log b < ((k : ℝ) + 1) * Real.log b :=
    (mul_lt_mul_right log_b_pos').mpr lt_floor_add_one

  -- Substitute log x using logb_mul_log_eq_log
  rw [logb_mul_log_eq_log hb hx] at h_mul_log_lt -- log x < (k+1) * log b

  -- Apply exp (strictly monotone)
  have h_exp_lt : Real.exp (Real.log x) < Real.exp (((k : ℝ) + 1) * Real.log b) :=
    Real.exp_lt_exp.mpr h_mul_log_lt

  -- Simplify LHS using exp_log
  rw [Real.exp_log hx_pos] at h_exp_lt -- x < exp(...)

  -- Simplify RHS using rpow_def_of_pos (backwards)
  rw [mul_comm ((k : ℝ) + 1) (Real.log b), ← Real.rpow_def_of_pos hb_pos] at h_exp_lt -- Changed: Added ←
  -- Now have: x < (b : ℝ) ^ ((k : ℝ) + 1)

  -- Rewrite exponent using Nat.cast_add_one
  have exp_eq : (k : ℝ) + 1 = (↑(k + 1) : ℝ) := (Nat.cast_add_one k).symm
  rw [exp_eq] at h_exp_lt -- x < (b : ℝ) ^ (↑(k + 1) : ℝ)

  -- Rewrite the expression in the hypothesis using rpow_natCast (forward direction)
  have hb_nonneg : 0 ≤ (b : ℝ) := le_of_lt hb_pos -- Need b ≥ 0 for rpow_natCast
  rw [Real.rpow_natCast (b : ℝ) (k + 1)] at h_exp_lt -- x < (b : ℝ) ^ (k + 1) (Nat exponent)

  -- The inequality now matches the goal
  exact h_exp_lt

/-- Lemma: For any `x ≥ 1` and integer `b ≥ 2`, there exists an integer `k` such that `b^k ≤ x < b^(k+1)`. This `k` is `floor(log_b(x))`. Uses Nat exponent version. -/
lemma exists_nat_pow_bounds {b : ℕ} {x : ℝ} (hb : b ≥ 2) (hx : x ≥ 1) :
  ∃ k : ℕ, (b : ℝ) ^ k ≤ x ∧ x < (b : ℝ) ^ (k + 1) := by
  -- Define k as the floor of log base b of x
  let k := Nat.floor (Real.logb b x)
  -- Claim existence of this k
  use k
  -- Prove the two inequalities using the helper lemmas with Nat exponents
  constructor
  · exact pow_nat_floor_logb_le_x hb hx
  · exact x_lt_pow_succ_floor_logb hb hx



/-- Helper: Prove 1 ≤ (b:ℝ)^k by induction for b ≥ 1. -/
lemma one_le_pow_of_one_le_real {b : ℝ} (hb : 1 ≤ b) (k : ℕ) : 1 ≤ b ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero, le_refl] -- 1 ≤ 1
  | succ k ih => -- ih: 1 ≤ b^k. Goal: 1 ≤ b^(k+1)
    rw [pow_succ] -- Goal: 1 ≤ b^k * b
    -- We know 1 ≤ b (hb)
    -- We know 1 ≤ b^k (ih)
    -- Since 1 ≤ b, we have 0 ≤ 1 ≤ b, so b is non-negative.
    have hb_nonneg : 0 ≤ b := le_trans zero_le_one hb
    -- Multiply the inequality ih (1 ≤ b^k) by b (non-negative) on the right:
    -- 1 * b ≤ b^k * b
    -- We need `mul_le_mul_of_nonneg_right` which holds in `LinearOrderedSemiring` like ℝ
    have h_mul_le : 1 * b ≤ b ^ k * b := by
      apply mul_le_mul_of_nonneg_right
      · exact ih -- The inequality 1 ≤ b^k
      · exact hb_nonneg -- Proof that the multiplier b is non-negative

    simp only [one_mul] at h_mul_le -- Simplify 1 * b to b. Now: b ≤ b^k * b
    -- We have 1 ≤ b (hb) and b ≤ b^k * b (h_mul_le)
    -- By transitivity of ≤ :
    exact le_trans hb h_mul_le

/-- Lemma: `1 ≤ (n : ℝ) ^ (m : ℝ)` given `n ≥ 1, m ≥ 1`. -/
lemma one_le_rpow_cast_pow {n m : ℕ} (hn : n ≥ 1) :
    1 ≤ (n : ℝ) ^ (m : ℝ) := by
  -- Cast n ≥ 1 to Real: ↑n ≥ 1
  have hn_real_ge_1 : (n : ℝ) ≥ 1 := Nat.one_le_cast.mpr hn
  -- Cast m ≥ 1 implies m ≥ 0 in Real: ↑m ≥ 0
  have hm_real_nonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m -- m ≥ 1 → m ≥ 0 holds for Nat

  -- Rewrite 1 as 1 ^ ↑m using Real.one_rpow
  rw [← Real.one_rpow (m : ℝ)] -- Goal: 1 ^ ↑m ≤ ↑n ^ ↑m

  -- Apply Real.rpow_le_rpow {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) {r : ℝ} (hr : 0 ≤ r) : x ^ r ≤ y ^ r
  -- Here x=1, y=↑n, r=↑m
  apply Real.rpow_le_rpow
  · -- Prove 0 ≤ 1
    exact zero_le_one
  · -- Prove 1 ≤ ↑n
    exact hn_real_ge_1
  · -- Prove 0 ≤ ↑m
    exact hm_real_nonneg

-- Helper lemma (should be placed earlier or imported)
lemma one_le_pow_cast {n m : ℕ} (hn : n ≥ 1) :
    1 ≤ (n : ℝ) ^ m := by
  have hn_real_ge_1 : (n : ℝ) ≥ 1 := Nat.one_le_cast.mpr hn
  -- Use library lemma for powers of reals ≥ 1
  exact one_le_pow_of_one_le_real hn_real_ge_1 m


lemma one_le_implies_pos {x : ℝ} (hx : x ≥ 1) : 0 < x := by linarith

/-- Lemma: `logb b` is monotone increasing for base `b ≥ 2` and arguments ≥ 1. -/
lemma logb_le_logb_of_le {b : ℕ} {y z : ℝ} (hb : b ≥ 2) (hy : y ≥ 1) (hz : z ≥ 1) (h_le : y ≤ z) :
    Real.logb b y ≤ Real.logb b z := by
  -- Preconditions for Real.logb
  have hb_pos : 0 < (b : ℝ) := cast_pos_of_ge_two hb
  have hb_ne_one : (b : ℝ) ≠ 1 := ne_of_gt (one_lt_cast_of_ge_two hb)
  have hy_pos : 0 < y := one_le_implies_pos hy
  have hz_pos : 0 < z := one_le_implies_pos hz

  -- Use Real.logb_le_logb which requires base > 1
  have hb_gt_one : (b : ℝ) > 1 := one_lt_cast_of_ge_two hb
  exact (Real.logb_le_logb hb_gt_one hy_pos hz_pos).mpr h_le

/-! ### Chunk 3.4c: logb of a power -/

/-- Lemma: `logb b (b^k) = k` for Nat exponent k. -/
lemma logb_pow_eq_self {b k : ℕ} (hb : b ≥ 2) :
    Real.logb b ((b : ℝ) ^ k) = (k : ℝ) := by
  -- Need base > 0 and base ≠ 1 for logb
  have hb_pos : 0 < (b : ℝ) := cast_pos_of_ge_two hb
  have hb_ne_one : (b : ℝ) ≠ 1 := ne_of_gt (one_lt_cast_of_ge_two hb)

  -- Use Real.logb_rpow after casting k to ℝ using Real.rpow_nat_cast
  -- Rewrite the Nat power to Real power (rpow) using conv
  conv =>
    lhs       -- Focus on the left-hand side: logb (↑b) (↑b ^ k)
    arg 2     -- Focus on the second argument: ↑b ^ k
    rw [← Real.rpow_natCast (b : ℝ) k] -- Rewrite ↑b ^ k to ↑b ^ (↑k : ℝ) using the theorem backwards
  -- Goal is now logb (↑b) (↑b ^ (↑k : ℝ)) = ↑k

  -- Apply Real.logb_rpow, providing the required proofs for the base b (which is ↑b here)
  rw [Real.logb_rpow hb_pos hb_ne_one] -- Goal: ↑k = ↑k
  -- The proof is complete as the goal becomes an identity.

/-! ### Chunk 3.4d: Lower bound on k using logb -/




/-- Lemma: `k ≤ logb b x` given `(b : ℝ) ^ k ≤ x`. -/
lemma k_le_logb_rpow {b k : ℕ} {x : ℝ} (hb : b ≥ 2) (hx : x ≥ 1)
    (hk_le_x_pow : (b : ℝ) ^ k ≤ x) :
    (k : ℝ) ≤ Real.logb b x := by
  -- Apply logb b to both sides of hk_le_x_pow using monotonicity
  have h_logb_le : Real.logb b ((b : ℝ) ^ k) ≤ Real.logb b x := by
    apply logb_le_logb_of_le hb
    · -- Prove 1 ≤ (b:ℝ)^k using the helper lemma
      apply one_le_pow_of_one_le_real
      · exact Nat.one_le_cast.mpr (Nat.le_of_lt hb) -- Need base ≥ 1
      -- k is the exponent argument
    · exact hx -- Given x ≥ 1
    · exact hk_le_x_pow

  -- Simplify the LHS using logb_pow_eq_self (ensure it's defined above)
  have h_lhs_eq_k : Real.logb b ((b : ℝ) ^ k) = (k : ℝ) := logb_pow_eq_self hb

  -- Rewrite the LHS in the inequality
  rw [h_lhs_eq_k] at h_logb_le
  exact h_logb_le

-- Define define the lemma logb_lt_logb_of_lt using Real.logb_lt_logb and place it before its usage.
-- This lemma states that if b ≥ 2 and x, y ≥ 1, then logb b x < logb b y if x < y.
lemma logb_lt_logb_of_lt {b : ℝ} (hb : b ≥ 2) {x y : ℝ} (hx : x ≥ 1) (hxy : x < y) :
    Real.logb b x < Real.logb b y := by
  -- Preconditions for Real.logb_lt_logb
  have hb_gt_one : 1 < b := by linarith -- b ≥ 2 implies b > 1
  have hx_pos : 0 < x := one_le_implies_pos hx -- x ≥ 1 implies x > 0
  -- hy_pos is not directly needed by Real.logb_lt_logb signature but good practice

  -- Apply the lemma from Real.logb with the correct arguments
  apply Real.logb_lt_logb hb_gt_one hx_pos hxy

/-- Lemma: `logb b x < k + 1` given `x < (b : ℝ) ^ (k + 1)`. -/
lemma logb_rpow_lt_k_plus_1 {b k : ℕ} {x : ℝ} (hb_nat : b ≥ 2) (hx : x ≥ 1)
    (hx_lt_kp1 : x < (b : ℝ) ^ (k + 1)) :
    Real.logb b x < (k + 1 : ℝ) := by
  -- Cast b to Real for logb operations
  let b_real := (b : ℝ)
  have hb : b_real ≥ 2 := by exact Nat.cast_le.mpr hb_nat

  -- Apply logb b to both sides of hx_lt_kp1 using strict monotonicity
  have h_logb_lt : Real.logb b_real x < Real.logb b_real (b_real ^ (k + 1)) := by
    -- Apply the lemma directly with the available hypotheses
    apply logb_lt_logb_of_lt hb hx hx_lt_kp1
    -- Removed the incorrect proof steps that followed the apply

  -- Simplify the RHS using logb_pow_eq_self
  have h_rhs_eq_kp1 : Real.logb b_real (b_real ^ (k + 1)) = (k + 1 : ℝ) := by
    -- Rewrite the RHS goal `(k + 1 : ℝ)` to `↑(k + 1)` using Nat.cast_add_one backwards
    rw [← Nat.cast_add_one]
    -- Now the goal is `logb b_real (b_real ^ (k + 1)) = ↑(k + 1)`
    -- Since b_real = ↑b, this matches the type of logb_pow_eq_self
    exact logb_pow_eq_self hb_nat-- Corrected line

  -- Rewrite the RHS in the inequality
  rw [h_rhs_eq_kp1] at h_logb_lt
  exact h_logb_lt

lemma logb_rpow_bounds_k {b : ℕ} {x : ℝ} (hb : b ≥ 2) (hx : x ≥ 1) :
    ∃ k : ℕ, Real.logb b x - 1 < (k : ℝ) ∧ (k : ℝ) ≤ Real.logb b x := by
  -- Use exists_nat_pow_bounds to find k such that b^k ≤ x < b^(k+1)
  rcases exists_nat_pow_bounds hb hx with ⟨k, h_bk_le_x, h_x_lt_bkp1⟩

  -- Prove the two inequalities for this k
  use k
  constructor
  · -- Prove logb b x - 1 < k
    -- Start from x < b^(k+1)
    have h_logb_lt_kp1 : Real.logb b x < (k + 1 : ℝ) := by
      apply logb_rpow_lt_k_plus_1 hb hx h_x_lt_bkp1
    -- The rewrite is not needed as ↑(k + 1) is often automatically ↑k + 1
    -- Subtract 1 from both sides using linarith
    linarith [h_logb_lt_kp1]
  · -- Prove k ≤ logb b x
    -- Start from b^k ≤ x
    have h_k_le_logb : (k : ℝ) ≤ Real.logb b x := by
      apply k_le_logb_rpow hb hx h_bk_le_x
    exact h_k_le_logb

/-- Lemma: `logb b (n^m) = m * logb b n` for Real exponent m.
Requires `b > 0`, `b ≠ 1` (implicit in `Real.logb`), and `n ≥ 1`. -/
lemma logb_rpow_eq_mul_logb {b n : ℕ} {m : ℝ} (hn : n ≥ 1) :
    Real.logb b ((n : ℝ) ^ m) = m * Real.logb b n := by
  -- Precondition required explicitly by the lemma Real.logb_rpow_eq_mul_logb_of_pos
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (by linarith [hn] : n > 0)
  -- (Implicit preconditions 0 < ↑b and ↑b ≠ 1 are handled by logb's definition)

  -- Apply the lemma, providing only the required explicit argument hn_pos
  exact Real.logb_rpow_eq_mul_logb_of_pos hn_pos
  -- Lean matches the implicit b in the lemma with ↑b from the goal,
  -- x with ↑n, and y with m.

/-! ### Chunk 3.4h: Logarithmic Trapping - Final Bound -/

-- Assume lemmas from LogF.lean (like logb_rpow_eq_mul_logb etc.) are available

/-- Lemma: `logb b (n^m) = m * logb b n` for Nat exponent m. -/
lemma logb_pow_eq_mul_logb_nat {b n m : ℕ} (_hb : b ≥ 2) (_hn : n ≥ 1) : -- hb, hn proofs not needed by logb_pow
    Real.logb b ((n : ℝ) ^ m) = (m : ℝ) * Real.logb b n := by
  -- The goal is logb (↑b) (↑n ^ m) = ↑m * logb ↑b ↑n
  -- The lemma statement is logb b' (x' ^ k') = ↑k' * logb b' x'
  -- Unifying: b' = ↑b, x' = ↑n, k' = m
  -- The instantiated lemma statement is identical to the goal.
  exact Real.logb_pow (b : ℝ) (n : ℝ) m


/-! Step 1: Prove logb b x = m * logb b n -/
lemma prove_logb_x_eq {n m b : ℕ} (hn : n ≥ 1) (hb : b ≥ 2) (x : ℝ) (hx_def : x = (n : ℝ) ^ m) :
    Real.logb b x = (m : ℝ) * Real.logb b n := by
  -- Substitute the definition of x into the goal
  rw [hx_def] -- Goal: logb ↑b (↑n ^ m) = ↑m * logb ↑b ↑n
  -- Apply the lemma for Nat exponents
  exact logb_pow_eq_mul_logb_nat hb hn

-- Retry Step 1 using the corrected lemma name for Nat powers
lemma prove_logb_x_eq_nat {n m b : ℕ} (hn : n ≥ 1) (hb : b ≥ 2) (x : ℝ) (hx_def : x = (n : ℝ) ^ m) :
    Real.logb b x = (m : ℝ) * Real.logb b n := by
  rw [hx_def] -- Goal: logb ↑b (↑n ^ m) = ↑m * logb ↑b ↑n
  exact logb_pow_eq_mul_logb_nat hb hn

/--
Lemma: If `k` satisfies the power bounds `(b : ℝ) ^ k ≤ x < (b : ℝ) ^ (k + 1)`,
then `k` also satisfies the logarithmic bounds `logb b x - 1 < k` and `k ≤ logb b x`.
-/
lemma logb_x_bounds_k {b k : ℕ} {x : ℝ} (hb : b ≥ 2) (hx : x ≥ 1)
    (h_pow_bounds : (b : ℝ) ^ k ≤ x ∧ x < (b : ℝ) ^ (k + 1)) :
    Real.logb b x - 1 < (k : ℝ) ∧ (k : ℝ) ≤ Real.logb b x := by
  -- Deconstruct the power bounds
  rcases h_pow_bounds with ⟨h_lower_pow, h_upper_pow⟩

  -- Prove the two required inequalities
  constructor
  · -- Prove logb b x - 1 < k
    -- Start from x < b^(k+1)
    have h_logb_lt_kp1 : Real.logb b x < (k + 1 : ℝ) := by
      apply logb_rpow_lt_k_plus_1 hb hx h_upper_pow
    -- The rewrite is not needed as ↑(k + 1) is often automatically ↑k + 1
    -- Subtract 1 from both sides using linarith
    linarith [h_logb_lt_kp1]
  · -- Prove k ≤ logb b x
    -- Start from b^k ≤ x
    have h_k_le_logb : (k : ℝ) ≤ Real.logb b x := by
      apply k_le_logb_rpow hb hx h_lower_pow
    exact h_k_le_logb

/--
Lemma: Translates bounds on `logb b x` in terms of `k` to bounds on
`m * logb b n` using the identity `logb b x = m * logb b n` where `x = (n:ℝ)^m`.
-/
lemma logb_n_times_m_bounds_k {n m b k : ℕ} (hn : n ≥ 1) (hb : b ≥ 2)
    (x : ℝ) (hx_def : x = (n : ℝ) ^ m)
    (h_logb_x_bounds : Real.logb b x - 1 < (k : ℝ) ∧ (k : ℝ) ≤ Real.logb b x) :
    (m : ℝ) * Real.logb b n - 1 < (k : ℝ) ∧ (k : ℝ) ≤ (m : ℝ) * Real.logb b n := by
  -- Prove the identity logb b x = m * logb b n
  have h_logb_x_eq : Real.logb b x = (m : ℝ) * Real.logb b n := by
    apply prove_logb_x_eq_nat hn hb x hx_def

  -- Rewrite the logb expression in the hypothesis bounds using the identity
  rw [h_logb_x_eq] at h_logb_x_bounds

  -- The hypothesis now directly matches the goal
  exact h_logb_x_bounds

/--
Lemma: Converts bounds involving `m * logb b n` to bounds involving `logb b n`
by dividing by `m`. Requires `m ≥ 1`.
-/
lemma logb_n_bounds_k_div_m {n m b k : ℕ} (_hn : n ≥ 1) (_hb : b ≥ 2) (hm : m ≥ 1)
    (h_logb_nm_bounds : (m : ℝ) * Real.logb b n - 1 < (k : ℝ) ∧ (k : ℝ) ≤ (m : ℝ) * Real.logb b n) :
    Real.logb b n - 1 / (m : ℝ) < (k : ℝ) / (m : ℝ) ∧ (k : ℝ) / (m : ℝ) ≤ Real.logb b n := by
  -- Deconstruct the input hypothesis
  rcases h_logb_nm_bounds with ⟨h_lower_mul, h_upper_mul⟩

  -- Need m > 0 for division properties
  have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr (by linarith [hm] : m > 0)

  constructor
  · -- Prove logb b n - 1 / m < k / m
    calc
      Real.logb b n - 1 / (m : ℝ) = ((m : ℝ) * Real.logb b n - 1) / m := by
        field_simp [hm_pos, mul_comm] -- Added mul_comm
      -- Use div_lt_div_iff_of_pos_right, which requires a < b to prove a / c < b / c
      _ < (k : ℝ) / m := by exact (div_lt_div_iff_of_pos_right hm_pos).mpr h_lower_mul

  · -- Prove k / m ≤ logb b n
    -- Use div_le_iff₀' which states (a / c ≤ b ↔ a ≤ c * b) for c > 0.
    -- Let a = k, c = m, b = logb b n.
    -- Goal is k / m ≤ logb b n. The lemma rewrites this to k ≤ m * logb b n.
    -- This is exactly h_upper_mul.
    exact (div_le_iff₀' hm_pos).mpr h_upper_mul

lemma lt_add_iff_sub_left_real (a b c : ℝ) : a < b + c ↔ a - c < b := by
  -- Prove forward direction: a < b + c → a - c < b
  apply Iff.intro
  · intro h
    calc
      a - c < b + c - c := by exact sub_lt_sub_right h c
      _ = b := by ring -- Simplifies b + c - c to b
  · -- Prove backward direction: a - c < b → a < b + c
    intro h
    calc
      a = a - c + c := by ring -- Rewrite a
      _ < b + c := by exact add_lt_add_right h c

/-! ### Chunk 3.4 - Breakdown Step 5 - Helper 5: Negation of Division -/
lemma helper_neg_div (a b : ℝ) : -(a / b) = -a / b := by
  field_simp -- Try field_simp first


lemma helper_neg_sub (a b : ℝ) : -(a - b) = b - a := by
  exact neg_sub a b

lemma le_add_iff_sub_left_real (a b c : ℝ) : a ≤ b + c ↔ a - b ≤ c := by
  apply Iff.intro
  · intro h -- a ≤ b + c
    calc
      a - b ≤ (b + c) - b := by exact sub_le_sub_right h b
      _ = c := by ring
  · intro h -- a - b ≤ c
    calc
      a = a - b + b := by ring
      _ ≤ c + b := by exact add_le_add_right h b
      _ = b + c := by rw [add_comm]

/-! ### Chunk 3.5 - Limit Argument Helpers -/

/--
Lemma (Archimedean Helper): For any `ε > 0`, there exists a natural number `m ≥ 1`
such that `1 / (m : ℝ) ≤ ε`.
-/
lemma exists_one_le_nat_one_div_le {ε : ℝ} (hε : ε > 0) :
    ∃ m : ℕ, m ≥ 1 ∧ 1 / (m : ℝ) ≤ ε := by
  -- Use the Archimedean property to find a natural k such that 1 / (k + 1) < ε
  rcases exists_nat_one_div_lt hε with ⟨k, hk⟩
  -- Let m = k + 1
  let m := k + 1
  -- Claim existence of this m
  use m
  -- Prove the two required properties: m ≥ 1 and 1 / m ≤ ε
  constructor
  · -- Prove m ≥ 1
    exact Nat.succ_pos k -- k + 1 is always ≥ 1 for any Nat k
  · -- Prove 1 / m ≤ ε
    -- We have hk : 1 / (↑k + 1) < ε
    -- Substitute m = k + 1 into hk
    have h_one_div_m_lt_ε : 1 / (m : ℝ) < ε := by
      -- Simplify the goal using the definition of m
      simp only [m]
      -- Rewrite ↑(k + 1) using Nat.cast_add_one
      rw [Nat.cast_add_one k]
      -- Apply the hypothesis hk
      exact hk
    -- Use le_of_lt to convert the strict inequality to ≤
    exact le_of_lt h_one_div_m_lt_ε


-- Replacements for Mathlib3 lemmas that are not in Mathlib4 yet
lemma pos_of_ge_one {x : ℝ} (h : 1 ≤ x) : 0 < x :=
  lt_of_lt_of_le zero_lt_one h

lemma pos_of_one_le {n : ℕ} (h : 1 ≤ n) : 0 < n :=
  Nat.lt_of_lt_of_le Nat.zero_lt_one h

lemma logb_eq_log {b x : ℝ} :
    logb b x = log x / log b := by
  rw [logb]

/--
The logarithm of the inverse equals the negative of the logarithm.
That is, for any positive real number `x`, we have `log(x⁻¹) = -log(x)`.
-/
lemma log_inv_eq_neg_log {x : ℝ} (_hx : 0 < x) :
    Real.log (x⁻¹) = -Real.log x := by
  -- Use the properties of logarithms
  simp [Real.log_inv]

lemma one_le_iff_pos {n : ℕ} : 1 ≤ n ↔ 0 < n := by
  simpa [Nat.pos_iff_ne_zero] using (Nat.one_le_iff_ne_zero (n:=n))  -- if you import `Nat.pos_iff_ne_zero`  [oai_citation:2‡Lean Community](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Fin/Basic.html?utm_source=chatgpt.com)


lemma sum_count_eq_card {N : ℕ} (s : Multiset (Fin N)) :
    ∑ i : Fin N, Multiset.count i s = Multiset.card s := by
  -- instantiate the library lemma with `s = Finset.univ`
  have hms : ∀ a ∈ s, (a : Fin N) ∈ (Finset.univ : Finset (Fin N)) := by
    intro a ha
    exact Finset.mem_univ _
  -- The goal is definitionally equal to the statement of Multiset.sum_count_eq_card
  exact (Multiset.sum_count_eq_card (s := (Finset.univ : Finset (Fin N))) (m := s) hms)

/-!
Helper lemma for `right_inv_beState_multiset`.
Shows that if element `i` is not in multiset `s`, replicating `i` by its count in `s` (which is 0)
results in the empty multiset `0`.
-/
lemma replicate_count_zero_of_not_mem {α : Type*} [DecidableEq α] {s : Multiset α} {i : α} (hi_not_mem : i ∉ s) :
    Multiset.replicate (Multiset.count i s) i = 0 := by
  -- Use the property that `i ∉ s` is equivalent to `count i s = 0`
  have h_count_eq_zero : Multiset.count i s = 0 := Multiset.count_eq_zero.mpr hi_not_mem
  -- Rewrite the count in the goal using this fact
  rw [h_count_eq_zero]
  -- Apply the definition of replicate with count 0
  rw [Multiset.replicate_zero]


@[simp] lemma toFinset_cons
    {α} [DecidableEq α] (a : α) (s : Multiset α) :
  (a ::ₘ s).toFinset = insert a s.toFinset := by
  -- `rw [Multiset.toFinset_cons]` is a simp lemma  :contentReference[oaicite:8]{index=8}
  simp

-- @[simp] lemma count_cons_self
--     {α} [DecidableEq α] (a : α) (s : Multiset α) :
--   Multiset.count a (a ::ₘ s) = Multiset.count a s + 1 := by
--   exact Multiset.count_cons_self a s

lemma count_cons_ne
    {α} [DecidableEq α] {a i : α} (h : i ≠ a) (s : Multiset α) :
  Multiset.count i (a ::ₘ s) = Multiset.count i s := by
  exact Multiset.count_cons_of_ne h s  -- Directly apply the lemma

lemma replicate_split {α} (n : ℕ) (a : α) :
    Multiset.replicate (n + 1) a =
      Multiset.replicate 1 a + Multiset.replicate n a := by
  rw [Nat.add_comm] -- Goal: replicate (1 + n) a = replicate 1 a + replicate n a
  exact Multiset.replicate_add 1 n a -- Apply the standard lemma
  -- `replicate_add`

lemma sum_congr_count
    {β} [AddCommMonoid β] {α} [DecidableEq α]
    {s : Finset α} {f g : α → β}
    (hfg : ∀ i ∈ s, f i = g i) :
  (∑ i ∈ s, f i) = ∑ i ∈ s, g i :=
by
  -- zipper lemma  `Finset.sum_congr`  :contentReference[oaicite:13]{index=13}
  simpa using Finset.sum_congr rfl hfg

@[simp] lemma sum_replicate_count_nil
    {α} [DecidableEq α] :
  (∑ i ∈ (0 : Multiset α).toFinset, -- Corrected summation notation
      Multiset.replicate (Multiset.count i (0 : Multiset α)) i) = (0 : Multiset α) :=
by
  rw [Multiset.toFinset_zero] -- (0 : Multiset α).toFinset = ∅
  exact Finset.sum_empty      -- Sum over empty finset is 0

/--
Lemma (Core Limit Argument): If the absolute difference between two real numbers `x` and `y`
is bounded by `1/m` for all natural numbers `m ≥ 1`, then `x` must equal `y`.
-/
lemma eq_of_abs_sub_le_inv_ge_one_nat {x y : ℝ} (h_bound : ∀ m : ℕ, m ≥ 1 → |x - y| ≤ 1 / (m : ℝ)) :
    x = y := by
  -- Use the metric space lemma eq_of_forall_dist_le
  -- The goal becomes: ∀ ε > 0, dist x y ≤ ε
  apply eq_of_forall_dist_le
  -- Introduce arbitrary ε > 0
  intro ε hε
  -- Show dist x y ≤ ε
  -- For Real numbers, dist x y = |x - y|
  simp_rw [dist_eq_norm_sub, Real.norm_eq_abs] -- Goal: |x - y| ≤ ε
  -- Use the Archimedean helper to find m ≥ 1 such that 1 / m ≤ ε
  rcases exists_one_le_nat_one_div_le hε with ⟨m, hm_ge_1, h_inv_m_le_ε⟩
  -- Use the hypothesis h_bound for this specific m
  have h_abs_le_inv_m : |x - y| ≤ 1 / (m : ℝ) := h_bound m hm_ge_1
  -- Combine the two inequalities using transitivity
  exact le_trans h_abs_le_inv_m h_inv_m_le_ε -- |x - y| ≤ 1 / m and 1 / m ≤ ε implies |x - y| ≤ ε

-- Re-include the custom exists_pow_ge lemma and its use in exists_pow2_bound
lemma exists_pow_ge {a n : ℕ} (ha : 1 < a) : ∃ k : ℕ, n ≤ a ^ k :=
by
  cases n with
  | zero =>
      use 0
      exact Nat.zero_le (a ^ 0)
  | succ m =>
      use (m + 1)
      have h_lt : m + 1 < a ^ (m + 1) := Nat.lt_pow_self ha
      exact Nat.le_of_lt h_lt


lemma nat_bounds_from_cast_pow_bounds {b k n m : ℕ}
    (h_le_cast : (b : ℝ) ^ k ≤ (n : ℝ) ^ m)
    (h_lt_cast : (n : ℝ) ^ m < (b : ℝ) ^ (k + 1)) :
    b ^ k ≤ n ^ m ∧ n ^ m < b ^ (k + 1) := by

  -- Rewrite the hypotheses using Nat.cast_pow forwards to get the form ↑(...) required by mp
  rw [← Nat.cast_pow b k] at h_le_cast      -- Goal: Transform (↑b)^k into ↑(b^k)
  rw [← Nat.cast_pow n m] at h_le_cast      -- Goal: Transform (↑n)^m into ↑(n^m)
                                            -- h_le_cast is now ↑(b^k) ≤ ↑(n^m)

  rw [← Nat.cast_pow n m] at h_lt_cast      -- Goal: Transform (↑n)^m into ↑(n^m)
  rw [← Nat.cast_pow b (k + 1)] at h_lt_cast -- Goal: Transform (↑b)^(k+1) into ↑(b^(k+1))
                                             -- h_lt_cast is now ↑(n^m) < ↑(b^(k+1))

  -- Convert the inequalities involving casts back to Nat inequalities using mp
  constructor
  · -- Prove b^k ≤ n^m
    exact Nat.cast_le.mp h_le_cast
  · -- Prove n^m < b^(k+1)
    exact Nat.cast_lt.mp h_lt_cast

lemma div_bounds_from_mul_bounds {A B C D E : ℝ} (hC : C > 0) (hD : D > 0)
    (h_le1 : A * C ≤ B * D) (h_le2 : B * D ≤ E * C) :
    A / D ≤ B / C ∧ B / C ≤ E / D := by
  constructor
  · -- Prove A / D ≤ B / C
    -- Use div_le_div_iff which states (a / d ≤ b / c ↔ a * c ≤ b * d) given d > 0, c > 0
    rwa [div_le_div_iff₀ hD hC] -- Rewrites goal A / D ≤ B / C to A * C ≤ B * D and uses h_le1
  · -- Prove B / C ≤ E / D
    -- Use div_le_div_iff which states (b / c ≤ e / d ↔ b * d ≤ e * c) given c > 0, d > 0
    rwa [div_le_div_iff₀ hC hD] -- Rewrites goal B / C ≤ E / D to B * D ≤ E * C and uses h_le2


/--
Helper: Rearranges the equality `a / b = c / d` to `a = (b / d) * c`,
given denominators are non-zero.
-/
lemma rearrange_ratio_equality {a b c d : ℝ} (hb : b ≠ 0) (_hd : d ≠ 0)
    (h_ratio : a / b = c / d) :
    a = (b / d) * c := by
  -- Start from a / b = c / d
  -- Multiply both sides by b
  rw [div_eq_iff hb] at h_ratio
  -- h_ratio: a = (c / d) * b
  -- Rearrange RHS: (c / d) * b = (c * b) / d
  rw [div_mul_eq_mul_div] at h_ratio
  -- h_ratio: a = (c * b) / d
  -- Commute multiplication in numerator: (c * b) / d = (b * c) / d
  rw [mul_comm c b] at h_ratio
  -- h_ratio: a = (b * c) / d
  -- Associate division differently: (b * c) / d = (b / d) * c using div_mul_eq_mul_div
  -- This step implicitly uses hd ≠ 0
  rw [← div_mul_eq_mul_div] at h_ratio
  -- h_ratio: a = (b / d) * c
  exact h_ratio

-- Helper to convert Real.log k to NNReal, assuming k ≥ 1 (so log k ≥ 0)
noncomputable def RealLogNatToNNReal (k : ℕ) (hk_ge1 : k ≥ 1) : NNReal :=
  ⟨Real.log (k : ℝ), by
    apply Real.log_nonneg
    rw [Nat.one_le_cast]
    exact hk_ge1
  ⟩


/-- Distributes division by a non-zero `NNReal` constant `d` out of a `Finset` sum. -/
lemma NNReal.sum_div {α : Type*} [DecidableEq α] (s : Finset α) (f : α → NNReal) (d : NNReal) (_hd_ne_zero : d ≠ 0) :
    (∑ i ∈ s, f i / d) = (∑ i ∈ s, f i) / d := by
  -- Proof by induction on the Finset s
  refine Finset.induction_on s ?base_case ?inductive_step
  · -- Base case: s = ∅
    simp only [Finset.sum_empty, zero_div]
  · -- Inductive step: s = insert x t, where x ∉ t
    intro x t hx_not_in_t ih_sum_div_t
    simp only [Finset.sum_insert hx_not_in_t]
    -- Goal: f x / d + ∑ (i : α) in t, f i / d = (f x + ∑ (i : α) in t, f i) / d
    rw [ih_sum_div_t] -- Apply induction hypothesis to the sum over t
    exact (div_add_div_same (f x) (∑ i ∈ t, f i) d)

/--
Constructs a probability distribution `P_rat : Fin n → NNReal` where each component
`P_rat i` is a rational number `(a i) / N_den`.
Requires `a i` to be natural numbers, `N_den` a positive natural number,
and `∑ a i = N_den`.
-/
noncomputable def create_rational_dist (n : ℕ) (a : Fin n → ℕ) (N_den : ℕ)
    (_h_sum_a_eq_N : ∑ i, a i = N_den) (_hN_den_pos : N_den > 0) : Fin n → NNReal :=
  fun i => (a i : NNReal) / (N_den : NNReal)

/--
The distribution created by `create_rational_dist` sums to 1, confirming it's a
valid probability distribution.
-/
lemma sum_create_rational_dist_eq_one (n : ℕ) (a : Fin n → ℕ) (N_den : ℕ)
    (h_sum_a_eq_N : ∑ i, a i = N_den) (hN_den_pos : N_den > 0) :
    ∑ i, (create_rational_dist n a N_den h_sum_a_eq_N hN_den_pos) i = 1 := by
  -- Unfold the definition of create_rational_dist
  simp_rw [create_rational_dist]
  -- Goal: ∑ (i : Fin n), (a i : NNReal) / (N_den : NNReal) = 1

  -- Need proof that (N_den : NNReal) ≠ 0 to use NNReal.sum_div
  have hN_den_nnreal_ne_zero : (N_den : NNReal) ≠ 0 := by
    simp [NNReal.coe_eq_zero, Nat.pos_iff_ne_zero] -- Goal is N_den ≠ 0 after this
    let hN_den_pos_ne_zero : N_den ≠ 0 := Nat.ne_of_gt hN_den_pos
    exact hN_den_pos_ne_zero -- This directly proves the goal N_den ≠ 0
  -- Goal: ∑ (i : Fin n), (a i : NNReal) / (N_den : NNReal) = 1

  -- Apply NNReal.sum_div
  rw [NNReal.sum_div (Finset.univ : Finset (Fin n)) (fun i => (a i : NNReal)) (N_den : NNReal) hN_den_nnreal_ne_zero]
  -- Goal after sum_div: (∑ i ∈ Finset.univ, (a i : NNReal)) / (N_den : NNReal) = 1

  -- Rewrite the sum of NNReal casts using Nat.cast_sum.
  -- Nat.cast_sum states: ((∑ i ∈ s, f i : ℕ) : NNReal) = ∑ i ∈ s, ((f i : ℕ) : NNReal)
  -- We want to change the numerator from ∑ i ∈ Finset.univ, ((a i : ℕ) : NNReal)
  -- to ((∑ i ∈ Finset.univ, (a i : ℕ)) : NNReal), so we use ← Nat.cast_sum.
  rw [← Nat.cast_sum (Finset.univ : Finset (Fin n)) a]
  -- Goal: (((∑ i ∈ Finset.univ, a i : ℕ) : NNReal)) / ((N_den : ℕ) : NNReal) = 1

  -- Use the hypothesis h_sum_a_eq_N.
  -- h_sum_a_eq_N is ∑ i, a i = N_den.
  -- Since (∑ i, a i) is definitionally (∑ i ∈ Finset.univ, a i), this rewrite works.
  rw [h_sum_a_eq_N]
  -- Goal: (((N_den : ℕ) : NNReal)) / ((N_den : ℕ) : NNReal) = 1

  simp [hN_den_nnreal_ne_zero]
  -- Goal: 1 = 1 (which is true by reflexivity)

-- We will stop here for this step as requested.
-- The next steps would involve generalizing DependentPairDist and IsEntropyCondAdd,
-- then proving `RUE_rational_formula_H_P_rat`.



/-- Helper lemma to equate real power of 2 with a Nat exponent to the cast of Nat power of 2. -/
lemma real_two_pow_nat_eq_cast_nat_pow_two (n : ℕ) : (2:ℝ) ^ n = ↑((2:ℕ) ^ n) := by
  rw [Nat.cast_two.symm] -- Goal: (↑(2:ℕ):ℝ) ^ n = ↑((2:ℕ) ^ n)
  exact (Nat.cast_pow 2 n).symm



/-!
This lemma proves that if you take the ceiling of the base-2 logarithm of k,
that number of bits is sufficient to represent k states.
This is the mathematical core of RECT.
-/
lemma needed_bits_lemma (k : ℕ) (hk_pos : k > 0) :
    k ≤ 2 ^ (Nat.ceil (Real.logb 2 k)) :=
by
  -- 1. Start with the property that x ≤ ⌈x⌉ for any x.
  have h_le_ceil : Real.logb 2 k ≤ ↑(Nat.ceil (Real.logb 2 k)) :=
    Nat.le_ceil _

  -- 2. The function 2^x is monotone for real exponents when the base ≥ 1.
  --    Apply this to both sides of the inequality.
  have h_rpow_le : (2 : ℝ) ^ (Real.logb 2 k) ≤ (2 : ℝ) ^ (↑(Nat.ceil (Real.logb 2 k)) : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (2:ℝ)) h_le_ceil)

  -- 3. Simplify the left-hand side: 2 ^ (logb 2 k) simplifies to k.
  have h_k_real_pos : 0 < (k : ℝ) := Nat.cast_pos.mpr hk_pos
  rw [Real.rpow_logb (by norm_num) (by norm_num) h_k_real_pos] at h_rpow_le
  -- h_rpow_le is now: `↑k ≤ 2 ^ (↑(Nat.ceil (Real.logb 2 k)))` (with a real exponent)

  -- 4. Convert the real power (rpow) on the RHS to a natural number power (pow).
  rw [Real.rpow_natCast] at h_rpow_le
  -- h_rpow_le is now: `↑k ≤ (2:ℝ) ^ (Nat.ceil (Real.logb 2 k))` (HPow with ℕ exponent)
  let L := Nat.ceil (Real.logb 2 k)
  -- h_rpow_le is effectively `↑k ≤ (2:ℝ) ^ L`

  -- 5. Rewrite (2:ℝ)^L to ↑(2^L) using the helper lemma.
  rw [real_two_pow_nat_eq_cast_nat_pow_two L] at h_rpow_le
  -- h_rpow_le is now: `↑k ≤ ↑(2 ^ L)`

  -- 6. Now the inequality is between two casted Nats, so `Nat.cast_le.mp` applies.
  exact Nat.cast_le.mp h_rpow_le
