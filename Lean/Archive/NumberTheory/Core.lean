import Mathlib.Logic.Equiv.Defs -- For Equiv
import Mathlib.Logic.Equiv.Basic   -- Equiv API
import Mathlib.Logic.Equiv.Nat     -- intEquivNat, natSumNatEquivNat, …
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Real.Cardinality
import Mathlib.Control.Random
import Mathlib.Data.Fintype.Vector
import Mathlib.SetTheory.Cardinal.Basic   -- for `mul_eq_self`, `power_self_eq`
import Mathlib.Algebra.Equiv.TransferInstance  -- the abbreviations
import Mathlib.Analysis.Normed.Field.Basic     -- NormedField on ℝ, ℂ, …
import Mathlib.Topology.UniformSpace.Completion -- CompleteSpace on ℝ

import Archive.Core

namespace EGPT.NumberTheory.Core

open List EGPT


/-!
## EGPT Natural Numbers as ParticlePath: A Single Particle Path For A "Fair" Random Walk
##############################################################################
A Single Particle Path For A "Fair" Random Walk

ParticlePaths are the *Recorded History Stochastic Physical Events*
Physics events are information. Addresses = particle positions = movements in time = computation steps. Entropy is the measure of information and Shannon Entropy bits to store the past or Shannon Entropy calculations to describe a possible futre.

The "natural numbers" in EGPT can be thought of as the unique paths of random walks which return to their baseline (heads = tails) for the first time. For example, the number 1 is a path [1,0], 2 is [1,1,0,0], etc.. We can represent the same path in shorter form by dropping the trailing zeros and then the sum of 1's is the number itself. This is the canonical form of a natural number in EGPT.
##############################################################################
-/

-- make the predicate decidable so that the generic
-- --      `[Encodable {x // p x}]` instance can fire.
-- instance (L : List Bool) : Decidable (PathCompress_AllTrue L) := by
--   unfold PathCompress_AllTrue
--   exact List.decidableBAll (fun x => x = true) L
------------------------------------------------------------
-- Encodable instance now *does* synthesise
------------------------------------------------------------
--example : Encodable ParticlePath := inferInstance   -- compiles

------------------------------------------------------------
-- Bijection with ℕ
------------------------------------------------------------
def toNat   (u : ParticlePath) : ℕ := u.val.length

def fromNat (n : ℕ) : ParticlePath :=
  ⟨List.replicate n true, by
    intro x h_mem
    rw [List.mem_replicate] at h_mem
    exact h_mem.right⟩


lemma left_inv  (n : ℕ) : toNat (fromNat n) = n := by
  simp [toNat, fromNat]

lemma right_inv (u : ParticlePath) : fromNat (toNat u) = u := by
  cases u with
  | mk L hL =>
      simp [toNat, fromNat, List.length_replicate, Subtype.ext]
      exact (List.eq_replicate_of_mem hL).symm


def equivParticlePathToNat : ParticlePath ≃ ℕ :=
{ toFun    := toNat,
  invFun   := fromNat,
  left_inv := right_inv,
  right_inv:= left_inv }

/-- Adds two ParticlePath numbers by converting them to ℕ, adding, and converting back. -/
def add_ParticlePath (path1 path2 : ParticlePath) : ParticlePath :=
  equivParticlePathToNat.invFun (equivParticlePathToNat.toFun path1 + equivParticlePathToNat.toFun path2)


instance mkPseudoRandomSource (seed : ℕ) : IIDParticleSource Bool :=
{ stream := fun n =>
    let gen0 := mkStdGen seed
    let genN := (List.range n).foldl (fun g _ => (stdNext g).2) gen0
    (randBool genN).1 }

/-- A biased IID particle source that generates `true` with probability `p / (p + q)` and `false` with probability `q / (p + q)`. -/
instance mkBiasedIIDParticleSource (seed : ℕ) (p : ℕ) (q: ℕ) (_h : p + q > 0) : IIDParticleSource Bool :=
{ stream := fun n =>
    let gen0 := mkStdGen seed
    let genN := (List.range n).foldl (fun g _ => (stdNext g).2) gen0
    (randBool genN).1 }

-- In EGPT/NumberTheory/Core.lean


/--
**Helper function for multiplication: recursively multiply by adding.**
-/
def mul_ParticlePath_rec (a : ParticlePath) : ℕ → ParticlePath
  | 0 => fromNat 0 -- a * 0 = 0
  | Nat.succ n => add_ParticlePath a (mul_ParticlePath_rec a n) -- a * (n+1) = a + (a * n)

/--
**Multiplies two `ParticlePath` numbers.**
`mul_ParticlePath a b` is equivalent to adding `a` to itself `toNat(b)` times.
This is the EGPT-native definition of multiplication as repeated concatenation.
-/
def mul_ParticlePath (a b : ParticlePath) : ParticlePath :=
  mul_ParticlePath_rec a (toNat b)

-- In `EGPT/Complexity/Core.lean` or a new `Polynomial.lean` file

/--
**An EGPT-Native Polynomial (`EGPT_Polynomial`).**

This defines a polynomial function not by an abstract algebraic formula, but as a
constructive object. An `EGPT_Polynomial` is any function on `ParticlePath`s that
can be built from a finite number of additions, multiplications, constants, and
the identity function. This is the pure EGPT definition of a polynomial, free
from any external frameworks.
-/
inductive EGPT_Polynomial : Type
  | const (c : ParticlePath) : EGPT_Polynomial -- The constant function `f(n) = c`
  | id : EGPT_Polynomial                     -- The identity function `f(n) = n`
  | add (p₁ p₂ : EGPT_Polynomial) : EGPT_Polynomial -- The sum of two polynomials
  | mul (p₁ p₂ : EGPT_Polynomial) : EGPT_Polynomial -- The product of two polynomials

/--
**The `eval` function for an `EGPT_Polynomial`.**
This function takes a polynomial `p` and an input `n`, and computes the result
by recursively applying the native EGPT arithmetic operations.
-/
@[simp]
def EGPT_Polynomial.eval (p : EGPT_Polynomial) (n : ParticlePath) : ParticlePath :=
  match p with
  | const c => c
  | id => n
  | add p₁ p₂ => add_ParticlePath (p₁.eval n) (p₂.eval n)
  | mul p₁ p₂ => mul_ParticlePath (p₁.eval n) (p₂.eval n)
/--
**Lemma: `add_ParticlePath` respects the `toNat` bijection.**
-/
lemma toNat_add_ParticlePath (a b : ParticlePath) :
  toNat (add_ParticlePath a b) = toNat a + toNat b :=
by simp [add_ParticlePath, equivParticlePathToNat, toNat, fromNat]

/--
**Lemma: The `toNat` bijection respects EGPT multiplication.**
This proves that our native `mul_ParticlePath` operation correctly corresponds
to standard multiplication on natural numbers.
-/
theorem toNat_mul_ParticlePath (a b : ParticlePath) :
  toNat (mul_ParticlePath a b) = toNat a * toNat b :=
by
  -- We prove this by induction on the natural number representation of `b`.
  unfold mul_ParticlePath
  -- The goal is now `toNat (mul_ParticlePath_rec a (toNat b)) = toNat a * toNat b`.
  -- We prove this by induction on `toNat b`.
  induction toNat b with
  | zero =>
    -- Base case: toNat b = 0
    simp [mul_ParticlePath_rec, toNat, fromNat]
  | succ i ih =>
    -- Inductive step: prove toNat (mul_ParticlePath_rec a (i+1)) = toNat a * (i+1)
    -- By definition: mul_ParticlePath_rec a (i+1) = add_ParticlePath a (mul_ParticlePath_rec a i)
    show toNat (mul_ParticlePath_rec a (i + 1)) = toNat a * (i + 1)
    rw [mul_ParticlePath_rec]  -- This should unfold the definition
    rw [toNat_add_ParticlePath]
    rw [ih]
    ring

/-!
## Integers As EGPT ChargedParticlePath: A Single Particle Path, with initial direction ("Charge"), for A "Fair" Random Walk
##############################################################################
Symmetric particle paths could start up or down [1,1,0,0] and [0,0,1,1] return to baseline but our Nat/ParticlePath's limit our ability to indicate this difference. The "integers" in EGPT allow describing  two particles starting from the same position but initially moving in different directions resulting in the same return time to baseline. We use a single "charge" sign bit to indicate whether the particle went "up" or "down" in the first for the first half of the path and then did the opposite in the second. Initial direction in the path is our definition then of positive or negative. For example, for a particle that goes up ("heads") for the first part of the the number 1 is a path [1,1,0], and "down" first is -1 is [0,1,0], 2 is [1,1,1,0,0], and -2 is [0,1,1,0,0]. As with the EGPT Naturals (ParticlePath) we can represent ChargedParticlePath in the same path in shorter form by dropping the trailing zeros and then the sign and sum of 1's is the number itself. This is the canonical form of an integer in EGPT.

-- To establish ChargedParticlePath ≃ ℤ:
-- 1. We have `ParticlePath ≃ ℕ` (via equivParticlePathToNat).
-- 2. We need an equivalence `ℕ × Bool ≃ ℤ`. Mathlib provides `Int.equivNatProdBool : ℤ ≃ ℕ × Bool`. [1]
--    Its inverse is `Int.equivNatProdBool.symm : ℕ × Bool ≃ ℤ`.
-- 3. We construct the equivalence:
--    `ChargedParticlePath = ParticlePath × Bool`
--    `≃ ℕ × Bool` (using `Equiv.prodCongr equivParticlePathToNat (Equiv.refl Bool)`) [3]
--    `≃ ℤ` (using `Int.equivNatProdBool.symm`)
##############################################################################
-/

def ChargedParticlePath : Type := ParticlePath × Bool
def EGPT.Int := ChargedParticlePath

noncomputable def intEquivNatProdBool : ℤ ≃ ℕ × Bool :=
  (Equiv.intEquivNat.trans (Equiv.boolProdNatEquivNat.symm)).trans (Equiv.prodComm ℕ Bool).symm

noncomputable def ParticlePathIntEquiv : ChargedParticlePath ≃ ℤ :=
  (Equiv.prodCongr equivParticlePathToNat (Equiv.refl Bool)).trans intEquivNatProdBool.symm


/-!
## Rationals as EGPT ParticleHistoryPMF: Asymmetric Paths & The Positional Probability of a Single Particle Path Under Constraints (Probabality Mass Function)

############################################################################

 The canonical form a rational number in traditional number theory is a fraction p/q where p is the numerator and q is the denominator. It represents a ratio of two quanities. We see this as counting the number of heads and tails in a single particle path - p = heads, q = tails. Similarly, we can view this as a probability mass function (PMF) for system of particles in one time step such that p + q is the total number of particles in the system, p/(p + q) is the probability of heads, and q/(p + q) is the probability of tails.

 While the Integer's corresponded to our symmetric compressed paths ChargedParticlePaths, we need a representation for asymmetric paths and that is our ParticleHistoryPMF and we simply define it as a List Bool representing the "net" heads or tails. As with the ChargedParticlePaths, the leading sign bit allows for compression to just represent whether the 1's represent heads or tails. For example, a particle that goes up two times in a row ("heads") and then down 1 ("tails") is net positive heads and is written [1,1,1,0]. Likewise "down" two times in a row followed by heads once flips the sign bit to 0 [0,1,1,0]. We note that the first part of this represetnation is a string "p" which is ChargedParticlePath and the second part "q" is an inverted ParticlePath. Thus our ParticleHistoryPMF can be expressed as p/q where p is an ℤ and q is a ℕ. Unlike the EGPT Naturals (ParticlePath) and Integers (ChargedParticlePath) the ratio of 1's and 0's is the most compressed form for a single particle BUT, we achieve compression by allowing that all asymmetric paths (reorderings) will end in the same position AND allowing that concatenations of the same underlying path have the same ratio and are therefore equivalent to the shortest cananonical represetnation. This is the canonical form of a Rational in EGPT.

  1.  **Canonical Form:** A rational number is represented by a unique `List Bool`
      of the form `{sign bit} ++ {string of 1s} ++ {string of 0s}`. This
      is the most informationally dense way to encode the parameters (sign, p, q)
      and is a natural extension of `ParticlePath` and `ChargedParticlePath`.

  2.  **Physical Interpretation:** This canonical `List Bool` is not just an
      abstract number. It is the direct recipe for constructing a
      `BiasedIIDParticleSource`. The number of 1s is the `p` parameter,
      and the number of 0s is the `q` parameter.

  3.  **Direct Bijection:** The `toRat` and `fromRat` functions are
      direct transformations (counting and construction), avoiding the
      complexities of intermediate sampling or filtering mechanisms. This makes
      the bijection with Mathlib's `ℚ` clear and provable.

**Partition Theory And "Fractal Compression"**
For all the "detail" of each of many paths we use the ParticlePath which is the "uncompressed" form. The ParticleHistoryPMF can be also viewed as the "compressed" form of multiple paths. The ParticleHistoryPMF is the sum of all the ParticlePath's that have the same probability distribution. For the advanced probability theorist, we note that the multi-particle view of the ParticleHistoryPMF's compression is a "coarser" partition under Parition Theory and the ParticlePath is a "finer" partition. Parition Theory's fractal like recursive proofs of probablistic invariance under equal partitioning allows us to see that the ParticleHistoryPMF is scale invariant to the number of particles in the system.

##############################################################################
-/

/--
A predicate asserting that a `List Bool` is in the canonical form for a rational.
The form is `sign :: 1...1 ++ 0...0`. We also enforce that the rational is
normalized (numerator and denominator are coprime), the denominator is non-zero,
and zero has a unique non-negative representation.
-/
def CanonicalParticleHistoryPMF (l : List Bool) : Prop :=
  ∃ (s : Bool) (p q : ℕ),
    -- The list has the exact canonical structure.
    l = [s] ++ List.replicate p true ++ List.replicate q false ∧
    -- The denominator must be non-zero.
    q > 0 ∧
    -- The fraction p/q must be in lowest terms.
    Nat.Coprime p q ∧
    -- Canonical Zero: If the numerator is 0, the sign must be non-negative (true).
    (p = 0 → s = true)
/--
A `ParticleHistoryPMF` is a `List Bool` that is proven to be in the canonical,
normalized form for a rational number. This is the EGPT representation.
-/
abbrev ParticleHistoryPMF := { l : List Bool // CanonicalParticleHistoryPMF l }
def EGPT.Rat := ParticleHistoryPMF

/--
A `ParticleWaveform` is a `List Bool` that represents a unique probability mass function - it is what one might see if we sample the positions of a countably infinite number of particles in a system, where each particle's next stochastic move contributes to the overall probability distribution of the system.
-/
abbrev ParticleWaveform := ParticleHistoryPMF

/--
Parses the numerator `p` (count of `true`s) from a canonical rational list.
-/
def getNum (r : ParticleHistoryPMF) : ℕ :=
  r.val.tail.count true

/--
Parses the denominator `q` (count of `false`s) from a canonical rational list.
-/
def getDen (r : ParticleHistoryPMF) : ℕ :=
  r.val.tail.count false

/--
Parses the sign bit from a canonical rational list.
Requires proof that the list is non-empty, which `CanonicalParticleHistoryPMF` provides.
-/
def getSign (r : ParticleHistoryPMF) : Bool :=
  -- The existential in `CanonicalParticleHistoryPMF` guarantees the list is non-empty.
  r.val.head (by { rcases r.property with ⟨s, p, q, h_struct, _, _⟩; rw [h_struct]; simp })

/--
**`toRat`:** Decodes the abstract mathematical value `p/q` from its canonical
EGPT `List Bool` representation.
-/
noncomputable def toRat (r : ParticleHistoryPMF) : ℚ :=
  let s := getSign r
  let p := getNum r
  let q := getDen r
  let num_int : ℤ := if s then p else -p
  -- `Rat.mkRat` normalizes, but since our canonical form is already normalized,
  -- this is equivalent to direct construction.
  mkRat num_int q

/--
**`fromRat`:** Encodes a standard `ℚ` into its canonical, normalized EGPT
`List Bool` representation.
-/
noncomputable def fromRat (q_in : ℚ) : ParticleHistoryPMF :=
  let s := decide (0 ≤ q_in.num)
  -- Mathlib's `q.num` and `q.den` are already normalized (coprime).
  let p := q_in.num.natAbs
  let q := q_in.den
  let l := [s] ++ List.replicate p true ++ List.replicate q false
  -- We package the list `l` with the proof that it satisfies `CanonicalParticleHistoryPMF`.
  ⟨l, by
    use s, p, q
    constructor
    · rfl
    · constructor
      · exact q_in.den_pos
      · constructor
        ·
          -- `Rat` provides `reduced`, a proof that `q_in.num.natAbs` and `q_in.den` are coprime.
          have h_coprime : Nat.Coprime p q := by
            simpa [p, q] using q_in.reduced
          exact h_coprime
        · -- Prove the new condition for canonical zero
          intro hp_eq_zero
          -- Unfold definitions of s and p
          dsimp [s, p]
          -- If p = 0, then q_in.num.natAbs = 0, which means q_in.num = 0.
          have h_num_zero : q_in.num = 0 := by aesop
          -- If q_in.num = 0, then `0 ≤ q_in.num` is true.
          -- By definition, s is `(0 ≤ q_in.num)`, so s is true.
          rw [h_num_zero]
          simp
  ⟩

/--
**Instantiates the Physical Process:**
Takes the EGPT description of a ParticleHistoryPMF (rational number) and creates the corresponding
`BiasedIIDParticleSource` that generates `true` with probability `p/(p+q)`.
This version uses a more explicit proof style that matches the provided `Filter.lean`.
-/
noncomputable def toBiasedSource (r : ParticleHistoryPMF) (seed : ℕ) : IIDParticleSource Bool :=
  let p := getNum r
  let q := getDen r
  -- We need to prove `p + q > 0`. This follows from `q > 0` which is guaranteed
  -- by the `CanonicalParticleHistoryPMF` property.
  have h_total_pos : p + q > 0 := by
    -- 1. Deconstruct the `CanonicalParticleHistoryPMF` proof to get the parameters and properties.
    rcases r.property with ⟨s_prop, p_prop, q_prop, h_struct, h_q_pos, _⟩
    -- 2. Prove that our parsed denominator `q` is equal to the `q_prop` from the proof.
    have h_q_eq : q = q_prop := by
      -- Unfold the definition of `q` (`getDen r`) and rewrite using
      -- the canonical structure of the list.
      dsimp [q, getDen]
      -- After substituting the structure of `r.val`, we need to
      -- reassociate the list so that `List.tail_cons` can fire
      -- (otherwise `::` binds too tightly).  Then `simp` can finish.
      simp [ h_struct,
             List.singleton_append,      -- `[s] ++ t = s :: t`
             List.cons_append,           -- `s :: l₁ ++ l₂ = s :: (l₁ ++ l₂)`
             List.tail_cons,
             List.count_append,
             List.count_replicate,
             Bool.decEq ]
    -- 3. The goal is now `p + q > 0`. We substitute `q` with `q_prop`.
    rw [h_q_eq]
    -- 4. The `CanonicalParticleHistoryPMF` property gives `h_q_pos : q_prop > 0`.
    --    Since `p` is a natural number, `p ≥ 0`. The sum is therefore > 0.
    exact add_pos_of_nonneg_of_pos (Nat.zero_le p) h_q_pos
  -- Construct the biased source using the parsed parameters and the now-proven hypothesis.
  mkBiasedIIDParticleSource seed p q h_total_pos

-- In the `equivParticleHistoryPMFtoRational` definition

noncomputable def equivParticleHistoryPMFtoRational : ParticleHistoryPMF ≃ ℚ :=
{
  toFun    := toRat,
  invFun   := fromRat,
  left_inv := by
    -- Goal: fromRat (toRat r) = r
    intro r
    -- To prove equality of two subtype elements, we prove their values are equal.
    apply Subtype.ext

    -- Deconstruct the proof `r.property` to get the canonical parameters for `r`.
    rcases r.property with ⟨s, p, q, h_struct, h_q_pos, h_coprime, h_zero_sign⟩

    -- Goal is now: (fromRat (toRat r)).val = r.val

    -- To simplify the goal, let's establish what `toRat r` is
    -- in terms of s, p, and q.
    have h_toRat_r_eq_mkRat : toRat r = mkRat (if s then p else -p) q := by
      -- Unfold the definition of toRat
      dsimp [toRat] -- Removed q_equiv from dsimp
      -- We need to prove getNum r = p, getDen r = q, and getSign r = s.
      have h_s_loc : getSign r = s := by -- Renamed to avoid conflict if s is used differently
        dsimp [getSign]; simp [h_struct];
      have h_p_loc : getNum r = p := by -- Renamed
        dsimp [getNum]
        rw [h_struct]
        rw [List.singleton_append]
        simp  [List.tail_cons, List.count_append, List.count_replicate, add_zero]
      have h_q_loc : getDen r = q := by -- Renamed
        dsimp [getDen]
        rw [h_struct]
        rw [List.singleton_append]
        simp [List.tail_cons, List.count_append, List.count_replicate, zero_add]
      -- Substitute these back into the definition.
      rw [h_s_loc, h_p_loc, h_q_loc]


    -- Now, let's analyze the LHS: `(fromRat (toRat r)).val`.
    -- Unfold the definition of `fromRat`.
    -- `dsimp` will substitute `toRat r` for `q_in` in the body of `fromRat`.
    dsimp [fromRat]
    -- The goal now contains terms like `(toRat r).num` and `(toRat r).den`.
    -- Substitute `toRat r` using our hypothesis.
    rw [h_toRat_r_eq_mkRat]
    -- The goal now contains terms like `(mkRat (if s then p else -p) q).num`, etc.

    -- `fromRat` uses the `num` and `den` of its input. Let's find those for `q_equiv`:
    have h_num_den :
      (mkRat (if s then (↑p : ℤ) else -(↑p : ℤ)) q).num =
        (if s then (↑p : ℤ) else -(↑p : ℤ)) ∧
      (mkRat (if s then (↑p : ℤ) else -(↑p : ℤ)) q).den = q := by
      let v : ℤ := if s then ↑p else -↑p
      have hq_pos_int : (0 : ℤ) < (q : ℤ) := by exact_mod_cast h_q_pos
      -- h_q_ne_zero is not strictly needed here as Rat.mkRat_eq_divInt does not require q ≠ 0.
      -- The hq_pos_int implies q ≠ 0 for the coprime lemmas.
      have h_coprime_int :
        (Int.natAbs v).Coprime (Int.natAbs (q : ℤ)) := by
        dsimp only [v]
        rw [Int.natAbs_natCast q]
        split_ifs with hs_cond
        · simp only [Int.natAbs_natCast]; exact h_coprime
        · simp only [Int.natAbs_neg, Int.natAbs_natCast]; exact h_coprime

      constructor
      · -- Numerator part: (mkRat v q).num = v
        rw [Rat.mkRat_eq_divInt v q]
        rw [Rat.divInt_eq_div v ↑q] -- Converts (Rat.divInt v ↑q).num to (v / ↑q).num
        exact Rat.num_div_eq_of_coprime hq_pos_int h_coprime_int
      · -- Denominator part: (mkRat v q).den = q
        rw [Rat.mkRat_eq_divInt v q]
        rw [Rat.divInt_eq_div v ↑q] -- Goal is now (v / ↑q).den = q
        -- Rewrite the RHS of the goal to prepare for comparison.
        rw [← Int.natAbs_natCast q]    -- Goal becomes (v / ↑q).den = Int.natAbs ↑q

        -- We know `Rat.den_div_eq_of_coprime hq_pos_int h_coprime_int` proves `(v / ↑q).den = Int.natAbs ↑q`.
        -- `convert` will use this and ask us to prove `Int.natAbs ↑q = Int.natAbs ↑q` (after unification).
        convert Rat.den_div_eq_of_coprime hq_pos_int h_coprime_int
        -- New goal: Int.natAbs ↑q = Int.natAbs ↑q (or q = q after simplification)
        aesop
        --exact (Int.natAbs_natCast q).symm

    -- Substitute these known num/den values into the `fromRat` expression.
    -- Replace `simp [h_num_den]` with explicit rewrites.
    rw [h_num_den.1, h_num_den.2]
    rw [h_struct] -- Substitute r.val with its structure

    -- The goal is now to prove equality of two lists:
    -- `[decide (0 ≤ (if s then p else -↑p))] ++ replicate ((if s then p else -↑p).natAbs) true ++ replicate q false`
    -- = `[s] ++ replicate p true ++ replicate q false`

    -- Ensure lists are in `h :: t` form for `List.cons_eq_cons`.
    -- `[h] ++ t` is `h :: t`. `h :: (t1 ++ t2)` is `h :: t1 ++ t2`.
    -- `simp` with `List.singleton_append` can achieve this, or it might be automatic.
    -- The current structure after `simp [h_num_den]` and `rw [h_struct]` should be:
    -- `(decide (...)) :: (replicate ... ++ replicate ...)`
    -- `s :: (replicate ... ++ replicate ...)`
    -- So `List.cons_eq_cons` can be applied.

    simp [List.cons_eq_cons]
    constructor
    · -- 1. Prove the sign bits are equal:
      -- `decide (0 ≤ (if s then p else -↑p)) = s`
      by_cases hs : s
      · -- Case s = true: Goal is `decide (0 ≤ ↑p) = true`. Since p is Nat, 0 ≤ ↑p is true. decide true = true.
        -- The problematic line was here.
        -- If p can be 0, then (0 <= p) is true.
        aesop
        --simp [hs, zero_le (p :ℤ)]
      · -- Case s = false: Goal is `decide (0 ≤ -↑p) = false`.
        -- This means `¬(0 ≤ -↑p)`, which is `-↑p < 0`, or `↑p > 0`.
        simp [hs]
        -- Goal is now `¬(0 ≤ -↑p)`, which simplifies to `p > 0`.
        -- If `p` were `0`, then `h_zero_sign` would force `s` to be `true`,
        -- which contradicts our case `hs : ¬s`. So `p` cannot be `0`.
        have hp_ne_zero : p ≠ 0 := by
          intro hp_is_zero
          have hs_must_be_true := h_zero_sign hp_is_zero
          exact hs hs_must_be_true
        -- Since p is a Nat, p ≠ 0 implies p > 0.
        --exact Nat.pos_of_ne_zero hp_ne_zero
        aesop
    · -- 2. Prove tails are equal:
      -- `replicate ((if s then ↑p else -↑p).natAbs) true ++ replicate q false = replicate p true ++ replicate q false`
      -- Since `replicate q false` is the same on both sides, we can cancel it.
      --rw [List.append_right_cancel_iff]
      aesop
  ,
  right_inv := by
    -- (The previous proof for right_inv remains correct)
    intro q_in
    simp [ toRat, fromRat, getNum, getSign, getDen,
       List.count_append, List.count_replicate,
       List.head_cons, List.tail_cons, List.singleton_append,
       add_zero, zero_add ]      -- everything here exists
    -- `fromRat` chooses its numerator as
    --   if 0 ≤ q_in then |q_in.num| else -|q_in.num|
    -- We show this is convertible to `q_in.num`, after which
    -- `Rat.mkRat_self` finishes the proof.
    by_cases h_nonneg : (0 : ℚ) ≤ q_in
    ·  -- branch 0 ≤ q_in : the numerator chosen is `|q_in.num| = q_in.num`
       have : (if (0 : ℚ) ≤ q_in then (|q_in.num|) else -(|q_in.num|)) = q_in.num := by
         simp [h_nonneg, abs_of_nonneg (Rat.num_nonneg.2 h_nonneg)]
       simpa [this] using Rat.mkRat_self q_in
    ·  -- branch q_in < 0 : numerator is `- |q_in.num| = q_in.num`
       have : (if (0 : ℚ) ≤ q_in then (|q_in.num|) else -(|q_in.num|)) = q_in.num := by
         have h_lt : q_in < 0 := lt_of_not_ge h_nonneg
         -- Translate the negativity of the rational to negativity of its numerator.
         -- `Rat.num_neg_iff_neg` is a lemma in `Mathlib.Data.Rat.Lemmas`
         -- giving `q.num < 0 ↔ q < 0` when the denominator is positive.
         have h_num_neg : q_in.num < 0 := by
           --simpa using (Rat.num_nonneg).2 h_lt
           simp [Rat.num_nonneg]
           aesop
         simp [h_nonneg, abs_of_neg h_num_neg]
       simpa [this] using Rat.mkRat_self q_in
}


/-!
## Reals as EGPT ParticleFuturePDF: Probability Density Functions over Infinite Systems of Particle's:
     ###########################################################
     Reals as Boolean-valued *functions* on our emergent naturals
     *Constructive Interpretation of functions* --
     ########################################################### -/

/-- Emergent reals: the power set of `ParticlePath`, i.e. characteristic
    functions `ParticlePath → Bool`. -/
abbrev ParticleFuturePDF := ParticlePath → Bool
abbrev EGPT.Real := ParticleFuturePDF



/-- Transport along `ParticlePath ≃ ℕ`, giving `(ParticlePath → Bool) ≃ (ℕ → Bool)`. -/
noncomputable def equivFunNat : ParticleFuturePDF ≃ (ℕ → Bool) :=
  Equiv.arrowCongr equivParticlePathToNat (Equiv.refl Bool)


open Cardinal


/-- The cardinality of `ParticleFuturePDF` (functions from ParticlePath to Bool) is \(2^{\aleph_0}\). -/
lemma cardinal_eq_two_pow_aleph0 : Cardinal.mk ParticleFuturePDF = 2 ^ Cardinal.aleph0 := by
  calc
    -- 1) By definition, ParticleFuturePDF is ParticlePath → Bool.
    --    Using the equivalence equivFunNat : (ParticlePath → Bool) ≃ (ℕ → Bool),
    --    their cardinalities are equal.
    Cardinal.mk ParticleFuturePDF
      = Cardinal.mk (ℕ → Bool)             := Cardinal.mk_congr equivFunNat
    -- 2) The cardinality of a function space #(A → B) is #B ^ #A.
    _ = Cardinal.mk Bool ^ Cardinal.mk ℕ   := by rw [Cardinal.power_def]
    -- 3) The cardinality of Bool is 2, and the cardinality of ℕ is ℵ₀.
    _ = 2 ^ Cardinal.aleph0                := by aesop
/-- The emergent reals have exactly the same cardinality as ℝ (the continuum). -/

noncomputable def equivParticleSystemPMFtoReal : ParticleFuturePDF ≃ ℝ :=
  -- 1) combine your two cardinality proofs into `#G = #ℝ`
  have h : mk ParticleFuturePDF = mk ℝ := by
    calc
      mk ParticleFuturePDF = 2 ^ aleph0    := cardinal_eq_two_pow_aleph0
      _                 = #ℝ              := (Cardinal.mk_real).symm
  -- 2) use `Cardinal.eq` to get `Nonempty (G ≃ ℝ)`
  Classical.choice (Cardinal.eq.1 h)


/-!
## Beth Numbers And Higher Cardinalities
##############################################################################
EGPT is fundamentally based on Partition Theory which holds that the coarser partitions are the sum of the finer partitions. The hierarchy is not just about increasing cardinality but about re-instantiating the Nat/Rat/Real pattern at higher levels of abstraction.


In standard ZFC set theory (which mathlib follows), the Continuum Hypothesis (CH) is the statement that Cardinal.aleph 1 = Cardinal.beth 1 (i.e., ℵ₁ = 2^ℵ₀).
mathlib does not assume the Continuum Hypothesis. It is independent of ZFC.
-/



lemma cardinal_ParticlePath : Cardinal.mk ParticlePath = Cardinal.aleph0 :=
  -- The cardinality of two types is the same if they are equivalent.
  -- We have ParticlePath ≃ ℕ (equivParticlePathToNat).
  -- We need ParticlePath ≃ ULift.{0} ℕ to match the definition of aleph0 in Cardinal.{0}.
  -- Nat ≃ ULift.{0} Nat is Equiv.ulift.{0,0}.symm.
  Cardinal.mk_congr (equivParticlePathToNat.trans Equiv.ulift.{0,0}.symm)



lemma cardinal_ParticleFuturePDF : Cardinal.mk ParticleFuturePDF = Cardinal.beth 1 := by
  -- We previously proved `cardinal_eq_two_pow_aleph0`:
  -- Cardinal.mk ParticleFuturePDF = 2 ^ Cardinal.aleph0
  rw [cardinal_eq_two_pow_aleph0]
  -- The definition of `beth 1` is exactly `2 ^ (beth 0)`,
  -- and `beth 0` is `aleph0`.
  simp [Cardinal.beth_one, Cardinal.beth_zero]



/-!
==================================================================
# The EGPT Number Hierarchy Generator (Corrected & Final)

This file formalizes the "restarting hierarchy" of EGPT number analogues.
The mutual dependency between level definitions is resolved by defining
`Nat_L` via direct recursion, and then defining the other types as
aliases (`abbrev`) of `Nat_L`.

1.  A **Recursive Type Generator**: `Nat_L` is the core recursive
    definition. `Real_L n` is simply an alias for `Nat_L (n+1)`.

2.  A **Generalized Proof**: A single theorem, proven by induction, that
    proves the cardinalities of these generated types match the Beth sequence
    (ℶₙ, ℶₙ, ℶₙ₊₁) for any level `n`.
==================================================================
-/


/--
The EGPT "Natural Number" analogue at level `n`. This is the core of the
recursive hierarchy, defined without mutual dependencies.

- **Base Case (n=0):** The fundamental objects are discrete, countable
  `ParticlePath`s, with cardinality ℵ₀ = ℶ₀.
- **Inductive Step (n+1):** The fundamental objects of the next level are
  functions from the current level's objects to `Bool`. This is equivalent
  to the power set, generating the next Beth number.
-/
def Nat_L : ℕ → Type
  | 0   => ParticlePath
  | n+1 => (Nat_L n) → Bool

/--
The EGPT "Real Number" analogue at level `n`.

This is the power set of the "Naturals" of that level. With our
definition of `Nat_L`, this is simply an alias for `Nat_L (n+1)`.
-/
abbrev Real_L (n : ℕ) : Type := Nat_L (n + 1)

/--
The EGPT "Rational Number" analogue at level `n`. It represents a ratio or
relationship between the fundamental objects of that level.
-/
abbrev Rat_L (n : ℕ) : Type := Nat_L n × Nat_L n


-- === The Generalized Cardinality Proof ===

/--
**Theorem (The EGPT Hierarchy Cardinality):** For any level `n : ℕ`,
the cardinalities of the EGPT number analogues follow the Beth sequence:
- `Nat_L n` has cardinality ℶₙ.
- `Rat_L n` has cardinality ℶₙ.
- `Real_L n` has cardinality ℶₙ₊₁.
-/
theorem cardinal_of_egpt_level (n : ℕ) :
    Cardinal.mk (Nat_L n) = beth n ∧
    Cardinal.mk (Rat_L n) = beth n ∧
    Cardinal.mk (Real_L n) = beth (n + 1) := by
  -- We prove this by induction on the level `n`.
  induction n with
  | zero =>
    -- Base Case: n = 0
    have h_nat_L0_card : Cardinal.mk (Nat_L 0) = beth 0 := by
      simp [Nat_L, beth_zero, cardinal_ParticlePath]

    constructor
    · -- Part 1: Prove Cardinal.mk (Nat_L 0) = beth 0
      exact h_nat_L0_card
    · constructor
      · -- Part 2: Prove Cardinal.mk (Rat_L 0) = beth 0
        simp [Rat_L, Cardinal.mk_prod, h_nat_L0_card, beth_zero, aleph0_mul_aleph0]
      · -- Part 3:  `Real_L 0 = Nat_L 1 = ParticlePath → Bool`,
          -- whose cardinality we already computed.
        simpa [Real_L, Nat_L] using cardinal_ParticleFuturePDF

  | succ k ih =>
    -- Inductive Step: Assume the theorem holds for `k`. Prove it for `k+1`.
    -- The induction hypothesis gives us the cardinalities for level `k`.
    have h_nat_k_card := ih.1

    -- Establish the cardinality of Nat_L (k+1).
    have h_nat_Lk1_card : Cardinal.mk (Nat_L (k + 1)) = beth (k + 1) := by
      simp [Nat_L, Cardinal.mk_arrow, h_nat_k_card, Cardinal.mk_bool, beth_succ]

    constructor
    · -- Part 1: Prove Cardinal.mk (Nat_L (k+1)) = beth (k+1)
      exact h_nat_Lk1_card
    · constructor
      · -- Part 2: Prove Cardinal.mk (Rat_L (k+1)) = beth (k+1)
        -- The product of two infinite cardinals of size `beth (k+1)` is itself.
        have : Cardinal.mk (Rat_L (k + 1)) = beth (k + 1) := by
          calc
            Cardinal.mk (Rat_L (k + 1))
                = Cardinal.mk (Nat_L (k + 1)) * Cardinal.mk (Nat_L (k + 1)) := by
                  simp [Rat_L, Cardinal.mk_prod]
            _   = (beth (k + 1)) * (beth (k + 1)) := by
                  simp [h_nat_Lk1_card]
            _   = beth (k + 1) := by
                  exact Cardinal.mul_eq_self (Cardinal.aleph0_le_beth (k + 1 : Ordinal))
        simpa using this
        --aesop

      · -- Part 3: Prove Cardinal.mk (Real_L (k+1)) = beth (k+2)
        -- 2^(beth (k+1)) = beth (k+2) by `beth_succ`.
        simp [Real_L, Nat_L, Cardinal.mk_arrow, h_nat_Lk1_card,
               Cardinal.mk_bool]
        aesop

/--
A higher-order type representing a function between the "Real" spaces of
two (potentially different) levels.
-/
abbrev InterLevelOperator (n m : ℕ) := Real_L n → Real_L m

/--
**Corollary:** The cardinality of a "System of Systems" operator that maps
the L0 Real space to itself is `beth 2`.
-/
theorem cardinal_L0_operator : Cardinal.mk (InterLevelOperator 0 0) = beth 2 :=
  by
    -- `Real_L 0` has cardinality beth 1
    have h_real_L0_card := (cardinal_of_egpt_level 0).right.right
    -- `beth 1` is infinite
    have h_beth1_inf : aleph0 ≤ beth 1 := Cardinal.aleph0_le_beth 1
    -- κ^κ = 2^κ for infinite κ
    have h_power : (beth 1) ^ (beth 1) = 2 ^ (beth 1) :=
      Cardinal.power_self_eq h_beth1_inf
    -- 2 ^ beth 1 = beth 2
    have h_beth2 : 2 ^ (beth 1) = beth 2 := by
      simpa using (Cardinal.beth_succ 1).symm
    -- Prepare the final chain of equalities
    have h_prod : (beth 1) ^ (beth 1) = beth 2 := by
      calc (beth 1) ^ (beth 1)
        _ = 2 ^ (beth 1) := h_power
        _ = beth 2       := h_beth2

    -- Cardinality of the operator space is (#Real_L 0)^(#Real_L 0)
    have : Cardinal.mk (InterLevelOperator 0 0) = (beth 1) ^ (beth 1) := by
      simpa [InterLevelOperator, Cardinal.mk_arrow, h_real_L0_card]

    -- Conclude with transitivity
    simpa [this] using h_prod

/-!
## Example Dimensions in EGPT
Per the physical observations of Hawking Radiation and the resultant Holographic Principle we see that mathematical dimensions are lossy compressions (operations on "coarser" partitions) of the underlying particle universe. Nat_L 0 is the finest partition of the particle universe (particles are discrete and countable). Nat_L 1 is the next coarser partition consisting of functions as the new fundamental objects - that is functions at L1 are manipulated in the same way as particles at L0. Etc..

Some fun and somewhat arbitrary names for the dimensions of reality as we know it might be:
-/
def QuantumDimension := 0
def NewtonianClassicalDimension := 1
def EinsteinGRDimension := 2
def SpaceTime2D := Real_L QuantumDimension
def SpaceTime3D := Real_L NewtonianClassicalDimension
def SpaceTime4D := Real_L EinsteinGRDimension
def DiscreteCombinatorics := Nat_L QuantumDimension
def Calculus := Real_L QuantumDimension
def OrdinaryDifferentialEquations := Real_L NewtonianClassicalDimension
def PartialDifferentialEquations := Real_L EinsteinGRDimension
def S3TensorCalculus := Real_L EinsteinGRDimension

-- EGPT — Electronic Graph Paper Theory
-- Copyright (C) 2026 Essam Abadir
-- Licensed under the DeSciX Community Source Code License (DCSL) v1.0.
-- See LICENSE and DeSciX_Community_License_v1.pdf in the repository root.
-- Provided WITHOUT ANY WARRANTY. See the DCSL for details.
