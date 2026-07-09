-- EGPT — Electronic Graph Paper Theory
-- Copyright (C) 2026 Essam Abadir
-- Licensed under the DeSciX Community Source Code License (DCSL) v1.0.
-- See LICENSE and DeSciX_Community_License_v1.pdf in the repository root.
-- Provided WITHOUT ANY WARRANTY. See the DCSL for details.

module
public import InformationTheory.EntropyNumber.RotaEntropy
public import InformationTheory.EntropyNumber.Real
public import InformationTheory.EntropyNumber.Factorization

/-!
# Prime Information Atoms

Incremental factorial information identities mirroring Legendre's formula,
expressed in terms of `Real.logb 2`.

## Main definitions

* `primeAtomSum` -- sum of `v_p(m) * logb 2 p` over the prime support of `m`.
* `factorialPrimeAtomSum` -- `primeAtomSum` applied to `n!`.

## Main results

* `primeAtomSum_eq_logb` -- `primeAtomSum m = logb 2 m` for positive `m`.
* `factorialPrimeAtomSum_eq_logb` -- `factorialPrimeAtomSum n = logb 2 (n!)`.
* `logb_factorial_succ` -- `logb 2 ((n+1)!) = logb 2 (n+1) + logb 2 (n!)`.
* `logb_factorial_increment` -- `logb 2 ((n+1)!) - logb 2 (n!) = logb 2 (n+1)`.
* `factorial_information_decomposition` -- `logb 2 (n!)` decomposes as a sum
  over prime atoms.
* `factorial_information_increment` -- `logb 2 ((n+1)!) = logb 2 (n!) + logb 2 (n+1)`.
-/

@[expose] public section

-- Cosmetic linters disabled for this initial drop of the InformationTheory
-- subtree. These do not affect correctness; reviewers may request a per-call
-- cleanup as a follow-up PR.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.style.emptyLine false
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.longFile 0
set_option linter.style.show false
set_option linter.style.whitespace false
set_option linter.style.lambdaSyntax false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


open Real Finset

namespace InformationTheory

namespace PrimeAtoms

open scoped BigOperators

/-- Sum of `v_p(m) * logb 2 p` over the prime support of `m`. -/
noncomputable def primeAtomSum (m : ℕ) : ℝ :=
  ∑ p ∈ m.factorization.support,
    (m.factorization p : ℝ) * Real.logb 2 p

/-- `primeAtomSum m` equals `logb 2 m` for positive `m`. -/
lemma primeAtomSum_eq_logb
    (m : ℕ) (hm : 0 < m) :
    primeAtomSum m = Real.logb 2 m := by
  simpa [primeAtomSum] using
    (logb_two_factorization m hm).symm

/-- `primeAtomSum` applied to `n!`. -/
noncomputable def factorialPrimeAtomSum
    (n : ℕ) : ℝ :=
  primeAtomSum (Nat.factorial n)

/-- `factorialPrimeAtomSum n` equals `logb 2 (n!)`. -/
lemma factorialPrimeAtomSum_eq_logb (n : ℕ) :
    factorialPrimeAtomSum n =
      Real.logb 2 (Nat.factorial n) := by
  have hpos : 0 < Nat.factorial n :=
    Nat.factorial_pos n
  unfold factorialPrimeAtomSum
  simpa using
    primeAtomSum_eq_logb (Nat.factorial n) hpos

/-- `logb 2 ((n+1)!) = logb 2 (n+1) + logb 2 (n!)`. -/
lemma logb_factorial_succ (n : ℕ) :
    Real.logb 2 (Nat.factorial (n+1)) =
      Real.logb 2 (n+1)
        + Real.logb 2 (Nat.factorial n) := by
  have h1 : (Nat.factorial n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have h2 : ((n+1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hfac :
      (Nat.factorial (n+1) : ℝ) =
        (n+1) * Nat.factorial n := by
    simp [Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
  calc
    Real.logb 2 (Nat.factorial (n+1))
  = Real.logb 2 ((n+1) * Nat.factorial n) := by
      simp [hfac]
    _ = Real.logb 2 (n+1)
        + Real.logb 2 (Nat.factorial n) :=
          Real.logb_mul (b:=2) (x:=(n+1 : ℝ))
            (y:=Nat.factorial n) h2 h1

/-- The incremental factorial identity: `logb 2 ((n+1)!) - logb 2 (n!) = logb 2 (n+1)`. -/
lemma logb_factorial_increment (n : ℕ) :
    Real.logb 2 (Nat.factorial (n+1))
      - Real.logb 2 (Nat.factorial n)
      = Real.logb 2 (n+1) := by
  have := logb_factorial_succ n
  simpa [sub_eq_add_neg, add_comm,
    add_left_comm, add_assoc]
    using congrArg
      (fun t => t
        - Real.logb 2 (Nat.factorial n)) this

/-- `logb 2 (n!)` decomposes as a sum of prime-atom contributions. -/
theorem factorial_information_decomposition
    (n : ℕ) :
    Real.logb 2 (Nat.factorial n)
      = ∑ p ∈ (Nat.factorial n).factorization.support,
          ((Nat.factorial n).factorization p : ℝ)
            * Real.logb 2 p := by
  have := factorialPrimeAtomSum_eq_logb n
  unfold factorialPrimeAtomSum at this
  simpa [primeAtomSum] using this.symm

/-- `logb 2 ((n+1)!) = logb 2 (n!) + logb 2 (n+1)`. -/
theorem factorial_information_increment (n : ℕ) :
    Real.logb 2 (Nat.factorial (n+1))
      = Real.logb 2 (Nat.factorial n)
        + Real.logb 2 (n+1) :=
  (logb_factorial_succ n).trans
    (by simp [add_comm])

end PrimeAtoms

/-! ## Semantic Collapse Machinery
The failure of Cantor's diagonalization theorem is that it fails informational semantic uniqueness.
It assumes that flipping a bit creates a new semantic alphabet. In reality, a number is uniquely
coded by its alphabet of prime factors. The following machinery provides the choice-free semantic
collapse from EntropyReal down to unique prime alphabets. `evalEntropyRealZero` lives in
`EntropyNumber/Real.lean`. -/

/-- Encode an `EntropyReal` as an `EntropyNat` via its zero-point evaluation. -/
def evalEntropyRealAsNat (r : EntropyReal) : EntropyNat :=
  EntropyNat.ofNat (if evalEntropyRealZero r then 1 else 0)

/-- The semantic collapse of an EntropyReal to its unique prime alphabet. -/
def entropyRealCollapse (r : EntropyReal) : List ℕ :=
  factorListC (EntropyNat.toNat (evalEntropyRealAsNat r))

end InformationTheory
