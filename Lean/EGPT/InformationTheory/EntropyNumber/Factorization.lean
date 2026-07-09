-- EGPT — Electronic Graph Paper Theory
-- Copyright (C) 2026 Essam Abadir
-- Licensed under the DeSciX Community Source Code License (DCSL) v1.0.
-- See LICENSE and DeSciX_Community_License_v1.pdf in the repository root.
-- Provided WITHOUT ANY WARRANTY. See the DCSL for details.

module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Prime.Basic

/-!
# Choice-free Nat factoriser

A fuel-bounded structural-recursion prime factoriser. Unlike Mathlib's
`Nat.factorization` / `Nat.primeFactorsList` (which both pull
`Classical.choice` through `Nat.minFac`), this implementation uses
only trial division with explicit fuel, mirroring `isPrimeBool`
and `findPrimeFromC`.

Output convention: returns a `List ℕ` of prime factors **with
multiplicity**, in non-decreasing order. For `n ≤ 1` the output is
the empty list (vacuously: `1` has no prime factors; `0` is
non-positive and gets the trivial empty result for total
constructive coverage).
-/

@[expose] public section

namespace InformationTheory

/-- Inner trial-division loop. `n` is the current quotient being
factored; `d` is the trial divisor; `fuelN` bounds the outer "extract
a factor" loop and `fuelD` bounds the inner divisor scan. -/
def factorListAux : ℕ → ℕ → ℕ → ℕ → List ℕ
  | 0, _,        _,     _     => []
  | _, 0,        _,     _     => []
  | _, 1,        _,     _     => []
  | fuelN + 1, n + 2, d, fuelD =>
    match fuelD with
    | 0 => [n + 2]
    | fuelD + 1 =>
      if d < 2 then
        factorListAux (fuelN + 1) (n + 2) 2 fuelD
      else if d * d > n + 2 then
        [n + 2]
      else if (n + 2) % d = 0 then
        d :: factorListAux fuelN ((n + 2) / d) d fuelD
      else
        factorListAux (fuelN + 1) (n + 2) (d + 1) fuelD

/-- Prime factor list of `n` (with multiplicity, non-decreasing).
Returns `[]` for `n ≤ 1`. Choice-free: the recursion is structural in
explicit fuel. -/
def factorListC (n : ℕ) : List ℕ :=
  factorListAux n n 2 n

end InformationTheory
