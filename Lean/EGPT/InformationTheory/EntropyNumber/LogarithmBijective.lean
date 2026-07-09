-- EGPT — Electronic Graph Paper Theory
-- Copyright (C) 2026 Essam Abadir
-- Licensed under the DeSciX Community Source Code License (DCSL) v1.0.
-- See LICENSE and DeSciX_Community_License_v1.pdf in the repository root.
-- Provided WITHOUT ANY WARRANTY. See the DCSL for details.

module

public import InformationTheory.EntropyNumber.Real
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.PNat.Basic

/-!
# Constructive Logarithms in Information Space

This file defines a choice-free, constructive extraction of the base-2 logarithm
of a natural number as a bit-stream (`EntropyReal`). This serves as Step 1 of the 
"Bijective Chain" approach to remove `Classical.choice` from the Fundamental Theorem 
of Arithmetic (FTA) and the Rota/Shannon entropy cluster.

The core insight is that `logb_C n` can be built entirely using integer arithmetic 
and `Nat.log2`, producing the exact `EntropyReal` bit-stream that `evaluate_binary_sequence` 
will project onto Lean's `ℝ`.

## Main definitions
* `logb_frac_bit` — extracts the `i`-th fractional bit of `log_2 n` via `Nat.log2 (n^(2^(i+1)))`.
* `logb_int_bit` — extracts the `j`-th bit of the integer part `Nat.log2 n`.
* `logb_C_seq` — interleaves the integer and fractional bits into a sequence `ℕ → Bool`.
* `logb_C` — bundles the sequence into an `EntropyReal`.
-/

@[expose] public section

namespace InformationTheory

/-- Extracts the `i`-th bit of the fractional part of `log_2 n`. 
    Since `log_2 n = Nat.log2 n + x` with `x ∈ [0, 1)`,
    `2^(i+1) x = log_2 (n^(2^(i+1))) - 2^(i+1) * Nat.log2 n`.
    The integer part of this is precisely `Nat.log2 (n^(2^(i+1))) - 2^(i+1) * Nat.log2 n`,
    and its parity gives the `i`-th bit of the fractional expansion. -/
def logb_frac_bit (n i : ℕ) : Bool :=
  let V_i := Nat.log2 (n ^ (2 ^ (i + 1))) - (2 ^ (i + 1)) * Nat.log2 n
  V_i % 2 == 1

/-- Extracts the `j`-th bit of the integer part of `log_2 n`.
    For `evaluate_binary_sequence`, `j = 0` encodes the sign (true for positive),
    and `j > 0` encodes the `(j-1)`-th bit of `Nat.log2 n`. -/
def logb_int_bit (n j : ℕ) : Bool :=
  if j = 0 then true
  else ((Nat.log2 n) / (2 ^ (j - 1))) % 2 == 1

/-- Interleaves the integer and fractional bits into a single `ℕ → Bool` sequence,
    matching the layout expected by `evaluate_binary_sequence`. -/
def logb_C_seq (n : ℕ) (i : ℕ) : Bool :=
  if i % 2 == 0 then
    logb_int_bit n (i / 2)
  else
    logb_frac_bit n (i / 2)

/-- The choice-free, computable logarithm of a natural number,
    represented as a bit-stream in information space (`EntropyReal`). -/
def logb_C (n : ℕ) : EntropyReal :=
  fun e => logb_C_seq n (EntropyNat.toNat e)

/-- The choice-free countable subspace of `EntropyReal` that corresponds to logarithms of positive integers.
    By bundling the source positive integer `src`, we avoid `Classical.choice` when inverting the map. -/
structure ConstructibleLog where
  val : EntropyReal
  src : PNat
  prop : logb_C src.val = val

instance : Coe ConstructibleLog EntropyReal := ⟨ConstructibleLog.val⟩

/-- The choice-free equivalence between ConstructibleLog and PNat. -/
def logEquivPNat : ConstructibleLog ≃ PNat where
  toFun c := c.src
  invFun n := ⟨logb_C n.val, n, rfl⟩
  left_inv c := by
    cases c with
    | mk val src prop =>
      dsimp
      subst prop
      rfl
  right_inv n := rfl

/-- Addition of ConstructibleLog, defined by pulling back integer multiplication.
    Because `log_add` is defined via the bijection, `log_add (logb_C x) (logb_C y) = logb_C (x * y)` 
    is true definitionally for positive integers x and y. -/
def log_add (a b : ConstructibleLog) : ConstructibleLog :=
  logEquivPNat.symm (a.src * b.src)

/-- Fold a list of positive integers into a total log using `log_add`. -/
def log_add_list : List PNat → ConstructibleLog
  | [] => logEquivPNat.invFun 1
  | p :: ps => log_add (logEquivPNat.invFun p) (log_add_list ps)

/-- The logarithmic fold of a list of positive integers is the logarithm of their product. -/
lemma log_add_list_eq_prod (L : List PNat) :
    log_add_list L = logEquivPNat.invFun L.prod := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [log_add_list, ih]
    unfold log_add
    change logEquivPNat.symm (x * xs.prod) = logEquivPNat.symm (x :: xs).prod
    rw [List.prod_cons]

end InformationTheory
