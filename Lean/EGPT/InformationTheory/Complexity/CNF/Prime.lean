-- EGPT — Electronic Graph Paper Theory
-- Copyright (C) 2026 Essam Abadir
-- Licensed under the DeSciX Community Source Code License (DCSL) v1.0.
-- See LICENSE and DeSciX_Community_License_v1.pdf in the repository root.
-- Provided WITHOUT ANY WARRANTY. See the DCSL for details.


module

public import InformationTheory.Complexity.CNF
public import Mathlib.Data.Nat.Prime.Infinite



/-!
# Prime Encoding for CNF Literals and Clauses

This file defines a prime-indexed encoding of CNF literals and clauses.
Each literal is mapped to a unique prime number via `primeIndexedAtom`,
and clauses are encoded as products of their literal primes.

## Main definitions

* `LiteralIndex` -- type alias for natural numbers representing literal indices.
* `LiteralToPrime` -- maps a literal to a positive natural number code.
* `primeIndexedAtom` -- a strictly increasing sequence of primes.
* `literalAtom` -- maps a literal to a unique prime via `primeIndexedAtom`.
* `ClauseComposite` -- type alias for the composite number encoding of a clause.
* `ClauseToComposite` -- encodes a clause as a product of literal codes.
* `clauseCompositePrime` -- encodes a clause as a product of prime-indexed atoms.
* `CNFToNumberList` / `CNFToPrimeNumberList` -- encode a CNF as a list of composites.

## Main results

* `primeIndexedAtom_prime` -- every term in the sequence is prime.
* `primeIndexedAtom_strictMono` -- the sequence is strictly increasing.
* `literalAtom_prime` -- the prime-indexed literal atom is prime.
* `literalAtom_injective` -- the prime-indexed literal atom map is injective.
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


namespace InformationTheory

open InformationTheory

/-- A Literal is an atom of information (a Prime). -/
abbrev LiteralIndex := ℕ -- We use Nat, but conceptually it's a Prime

/-- Map a literal to a unique atom code (prime-like factor token). -/
def LiteralToPrime {k : ℕ} (lit : Literal k) : ℕ :=
  lit.toNat + 1

/--
`primeIndexedAtom n` is a strictly increasing prime sequence.
It starts at `2`, and each successor is chosen as a prime at least `prev + 1`.
-/
noncomputable def primeIndexedAtom : ℕ → ℕ
  | 0 => 2
  | n + 1 => Nat.find (Nat.exists_infinite_primes (primeIndexedAtom n + 1))

/-- Every term in `primeIndexedAtom` is prime. -/
lemma primeIndexedAtom_prime (n : ℕ) : Nat.Prime (primeIndexedAtom n) := by
  induction n with
  | zero =>
      simpa [primeIndexedAtom] using Nat.prime_two
  | succ n _ih =>
      simpa [primeIndexedAtom] using
        (Nat.find_spec
          (Nat.exists_infinite_primes
            (primeIndexedAtom n + 1))).2

/-- `primeIndexedAtom` is strictly increasing. -/
lemma primeIndexedAtom_strictMono : StrictMono primeIndexedAtom := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hbound : primeIndexedAtom n + 1 ≤ primeIndexedAtom (n + 1) := by
    simpa [primeIndexedAtom] using
      (Nat.find_spec
        (Nat.exists_infinite_primes
          (primeIndexedAtom n + 1))).1
  exact lt_of_lt_of_le (Nat.lt_succ_self (primeIndexedAtom n)) hbound

/-- `primeIndexedAtom` is injective. -/
lemma primeIndexedAtom_injective : Function.Injective primeIndexedAtom :=
  primeIndexedAtom_strictMono.injective

/--
Prime-indexed atom for literals.
This is the theorem-bearing encoding path used by SAT common-factor proofs.
-/
noncomputable def literalAtom {k : ℕ} (lit : Literal k) : ℕ :=
  primeIndexedAtom (Encodable.encode lit)

/-- The prime-indexed literal atom is prime. -/
lemma literalAtom_prime {k : ℕ} (lit : Literal k) : Nat.Prime (literalAtom lit) := by
  simpa [literalAtom] using primeIndexedAtom_prime (Encodable.encode lit)

/-- The prime-indexed literal atom map is injective. -/
lemma literalAtom_injective {k : ℕ} : Function.Injective (@literalAtom k) := by
  intro l₁ l₂ h
  apply Encodable.encode_injective
  exact primeIndexedAtom_injective (by simpa [literalAtom] using h)

/-!
## Computable Prime Sequence

Each literal must map to a unique PRIME — a vector, not a scalar.
The noncomputable `primeIndexedAtom` already does this via `Nat.find`.
Here we provide a computable version using `Nat.Prime` (which is
decidable via Mathlib) and bounded search.
-/

/-- Computable primality test. `Nat.Prime` is decidable in Mathlib. -/
instance : DecidablePred Nat.Prime := Nat.decidablePrime

/-- Find the smallest prime ≥ `n`, searching up to `bound`.
Returns `n` as fallback if bound is exhausted (should not happen
for reasonable inputs — Bertrand's postulate guarantees a prime
between n and 2n). -/
def findPrimeFrom (n bound : ℕ) : ℕ :=
  match bound with
  | 0 => n
  | bound + 1 =>
    if Nat.Prime n then n
    else findPrimeFrom (n + 1) bound

/-- The nth prime, computably. Uses `findPrimeFrom` with a generous
bound. The sequence starts: 2, 3, 5, 7, 11, 13, ... -/
def nthPrimeComputable : ℕ → ℕ
  | 0 => 2
  | n + 1 =>
    let prev := nthPrimeComputable n
    findPrimeFrom (prev + 1) (prev + 2)

/-- The nth odd prime, computably. Equivalent to `nthPrimeComputable (n+1)`,
which skips the base case `2`. The sequence starts: 3, 5, 7, 11, 13, ...
This is the canonical variable-prime allocator for the polynomial-system
encoding of CNF (Translation 1): each variable index `v` gets the unique
odd prime `nthOddPrime v`, and the negation of a literal is realised as
the reciprocal `1 / nthOddPrime v` so that a literal and its negation
share the same prime but with opposite multiplicative orientation. -/
def nthOddPrime (n : ℕ) : ℕ := nthPrimeComputable (n + 1)

/-! ## Choice-free primality and prime allocation

The Mathlib `Nat.decidablePrime` instance pulls `Classical.choice` (via
`Nat.minFac` / `Nat.minFac_prime`, which themselves transitively depend on
`Real.log` infrastructure). The Mathlib `Nat.exists_infinite_primes` lemma
also leaks `Classical.choice`, which is why `primeIndexedAtom` above closes
to `[propext, Classical.choice, Quot.sound]`. Likewise the canonical
information-theoretic prime decompositions (`PrimeAtoms.primeAtomSum_eq_logb`,
`fta_via_information`, `factorial_information_increment`, …) all route
through `Real.logb` and inherit `Classical.choice`.

Translation 1 (`InformationTheory.Isomorphisms.CNF.CNFPolynomialSystem`) and any future
`{propext, Quot.sound}`-only consumer needs a **choice-free** prime
allocator. We therefore provide a local trial-division primality test, a
matching allocator, and the constructive monotonicity lemmas all callers
need. The contracts mirror those of `primeIndexedAtom` /
`primeIndexedAtom_strictMono` exactly — `nthPrimeC` is the choice-free peer
of `primeIndexedAtom`. -/

/-- A choice-free trial-division primality test on `ℕ`.
Uses bounded recursion; the `fuel` argument is always at least `n` so the
search reaches `√n` even in the worst case. -/
def isPrimeBool (n : ℕ) : Bool :=
  if n < 2 then false
  else
    let rec loop (d : ℕ) (fuel : ℕ) : Bool :=
      match fuel with
      | 0 => true
      | fuel + 1 =>
        if d * d > n then true
        else if n % d = 0 then false
        else loop (d + 1) fuel
    loop 2 n

/-- Find the smallest prime `≥ n` (per `isPrimeBool`), searching up to
`bound` steps. The fallback returns `n` if the bound is exhausted; with a
generous bound this branch is unreachable for reasonable inputs. -/
def findPrimeFromC (n bound : ℕ) : ℕ :=
  match bound with
  | 0 => n
  | bound + 1 =>
    if isPrimeBool n then n
    else findPrimeFromC (n + 1) bound

/-- A choice-free `nthPrimeComputable`. Sequence: 2, 3, 5, 7, 11, 13, ... -/
def nthPrimeC : ℕ → ℕ
  | 0 => 2
  | n + 1 =>
    let prev := nthPrimeC n
    findPrimeFromC (prev + 1) (prev + 2)

/-- A choice-free `nthOddPrime`. Sequence: 3, 5, 7, 11, 13, ... -/
def nthOddPrimeC (n : ℕ) : ℕ := nthPrimeC (n + 1)

/-! ### Choice-free monotonicity and positivity for the `nthPrimeC` allocator

These mirror `primeIndexedAtom_strictMono` (which is choice-tainted) but live
on the constructive side. They are the canonical lemmas any choice-free
consumer of the prime allocator should reach for. -/

/-- `findPrimeFromC` returns a value at least as large as its starting point. -/
lemma findPrimeFromC_ge (m b : ℕ) : m ≤ findPrimeFromC m b := by
  induction b generalizing m with
  | zero => exact Nat.le_refl _
  | succ b ih =>
    unfold findPrimeFromC
    split_ifs with hp
    · exact Nat.le_refl _
    · exact Nat.le_trans (Nat.le_succ _) (ih (m + 1))

/-- `nthPrimeC` is strictly positive for every input. -/
lemma nthPrimeC_pos (n : ℕ) : 0 < nthPrimeC n := by
  induction n with
  | zero => decide
  | succ n ih =>
    unfold nthPrimeC
    exact lt_of_lt_of_le (Nat.succ_pos _) (findPrimeFromC_ge _ _)

/-- `nthOddPrimeC` is strictly positive. -/
lemma nthOddPrimeC_pos (n : ℕ) : 0 < nthOddPrimeC n := by
  unfold nthOddPrimeC
  exact nthPrimeC_pos _

/-- `nthOddPrimeC` is non-zero. -/
lemma nthOddPrimeC_ne_zero (n : ℕ) : nthOddPrimeC n ≠ 0 :=
  Nat.pos_iff_ne_zero.mp (nthOddPrimeC_pos n)

/-- Each successor of `nthPrimeC` is strictly greater: the recursion
`nthPrimeC (n+1) = findPrimeFromC (prev+1) _` returns at least `prev+1`. -/
lemma nthPrimeC_succ_ge (n : ℕ) :
    nthPrimeC n + 1 ≤ nthPrimeC (n + 1) := by
  show nthPrimeC n + 1 ≤
    findPrimeFromC (nthPrimeC n + 1) (nthPrimeC n + 2)
  exact findPrimeFromC_ge _ _

/-- `nthPrimeC (n+1) ≠ 1`: a successor is at least `prev+1 ≥ 2`. -/
lemma nthPrimeC_succ_ne_one (n : ℕ) : nthPrimeC (n + 1) ≠ 1 := by
  intro h
  have h_ge := nthPrimeC_succ_ge n
  have h_prev_pos : 0 < nthPrimeC n := nthPrimeC_pos n
  omega

/-- `nthOddPrimeC n ≠ 1` for all `n`. -/
lemma nthOddPrimeC_ne_one (n : ℕ) : nthOddPrimeC n ≠ 1 := by
  unfold nthOddPrimeC
  exact nthPrimeC_succ_ne_one n

/-- Strict monotonicity of `nthPrimeC`: `m < n → nthPrimeC m < nthPrimeC n`.
This is the choice-free peer of `primeIndexedAtom_strictMono`. -/
lemma nthPrimeC_lt_of_lt :
    ∀ {m n : ℕ}, m < n → nthPrimeC m < nthPrimeC n := by
  intro m n h
  induction n with
  | zero => exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    have h_step : nthPrimeC n < nthPrimeC (n + 1) := by
      have := nthPrimeC_succ_ge n
      omega
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hlt | heq
    · exact lt_trans (ih hlt) h_step
    · subst heq
      exact h_step

/-- `nthPrimeC` is strictly monotone — packaged in `StrictMono` form. -/
lemma nthPrimeC_strictMono : StrictMono nthPrimeC := fun _ _ h => nthPrimeC_lt_of_lt h

/-- `nthPrimeC` is injective. -/
lemma nthPrimeC_injective : Function.Injective nthPrimeC :=
  nthPrimeC_strictMono.injective

/-- Strict monotonicity of `nthOddPrimeC`. The choice-free peer of
`primeIndexedAtom_strictMono` for the odd-only sequence. -/
lemma nthOddPrimeC_strictMono : StrictMono nthOddPrimeC := by
  intro m n h_mn
  unfold nthOddPrimeC
  exact nthPrimeC_lt_of_lt (by omega)

/-- `nthOddPrimeC` is injective. -/
lemma nthOddPrimeC_injective : Function.Injective nthOddPrimeC :=
  nthOddPrimeC_strictMono.injective

/-!
## Variable Prime

`variablePrime` maps each variable index to a unique prime number via
`nthPrimeComputable`. Each variable maps to one prime, regardless of
polarity. `x₀` and `¬x₀` share the same prime — the sign is carried
separately as a Bool.
-/

/-- The prime for a variable index. Each variable maps to one prime,
regardless of polarity. `x₀` and `¬x₀` share the same prime. -/
def variablePrime {k : ℕ} (idx : Fin k) : ℕ :=
  nthPrimeComputable idx.val

/-- `Literal.toNat` is injective. -/
lemma Literal.toNat_injective {k : ℕ} :
    Function.Injective (@Literal.toNat k) := by
  intro ⟨idx₁, pol₁⟩ ⟨idx₂, pol₂⟩ h
  simp only [Literal.toNat] at h
  have h_pol : pol₁ = pol₂ := by
    by_contra hne
    cases pol₁ <;> cases pol₂ <;> simp_all <;> omega
  subst h_pol
  have h_idx : idx₁.val = idx₂.val := by
    cases pol₁ <;> omega
  congr 1; exact Fin.ext h_idx

/-- Clause composite: product of variable primes in the clause. -/
def clauseComposite {k : ℕ} (clause : Clause k) : ℕ :=
  (clause.map (fun lit => variablePrime lit.particle_idx)).prod

/-- Global composite: product of ALL variable primes in the CNF. -/
def cnfComposite {k : ℕ} (cnf : List (List (Literal k))) : ℕ :=
  ((cnf.flatMap id).map (fun lit => variablePrime lit.particle_idx)).prod

/-- A Clause is a Composite Number (product of its literals). -/
abbrev ClauseComposite := ℕ

/-- Encode a clause as a composite number (product of its literal codes). -/
noncomputable def ClauseToComposite {k : ℕ} (clause : Clause k) : ClauseComposite :=
  (clause.map LiteralToPrime).prod

/--
Clause composite using the prime-indexed atom encoding.
This is used for SAT-compatible common-factor predicates.
-/
noncomputable def clauseCompositePrime {k : ℕ} (clause : Clause k) : ClauseComposite :=
  (clause.map literalAtom).prod

/-- A CNF is a list of Composites. -/
noncomputable def CNFToNumberList {k : ℕ} (cnf : SyntacticCNF k) : List ClauseComposite :=
  cnf.map ClauseToComposite

/-- CNF number list built from prime-indexed clause composites. -/
noncomputable def CNFToPrimeNumberList {k : ℕ} (cnf : SyntacticCNF k) : List ClauseComposite :=
  cnf.map clauseCompositePrime

/-!
## Prime Dictionary

The deduplicated list of variable primes from a CNF. One prime per variable
that appears, regardless of polarity. Used by `StandardComplexity.lean` for
prime atom detection.
-/

/-- Extract the variable primes from a clause (ignoring polarity). -/
def clauseVariablePrimes {k : ℕ} (clause : Clause k) : List ℕ :=
  clause.map (fun lit => variablePrime lit.particle_idx)

/-- The prime dictionary: deduplicated variable primes from the CNF.
One prime per variable that appears, regardless of polarity.
Every entry is a genuine prime -- a vector, not a scalar. -/
def allVectors {k : ℕ} (cnf : SyntacticCNF k) : List ℕ :=
  (cnf.flatMap clauseVariablePrimes).eraseDups

/-- Backward-compatible alias: the deduplicated prime atoms. -/
abbrev cnfPrimeAtoms {k : ℕ} (cnf : SyntacticCNF k) : List ℕ :=
  allVectors cnf

/-- Does the CNF have extractable prime atoms? Returns `true` iff
at least one prime vector appears across the CNF's clauses. -/
def hasExtractableAtoms {k : ℕ} (cnf : SyntacticCNF k) : Bool :=
  (allVectors cnf).length > 0

set_option linter.flexible false in
/-- If `hasExtractableAtoms` returns `true`, the CNF has prime atoms. -/
theorem hasExtractableAtoms_sound {k : ℕ} (cnf : SyntacticCNF k)
    (h : hasExtractableAtoms cnf = true) :
    (cnfPrimeAtoms cnf).length > 0 := by
  simp [hasExtractableAtoms] at h
  exact h

set_option linter.flexible false in
/-- If the CNF has clauses with literals, then
`hasExtractableAtoms` returns `true`. -/
theorem hasExtractableAtoms_complete {k : ℕ} (cnf : SyntacticCNF k)
    (h : (cnfPrimeAtoms cnf).length > 0) :
    hasExtractableAtoms cnf = true := by
  simp [hasExtractableAtoms]
  exact h

/-- `hasExtractableAtoms` iff the CNF has at least one prime atom. -/
theorem hasExtractableAtoms_iff {k : ℕ} (cnf : SyntacticCNF k) :
    (cnfPrimeAtoms cnf).length > 0 ↔
    hasExtractableAtoms cnf = true :=
  ⟨hasExtractableAtoms_complete cnf, hasExtractableAtoms_sound cnf⟩

end InformationTheory
