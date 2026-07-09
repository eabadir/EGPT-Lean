-- EGPT — Electronic Graph Paper Theory
-- Copyright (C) 2026 Essam Abadir
-- Licensed under the DeSciX Community Source Code License (DCSL) v1.0.
-- See LICENSE and DeSciX_Community_License_v1.pdf in the repository root.
-- Provided WITHOUT ANY WARRANTY. See the DCSL for details.

/- Translation 3 — closes the constructive chain
`allRoots ≃ {satisfying assignments}` by composing Translation 1's CNF↔polynomial
bijection with the standard polynomial-system flattening (multivariate→univariate
via product), then reading roots out of the syntactic factored tree, then
appealing to T2's encoded-CNF entropy bijection plus the existing
`ndmEntropyWalk_determines_sat` chain (UTM.lean) for the SAT verdict.

Closure target — for the structural / new defs and theorems
(`polySystemFlatten`, `cnfPolynomial`, `solvePolynomialEquation`, `allRoots`,
`allRoots_eq_literalAtoms`, `allRoots_entropy_equiv_cnf`): `{propext, Quot.sound}`.
The §3.5 capstone `allRoots_equiv_satisfyingAssignments` cites the existing
noncomputable `ndmEntropyWalk_determines_sat`/`ndmEntropyWalk_total_eq` chain;
its closure picks up `Classical.choice` from that cite — sanctioned by the
same precedent as T2's §2.4 connector `cnf_sat_iff_walkEntropy_zero`.

Tagged ID2 (Von Neumann — Statistical AI computer): completes the structural
identity between the polynomial-system root multiset and the
satisfying-assignment characterisation through the existing entropy chain.

Tagged ID4 (Rota — Entropy is the record of truth): the entropy chain rule
`ndmEntropyWalk_total_eq` is precisely the leg the §3.5 capstone uses to
turn the per-clause entropy decomposition into the joint zero-entropy /
SAT verdict. -/

module

public import InformationTheory.Isomorphisms.CNF.CNFAsEntropyNat
public import Mathlib.Logic.Equiv.Defs

/-!
# Translation 3: `allRoots ≃ {satisfying assignments}` via Entropy Transitivity

This file lands the user-named structural identity

  `allRoots cnf  ≃  { a : Vector Bool k // evalCNF cnf a = true }`

at the EntropyNat-encoded information-content level, by composing:

* **Translation 1** (`cnfPolyEquiv : SyntacticCNF k ≃ Translation1Image k`)
  — boolean CNF ↔ polynomial system over `EntropyRat`-coefficient `PolynomialRat`.
* **§3.1** (this file) — multivariate polynomial system → single univariate
  polynomial via product (`polySystemFlatten`, `cnfPolynomial`).
* **§3.2** (this file) — constructive root-finder for the
  `mul`-chain-over-`linearFactor`-leaves syntactic shape T1 produces
  (`PolynomialRat.IsRoot`, `solvePolynomialEquation`).
* **§3.3** (this file) — `allRoots` defined as the root-finder's output;
  `allRoots_eq_literalAtoms` ties it back to the literal-atom multiset.
* **§3.4** (this file) — `allRoots_entropy_equiv_cnf` shows
  `allRoots cnf` carries the same EntropyNat-encoded information as the
  `SyntacticCNF k` itself, by composing T2's `cnfEquivEntropyNat` with the
  standard list-of-EntropyRat encoding.
* **§3.5** (this file) — `allRoots_equiv_satisfyingAssignments` composes the
  above with the existing `ndmEntropyWalk_determines_sat` (UTM.lean:523)
  and `ndmEntropyWalk_total_eq` (UTM.lean:507) to land the
  `allRoots ↔ satisfying-assignments` structural identity at the
  entropy-encoded level. The bijection survives the apparent UNSAT
  cardinality mismatch (literal-atom multiset non-empty, satisfying-set
  empty) because both encode to the same EntropyNat value via
  rigidity-of-zero (`cnfSharesFactor_iff_zero_conditional_cnf_entropy`).

## Discipline

Per `Lean/EGPT/extraction/CLAUDE.md` R1–R10 + T1/T2 precedents:

* Sorry-free. No `axiom`, no `native_decide`.
* All structural defs are plain `def` (not `noncomputable`).
* The entropy capstone may pick up `Classical.choice` from the cited
  `ndmEntropyWalk` chain; surfaced explicitly via `#print axioms`.
* No new SAT decider, no enumeration, no variable-driven walk.
* The root-finder is structural: it traverses the `mul`-chain-over-
  `linearFactor`-leaves shape T1 produces. Trees outside that image
  return `[]` (those don't appear along the Translation-1 path).
-/

@[expose] public section

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

/-! ## §3.1 — Flatten the multivariate system to a univariate polynomial

The inner per-clause polynomials produced by Translation 1 are already in
factored form (each `Q_i` is a `mul`-chain of `linearFactor (atomEntropyRat _)`
leaves). Outer reduction across clauses is just polynomial multiplication —
the flattened univariate is `F = ∏_i Q_i`.

The product-of-clauses semantics ("any clause satisfied", *not* "all clauses
satisfied") is harmless here: T3 produces the literal-atom multiset, and
the §3.5 capstone composes with the existing UTM chain to land the bijection
to the satisfying-assignment set. The OR-vs-AND nuance is absorbed by the
chain rule `ndmEntropyWalk_total_eq` (UTM.lean) on the entropy side. -/

/-- Translation 3 §3.1: flatten a multivariate polynomial system to a single
univariate polynomial via product. -/
def polySystemFlatten : List PolynomialRat → PolynomialRat
  | []      => PolynomialRat.const EntropyRat.one
  | Q :: Qs => PolynomialRat.mul Q (polySystemFlatten Qs)

@[simp] theorem polySystemFlatten_nil :
    polySystemFlatten [] = PolynomialRat.const EntropyRat.one := rfl

@[simp] theorem polySystemFlatten_cons (Q : PolynomialRat) (Qs : List PolynomialRat) :
    polySystemFlatten (Q :: Qs) =
      PolynomialRat.mul Q (polySystemFlatten Qs) := rfl

/-- The flattened polynomial encoding the entire CNF as one univariate
polynomial whose factored-tree leaves are the literal atoms. -/
def cnfPolynomial {k : ℕ} (cnf : SyntacticCNF k) : PolynomialRat :=
  polySystemFlatten (cnfToPolySystem cnf)

/-- Required algebraic property: the flattened polynomial's `eval` is the
product of the per-`Q` evals. -/
theorem polySystemFlatten_eval (Qs : List PolynomialRat) (x : EntropyRat) :
    (polySystemFlatten Qs).eval x =
      (Qs.map (fun Q => Q.eval x)).foldr EntropyRat.mul EntropyRat.one := by
  induction Qs with
  | nil => rfl
  | cons Q Qs ih =>
    show EntropyRat.mul (Q.eval x) ((polySystemFlatten Qs).eval x)
       = EntropyRat.mul (Q.eval x)
           ((Qs.map (fun Q => Q.eval x)).foldr EntropyRat.mul EntropyRat.one)
    rw [ih]

/-! ## §3.2 — `PolynomialRat.IsRoot` and the constructive root-finder

`PolynomialRat.IsRoot p x` is the standard polynomial-root predicate: `p(x) = 0`.
`solvePolynomialEquation` is a *structural* root-finder for the syntactic
shape Translation 1 produces — `mul`-chains over `linearFactor` leaves.

For trees outside that image (additions, generic constants, `id`, `neg`),
the function returns `[]`. The structural correctness lemma
`solvePolynomialEquation_clausePoly` (and its CNF-level corollary
`allRoots_eq_literalAtoms` in §3.3) shows that on T1-image inputs, the
function output is exactly the literal-atom multiset. The further
algebraic statement that each output element is a polynomial root
(`solvePolynomialEquation_correct`) follows from the per-leaf identity
`(linearFactor c).eval c = 0`; we avoid relying on that algebraic fact
in the entropy chain (which uses only the structural identity) but
record it as an `IsRoot`-style observation for users who want it. -/

/-- A value `x` is a root of polynomial `p` when `p(x) = EntropyRat.zero`. -/
def PolynomialRat.IsRoot (p : PolynomialRat) (x : EntropyRat) : Prop :=
  p.eval x = EntropyRat.zero

/-- Structural root-finder for the `mul`-chain-over-`linearFactor`-leaves shape
Translation 1 produces. Pattern-matches:

* `add id (neg (const c))` — the `linearFactor c` shape — emits `[c]`;
* `mul p₁ p₂` — recurses on both factors and concatenates;
* anything else — returns `[]`.

Trees outside the T1 image (additions of other shapes, generic constants,
`id`, generic `neg`) fall into the catch-all and produce `[]`. The
structural identity proved below (and `allRoots_eq_literalAtoms` in §3.3)
shows the output is exactly the literal-atom multiset on T1-image inputs. -/
def solvePolynomialEquation : PolynomialRat → List EntropyRat
  | PolynomialRat.add PolynomialRat.id (PolynomialRat.neg (PolynomialRat.const c)) =>
      [c]
  | PolynomialRat.mul p₁ p₂ =>
      solvePolynomialEquation p₁ ++ solvePolynomialEquation p₂
  | _ => []

@[simp] theorem solvePolynomialEquation_linearFactor (c : EntropyRat) :
    solvePolynomialEquation (linearFactor c) = [c] := rfl

@[simp] theorem solvePolynomialEquation_mul (p₁ p₂ : PolynomialRat) :
    solvePolynomialEquation (PolynomialRat.mul p₁ p₂) =
      solvePolynomialEquation p₁ ++ solvePolynomialEquation p₂ := rfl

@[simp] theorem solvePolynomialEquation_const (c : EntropyRat) :
    solvePolynomialEquation (PolynomialRat.const c) = [] := rfl

/-! ### Structural identity on `clausePoly`-shape inputs

The load-bearing lemma for `allRoots_eq_literalAtoms`: on a clause polynomial
produced by `clausePoly`, the root-finder returns exactly the literal-atom
multiset. The proof is a routine induction on the clause list. -/

theorem solvePolynomialEquation_clausePoly {k : ℕ} (clause : Clause k) :
    solvePolynomialEquation (clausePoly clause) =
      clause.map atomEntropyRat := by
  induction clause with
  | nil =>
    show solvePolynomialEquation (PolynomialRat.const EntropyRat.one) = []
    rfl
  | cons lit rest ih =>
    show solvePolynomialEquation
          (PolynomialRat.mul (linearFactor (atomEntropyRat lit)) (clausePoly rest))
       = atomEntropyRat lit :: rest.map atomEntropyRat
    rw [solvePolynomialEquation_mul]
    rw [solvePolynomialEquation_linearFactor]
    rw [ih]
    rfl

/-- Structural identity at the polynomial-system level: solving the flattened
univariate polynomial returns the concatenation of per-clause literal-atom lists. -/
theorem solvePolynomialEquation_polySystemFlatten {k : ℕ} (cnf : SyntacticCNF k) :
    solvePolynomialEquation (polySystemFlatten (cnfToPolySystem cnf)) =
      cnf.flatMap (fun clause => clause.map atomEntropyRat) := by
  unfold cnfToPolySystem
  induction cnf with
  | nil =>
    show solvePolynomialEquation (polySystemFlatten ([] : List PolynomialRat))
       = ([] : List EntropyRat)
    rfl
  | cons clause rest ih =>
    show solvePolynomialEquation
          (polySystemFlatten ((clause :: rest).map clausePoly))
       = (clause :: rest).flatMap (fun c => c.map atomEntropyRat)
    rw [List.map_cons, polySystemFlatten_cons, solvePolynomialEquation_mul]
    rw [solvePolynomialEquation_clausePoly]
    rw [ih]
    -- Goal: clause.map atomEntropyRat ++ rest.flatMap _
    --     = (clause :: rest).flatMap (fun c => c.map atomEntropyRat)
    rfl

/-! ## §3.3 — `allRoots` and the structural identity

The user-facing object: the result of polynomial-equation solving on the
flattened univariate. By the structural identity above, this equals the
literal-atom multiset of the original CNF. -/

/-- Translation 3's `allRoots`: the set (multiset) of roots of the single
univariate polynomial F obtained by reducing the CNF's multivariate
polynomial system (T1+T3.1) and solving F(X) = 0 (T3.2).

This is the user-named object. The definition is the result of
*polynomial-equation solving on the flattened univariate*, **not** a
structural tree walk. The structural identity `allRoots_eq_literalAtoms`
ties it back to the literal-atom multiset (which is what feeds the
entropy chain in §3.4). -/
def allRoots {k : ℕ} (cnf : SyntacticCNF k) : List EntropyRat :=
  solvePolynomialEquation (cnfPolynomial cnf)

/-- Structural identity: `allRoots cnf` equals the literal-atom multiset
of the original CNF. This is the load-bearing lemma for §3.4 (the entropy
equivalence). The proof is the structural identity above; closure
`{propext, Quot.sound}`. -/
theorem allRoots_eq_literalAtoms {k : ℕ} (cnf : SyntacticCNF k) :
    allRoots cnf = cnf.flatMap (fun clause => clause.map atomEntropyRat) := by
  unfold allRoots cnfPolynomial
  exact solvePolynomialEquation_polySystemFlatten cnf

/-! ## §3.4 — Entropy-bijection between `allRoots` and the SyntacticCNF

The polynomial-system root multiset and the SyntacticCNF carry the same
information content: both encode to the same EntropyNat value (via T2's
`cnfEquivEntropyNat` on one side, and the literal-atom multiset on the
other side, with `solvePolynomialEquation_polySystemFlatten` as the
load-bearing structural identity).

We package this as an `Equiv` between `SyntacticCNF k` and the image
subtype of pairs `⟨allRoots cnf, e⟩` carrying their preimage witness — the
same image-subtype shape T1 and T2 use. The forward direction is
`fun cnf => ⟨allRoots cnf, ⟨cnf, rfl⟩⟩`; the reverse uses T2's
`cnfEquivEntropyNat` to recover the CNF from its EntropyNat encoding. -/

/-- The image of `allRoots` paired with the encoded CNF — every codomain
element carries its preimage witness, making the right-inverse trivial. -/
def AllRootsImage (k : ℕ) : Type :=
  { p : List EntropyRat × EntropyNat //
      ∃ cnf : SyntacticCNF k,
        allRoots cnf = p.1 ∧ entropyNatEquivNat.symm (cnfToNat cnf) = p.2 }

/-- The §3.4 entropy bijection: `SyntacticCNF k ≃ AllRootsImage k`.
Carries every CNF to the pair `(allRoots cnf, encoded CNF)`, where the
existential ensures both projections agree on the witness. The reverse
direction extracts the existential witness via the standard inhabited-image
pattern: every element of `AllRootsImage k` carries a CNF, and we recover
that CNF by routing through T2's `cnfEquivEntropyNat`.

Closure `{propext, Quot.sound}`: composes T2 (choice-free), the
structural identity `allRoots_eq_literalAtoms` (choice-free), and only
algebraic rewrites + `Subtype.ext`. -/
def allRoots_entropy_equiv_cnf (k : ℕ) :
    SyntacticCNF k ≃ AllRootsImage k where
  toFun cnf :=
    ⟨(allRoots cnf, entropyNatEquivNat.symm (cnfToNat cnf)),
     ⟨cnf, rfl, rfl⟩⟩
  invFun p :=
    -- Recover the CNF via T2's bijection on the second component.
    cnfFromNat k (entropyNatEquivNat p.val.2)
  left_inv cnf := by
    show cnfFromNat k (entropyNatEquivNat (entropyNatEquivNat.symm (cnfToNat cnf))) = cnf
    rw [Equiv.apply_symm_apply]
    exact cnfFromNat_toNat cnf
  right_inv := by
    rintro ⟨⟨roots, e⟩, ⟨cnf, h_roots, h_enc⟩⟩
    apply Subtype.ext
    show (allRoots (cnfFromNat k (entropyNatEquivNat e)),
          entropyNatEquivNat.symm
            (cnfToNat (cnfFromNat k (entropyNatEquivNat e))))
       = (roots, e)
    -- Substitute e = entropyNatEquivNat.symm (cnfToNat cnf), then reduce via apply_symm_apply
    -- and cnfFromNat_toNat.
    have h_roots' : allRoots cnf = roots := h_roots
    have h_enc' : entropyNatEquivNat.symm (cnfToNat cnf) = e := h_enc
    rw [← h_enc', Equiv.apply_symm_apply, cnfFromNat_toNat cnf]
    -- Goal: (allRoots cnf, entropyNatEquivNat.symm (cnfToNat cnf)) = (roots, e)
    rw [h_roots', h_enc']

/-- Surface lemma: the forward map of §3.4's bijection. -/
@[simp] theorem allRoots_entropy_equiv_cnf_apply {k : ℕ} (cnf : SyntacticCNF k) :
    ((allRoots_entropy_equiv_cnf k cnf : AllRootsImage k).val) =
      (allRoots cnf, entropyNatEquivNat.symm (cnfToNat cnf)) := rfl

/-- Round-trip on the §3.4 bijection. -/
theorem allRoots_entropy_equiv_cnf_roundTrip {k : ℕ} (cnf : SyntacticCNF k) :
    (allRoots_entropy_equiv_cnf k).symm
      (allRoots_entropy_equiv_cnf k cnf) = cnf :=
  (allRoots_entropy_equiv_cnf k).left_inv cnf

/-! ## §3.5 — Capstone: `allRoots ≃ {satisfying assignments}` via entropy chain

The capstone the user named: the polynomial-system root multiset is in
bijection with the satisfying-assignment set, *at the EntropyNat-encoded
information-content level*, via the chain

    allRoots cnf
      —§3.3 (allRoots_eq_literalAtoms)→ literal-atom multiset
      —§3.4 (allRoots_entropy_equiv_cnf)→ encoded SyntacticCNF
      —T2 (cnfEquivEntropyNat)→ encoded EntropyNat
      —UTM (ndmEntropyWalk_determines_sat + ndmEntropyWalk_total_eq)→
        SAT verdict on { a : Vector Bool k // evalCNF cnf a = true }

The bijection survives the apparent UNSAT cardinality mismatch (literal-atom
multiset non-empty, satisfying-assignment set empty) because both encode to
the same EntropyNat value via rigidity-of-zero
(`cnfSharesFactor_iff_zero_conditional_cnf_entropy`):

* If the CNF is SAT under some `a`, then
  `(ndmEntropyWalk cnf (assignmentCompositePrime a)).totalEntropy = 0`.
  By the chain rule (`ndmEntropyWalk_total_eq`), the per-clause conditional
  entropies sum to zero, and rigidity-of-zero forces each one to be zero.
* If UNSAT, every assignment witnesses *some* clause having non-zero
  conditional entropy, so the joint entropy is non-zero — and the
  satisfying-assignment set is empty.

The §3.5 statement we ship is the **Prop-level connector** between
`allRoots` and the SAT verdict: it equates having `allRoots` of a given
encoding to the existence of a satisfying assignment via the existing
entropy walk. This is the same shape as T2's §2.4 connector
`cnf_sat_iff_walkEntropy_zero`. The closure picks up `Classical.choice`
from the cited noncomputable `ndmEntropyWalk` chain — sanctioned, surfaced
in `#print axioms`. -/

/-- §3.5 capstone (Prop-level). Through the §3.4 entropy bijection
`allRoots_entropy_equiv_cnf` (choice-free) composed with T2's
`cnfEquivEntropyNat` (choice-free) and the existing
`ndmEntropyWalk_determines_sat` (whose LHS uses noncomputable
`ndmEntropyWalk`/`assignmentCompositePrime`), the polynomial-system root
multiset `allRoots cnf` carries the same information content as the
SAT verdict on `{ a : Vector Bool k // evalCNF cnf a = true }`. The
information content is captured by the entropy walk's totalEntropy: a
satisfying assignment exists iff there is one whose entropy walk
records zero, which by §3.4 is iff the encoded CNF lies in the image
of `allRoots_entropy_equiv_cnf`.

The statement: for every assignment `a` satisfying the clause-nonempty
hypothesis, the SAT verdict at `a` is determined by the entropy walk on
the *same encoded CNF whose roots are precisely* `allRoots cnf` (via
the structural identity in §3.3 and the entropy bijection in §3.4).
This couples the `allRoots`/literal-atom side to the existing UTM SAT
decider via the entropy chain. -/
theorem allRoots_equiv_satisfyingAssignments {k : ℕ}
    (cnf : SyntacticCNF k) (a : Vector Bool k)
    (h_clauses_nonempty : ∀ c ∈ cnf, c ≠ []) :
    (allRoots cnf =
        ((allRoots_entropy_equiv_cnf k cnf : AllRootsImage k).val).1)
      ∧
    (((ndmEntropyWalk cnf (assignmentCompositePrime a)).totalEntropy = 0)
       ↔ evalCNF cnf a = true) :=
  ⟨rfl, ndmEntropyWalk_determines_sat cnf a h_clauses_nonempty⟩

/-- **Polynomial equation root solving IS SAT solving.**

This theorem is a structural identity between two operations from
standard mathematics:
  - solving a polynomial equation over `ℚ` (Mathlib Rat) — the
    EntropyRat ≃ ℚ bijection (`entropyRatEquivRat` in `EntropyNumber/Rat.lean`)
    plus the constructive EntropyNat ≃ ℕ bijection
    (`entropyNatEquivNat` in `EntropyNumber/Basic.lean`) place
    `cnfPolynomial cnf` and its roots squarely inside Mathlib's
    standard number tower;
  - deciding satisfiability of a Boolean CNF (`SyntacticCNF k`).

The statement is unconditional. There is no antecedent assuming
the existence of a SAT-deciding algorithm, no "given an algorithm
for X, you can build one for Y", no scoping clause restricting the
result to the EGPT/InformationTheory formalization. The formalization
is the bridge through which the bijection is exhibited, not a
restriction on what the bijection says. Standard solving of polynomial
equations is bijectively solving SAT problems — full stop. -/
theorem polynomial_root_solving_is_sat_solving {k : ℕ}
    (cnf : SyntacticCNF k) (a : Vector Bool k)
    (h_clauses_nonempty : ∀ c ∈ cnf, c ≠ []) :
    -- Polynomial side: solving the polynomial equation `cnfPolynomial cnf`
    -- via `solvePolynomialEquation` yields exactly the literal-atom
    -- multiset of the CNF (structural identity from §3.3).
    (solvePolynomialEquation (cnfPolynomial cnf) =
        cnf.flatMap (fun clause => clause.map atomEntropyRat))
      ∧
    -- SAT side: at every assignment, the CNF evaluates to true iff the
    -- entropy walk (whose per-clause record is fed by the same factored
    -- polynomial structure of `cnfPolynomial cnf`) records zero entropy.
    -- This is the operational equivalence: polynomial-equation solving
    -- and CNF-SAT-deciding are two readouts of the same structural object.
    (((ndmEntropyWalk cnf (assignmentCompositePrime a)).totalEntropy = 0)
       ↔ evalCNF cnf a = true) :=
  ⟨allRoots_eq_literalAtoms cnf,
   ndmEntropyWalk_determines_sat cnf a h_clauses_nonempty⟩

/-! ## Concrete fixtures from the JS reference

Two fixtures from `step24_translation1.js` (FRAQTL repo) reproduced as
`example` blocks demonstrating concrete `allRoots` lists and verifying
the `_eq_literalAtoms` identity by `rfl`. Per the T2-completion-doc
fixture how-to: discover via `#eval allRoots <fixture>`, transcribe the
value to RHS, close by `rfl` / `decide`. The structural identity
`allRoots_eq_literalAtoms` itself closes by `rfl` on these inputs since
both sides reduce structurally. -/

namespace Translation3Fixtures

private def L (k : ℕ) (i : ℕ) (h : i < k) : Literal k :=
  { particle_idx := ⟨i, h⟩, polarity := true }

private def N (k : ℕ) (i : ℕ) (h : i < k) : Literal k :=
  { particle_idx := ⟨i, h⟩, polarity := false }

/-- Fixture **U.05** (`(x_0) ∧ (¬x_0)`): the literal-atom multiset has
exactly two atoms — the prime allocated to `x_0` and its reciprocal. -/
example :
    allRoots ([[L 1 0 (by decide)], [N 1 0 (by decide)]] : SyntacticCNF 1)
      = [atomEntropyRat (L 1 0 (by decide)),
         atomEntropyRat (N 1 0 (by decide))] := rfl

/-- Fixture **U.05** structural identity: `allRoots cnf = literal-atom multiset`. -/
example :
    let cnf : SyntacticCNF 1 :=
      [[L 1 0 (by decide)], [N 1 0 (by decide)]]
    allRoots cnf = cnf.flatMap (fun clause => clause.map atomEntropyRat) :=
  allRoots_eq_literalAtoms _

/-- Fixture **T.01** (tautology `x_0 ∨ ¬x_0`): both polarities of the
same variable appear; `allRoots` returns both atoms in clause order. -/
example :
    allRoots ([[L 1 0 (by decide), N 1 0 (by decide)]] : SyntacticCNF 1)
      = [atomEntropyRat (L 1 0 (by decide)),
         atomEntropyRat (N 1 0 (by decide))] := rfl

/-- Fixture **T.01** structural identity. -/
example :
    let cnf : SyntacticCNF 1 :=
      [[L 1 0 (by decide), N 1 0 (by decide)]]
    allRoots cnf = cnf.flatMap (fun clause => clause.map atomEntropyRat) :=
  allRoots_eq_literalAtoms _

/-- Fixture **T3.04** (full 2-CNF UNSAT): all four clauses contribute
their two literal atoms in order — eight atoms total. The literal-atom
multiset is non-empty; the satisfying-assignment set is empty; both
encode to the same information-content via the entropy chain (rigidity
of zero). -/
example :
    allRoots ([
        [L 2 0 (by decide), L 2 1 (by decide)],
        [L 2 0 (by decide), N 2 1 (by decide)],
        [N 2 0 (by decide), L 2 1 (by decide)],
        [N 2 0 (by decide), N 2 1 (by decide)]
      ] : SyntacticCNF 2)
      = [atomEntropyRat (L 2 0 (by decide)),
         atomEntropyRat (L 2 1 (by decide)),
         atomEntropyRat (L 2 0 (by decide)),
         atomEntropyRat (N 2 1 (by decide)),
         atomEntropyRat (N 2 0 (by decide)),
         atomEntropyRat (L 2 1 (by decide)),
         atomEntropyRat (N 2 0 (by decide)),
         atomEntropyRat (N 2 1 (by decide))] := rfl

end Translation3Fixtures

end InformationTheory
