/-
`#extract_to_c` meta-command — Phase 1 Pass B (Expr-walking).

Decomposing extractor: walks the target theorem's TYPE (a Prop of the form
`a < b` over ℝ), matches applied constants against a fixed realizer table,
and emits C that composes the fragments. Same walker, same registry, different
theorems — no per-theorem templates.

Supported realizers (ℝ-level only, Pass B MVP):
  - `@LT.lt ℝ _ a b`         → `egpt_cmp(<a>, <b>) == -1`
  - `@OfNat.ofNat ℝ n _`     → `egpt_from_i64(<n>)`
  - `Real.exp x`             → `exp_partial_sum(<x>, BUDGET)`  (helper in preamble)

Not supported yet (will error loudly; that's the point — registry coverage
is explicit): anything else. Pass C extends the table.

Target theorems that work under this walker:
  - Extraction.exp_one_gt_two : (2 : ℝ) < Real.exp 1
  - Extraction.exp_one_lt_three : Real.exp 1 < 3
Both extract through the SAME realizer set — the thesis validation.
-/

import Lean
import Mathlib.Analysis.Complex.ExponentialBounds

open Lean Elab Command

namespace Extraction

/-- Alias of Mathlib's `Real.exp_one_gt_two` — first target. -/
theorem exp_one_gt_two : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two

/-- Alias of Mathlib's `Real.exp_one_lt_three` — second target. Same shape
family, different operand ordering and constants. Proves the walker isn't
template-matching on the theorem name. -/
theorem exp_one_lt_three : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_three

/-- Alias of Mathlib's `Real.one_lt_sqrt_two` — third target. Introduces
a new noncomputable transcendental (`Real.sqrt`) to the realizer registry,
demonstrating composition across multiple per-constant realizers through
the same walker. -/
theorem one_lt_sqrt_two : (1 : ℝ) < Real.sqrt 2 := Real.one_lt_sqrt_two

/-- Fourth target: combines `Real.sqrt`, `HAdd.hAdd`, `OfNat.ofNat`, and
`LT.lt` in a single statement. Exercises registry composition across
binary operators — the walker threads sub-expressions through each
realizer independently. -/
theorem two_lt_one_plus_sqrt_two : (2 : ℝ) < 1 + Real.sqrt 2 := by
  have h : (1 : ℝ) < Real.sqrt 2 := Real.one_lt_sqrt_two
  linarith

/-- Fifth target: `Classical.choice` in the STATEMENT itself. The walker's
Classical.choice realizer dispatches on the implicit type arg (ℝ here) and
returns the registered canonical inhabitant (`egpt_from_i64(0)`). Because
the statement multiplies by 0, the inequality holds regardless of which
real the axiom picks — so our canonical-inhabitant substitution is sound.
This is the first target that genuinely exercises a uniform
`Classical.choice` realizer, not just the noncomputable-def pattern. -/
theorem classical_choice_mul_zero_lt_one :
    (@Classical.choice ℝ ⟨(37 : ℝ)⟩) * 0 < 1 := by
  simp

/-- Sixth target: an existential. Forces the walker to decompose
`∃ x : α, P x` — descend into the lambda body, realize the predicate
with the bound variable bound to a C witness, emit a bounded search
loop in `main()` that tries candidates. For `x * x = 4`, candidate `2`
wins on the third iteration. -/
theorem exists_sq_eq_four : ∃ x : ℝ, x * x = 4 := ⟨2, by norm_num⟩

/-- Seventh target: conjunction. Exercises `And`, combining two Pass-B
style inequalities in a single statement. The realizer emits
`((<lhs>) && (<rhs>))` — short-circuit evaluation in C. Proves the
walker composes propositional connectives via the same CMode.expr path. -/
theorem exp_one_between_two_and_three :
    (2 : ℝ) < Real.exp 1 ∧ Real.exp 1 < 3 :=
  ⟨Real.exp_one_gt_two, Real.exp_one_lt_three⟩

/-- Eighth target: disjunction. Dual of `And`; realizer emits
`((<lhs>) || (<rhs>))`. Provable from the first disjunct. -/
theorem exp_one_lt_three_or_huge : Real.exp 1 < 3 ∨ 100 < Real.exp 1 :=
  Or.inl Real.exp_one_lt_three

/-- Ninth target: universal over a finite type. Forces the walker to
handle `Expr.forallE` with a `Fin N` binder — the dual of `Exists`.
Emits an AND-reduced search loop: short-circuits to `false` on the
first counterexample; accumulates `true` over the full enumeration.
The body uses `Fin.val` which the walker pass-through realizes to the
bound witness variable. -/
theorem forall_fin_three_val_lt_three : ∀ x : Fin 3, x.val < 3 :=
  fun x => x.isLt

/-! ## Axiom-closure gate -/

private def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

private def axiomViolations (thmName : Name) : CommandElabM (Option (Array Name)) := do
  let used ← Lean.collectAxioms thmName
  let bad  := used.filter (fun a => !allowedAxioms.contains a)
  if bad.isEmpty then return none else return some bad

/-! ## The walker

`realizeReal`  : Expr → Option String  — emits a C expression of type `EgptNumber *`
`realizeProp`  : Expr → Option CMode   — emits a C int expression OR a statement block

Both return `none` if the Expr doesn't match a registered pattern. `none`
surfaces as a user-visible error listing the offending sub-expression so the
user knows exactly which realizer to add. The two functions are mutually
recursive (e.g. `Decidable.decide` in `realizeReal` calls into `realizeProp`),
so they live in a `mutual` block. -/

/-- Realization mode: a Prop realizes either as a single C int expression
(Pass B–E style) or as a statement block that assigns to `result`
(Pass F: existentials and any future multi-statement shapes). -/
inductive CMode where
  | expr  : String → CMode
  | block : String → CMode
  deriving Inhabited

/-- Extract a natural-number literal from an `OfNat` second argument.
The Expr shape for `(2 : ℝ)` is `@OfNat.ofNat ℝ 2 (instOfNatReal …)` where
the middle arg is a `.lit (.natVal 2)` in this Lean version. -/
private def natLitOf : Expr → Option Nat
  | .lit (.natVal n) => some n
  | _ => none

/-- Extract a Nat literal from an Expr that may be `.lit (.natVal n)`
or `@OfNat.ofNat Nat n (instOfNatNat n)`. -/
private def extractNatLit (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | _ =>
    match e.getAppFnArgs with
    | (``OfNat.ofNat, #[_α, n, _inst]) => natLitOf n
    | _ => none

mutual

/-- Emit a C expression of type `EgptNumber *` from a real-valued Lean Expr.
Returns `none` (unrecognized pattern) — surfaces as user-visible error
listing the missing realizer.

Handles `Expr.bvar 0` as `"__witness"` — the identifier we bind in the
search loop emitted for `Exists` / `∀`. Deeper de Bruijn indices are
not supported (no nested binders in the MVP). `Fin.val` is a
pass-through: `Fin.val x` realizes to whatever `x` realizes to, so
inside a `∀ x : Fin N, P` body, `x.val` becomes `__witness`. -/
partial def realizeReal : Expr → Option String := fun e =>
  match e with
  | .bvar 0 => some "__witness"
  | _ =>
  match e.getAppFnArgs with
  | (``Fin.val, #[_n, x]) => realizeReal x  -- pass-through ℕ view of Fin
  | (``Real.exp, #[x]) => do
      let xc ← realizeReal x
      return s!"exp_partial_sum({xc}, BUDGET)"
  | (``Real.sqrt, #[x]) => do
      let xc ← realizeReal x
      return s!"sqrt_partial_newton({xc}, BUDGET)"
  | (``HAdd.hAdd, #[_α, _β, _γ, _inst, a, b]) => do
      let ac ← realizeReal a
      let bc ← realizeReal b
      return s!"egpt_add({ac}, {bc})"
  | (``HSub.hSub, #[_α, _β, _γ, _inst, a, b]) => do
      let ac ← realizeReal a
      let bc ← realizeReal b
      return s!"egpt_sub({ac}, {bc})"
  | (``HMul.hMul, #[_α, _β, _γ, _inst, a, b]) => do
      let ac ← realizeReal a
      let bc ← realizeReal b
      return s!"egpt_mul({ac}, {bc})"
  | (``OfNat.ofNat, #[_α, n, _inst]) => do
      let k ← natLitOf n
      return s!"egpt_from_i64({k})"
  -- Canonical-inhabitant primitives: every "produce-an-α-from-a-witness"
  -- form routes through the same type-indexed dispatch. Extending the
  -- domain (ℂ, ℚ, user types) is one match arm per type. Phase 3b adds
  -- ℕ and ℤ; Phase 3a registered ℝ. Inlined in both arms (Lean's
  -- forward-decl rules make a shared helper awkward to express here).
  | (``Classical.choice, #[α, _hne]) =>
      match α.getAppFnArgs with
      | (``Real, #[]) => some "egpt_from_i64(0)"
      | (``Nat,  #[]) => some "egpt_from_i64(0)"
      | (``Int,  #[]) => some "egpt_from_i64(0)"
      | _             => none
  | (``Nonempty.some, #[α, _h]) =>
      match α.getAppFnArgs with
      | (``Real, #[]) => some "egpt_from_i64(0)"
      | (``Nat,  #[]) => some "egpt_from_i64(0)"
      | (``Int,  #[]) => some "egpt_from_i64(0)"
      | _             => none
  -- `@Decidable.decide P _inst : Bool`. Realize P as a CMode.expr,
  -- wrap in a C ternary returning egpt_from_i64(1) or egpt_from_i64(0).
  -- Hack: the def's Lean type is Bool but our convention emits EgptNumber*
  -- everywhere; printed "1"/"0" decodes the Bool unambiguously. Covers
  -- Classical.dec / Classical.propDecidable transitively (their Decidable
  -- instances are erased at the LCNF level into `decide` calls).
  | (``Decidable.decide, #[p, _inst]) =>
      match realizeProp p with
      | some (.expr pe) =>
          some s!"({pe} ? egpt_from_i64(1) : egpt_from_i64(0))"
      | _ => none
  -- `@Classical.choose α (fun x => P x) h : α`. Bounded witness search
  -- expressed as a GNU statement-expression (non-portable; works under
  -- `cc` on macOS/Linux clang/gcc). Witness comes from realizing the
  -- predicate's lambda body with `bvar 0 → __witness`.
  | (``Classical.choose, #[α, body, _h]) =>
      match α.getAppFnArgs, body with
      | (``Real, #[]), .lam _ _ bodyExpr _ =>
          match realizeProp bodyExpr with
          | some (.expr bodyC) =>
              let block :=
                "({ EgptNumber *__result = egpt_from_i64(0); "
                ++ "for (int __i = 0; __i < 16; ++__i) { "
                ++ "EgptNumber *__witness = egpt_from_i64((int64_t)__i); "
                ++ "int __hold = " ++ bodyC ++ "; "
                ++ "if (__hold) { egpt_free(__result); __result = __witness; break; } "
                ++ "egpt_free(__witness); "
                ++ "} __result; })"
              some block
          | _ => none
      | _, _ => none
  | _ => none

/-- Emit C for a Prop-valued Lean Expr. Most shapes produce an `expr`;
`Exists` and `∀ x : Fin N` produce a `block` containing a bounded search
or universal-enumeration loop. -/
partial def realizeProp (e : Expr) : Option CMode :=
  -- Binder shapes (direct Expr match — not via getAppFnArgs).
  match e with
  | .forallE _ binderType body _ =>
      -- Only `∀ x : Fin N, P x` is in MVP scope.
      match binderType.getAppFnArgs with
      | (``Fin, #[nExpr]) => do
          let n ← extractNatLit nExpr
          match ← realizeProp body with
          | .expr bodyC =>
              let block :=
                "    result = 1;\n"
                ++ "    for (int __i = 0; __i < " ++ toString n ++ "; ++__i) {\n"
                ++ "        EgptNumber *__witness = egpt_from_i64((int64_t)__i);\n"
                ++ "        int __hold = " ++ bodyC ++ ";\n"
                ++ "        egpt_free(__witness);\n"
                ++ "        if (!__hold) { result = 0; break; }\n"
                ++ "    }\n"
              some (.block block)
          | _ => none
      | _ => none
  | _ =>
  -- Applied-constant shapes.
  match e.getAppFnArgs with
  | (``LT.lt, #[_α, _inst, a, b]) => do
      let ac ← realizeReal a
      let bc ← realizeReal b
      return .expr s!"(egpt_cmp({ac}, {bc}) == -1)"
  | (``Eq, #[_α, a, b]) => do
      let ac ← realizeReal a
      let bc ← realizeReal b
      return .expr s!"(egpt_cmp({ac}, {bc}) == 0)"
  | (``And, #[p, q]) => do
      -- Both conjuncts must realize as expressions; block-mode conjunction
      -- (e.g. Exists ∧ Exists) is deferred — would need scoped search loops.
      match (← realizeProp p), (← realizeProp q) with
      | .expr pe, .expr qe => return .expr s!"(({pe}) && ({qe}))"
      | _, _ => none
  | (``Or, #[p, q]) => do
      match (← realizeProp p), (← realizeProp q) with
      | .expr pe, .expr qe => return .expr s!"(({pe}) || ({qe}))"
      | _, _ => none
  | (``Exists, #[α, body]) =>
      -- Only ℝ-typed existentials with a lambda body are supported in MVP.
      match α.getAppFnArgs, body with
      | (``Real, #[]), .lam _ _ bodyExpr _ =>
          -- Realize the predicate body with `bvar 0` as `__witness`.
          match realizeProp bodyExpr with
          | some (.expr bodyC) =>
              let searchBudget := 16
              let block :=
                "    for (int __i = 0; __i < " ++ toString searchBudget ++ "; ++__i) {\n"
                ++ "        EgptNumber *__witness = egpt_from_i64((int64_t)__i);\n"
                ++ "        int __hold = " ++ bodyC ++ ";\n"
                ++ "        egpt_free(__witness);\n"
                ++ "        if (__hold) { result = 1; break; }\n"
                ++ "    }\n"
              some (.block block)
          | _ => none
      | _, _ => none
  | _ => none

end -- mutual

/-! ## C emission

Preamble is a fixed string; main body is built by threading realized
sub-expressions through a template. The preamble declares `exp_partial_sum`
as a static helper — no FRAQTL runtime additions needed. -/

private def cPreamble : String := "/*
 * extracted.c — generated by #extract_to_c (Pass B walker).
 * Runtime: egpt_num (FRAQTL/fat/crates/egpt_num).
 */

#include <stdio.h>
#include <stdlib.h>
#include \"egpt_num.h\"

#define BUDGET 16

/* Realizer for Real.exp via monotone Taylor partial sums.
 * S_N(x) = Σ_{k=0..N} x^k / k!  — converges to exp(x) from below for x ≥ 0.
 * Caller owns the returned handle; free with egpt_free.
 */
static EgptNumber *exp_partial_sum(const EgptNumber *x, int budget) {
    EgptNumber *s = egpt_from_i64(1);    /* S_0 = 1 */
    EgptNumber *term = egpt_from_i64(1); /* x^0 / 0! = 1 */
    for (int k = 1; k <= budget; ++k) {
        EgptNumber *k_num = egpt_from_i64((int64_t)k);
        EgptNumber *tx    = egpt_mul(term, x);
        EgptNumber *new_term = egpt_div(tx, k_num);
        egpt_free(term); egpt_free(k_num); egpt_free(tx);
        term = new_term;
        EgptNumber *new_s = egpt_add(s, term);
        egpt_free(s);
        s = new_s;
    }
    egpt_free(term);
    return s;
}

/* Realizer for Real.sqrt via Newton's method on exact rationals.
 *   y_{n+1} = (y_n + x/y_n) / 2,  y_0 = x + 1   (y_0 > sqrt(x) for x ≥ 0).
 * Newton converges monotonically from above; all iterates are upper bounds
 * on the true sqrt. Sound for inequalities of the form `k < sqrt(x)` when
 * k < sqrt(x) strictly; unsound tight upper-bound inequalities without
 * additional budget reasoning — see PLAN.md §Pass C caveats.
 */
static EgptNumber *sqrt_partial_newton(const EgptNumber *x, int budget) {
    EgptNumber *two = egpt_from_i64(2);
    EgptNumber *one = egpt_from_i64(1);
    EgptNumber *y = egpt_add(x, one);  /* y_0 = x + 1 */
    egpt_free(one);
    for (int i = 0; i < budget; ++i) {
        EgptNumber *xy = egpt_div(x, y);
        EgptNumber *sum = egpt_add(y, xy);
        EgptNumber *new_y = egpt_div(sum, two);
        egpt_free(xy); egpt_free(sum); egpt_free(y);
        y = new_y;
    }
    egpt_free(two);
    return y;
}

"

/-- Compose the C source around a realized proposition. Two flavours:
`.expr` becomes a single assignment to `result`; `.block` emits a
pre-computed multi-statement block that assigns `result` itself. -/
private def buildC (thmName : Name) (body : CMode) : String :=
  let mainBody :=
    match body with
    | .expr e  => "    int result = " ++ e ++ ";\n"
    | .block b => "    int result = 0;\n" ++ b
  cPreamble
    ++ "/* Target theorem: " ++ thmName.toString ++ " */\n"
    ++ "int main(void) {\n"
    ++ mainBody
    ++ "    printf(\"%s\\n\", result ? \"true\" : \"false\");\n"
    ++ "    return result ? 0 : 1;\n"
    ++ "}\n"

/-! ## The command -/

syntax (name := extractToC) "#extract_to_c " ident : command

@[command_elab extractToC]
def elabExtractToC : CommandElab := fun stx => do
  match stx with
  | `(#extract_to_c $id:ident) =>
      let thmName := id.getId
      let env ← getEnv
      -- Existence.
      let some info := env.find? thmName | throwError s!"unknown theorem: {thmName}"
      -- Axiom closure gate.
      if let some bad ← axiomViolations thmName then
        throwError s!"axiom closure check failed for {thmName}: disallowed axioms {bad.toList}"
      -- Walk the theorem's TYPE (not its proof).
      let propExpr := info.type
      let some cBody := realizeProp propExpr
        | throwError s!"realizer miss on {thmName}: no realizer for top-level Expr {propExpr}"
      -- Emit.
      let cSource := buildC thmName cBody
      let expectedStdout := "true\n"
      -- Per-theorem output dir for multi-target runs.
      let outDir := s!"extraction/prototype/{thmName.toString.replace "." "_"}"
      IO.FS.createDirAll outDir
      IO.FS.writeFile s!"{outDir}/extracted.c" cSource
      IO.FS.writeFile s!"{outDir}/expected_output.txt" expectedStdout
      logInfo m!"✓ extracted {thmName} → {outDir}/extracted.c"
  | _ => throwUnsupportedSyntax

/-! ## Phase 3a-prototype — term-content extraction

PLAN.md §Phase 3a describes a Lean LCNF-pass intercept that rewrites
`Classical.choice α h` to `@Inhabited.default α (synthInstance ...)`
*during compilation*, with `@[extract_safe]` gating `compileDecl`'s
noncomputable refusal. That intercept requires Lean toolchain
modifications (relaxing `Lean.Compiler.compileDecl`, registering an
LCNF pass) — out of scope for user-land code.

This section ships the closest user-land analog: a `#extract_def`
command that walks a noncomputable def's *value* (its term, not its
type) via the same `realizeReal` walker as Phase 1, and emits a C
function returning the realized inhabitant. The `@[extract_safe]` gate
described in PLAN.md cannot be a same-file attribute (Lean's attribute
registration runs at module-load, not in-file), so the user-land
prototype gates on the axiom-closure check alone — same warrant the
Phase 1 walker uses. The full toolchain version would add the gate
attribute in a separate file plus a `compileDecl` relaxation. -/

private def buildCDef (defName : Name) (cName : String) (bodyC : String) : String :=
  cPreamble
    ++ "/* Phase 3a-prototype — term-content extraction of "
    ++ defName.toString ++ " */\n"
    ++ "EgptNumber *" ++ cName ++ "(void) {\n"
    ++ "    return " ++ bodyC ++ ";\n"
    ++ "}\n\n"
    ++ "int main(void) {\n"
    ++ "    EgptNumber *r = " ++ cName ++ "();\n"
    ++ "    char *s = egpt_to_cstring(r);\n"
    ++ "    printf(\"%s\\n\", s);\n"
    ++ "    egpt_string_free(s);\n"
    ++ "    egpt_free(r);\n"
    ++ "    return 0;\n"
    ++ "}\n"

syntax (name := extractDef) "#extract_def " ident : command

@[command_elab extractDef]
def elabExtractDef : CommandElab := fun stx => do
  match stx with
  | `(#extract_def $id:ident) =>
      let defName := id.getId
      let env ← getEnv
      let some info := env.find? defName
        | throwError s!"unknown def: {defName}"
      -- Axiom-closure gate, same as #extract_to_c. The `@[extract_safe]`
      -- gate from PLAN.md §Phase 3a is future Lean-toolchain work; for
      -- this prototype the axiom check is the only warrant.
      if let some bad ← axiomViolations defName then
        throwError s!"axiom closure check failed for {defName}: \
                     disallowed axioms {bad.toList}"
      -- Pull the def's value (term, not type).
      let some defValue := info.value?
        | throwError s!"{defName} has no value (axiom or opaque?)"
      -- Walk the body via realizeReal (Phase 1 walker reused — same
      -- realizer table, same correctness story).
      let some bodyC := realizeReal defValue
        | throwError s!"realizer miss in body of {defName}: \
                       no realizer for Expr {defValue}"
      let cName := defName.toString.replace "." "_"
      let cSource := buildCDef defName cName bodyC
      let outDir := s!"extraction/prototype/{cName}"
      IO.FS.createDirAll outDir
      IO.FS.writeFile s!"{outDir}/extracted.c" cSource
      IO.FS.writeFile s!"{outDir}/expected_output.txt" "0\n"
      logInfo m!"✓ extracted def {defName} → {outDir}/extracted.c"
  | _ => throwUnsupportedSyntax

/-! ## Phase 3a-prototype target -/

/-- Phase 3a target. A `noncomputable def` whose value is literally
`Classical.choice` over ℝ. Validates the term-content extraction path:
`#extract_def` reads the def's value, walks it via the same
`realizeReal` from Phase 1, dispatches the `Classical.choice` realizer
(Pass E) on `α = ℝ`, and emits `egpt_from_i64(0)` as the canonical
inhabitant. -/
noncomputable def classical_choice_real : ℝ := Classical.choice ⟨(0 : ℝ)⟩

/-- Phase 3b target — `Classical.choice` extended to ℕ. Validates
that the realizer dispatch generalizes to a second type with one
registry entry. Emits `egpt_from_i64(0)` (ℕ's canonical 0). -/
noncomputable def classical_choice_nat : ℕ := Classical.choice ⟨(0 : ℕ)⟩

/-- Phase 3b target — `Nonempty.some` instead of `Classical.choice`.
Different surface (field projection on the Nonempty witness), same
type-indexed canonical-inhabitant semantics. The walker recognizes
the `Nonempty.some` pattern and routes to the same dispatch. -/
noncomputable def nonempty_some_real : ℝ := (⟨(0 : ℝ)⟩ : Nonempty ℝ).some

/-- Phase 3b target — `Decidable.decide` over an ℝ inequality. The
walker realizes the inner Prop via `realizeProp`, wraps it in a C
ternary returning `egpt_from_i64(1)` (true) or `egpt_from_i64(0)`
(false). Output: `1` for `2 < 3`. Covers the `Classical.dec` /
`Classical.propDecidable` family transitively — they all collapse
through `decide` at the LCNF level. -/
noncomputable def decide_two_lt_three : Bool := decide ((2 : ℝ) < 3)

/-- Phase 3b target — `Classical.choose` over an existential. The
walker emits a bounded witness search via a GNU statement-expression
(non-portable but `cc` on macOS/Linux supports it). Witness for
`x * x = 4` is `2`. On search failure within budget, falls back to
the canonical inhabitant `egpt_from_i64(0)`. -/
noncomputable def some_sq_eq_four : ℝ :=
  Classical.choose (⟨2, by norm_num⟩ : ∃ x : ℝ, x * x = 4)

end Extraction

-- Axiom gates — theorems (Phase 1).
#print axioms Extraction.exp_one_gt_two
#print axioms Extraction.exp_one_lt_three
#print axioms Extraction.one_lt_sqrt_two
#print axioms Extraction.two_lt_one_plus_sqrt_two
#print axioms Extraction.classical_choice_mul_zero_lt_one
#print axioms Extraction.exists_sq_eq_four
#print axioms Extraction.exp_one_between_two_and_three
#print axioms Extraction.exp_one_lt_three_or_huge
#print axioms Extraction.forall_fin_three_val_lt_three

-- Axiom gates — definitions (Phase 3a/3b-prototype).
#print axioms Extraction.classical_choice_real
#print axioms Extraction.classical_choice_nat
#print axioms Extraction.nonempty_some_real
#print axioms Extraction.decide_two_lt_three
#print axioms Extraction.some_sq_eq_four

-- Decomposing extraction — SAME walker, NINE different theorems.
#extract_to_c Extraction.exp_one_gt_two
#extract_to_c Extraction.exp_one_lt_three
#extract_to_c Extraction.one_lt_sqrt_two
#extract_to_c Extraction.two_lt_one_plus_sqrt_two
#extract_to_c Extraction.classical_choice_mul_zero_lt_one
#extract_to_c Extraction.exists_sq_eq_four
#extract_to_c Extraction.exp_one_between_two_and_three
#extract_to_c Extraction.exp_one_lt_three_or_huge
#extract_to_c Extraction.forall_fin_three_val_lt_three

-- Term-content extraction — Phase 3a/3b-prototype.
#extract_def Extraction.classical_choice_real
#extract_def Extraction.classical_choice_nat
#extract_def Extraction.nonempty_some_real
#extract_def Extraction.decide_two_lt_three
#extract_def Extraction.some_sq_eq_four
