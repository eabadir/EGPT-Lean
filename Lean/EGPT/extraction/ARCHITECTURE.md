# ARCHITECTURE — `#extract_to_c` Extraction Prototype

**Companion to:** [AUDIT.md](AUDIT.md), [PLAN.md](PLAN.md), [RISKS.md](RISKS.md).
**Last updated:** 2026-04-24 (Phase 2 wrap, post Pass H).

This document describes the working architecture of the
`#extract_to_c` prototype as of commit `0497796` on the
`feat/extraction-prototype` branch. It is a snapshot of the present,
not a forward design.

---

## 1. Data flow

```
┌──────────────────────────┐     ┌─────────────────────┐     ┌──────────────────┐
│  Lean theorem (Mathlib)  │ →   │  Expr walker        │ →   │  Emitted C file  │
│  classical proof OK      │     │  per-constant       │     │  extracted.c     │
│  #print axioms = allowed │     │  realizer dispatch  │     │  with preamble   │
└──────────────────────────┘     └─────────────────────┘     └────────┬─────────┘
                                                                       │
                                                                       ▼
                                                        ┌──────────────────────┐
                                                        │  cc + libegpt_num    │
                                                        │  (BigInt rational    │
                                                        │  C runtime, no float)│
                                                        └────────┬─────────────┘
                                                                 │
                                                                 ▼
                                                        ┌──────────────────────┐
                                                        │  ./extracted_bin     │
                                                        │  prints "true"       │
                                                        │  exit 0              │
                                                        └──────────────────────┘
```

The walker never touches the theorem's *proof*. It walks the
**statement type** as an `Expr`, looks up applied-constant names and
binder shapes in a fixed realizer table, and composes C fragments.
The proof's validity (and its reliance on `Classical.choice`) is
captured upstream by the axiom-closure gate.

---

## 2. The walker — two realizers + one discriminator

All in [ExtractionCommand.lean](ExtractionCommand.lean).

### 2.1 `CMode` — expression vs. block discriminator

```lean
inductive CMode where
  | expr  : String → CMode   -- single C `int` expression
  | block : String → CMode   -- multi-statement block assigning `result`
```

Pass B–E / G produce `.expr`. Pass F (existentials) and Pass H
(universals) produce `.block` because the search / enumeration loop
can't be written as a single C expression.

### 2.2 `realizeReal : Expr → Option String`

Emits a C expression of type `EgptNumber *`. Partial match on:

| Lean `Expr` shape | C fragment | Added in |
|---|---|---|
| `.bvar 0` | `"__witness"` | Pass F |
| `@Fin.val n x` | `realizeReal x` (pass-through) | Pass H |
| `@Real.exp x` | `exp_partial_sum(<x>, BUDGET)` | Pass B |
| `@Real.sqrt x` | `sqrt_partial_newton(<x>, BUDGET)` | Pass C |
| `@HAdd.hAdd _ _ _ _ a b` | `egpt_add(<a>, <b>)` | Pass D |
| `@HSub.hSub _ _ _ _ a b` | `egpt_sub(<a>, <b>)` | Pass D |
| `@HMul.hMul _ _ _ _ a b` | `egpt_mul(<a>, <b>)` | Pass D |
| `@OfNat.ofNat _ n _` | `egpt_from_i64(<n>)` | Pass B |
| `@Classical.choice α _` | (α = ℝ) `egpt_from_i64(0)` | Pass E |

Note we ignore the type-class argument in the arithmetic / `LT`
patterns — `HAdd.hAdd ℕ` and `HAdd.hAdd ℝ` both route to `egpt_add`
because the runtime is type-agnostic (everything is a BigInt
rational; ℕ literals are integers, ℝ literals go through the same
path). Provability in Lean catches type mismatches upstream.

### 2.3 `realizeProp : Expr → Option CMode`

Top-level prop dispatcher. Direct Expr match for binders, then
`getAppFnArgs` for applied connectives:

| Shape | CMode | C output |
|---|---|---|
| `Expr.forallE _ (Fin N) body _` | `.block` | AND-reduced loop over `[0, N)` |
| `@LT.lt _ _ a b` | `.expr` | `(egpt_cmp(<a>, <b>) == -1)` |
| `@Eq _ a b` | `.expr` | `(egpt_cmp(<a>, <b>) == 0)` |
| `@And p q` | `.expr` | `((<p>) && (<q>))` |
| `@Or p q` | `.expr` | `((<p>) \|\| (<q>))` |
| `@Exists α body-lambda` | `.block` | bounded search loop |

Marked `partial` because it recurses through `Exists`, `forallE`,
`And`, `Or` into sub-props.

### 2.4 `buildC : Name → CMode → String`

Wraps the realized prop in a `main()` function. `.expr` becomes
`int result = <e>;`; `.block` becomes `int result = 0; <b>`.
Preamble (fixed) declares `exp_partial_sum` and `sqrt_partial_newton`
helpers. All file I/O goes through `IO.FS.writeFile` in the command
elaborator.

---

## 3. The axiom-closure gate

Before emitting C, `#extract_to_c` calls `Lean.collectAxioms thmName`
and rejects any axiom outside `{propext, Classical.choice, Quot.sound}`.
This catches silent noncomputable-escape hatches that would otherwise
produce C the realizers can't back.

Each of the nine prototype targets has been gate-verified. Eight
depend on `{propext, Classical.choice, Quot.sound}`; one
(`forall_fin_three_val_lt_three`) depends on no axioms — its proof is
purely constructive.

---

## 4. The runtime — `egpt_num` C ABI

Lives in [FRAQTL `feat/egpt-num-cffi`](../../../../Unkamon/FRAQTL/fat/crates/egpt_num/)
(commit `f4ba38b`). The C-emitted code includes
[`egpt_num.h`](../../../../Unkamon/FRAQTL/fat/crates/egpt_num/include/egpt_num.h)
and links against `libegpt_num.dylib`.

### 4.1 ABI surface

| Function | Purpose |
|---|---|
| `egpt_from_i64(i64) → EgptNumber *` | construct from integer |
| `egpt_from_rational_i64(i64, i64)` | construct from rational |
| `egpt_add / egpt_sub / egpt_mul / egpt_div` | arithmetic |
| `egpt_cmp(a, b) → {-1, 0, 1}` | total order |
| `egpt_free(p)` | destructor |
| `egpt_to_cstring / egpt_string_free` | serialization |

### 4.2 Memory model

Every arithmetic op allocates a fresh `EgptNumber *`; caller owns it
and must `egpt_free`. No reference counting, no aliasing across
handles. The walker emits code that leaks intermediate allocations in
complex expressions — acceptable for a prototype (bounded loops have
bounded leaks, ≤ a few hundred bytes per theorem).

### 4.3 Inline helpers emitted by the walker

Realizers for `Real.exp` and `Real.sqrt` inject two helpers into the
C preamble:

- `exp_partial_sum(x, budget)` — Taylor series `Σ_{k=0..N} x^k / k!`.
  Monotone lower bound on `exp(x)` for `x ≥ 0`.
- `sqrt_partial_newton(x, budget)` — Newton from above,
  `y_0 = x + 1`, `y_{n+1} = (y_n + x/y_n) / 2`. Monotone upper bound
  on `sqrt(x)` for `x ≥ 0`.

Both use only the `egpt_num` primitives. See [RISKS.md](RISKS.md) for
precision / soundness caveats.

---

## 5. Extension procedures

### 5.1 Adding a new ℝ-returning Mathlib function

1. Pick the Mathlib `noncomputable def` (or any other ℝ-valued
   function) that should realize into the pipeline.
2. Add an arm to `realizeReal` in `ExtractionCommand.lean`:
   ```lean
   | (``Real.log, #[x]) => do
       let xc ← realizeReal x
       return s!"log_partial_<strategy>({xc}, BUDGET)"
   ```
3. Add a matching C helper to `cPreamble` that uses `egpt_num`
   primitives. For transcendentals: decide on a series or
   iteration and track whether it bounds from above or below.
4. Write a target theorem `Extraction.foo_<prop>`, prove it via
   Mathlib or `by` tactic.
5. `#extract_to_c Extraction.foo_<prop>` — walker emits
   `prototype/Extraction_foo_<prop>/extracted.c`.
6. `make diff` green.

### 5.2 Adding a new propositional connective

1. Arm `realizeProp` directly for the `Expr.` shape (if it's a core
   binder like `forallE`) or via `getAppFnArgs` for applied
   constants (`@Or p q`, etc.).
2. Decide on `.expr` vs `.block` based on whether the emission
   fits as a single C expression.
3. Add a target exercising the shape; gate + extract + diff.

### 5.3 Adding a new type to `Classical.choice`'s domain

Single line in the `realizeReal` match on `Classical.choice`:

```lean
| (``Classical.choice, #[α, _hne]) =>
    match α.getAppFnArgs with
    | (``Real, #[]) => some "egpt_from_i64(0)"
    | (``Nat,  #[]) => some "egpt_from_i64(0)"      -- ℕ's canonical
    | (``Int,  #[]) => some "egpt_from_i64(0)"      -- ℤ's canonical
    | _             => none
```

Soundness relies on the same argument that made Pass E clean: a
statement is provable for `Classical.choice α h` iff it's provable
for *any* inhabitant of α — so any specific inhabitant we return is
sound.

---

## 6. Where each commit lives

| Pass | EGPT-research commit | FRAQTL commit | Gain |
|---|---|---|---|
| 0 | — | `f4ba38b` | runtime |
| A | `54165e2` | — | template walker (retired) |
| B | `4a69761` | — | decomposing walker |
| C | `29872a0` | — | Real.sqrt |
| D | `26ef0e0` | — | HAdd / HSub / HMul |
| E | `7bd735b` | — | uniform Classical.choice |
| F | `81f749d` | — | Exists + Eq + bvar |
| G | `2729fb7` | — | And |
| H | `0497796` | — | Or + ∀-over-Fin |
