# RISKS — honest-gap register

**Companion to:** [AUDIT.md](AUDIT.md), [PLAN.md](PLAN.md),
[ARCHITECTURE.md](ARCHITECTURE.md).
**Last updated:** 2026-04-24 (Phase 2 wrap, post Pass H).

What the extraction prototype cannot currently do, or does in a way
that might bite under less-permissive inputs. Each entry calls out
the risk, the symptom, and the path to fix it.

---

## 1. Approximation-based realizers with no precision threading

### 1.1 `Real.exp` via Taylor partial sums

**How it's implemented:** `exp_partial_sum(x, budget)` computes
`Σ_{k=0..N} x^k / k!`. For `x ≥ 0`, this is a monotone lower bound on
`exp(x)`.

**Sound for:** `k < exp(x)` comparisons where the gap `exp(x) − k`
exceeds the truncation error at the fixed budget (currently 16).

**Unsound for:**
- Tight upper-bound comparisons like `exp(x) < k` where `k` is
  strictly below `exp(x)` but within the truncation residual. Pass B
  target `Real.exp 1 < 3` happens to work because `exp(1) ≈ 2.718`
  and the 16-term partial sum is well below 3. A target like
  `Real.exp 1 < 2.72` would be unsound at budget 16 — the partial sum
  exceeds `2.72` well before it approaches `exp(1)`.
- `x < 0`: series alternates, partial sums no longer monotone.

**Fix path:** adaptive budget (increase until the next term is below
the required resolution) + interval bounds (sum plus remainder
estimate). Not in MVP.

### 1.2 `Real.sqrt` via Newton from above

**How it's implemented:** `sqrt_partial_newton(x, budget)` starts
`y_0 = x + 1` (always above `sqrt(x)` for `x ≥ 0`) and iterates
`y_{n+1} = (y_n + x/y_n) / 2`. Converges monotonically from above.

**Sound for:** `k < sqrt(x)` comparisons where `k < sqrt(x)` strictly
with enough gap. Pass C target `1 < Real.sqrt 2` works.

**Unsound for:**
- Tight upper-bound comparisons like `sqrt(x) < k` with `k` narrowly
  above `sqrt(x)`. Our partial sum is above `sqrt(x)`, so the
  emitted `egpt_cmp(sqrt_newton, k)` might return `1` (greater) at
  small budgets even when `sqrt(x) < k` is mathematically true.
- Equalities like `sqrt(x) = y` where `y` is the exact irrational
  — Newton on rationals never converges in a finite number of steps
  to an irrational fixed point.

**Fix path:** same as exp — adaptive budget, two-sided interval.

### 1.3 Impact on Pass F `Eq` realizer

`realizeProp` `Eq` emits `egpt_cmp(a, b) == 0`. For our prototype's
existential target `∃ x : ℝ, x * x = 4` the witness is `2` (a
rational), so equality is bit-exact. For existentials with irrational
witnesses (`∃ x : ℝ, x * x = 2`, witness `sqrt(2)`), the bounded
search would never find an exact witness — it would need either a
rational witness or an approximate-equality realizer.

---

## 2. Bounded witness search

`Exists` realizer enumerates `egpt_from_i64(0 .. 15)`. Any target
whose witness is outside `{0, ..., 15}` fails silently — the loop
exits with `result = 0` and prints `false`.

**Miss modes:**
- Negative witnesses (never generated).
- Witnesses `> 15` (exceeds budget).
- Non-integer rational witnesses (never generated).
- Irrational witnesses (fundamentally out of reach of this strategy).

**Fix path:** per-predicate-shape search strategies keyed by the
body's Expr pattern. For `∃ x : ℝ, x * x = k`, recognize the
square-root shape and call `sqrt_partial_newton(k, BUDGET)` as the
candidate directly.

---

## 3. Walker limitations

### 3.1 No nested binders

`bvar 0` is hardcoded to `"__witness"`. A nested `∃ x, ∃ y, P x y`
would have `y → bvar 0` and `x → bvar 1`, but the walker doesn't
know about `bvar 1`. Nested-binder existentials / universals will
realize-miss.

**Fix:** track a de Bruijn stack of witness names during walker
descent.

### 3.2 No `Forall` over non-`Fin` domains

`∀ x : α, P x` only matches when `α = Fin N` for a concrete literal
`N`. `∀ x : ℕ, P x` (infinite domain) or `∀ x : MyType, P x`
(user-type) realize-miss — correctly, since we have no way to
enumerate infinite or opaque domains.

Acceptable design limitation, not a bug.

### 3.3 Type-class arguments are ignored

Patterns like `@HAdd.hAdd α β γ inst a b` ignore `inst`. This is
fine as long as the runtime dispatch is type-agnostic (it is —
everything goes through `egpt_num` BigInt rationals). If someone
uses a non-standard `HAdd` instance with different semantics
(e.g. modular addition over `Fin N`), the walker would emit
`egpt_add` anyway, producing mathematically wrong results.

**Fix:** explicit type check on `α`, restrict patterns to the
expected type.

### 3.4 `OfNat` literal extraction is surface-syntactic

`natLitOf` only recognizes `.lit (.natVal n)`. If Lean elaborates a
literal via a chain like `Nat.succ (Nat.succ Nat.zero)`, the
walker misses. In practice Lean always uses raw literals for small
numbers, but this is an assumption.

---

## 4. Correctness story — no composition meta-theorem

The correctness warrant for each realizer is:

- `egpt_num` arithmetic is bit-exact (BigInt rationals, JS parity
  tested).
- `entropyRealEquivReal` is a proven Mathlib bijection
  `EntropyReal ≃ ℝ`.
- Per-realizer: `exp_partial_sum` = Taylor truncation ≤ `Real.exp`;
  `sqrt_partial_newton` = Newton-from-above ≥ `Real.sqrt`.

What is **not** proven:

- That the *composition* of these realizers preserves the theorem's
  truth conditions through arbitrary Expr trees.
- That our witness-search realizer for `Exists` is sound — it just
  tries candidates; it doesn't witness that non-finding implies
  non-existence.
- That the uniform `Classical.choice` realizer is sound for all
  statements the axiom appears in — our argument is informal
  ("provable statements using `Classical.choice α` don't depend on
  the specific inhabitant"), not mechanized.

**Fix path:** a Lean-level composition meta-theorem. Probably
expressed as: "for every theorem `h : P` in the gated axiom class,
the emitted C's output is Boolean-equal to `Decidable.decide P` under
the realizer substitution." This is substantial work; deferred.

---

## 5. Axiom-closure gate is necessary but not sufficient

Our gate accepts `{propext, Classical.choice, Quot.sound}`. These are
the standard Mathlib axioms, so most classical theorems pass. But:

- The gate doesn't prevent a theorem from using a `noncomputable def`
  whose implementation depends on `Classical.choice` — it just
  requires that the realizer substitution for that def is registered.
- A theorem might use `Quot.sound` in a way our walker can't
  decompose (quotient types). The walker would realize-miss, not
  produce a wrong answer. But the failure mode is silent: "no
  realizer for this Expr" rather than "this shape is fundamentally
  out of scope".

---

## 6. Runtime / build

### 6.1 `egpt_num` FFI has no semver contract

The C ABI is stable by happy accident — we control both ends. If
`libegpt_num` is distributed independently, a future `egpt_num`
renaming `egpt_add` would silently break prior emitted `extracted.c`
files. Before any third-party distribution, add ABI versioning.

### 6.2 Memory leaks in emitted C

Intermediate `EgptNumber *` allocations inside complex expressions
are not freed. For one-shot CLI binaries, this is fine. For emitted
code that runs as a library, the leak amount per call scales with
expression depth.

**Fix:** optimize walker emission to track and free intermediates, or
rely on arena allocation in a future `egpt_num` variant.

### 6.3 Newton initial guess for sqrt

`y_0 = x + 1` works for all `x ≥ 0` but is overly conservative for
`x ≫ 1`. For `x = 10^6`, `y_0 = 10^6 + 1`, which takes ~20 Newton
iterations to converge toward `sqrt(10^6) = 1000`. For `x < 0`, the
initial guess is still positive but sqrt is undefined — the loop
produces nonsense (Lean's `Real.sqrt` returns 0 for negative inputs;
our realizer doesn't match that convention).

**Fix:** branch on `sign(x)`, and pick a better initial guess.
Deferred.

---

## 7. Scope limitations that are *not* prototype bugs

These are honest design choices for the prototype and don't become
"fixes" later — they become "Phase 3+ design decisions":

- **Only ℝ / Fin N in the realizer domain.** ℕ, ℤ, ℚ extraction
  would require parallel runtimes or a unified rational
  representation (we have that — `egpt_num`) plus type-specific
  comparison conventions. Easy to add; deferred.
- **No upstreaming to Mathlib.** Extraction is a fork-level
  experiment; the walker lives in `EGPT-research/Lean/EGPT/`, not in
  the main Mathlib tree.
- **No LCNF fork.** Option B in the Zulip handoff. We stayed with
  Option A (post-elaboration Expr rewriting) for the prototype.
  Option B is what a production-grade extractor would ultimately
  need for performance and correctness under Lean's full elaboration
  pipeline.
- **No integration with Lean's extraction pipeline (`@[extern]`,
  etc.).** Our `#extract_to_c` is a standalone meta-command, not an
  extension of the compiler itself.
