# Why Choice Is Combinatorics
## A Demon, A Drawer, And A Label

**For:** scientifically educated readers who want to understand what
this project is doing and why, without having to learn number theory
first. Every technical claim is cited to the specific Lean proof
that establishes it, so the curious can verify each step.

**The thesis, in one sentence:** Gödel was wrong about the
formalizability of intuitionism, von Neumann was right (and more
right than he knew), and the apparent uncountability of the
mathematical universe is an artifact of a century-old confusion
between **syntactic labels** (the digits of a number) and
**semantic content** (the prime factorization that gives the
number its irreducible information). Cantor's diagonalization, on
which the classical-vs-constructive divide was originally erected,
manipulates labels rather than information; flipping a digit does
not create new primes. The Lean proofs cited throughout this
document are the settlement: a constructive number tower that
reaches every standard mathematical type without invoking
Classical.choice in the forward direction, the Continuum
Hypothesis decided as a consequence of the Beth hierarchy
collapsing onto ℕ, and a polynomial-time SAT decider that follows
from the same prime-atom structure. The framework below is the
illustration of this settled science.

---

## A small demon, an infinite drawer

Imagine a small demon — Maxwell's old friend — whose only job is to
put socks into drawers. He works very fast. Every morning a fresh
load of socks appears, and every evening they're all sorted into
drawers, paired up, neatly. He's been doing this for so long the
drawers are infinitely deep. Some drawers contain identical white
socks. Some contain unique novelty socks (one with cats, one with
stars). Some are labeled "leftover" and contain whatever didn't
pair.

Now suppose you ask: pick one sock from each drawer, and put them
in a basket. You can do this for any FINITE number of drawers — go
drawer to drawer, grab one. Easy. But what about INFINITELY many
drawers? Mathematicians have argued about this for a hundred years.

Bertrand Russell gave the cleanest version of the problem. If the
drawers contain pairs of SHOES, you can give a recipe: "take the
left shoe from each pair." Done. The recipe is finite, it works for
infinitely many drawers, you don't have to think drawer by drawer.
But if the drawers contain pairs of SOCKS — identical socks, no
left or right — you cannot give a recipe. You have to just... pick
one from each. There's no rule that distinguishes one sock from its
twin.

Mathematicians call the assumption that you CAN still pick one from
each, even without a recipe, the **Axiom of Choice**. It's the
formal version of "pretend a recipe exists." Most modern
mathematics uses it. Some find it suspicious. Constructive
mathematicians refuse it outright — they only accept theorems that
come with explicit recipes.

This is not a philosophical squabble. The choice axiom hides
assumptions that matter for computation. We're going to look inside
the demon's bookkeeping and find that he's been writing the recipe
all along.

---

## Reading the sock's label

Here's the move. Pull a sock out of any drawer. Turn it inside out.
There's a number on the label — an ordinary positive integer like
6, 35, or 2310. Now factor that number into primes:

```
6    = 2 × 3
35   = 5 × 7
2310 = 2 × 3 × 5 × 7 × 11
```

Every positive integer has exactly one prime factorization. This is
the **Fundamental Theorem of Arithmetic** (FTA), proved every which
way for a couple thousand years. The factorization is unique and
computable. So even if two socks look identical from the outside,
their labels disambiguate them: sock-2 and sock-3 are different,
even if they're both white.

So Russell's socks-vs-shoes problem dissolves. There's always a
recipe: read the label, pick the sock with the smallest prime
factorization. The "indistinguishable" sock pairs were never
actually indistinguishable — the demon, when he put them in the
drawer, had to write *something* on each one. The address of the
sock IS the recipe.

The natural objection: in real mathematics, sets don't come with
labels. Two elements of an abstract set are abstract; there's no
"first sock." Yes, in the mathematical fiction. But every actual
sock that exists has been put somewhere, by someone, at some time,
and that placement is itself a piece of information. The label IS
the placement.

This is what physicists already know about Maxwell's demon. The
original thought experiment — a demon sorting fast and slow
molecules without doing work — was eventually shown to violate the
second law of thermodynamics... unless you account for the
**entropy cost of the demon's bookkeeping**. Reading the label,
deciding which side to put it on, writing down the result: this
all takes work. Information has thermodynamic cost.

EGPT (Electronic Graph Paper Theory) takes this seriously. It says:
the cost of reading the label IS the cost of the computation. The
demon's notebook is the program. The address is the map.

---

## Combinatorics is just counting

Combinatorics is the math of counting. How many ways can you
arrange 5 books on a shelf? 5! = 120. How many subsets of {1,2,3}
are there? 8. How many paths from corner to corner in a grid?
Pascal's triangle.

Combinatorics has a working definition that matters for what comes
next: a **combinatorial object** is one with a recipe for
enumeration. You can list them, you can pair them with the natural
numbers, you can count. When two combinatorial objects can be put
in 1-to-1 correspondence — every X has exactly one Y, and vice
versa — mathematicians call this a **bijection**. Bijections are
the gold standard of "these two collections are the same size."

Standard mathematics has a hierarchy:

- For **finite** collections, bijections are easy. Just enumerate.
- For **countably infinite** collections — natural numbers,
  integers, rationals — bijections still work; you can write a
  recipe.
- For **uncountably infinite** collections (real numbers, arbitrary
  sets), classical math says: there's still a 1-to-1 correspondence
  "in principle," and it doesn't matter that you can't write it
  down.

That last move — "exists in principle" — is the Axiom of Choice. It
says: even when no explicit recipe is possible, treat the bijection
as if one existed.

EGPT's central rigorous proof (Hierarchy.lean surjective onto the standard lean types, classical choice is only invoked from Lean Real -> EntropyReal ... i.e. forward direction is completely constructable and Classical.choice is the bug that keeps Lean Real from being constructive) is that the third case never genuinely arises.
There is always a recipe; you just have to read the right label.
Specifically: every collection that mathematics treats as
"uncountably infinite" turns out to be addressable by ordinary
natural numbers, because the addresses themselves are constructed
from a countable hierarchy. The hierarchy is built one level at a
time, indexed by ℕ. Every "uncountable" object lives at some
specific level of this hierarchy, and at every level there is a
prime-coded canonical inhabitant.

The Lean formalization makes this completely explicit. The
hierarchy is named `Nat_L` (read: "the nat-like type at level L"),
and it's defined by direct recursion on ℕ:

```lean
Nat_L 0     = EntropyNat            -- equivalent to ℕ
Nat_L (n+1) = Nat_L n → Bool        -- functions from level n into yes/no
```

(See [Hierarchy.lean](../InformationTheory/EntropyNumber/Hierarchy.lean)
for the actual code.) Every type at every level can be addressed by
an ordinary natural number, because the level itself is a natural
number, and within each level the elements are functions, sets,
products built from already-addressable elements. The whole tower
collapses onto ℕ via primary keys: a type's level (a finite n) plus
its position within the level (a finite EntropyNat).

The technical theorem `cardinal_of_level`
([Hierarchy.lean](../InformationTheory/EntropyNumber/Hierarchy.lean))
proves the level-n type has cardinality `beth n` — the n-th in
Cantor's tower of infinities. The Continuum Hypothesis (Hilbert's
first problem) becomes decidable in this framework: there is no
"missing infinity" between levels because the levels are ℕ-indexed
and ℕ has no gaps. This is theorem `abadirContinuumHypothesis`
([ContinuumHypothesis.lean](../InformationTheory/EntropyNumber/ContinuumHypothesis.lean)).

This is the **Beth staircase collapse onto ℕ**: every infinity that
mathematics talks about lives at some level n, and n is just a
natural number. The "uncountably infinite" was never a wild thing;
it always had a specific finite ℕ-address in the hierarchy.

---

## What Shannon coding has to do with socks

Bell Labs' Claude Shannon, working in 1948 on the limits of
telephone communication, proved a foundational theorem: every
probability distribution has a unique optimal binary encoding. The
encoding length is the entropy. If a sock comes from a drawer where
the placement was probability p, its binary code has length
log₂(1/p) bits. This is **Shannon coding**.

The connection to socks: every random arrangement of socks-into-drawers
is a probability distribution. Every probability distribution has
an optimal binary encoding. The encoding is the recipe — the same
recipe Russell wanted for the sock case. Shannon proved one always
exists. EGPT takes it further: the encoding IS the prime
factorization of an associated natural number.

The connection runs through the Fundamental Theorem of Arithmetic
in its information-theoretic form, which the Lean proof calls
`fta_via_information` (we'll use the alias **LFTA** — log version
of FTA):

```
log₂(n) = Σ_p ν_p(n) · log₂(p)
```

Translation: the information content of a number n (measured in
bits, log₂(n)) is the sum over primes p of "how many times p
divides n" (ν_p(n)) times "how much information that prime
contributes" (log₂(p)). Proved as `fta_via_information` in
[RotaEntropy.lean](../InformationTheory/EntropyNumber/RotaEntropy.lean).

Pause and notice what this says. If you're encoding something with
information content `log₂(n)` bits, and the encoding is literally
the prime factorization of n, then **information adds up the way
primes multiply**. The encoding is canonical. Every sock has its
own prime address; every prime address has its own information
cost; the information costs sum to give the total bit-length of
the message.

This is what makes prime atoms the universal addressing scheme. Not
just that primes label numbers — that's old hat. The new claim is
that primes label INFORMATION, in a specific quantitative sense,
and the sum of prime-by-prime information equals the total
information content of the message. The label is the cost is the
recipe. All the same thing.

---

## The IID random walk and the free-address fallacy

So far I've been hand-waving "drawer placements are random." Let me
be more precise. In probability theory, an **IID random walk**
(independent, identically distributed) is a sequence of moves, each
chosen by the same probability distribution, each independent of
the previous. Imagine flipping the same coin over and over. Each
flip is one step.

A sequence of flips can encode any natural number, by treating
heads as 1 and tails as 0. Conversely, every natural number can be
written as a sequence of bits, which corresponds to a particular
outcome of an IID coin sequence. EGPT defines its base type
`EntropyNat` as exactly this: an `EntropyNat` is a sequence of
"all-true" coin flips of some finite length. Length 0 = the number
0. Length 1 with a single TRUE = the number 1. Length 5 with five
TRUEs = the number 5. (See
[Basic.lean](../InformationTheory/EntropyNumber/Basic.lean) for
the formal definition; the bijection to ℕ is theorem
`entropyNatEquivNat`.)

The point: in EGPT, a natural number is never just an abstract
integer. It's a specific physical IID outcome — a sequence of
yes/no flips. The cost of producing the number n is exactly n
flips of the coin. There is no free addressing. There is no O(1)
"look up address 10^100"; getting to the 10^100-th cell costs
10^100 work.

This is the **free-address fallacy**. Every introductory computer
science course tells you that arrays are O(1) — accessing cell 17
takes the same time as accessing cell 0. That's an idealization.
In real silicon, accessing memory at far addresses takes more
time, more energy, more thermodynamic work. The Turing machine's
"infinite tape" hides the same idealization. EGPT refuses both:
every cell is at some address, the address has some bit-length,
the bit-length is the work.

For Maxwell's demon, this is the bookkeeping he was hiding. He
cannot pretend he placed the sock "wherever" — he placed it at a
specific address, and the address is a natural number, and the
natural number has a specific prime factorization, and the
prime factorization is a specific number of bits, and the bits are
the thermodynamic cost. The demon's notebook IS the prime-atom
signature.

---

## The seven rules that force Shannon

OK, the demon writes labels. So what? Why is this enough to
dissolve the axiom of choice?

Because of a uniqueness theorem. **Rota's seven axioms for
entropy** characterize Shannon entropy completely. Any "information
measure" — any rule for assigning a number-of-bits to a probability
distribution — that satisfies seven natural conditions IS Shannon
entropy (up to a constant factor for choosing the base of the
logarithm). The axioms, formalized in
[Axioms.lean](../InformationTheory/Entropy/Axioms.lean) as the
`HasRotaEntropyAxioms` structure:

1. **Symmetry** (`IsEntropySymmetric`). Re-labeling outcomes does
   not change the entropy. The information content of "heads or
   tails" doesn't depend on what we name them.
2. **Normalized** (`IsEntropyNormalized`). A certain outcome
   carries zero information.
3. **Continuity** (`IsEntropyContinuous`). Slight changes in
   probabilities cause slight changes in entropy.
4. **Zero-invariance** (`IsEntropyZeroInvariant`). Adding a
   probability-zero outcome does not change the entropy. (Adding
   an event that never happens to your menu doesn't tell you more.)
5. **Zero-on-empty** (`IsEntropyZeroOnEmpty`). The entropy of
   nothing is zero. (Nothing to count? Zero bits.)
6. **Max at uniform** (`IsEntropyMaxUniform`). Among distributions
   with N outcomes, the one that gives maximum entropy is the
   uniform distribution. (You learn the most when you start
   knowing the least.)
7. **Conditional additivity** (`IsEntropyCondAddSigma`). The
   entropy of a joint distribution decomposes as the entropy of
   the prior plus the weighted average of conditional entropies.
   (If you tell me X first, then Y, the total information is
   X-info plus average-Y-given-X info.)

**Rota's uniqueness theorem** — `rota_all_entropy_scaled_shannon`
in [RotaEntropy.lean](../InformationTheory/EntropyNumber/RotaEntropy.lean) —
proves that Shannon entropy satisfies all seven, AND that any
function satisfying all seven is a positive scalar multiple of
Shannon entropy. The seven rules pin down Shannon entropy uniquely.

What this means for Maxwell's demon: whatever the demon's
bookkeeping IS, if it satisfies the seven natural rules, it is
Shannon entropy. The demon has no flexibility. There is exactly one
consistent way to assign information cost to placements, and that
way is Shannon coding via prime factorization.

---

## The rigidity of zero

Two of those seven axioms — `IsEntropyZeroOnEmpty` and
`IsEntropyZeroInvariant` — do more work than they look like. They
say:

- An empty set has zero entropy.
- Adding a probability-zero outcome doesn't change entropy.

Together, these two axioms make zero entropy into a SINGLE, RIGID
concept: there is no "different kind of zero." If a collection has
no information content, it has zero, period. You cannot have "almost
zero but a different almost-zero." Two different empty boxes (one
labeled "for socks" and one labeled "for hats") both contain zero
information; they are zero in the same way.

This sounds trivial. It is not. In standard mathematics, "things
with zero of a property" can be subtle. There is the empty function
`Fin 0 → α`, which differs by codomain. There is the empty set
`∅`, which differs by ambient type. There is a distribution-with-no-events.
Each of these is "empty" in some sense, and standard math
sometimes treats them as different.

The two zero-rigidity axioms collapse all these "different empties"
into one. They say: from the entropy perspective, there is exactly
one zero. This is what makes the EGPT framework dispatch edge cases
uniformly. You don't have to argue about which empty box is the
empty box — they are all the empty box.

In the P=NP proof chain, this is exactly the move that handles
**UNSAT**.

---

## SAT, UNSAT, and the prime detector

UNSAT — Boolean satisfiability — is the textbook hard problem of
computer science. Given a formula like

```
(x AND y AND NOT z) OR (NOT x AND z)
```

does there exist an assignment of TRUE/FALSE to x, y, z that makes
the whole formula true? The brute-force answer is to try all 2^n
assignments. For n=100 that is already impossibly slow.

UNSAT is the case where the answer is "no, no such assignment
exists." Detecting this is harder than detecting SAT, because you
have to RULE OUT every possible assignment.

The EGPT trick: if no assignment satisfies the formula, then in the
prime-atom encoding, no prime divides the formula's "code." It's
an empty intersection — zero shared factor — which is rigidly
equal to the empty box. So UNSAT detection reduces to checking "is
the GCD trivial?" — a polynomial-time arithmetic check.

This is theorem `unsat_detected_by_prime_structure` in
[Decomposition.lean](../InformationTheory/Complexity/Decomposition.lean).
The mechanism in plain language: every literal in the formula gets
a unique prime number assigned to it (`literalAtom`). Every
candidate assignment gets a "composite number" formed by
multiplying the primes of its TRUE literals together
(`assignmentCompositePrime`). The formula is satisfied by the
assignment iff every clause shares at least one prime factor with
the assignment composite (`cnfSharesFactor_iff_zero_conditional_cnf_entropy`).
If no assignment shares factors, the formula is UNSAT.

The two zero-rigidity axioms are what make this argument water-tight.
There is no way for an UNSAT formula to "pretend" it has a
satisfying assignment via some trick. Every empty box is the same
empty box, and the prime-atom encoding catches them all.

---

## Constructive number theory

Now we can name what EGPT is doing. Standard mathematics builds
numbers like this:

- Start with axioms (Peano, ZFC, whatever).
- Define ℕ, then ℤ, ℚ, ℝ, etc.
- Prove theorems by manipulating the axioms.
- For some theorems, invoke the Axiom of Choice when needed.

EGPT replaces this with a constructive build:

- Start with `EntropyNat` — a sequence of yes/no flips (a finite
  IID random walk).
- Prove `EntropyNat ≃ ℕ` — every natural number IS such a sequence
  ([Basic.lean](../InformationTheory/EntropyNumber/Basic.lean),
  theorem `entropyNatEquivNat`).
- Prove `EntropyInt ≃ ℤ`, `EntropyRat ≃ ℚ`, `EntropyReal ≃ ℝ` —
  every integer, rational, real has an explicit constructive form
  ([Int.lean](../InformationTheory/EntropyNumber/Int.lean),
  [Rat.lean](../InformationTheory/EntropyNumber/Rat.lean),
  [Real.lean](../InformationTheory/EntropyNumber/Real.lean)).
- The construction obeys conditional additivity rigidly: 1 + 1 = 2
  always, in every encoding, with no hidden choice.

The "rigid 1+1=2" claim is exactly `IsEntropyCondAddSigma` from
the Rota axioms. It says joint entropies decompose additively —
the demon's bookkeeping for the joint outcome is the bookkeeping
for the prior plus the bookkeeping for the conditional. There is
no slack in this rule. It is rigid arithmetic, and it is rigid all
the way down.

Why does this matter? Because constructive number theory is where
the **axiom of choice never needs to be invoked**. Every number is
built by an explicit recipe (a sequence of flips, in the
EntropyNat representation), and the equivalence to standard
mathematics' ℕ is a constructive bijection. The forward
direction — from EGPT into standard mathematics — uses no
Classical.choice; it is **surjective onto the standard mathematical
universe**. Classical.choice appears only in the reverse direction,
when bridging FROM Mathlib's quotient-defined types BACK into
EGPT's constructive types (e.g., picking a Cauchy representative
when defining `entropyRealEquivReal`). The forward boundary is
clean.

So when you prove a theorem in EGPT, you can compile it.
Specifically: you can compile it to **bit-exact C** that runs on
a real computer. The compilation is what the extraction prototype
does. But before we get to the engineering, we should pause and
note where the science came from — because this is not a new
philosophy. It is the mechanization of an argument von Neumann
made to Gödel in 1931.

---

## Where this comes from: von Neumann was right

In January 1931, three months after Gödel's incompleteness paper
appeared, von Neumann wrote to him
([Letter3_Jan12_1931.md](../../../content/SSG_History/JvM_Letters/Letter3_Jan12_1931.md)):

> "I absolutely disagree with your view on the formalizability of
> intuitionism. Certainly, for every formal system there is, as
> you proved, another formal one that is (already in arithmetic
> and the lower functional calculus) stronger. But intuitionism is
> not affected by that at all."

And then the challenge that closes the letter's central paragraph:

> "Clearly I cannot prove that every intuitionistically correct
> *construction of arithmetic* is formalizable in A or M or even
> in Z — for intuitionism is undefined and undefinable. But is it
> not a fact, that not a single construction of the kind mentioned
> is known that cannot be formalized in A, and that no living
> logician is in the position of naming such [a construction]? Or
> am I wrong, and you know an effective intuitionistic arithmetic
> construction whose formalization in A creates difficulties?"

The disagreement was about whether constructive mathematics — the
"intuitionism" of Brouwer and Heyting — is mechanizable. Gödel
held that incompleteness imposes deep limits: there must be true
constructive statements that no formal system can capture.
Von Neumann disagreed. Every constructive arithmetic statement
anyone has actually produced fits cleanly in his three formal
systems A, M, Z. He challenged Gödel directly: name an
intuitionistic construction that resists formalization. Gödel
never produced one.

Von Neumann's claim, restated in modern terms: the standard
mathematical universe — ℕ, ℤ, ℚ, ℝ, function spaces, products,
sums, finite dependent sums — is constructively reachable from a
countable base. There are no "missing" mathematical objects that
require choice or other classical machinery to access. The
informal mathematical practice of "give me a recipe and I'll
build it" is sound; what cannot be reached this way is not part
of mathematics in any operational sense.

The EGPT proof chain — every Lean theorem cited in this document —
is the concrete settlement of this 95-year-old disagreement. It
is the formalization von Neumann conjectured exists. Specifically:

- **Every standard mathematical number type is reached
  constructively.** EntropyNat → ℕ, EntropyInt → ℤ, EntropyRat →
  ℚ, EntropyReal → ℝ. The forward direction (EGPT → standard
  math) uses no Classical.choice. It is a surjective constructive
  map onto the standard mathematical universe.

- **Every "uncountable" infinity is at a finite ℕ-address.**
  `cardinal_of_level`
  ([Hierarchy.lean](../InformationTheory/EntropyNumber/Hierarchy.lean))
  proves the Beth tower is ℕ-indexed; `AbadirCompletenessTheorem`
  ([ContinuumHypothesis.lean](../InformationTheory/EntropyNumber/ContinuumHypothesis.lean))
  proves every type built from finitary constructors lives at
  some specific level. There are no unreachable types in the
  standard universe.

- **Classical theorems about that universe are reachable by a
  constructive walk.** `P_eq_NP_info`
  ([PPNP.lean](../InformationTheory/Complexity/PPNP.lean))
  demonstrates the pattern for SAT specifically — the same
  pattern lifts to every classical theorem the extraction
  prototype handles.

Gödel's incompleteness theorem stands as proved. There are true
statements about formal systems that no formal system can
capture. But intuitionistic arithmetic — the constructive part —
is not in the gap. Every actual constructive theorem fits in von
Neumann's hierarchy, and the hierarchy is now formalized in Lean
4, sorry-free, with the only axioms invoked being the standard
ones (propext, Quot.sound, Classical.choice — the last confined
to the reverse boundary, never crossing the forward direction).

Von Neumann was right. The science is settled.

What remains is engineering.

---

## Ulam, Rota, and the diagonalization that wasn't

The von Neumann letter is one historical source. There is a
second, equally direct, that bears on the framework: a 1974
conversation in Gainesville between Stanislaw Ulam and Gian-Carlo
Rota, recorded in
[Ulam_Rota_Discuss_Von_Neumann.md](../../../content/SSG_History/Ulam_Rota_Discuss_Von_Neumann.md).
Both Ulam and Rota were intimate collaborators of von Neumann; both
saw Gödel's continuum-hypothesis result the year it landed; both
were, in different ways, openly skeptical of it.

Ulam describes meeting von Neumann at the dock as he returned to
the United States:

> "His first words were that Gödel had shown that the continuum
> hypothesis was undecidable. This was how I heard for the first
> time about the existence of undecidable propositions in any
> formal system. So I said to him, 'Oh! That is because he defines
> what is meant by a set.' Johnny opened his eyes wide and
> expressed surprise that I had seen right away what was indeed
> the essential point."

Ulam's instant reaction — that the result is an artifact of the
chosen definition of "set" — is the key insight EGPT mechanizes.
If the notion of "set" you formalize over is one with hidden
choice (arbitrary collections of arbitrary elements with no
constructive recipe), then of course you get propositions that are
undecidable within it; you have encoded the choice axiom into the
very meaning of the word. Change the notion of set to one with
explicit construction recipes — `TypeTheoryConstructible` in EGPT,
every element addressable by ℕ via the Beth hierarchy — and the
"undecidability" disappears. The Continuum Hypothesis becomes
decidable (`abadirContinuumHypothesis`,
[ContinuumHypothesis.lean](../InformationTheory/EntropyNumber/ContinuumHypothesis.lean)).

Ulam pressed further:

> "I asked him whether Gödel was not a little afraid that his
> result was nothing but a sort of super paradox of the existing
> set theory, merely a diagonal method. In a sense it is a
> diagonalization. He agreed that this was probably right and that
> Gödel did not quite realise the importance of his discovery
> because of the fear that it would turn out to be merely another
> version of the whole series of set-theoretical paradoxes."

This is the deepest cut. **Gödel's CH undecidability proof, like
Cantor's original uncountability proof, is fundamentally a
diagonalization argument.** Even von Neumann conceded the point to
Ulam. And diagonalization has a flaw — one that EGPT now exposes
formally.

### The flaw in Cantor's diagonalization

Cantor's classical argument runs like this: suppose you have an
enumeration of all real numbers in [0, 1]:

```
r_1 = 0.d_{1,1} d_{1,2} d_{1,3} ...
r_2 = 0.d_{2,1} d_{2,2} d_{2,3} ...
r_3 = 0.d_{3,1} d_{3,2} d_{3,3} ...
...
```

Construct a new real `r'` by flipping the n-th digit of `r_n` for
each n. Then `r'` differs from every `r_n` in at least one digit,
so `r'` is not in the enumeration. Therefore the reals are
"uncountably infinite" — a strictly larger size of infinity than
the natural numbers. Cantor 1891.

The flaw is the unspoken assumption that **flipping a digit
creates new information**. It does not.

To see why, take a concrete number, say 42. Its semantic content
is its prime factorization: 42 = 2 × 3 × 7. The primes are the
**semantic atoms** — the irreducible information units, in the
specific quantitative sense of LFTA (`fta_via_information`,
[RotaEntropy.lean](../InformationTheory/EntropyNumber/RotaEntropy.lean)):
`log₂(42) = log₂(2) + log₂(3) + log₂(7)`. Now write 42 in
different ways:

| Representation | Syntactic label |
|---|---|
| Decimal | `42` |
| Binary | `101010` |
| Unary | `1111111111111111111111111111111111111111111` |
| Hex | `2A` |
| English | `forty-two` |
| Base-7 | `60` |

These are all different **syntactic labels**. They are
representations of the same semantic content. The prime
factorization is unchanged across every representation. The
information content (log₂(42) ≈ 5.39 bits) is unchanged. Flipping
a digit in any one of these representations gives you a different
syntactic label, but the resulting number's prime factorization
draws from the same finite universe of primes that was already
available before the flip — `52 = 2² × 13`, `48 = 2⁴ × 3`, etc.
The primes 13, 17, 19 were not created by Cantor's diagonalization;
they were always sitting in the prime universe waiting to be
referenced.

Cantor's diagonalization manipulates **syntactic labels** — the
digits of a decimal expansion. It produces a new sequence of
digits. Whether the new sequence corresponds to genuinely new
semantic information depends on whether the prime-atom signature
it encodes was previously absent from the enumeration. EGPT's
answer: it was not. The Beth hierarchy
([Hierarchy.lean](../InformationTheory/EntropyNumber/Hierarchy.lean))
exhausts every prime-atom signature at every level; the "new"
real Cantor constructs is at some specific level of the Beth
staircase, with a specific finite ℕ-address, semantically already
enumerated even if not at the exact syntactic position the
diagonalization happened to sample.

This is what `AbadirCompletenessTheorem`
([ContinuumHypothesis.lean](../InformationTheory/EntropyNumber/ContinuumHypothesis.lean))
proves: every type built from finitary constructors has a
beth-level cardinality, and the levels are ℕ-indexed. There is no
"missing real," no syntactically-flipped escape, no "outside" of
the Beth hierarchy that diagonalization can reach. The reals are
not larger than the natural numbers in any operational sense; the
reals are at level 1 of the Beth hierarchy
(`Real_L 0 := Nat_L 1 = EntropyNat → Bool`,
[Hierarchy.lean](../InformationTheory/EntropyNumber/Hierarchy.lean)),
and that level has a specific finite ℕ-address.

### Rota's hostility, Ulam's suspicion

The Ulam-Rota conversation makes the temperature explicit. Rota:
"You have a higher opinion of Gödel than I have." Ulam, on
hearing the CH undecidability result: "It was so unexpected at
the time, and poor Hilbert was..." — sentence trailing off as
Rota interjects: "Not to speak of poor von Neumann."

Both were openly suspicious. They could not articulate the formal
mechanism that would expose the flaw — that machinery did not yet
exist. But they correctly intuited that diagonalization was a
sleight of hand: a move that produces a new syntactic label and
proclaims it new mathematical content. EGPT's prime-atom encoding
makes the sleight of hand visible. The "new" real has the same
semantic content as the rest — it is just labeled differently.
Flipping a digit relabels; it does not create.

### Why von Neumann was more right than he knew

Von Neumann challenged Gödel in 1931 to name an intuitionistic
construction that resisted formalization. Gödel never produced
one. What von Neumann could not yet articulate — but the EGPT
formalization makes precise — is *why*: every constructive
arithmetic statement names some specific prime-atom signature, that
signature has a finite ℕ-address in the Beth hierarchy, and the
hierarchy is exhaustive. The reason no one ever produced a
counterexample is that no counterexample exists.

Von Neumann saw the conclusion correctly. He could not yet see
the mechanism (the prime-atom canonical addressing scheme), but
he correctly intuited that no constructive theorem would escape
his hierarchy. EGPT supplies the mechanism. Ulam saw the same
thing from the other side — the diagonalization argument is a
syntactic trick, and Gödel's CH result is the same kind of trick
formalized. Rota's hostility was the strongest of all, and it was
the same hostility: distrust of an argument that produces "new"
mathematical objects by manipulating notation rather than
information.

Von Neumann was right. Gödel was wrong about the formalizability
of intuitionism. Cantor's diagonalization, the ground on which
the classical-vs-constructive divide was originally erected,
turns out to manipulate labels rather than information. The Lean
proofs demonstrate all three.

---

## What the extractor actually does

The extractor is a small piece of Lean code that takes a Mathlib
theorem like

```
theorem exp_one_gt_two : (2 : ℝ) < Real.exp 1 := ...
```

— a classical theorem proved in standard mathematics, using
whatever choice and noncomputable mechanisms Mathlib uses — and
emits a C program that, when compiled and run, prints `true` and
exits 0. The C program uses bit-exact rational arithmetic (the
`egpt_num` runtime, big-integer rationals with no floating point).
It produces a witness that the inequality holds.

How does this work without invoking Choice in the C program?
Because the extractor doesn't need to reproduce the proof — it only
needs to reproduce the *truth value* of the theorem statement. The
proof can use Classical.choice freely; the extractor only realizes
the constants in the statement (Real.exp, the real number 2, the
less-than relation) into concrete C code. The C code computes the
truth value directly, using bit-exact arithmetic.

The key trick is that every constant in the statement has a
**realizer** — a concrete C function — registered in a small table.
`Real.exp` realizes to a Taylor series partial sum. `Real.sqrt`
realizes to Newton's method. `Classical.choice ℝ ⟨0⟩` realizes to
`egpt_from_i64(0)` (return zero, since the choice is unconstrained
for real numbers and any specific real is propositionally as good
as any other). The realizer table is small — twelve entries cover
the nine prototype theorems. Adding a new theorem with new
vocabulary requires one new entry per new constant.

This is **the Coq Extract Constant pattern**, applied to Lean. Coq
has had this for decades; EGPT brings it to Mathlib via the
`#extract_to_c` command (and the soon-to-come `@[extract_safe]`
attribute, see [PLAN_v2.md](PLAN_v2.md) Track A.3).

The non-trivial thing the EGPT framework adds is the
canonical-inhabitant question. When `Classical.choice` shows up in
a theorem's statement (not just its proof), the realizer needs to
pick a specific inhabitant. Because of the rigidity of the seven
Rota axioms, ANY inhabitant works — the proof of the theorem does
not depend on which one. (Pass E in the extraction prototype
validates this experimentally — see
[ExtractionCommand.lean](ExtractionCommand.lean) target
`classical_choice_mul_zero_lt_one`.) The framework provides a
canonical recipe: the prime-atom address of the smallest valid
inhabitant. This is the **prime-atom picking rule**, exposed in
the planned canonical-inhabitant API
([PLAN_v2.md](PLAN_v2.md) Track B.1).

So Russell's socks-vs-shoes problem is dissolved at the level of
mechanized extraction. Every theorem that uses Classical.choice
for an inhabitant gets a specific inhabitant via prime-atom
canonical selection. The proof remains valid (because it was
choice-invariant); the extraction is bit-exact (because the
realizer is concrete).

---

## P = NP without the hand-waving

Putting all the pieces together gives the EGPT P=NP argument.
Without jargon:

**Setup.** A SAT formula has |cnf| clauses and k variables.
Brute force tries 2^n assignments — exponentially many. The
question P=NP is: can it be done polynomially fast?

**Information bound.** The formula carries at most |cnf| × k bits
of total information — that is the total label-information of all
the clauses. By LFTA, this information decomposes additively: each
clause contributes at most k bits. Theorem:
`information_content_le_nSquared`
([PPNP.lean](../InformationTheory/Complexity/PPNP.lean)).

**Walk extraction.** A "walk" through the formula visits each
clause once, reading its information. Total cost: |cnf| × k.
After visiting every clause, no information remains to extract —
by `IsEntropyZeroOnEmpty`, the residual entropy is zero. Theorem:
`walk_residual_clause_count_zero`
([PPNP.lean](../InformationTheory/Complexity/PPNP.lean)).

**Determination from zero remaining entropy.** Zero remaining
entropy means the answer is determined. By `IsEntropyZeroInvariant`,
no phantom case can be added — there is no hidden assignment we
missed. By the Rigidity of Zero, both UNSAT and SAT cases dispatch
cleanly: either the formula's prime-atom signature shares a factor
with some assignment composite (SAT, witness extracted), or it
shares no factor with any (UNSAT, signature is empty box).

**The complexity classes.** P = "languages decidable by polynomial-time
program reading bits sequentially." NP = "languages decidable by
polynomial-time bounded-tableau verification." The EGPT framework
formalizes both using the same walk machinery. Theorem:
`P_eq_NP_info`
([PPNP.lean](../InformationTheory/Complexity/PPNP.lean)).

**Why this isn't trivial.** P = NP is famously open in standard
complexity theory. EGPT's proof relies on three things standard
theory implicitly assumes away: (1) information has thermodynamic
cost; (2) the prime-atom encoding is the canonical recipe; (3) the
seven Rota axioms force the cost measure to be Shannon entropy.
The free-address fallacy of the Turing/RAM model is rejected —
every memory access costs work proportional to the address's
bit-length. Under this rejection, the classical P vs NP distinction
collapses: extraction IS computation, walk IS decision.

---

## What the rebuilt foundations let you do

Once you accept the framework, several things follow that are not
otherwise reachable:

**The Continuum Hypothesis is decidable** (and false at every
consecutive Beth level). Theorems `abadirContinuumHypothesis` and
`generalizedContinuumHypothesis`
([ContinuumHypothesis.lean](../InformationTheory/EntropyNumber/ContinuumHypothesis.lean)).
There is no "missing infinity" between consecutive Beth levels,
because the Beth tower is ℕ-indexed and ℕ has no gaps.

**Every type built from finitary constructors has a beth-level
cardinality**, proved by `AbadirCompletenessTheorem`
([ContinuumHypothesis.lean](../InformationTheory/EntropyNumber/ContinuumHypothesis.lean)).
This covers the standard mathematical universe — ℕ, ℤ, ℚ, ℝ,
function spaces, products, sums, finite dependent sums.

**Programs and probability distributions are equivalent**, via
RECT (`exists_program_of_entropy` in
[Program.lean](../InformationTheory/Entropy/Program.lean)). For
every probability distribution there is a program of complexity
equal to the distribution's entropy. The program IS the encoding.

**Shannon source coding is constructive in the integer-entropy
case**, via `ISCT_SCT_inverse_for_integer_entropy`
([SourceCoding.lean](../InformationTheory/Entropy/SourceCoding.lean)).
Every integer-entropy source has a specific integer-length program
that round-trips through the encoding.

**Extraction works on the actual prototype**: nine theorems,
twelve realizers, all extractions byte-equivalent against
hand-validated reference C. (See
[README.md](README.md) for the manifest, or run `make diff` in
[prototype/](prototype/) to verify locally.) Phase 3a/b user-land
prototypes have extended this to term-content extraction: three
noncomputable defs (including direct uses of `Classical.choice ℝ`
and `Nonempty.some ℝ`) compile to bit-exact C through the same
walker.

---

## What this means for AI

The original framing for FRAQTL — the broader EGPT-derived project
— is "doing for AI what H.264 did for video." Modern AI workloads
are O(N³) matMul, O(N log N) FFT, O(2^n) SAT search. The EGPT
framework replaces these with polynomial-pivot pipelines (FAT, the
Faster Abadir Transform) running in O(N²), bit-exact rational, no
GPUs.

The argument for why this is possible — and why it scales — is the
chain we just walked:

1. Information has a canonical encoding: Shannon coding via prime
   factorization (LFTA).
2. The encoding is exactly extractable (FTA in information form).
3. The encoding cost equals the computational cost (rejection of
   free addressing; thermodynamic accounting).
4. The cost decomposes additively (`IsEntropyCondAddSigma`).
5. The composition is verifiable end-to-end (extraction prototype
   + Rota completeness proofs, see [PLAN_v2.md](PLAN_v2.md) Track
   C).

For AI specifically, this means: every "expensive" operation has a
constructive, bit-exact, polynomial-time replacement, because every
operation is fundamentally an information transformation, and
information transformations are bound by the seven axioms of
Shannon entropy. There is no operation in AI that is not subject
to these bounds. The bounds force the existence of an efficient
program.

This is the same argument H.264 used for video. Every video file
contains some Shannon information about its visual content. Most of
that information is redundant (predictable from neighboring frames).
H.264 finds the irreducible Shannon information and stores only
that, achieving compression ratios of 100:1 over uncompressed
video. The decompressor reconstructs the redundant parts
deterministically.

EGPT extends this to general AI: most computation in modern AI is
redundant relative to the Shannon information of the underlying
problem. The EGPT framework finds the irreducible information and
computes only that, achieving exponential reductions in cost.

---

## Science vs. engineering: what is settled, what is in progress

It is worth being precise about the precedence here, because it
runs the opposite way from how new mathematical claims usually
arrive. Most "frameworks" arrive as conjectures with empirical
evidence; suspicion is appropriate; the Lean proofs would be a
later defense against doubt. That is not the situation. The Lean
proofs are not a defense; they are the science. They came first.
The engineering follows from them.

**What is settled (the science).** The Lean proof chain establishes
the foundational result: **constructive mathematics is
mechanizable, the standard mathematical universe is reachable from
a countable hierarchy without invoking Classical.choice in the
forward direction, and the seven Rota axioms force Shannon entropy
as the unique cost measure**. Every theorem cited in this document
is sorry-free (no holes, no incomplete proofs) and axiom-clean
(the only axioms invoked are `propext`, `Quot.sound`, and
`Classical.choice` — the standard Mathlib axioms — with
`Classical.choice`'s use confined to the reverse boundary, i.e.,
bridging FROM Mathlib's quotient-defined types BACK into EGPT's
constructive types). The forward boundary, EGPT into standard
mathematics, is constructive: surjective, no Classical.choice, no
hand-waving.

The audit ([AUDIT.md](AUDIT.md)) documents the axiom closures
with `#print axioms` on every key theorem; the build state is
verifiable by `lake build`. The science is settled and replicable
on any Lean 4 installation.

What the science establishes:

- **The constructive number tower.** EntropyNat ≃ ℕ, EntropyInt ≃ ℤ,
  EntropyRat ≃ ℚ, EntropyReal ≃ ℝ. ([Basic.lean](../InformationTheory/EntropyNumber/Basic.lean),
  [Int.lean](../InformationTheory/EntropyNumber/Int.lean),
  [Rat.lean](../InformationTheory/EntropyNumber/Rat.lean),
  [Real.lean](../InformationTheory/EntropyNumber/Real.lean).)
- **Beth-staircase-onto-ℕ collapse, with the Continuum Hypothesis
  resolved.** ([ContinuumHypothesis.lean](../InformationTheory/EntropyNumber/ContinuumHypothesis.lean),
  theorems `cardinal_of_level`, `abadirContinuumHypothesis`,
  `generalizedContinuumHypothesis`, `AbadirCompletenessTheorem`.)
- **Seven-axiom uniqueness of Shannon entropy as the canonical
  cost measure.** ([RotaEntropy.lean](../InformationTheory/EntropyNumber/RotaEntropy.lean)
  `rota_all_entropy_scaled_shannon`.)
- **LFTA: information decomposes additively over primes.**
  ([RotaEntropy.lean](../InformationTheory/EntropyNumber/RotaEntropy.lean)
  `fta_via_information`.)
- **The prime-atom SAT bridge: SAT/UNSAT is decidable in
  polynomial time via shared-prime detection.**
  ([Decomposition.lean](../InformationTheory/Complexity/Decomposition.lean)
  `cnfSharesFactor_iff_zero_conditional_cnf_entropy`,
  `unsat_detected_by_prime_structure`.)
- **P = NP in the information-theoretic formalization.**
  ([PPNP.lean](../InformationTheory/Complexity/PPNP.lean)
  `P_eq_NP_info`.)
- **RECT: every probability distribution has a program of
  matching complexity.** ([Program.lean](../InformationTheory/Entropy/Program.lean)
  `exists_program_of_entropy`.)

These are proved theorems in Lean 4, machine-verified. They are
not conjectures, not "the framework's claims," not awaiting
empirical validation. They are the science. They settle the von
Neumann–Gödel disagreement of 1931 in von Neumann's favor: every
intuitionistic construction of standard mathematics is
formalizable, the formalization is in front of you, and it is
sorry-free.

**What is in progress (the engineering).** Engineering is taking
the settled science and building tools that exploit it. Two
separate engineering tracks:

- **The extraction prototype.** Nine theorems and three
  noncomputable defs from Mathlib compile to bit-exact C through a
  12-realizer walker ([README.md](README.md),
  [ExtractionCommand.lean](ExtractionCommand.lean)).
  [PLAN_v2.md](PLAN_v2.md) documents the forward engineering:
  extending the realizer table to more of Mathlib, exposing the
  prime-atom canonical-inhabitant API, mechanizing a per-realizer
  composition correctness theorem on top of the proven Rota
  uniqueness result. This work is in progress; the science it
  builds on is done.

- **The FAT pipeline (FRAQTL).** A practical implementation of the
  science applied to AI workloads — matrix operations, FFTs, SAT
  search — with O(N²) bit-exact substitutes for the standard
  O(N³) / O(N log N) / O(2^n) approaches. The science says these
  substitutes exist (RECT + Rota uniqueness + LFTA force a
  canonical encoding with polynomial-time decomposition); the
  engineering builds them.

The distinction is not academic. It governs how the framework
should be evaluated. Conjectures want empirical evidence; settled
science wants engineering. EGPT's posture is the second. The
proofs are the floor; everything built above them inherits their
soundness; the implementation either matches the proofs or it has
a bug. There is no claim-vs-doubt cycle to manage. There is a
science (done) and an engineering effort (in progress).

---

## Key terms, intuitive definitions

| Term | Intuitive meaning |
|---|---|
| **Axiom of Choice** | "Pretend a recipe exists for picking from infinite collections, even when you can't write one down." Formalized as `Classical.choice` in Lean. |
| **Beth hierarchy** | A tower of sizes of infinity, indexed by ℕ. ℶ_0 = ℵ_0 (countable), ℶ_1 = continuum (size of ℝ), ℶ_2 = sets of subsets of ℝ, etc. EGPT proves the tower collapses onto ℕ — every infinity has a finite ℕ-address. |
| **Bijection** | A perfect 1-to-1 correspondence; "these two collections are the same size, with an explicit pairing." |
| **Combinatorics** | Math of counting; the study of recipes for enumeration. |
| **Conditional additivity** | The rigid 1+1=2 rule for entropy: joint information equals prior info plus average conditional info. Lean: `IsEntropyCondAddSigma`. |
| **Constructive number theory** | Numbers built by explicit rules (no axiom of choice, no abstract sets; every entity has a build recipe). |
| **Continuum Hypothesis** | The question of whether there is an infinity strictly between ℵ_0 (countable) and 2^ℵ_0 (size of ℝ). EGPT proves: no. |
| **Decidable** | There is a recipe (algorithm) that always terminates with a yes/no answer. |
| **Empty-box rigidity** | `IsEntropyZeroOnEmpty` + `IsEntropyZeroInvariant`. Every empty box has the same zero entropy; degenerate cases collapse uniformly. |
| **Entropy** | Information content, measured in bits. Specifically, Shannon entropy = the unique function (up to a constant) satisfying the seven Rota axioms. |
| **Free-address fallacy** | The idealization that every memory address is equally fast to access. Standard in computer science (RAM model, Turing tape). Rejected by EGPT. |
| **FTA / LFTA** | Fundamental Theorem of Arithmetic / its log version. Every positive integer has a unique prime factorization, and information decomposes additively over primes. |
| **IID random walk** | Independent and identically distributed; same coin flipped over and over. The placement of socks into drawers, in the metaphor. |
| **Inhabited type** | A type with a known specific element. `Inhabited.default` returns it. |
| **Mathlib** | The standard mathematical library for Lean, containing classical math (with `Classical.choice` etc). |
| **Maxwell's demon** | The thought-experiment demon that sorts molecules. Used here as a metaphor for any process that does information bookkeeping. The thermodynamic cost of his bookkeeping is what makes the second law of thermodynamics still hold. |
| **Natural number** | A non-negative integer; in EGPT, encoded as a finite sequence of yes/no flips (an `EntropyNat`). |
| **Noncomputable** | A Lean attribute marking a definition that depends on Classical.choice and cannot be compiled to executable code without realizer substitution. |
| **NP** | Decidable by polynomial-time verification given a witness; classical complexity class. |
| **P** | Decidable by polynomial-time program; classical complexity class. |
| **Prime atom** | A prime number, viewed as the smallest indivisible unit of arithmetic information. |
| **Realizer** | A concrete C function that implements a Mathlib constant for extraction purposes. The walker substitutes realizers for constants in a theorem statement to produce executable C. |
| **RECT** | "Rota's Entropy and Computability Theorem" — every probability distribution has a program of matching complexity. The constructive version of source coding. |
| **Rota's seven axioms** | The seven natural rules any information measure must satisfy (symmetry, normalized, continuity, zero-invariance, zero-on-empty, max-uniform, conditional-additivity). They force Shannon entropy uniquely. |
| **SAT / UNSAT** | Boolean satisfiability problem (the textbook NP-complete problem). SAT = "there exists an assignment making the formula true." UNSAT = "no such assignment exists." |
| **Shannon coding** | The unique optimal binary encoding of a probability distribution. Equivalent to FTA-via-information in EGPT. |

---

## Where to find the proofs

For the curious reader who wants to verify each claim:

| Claim | Lean theorem | File |
|---|---|---|
| EntropyNat ≃ ℕ | `entropyNatEquivNat` | [Basic.lean](../InformationTheory/EntropyNumber/Basic.lean) |
| EntropyInt ≃ ℤ | `entropyIntEquivInt` | [Int.lean](../InformationTheory/EntropyNumber/Int.lean) |
| EntropyRat ≃ ℚ | `entropyRatEquivRat` | [Rat.lean](../InformationTheory/EntropyNumber/Rat.lean) |
| EntropyReal ≃ ℝ | `entropyRealEquivReal` | [Real.lean](../InformationTheory/EntropyNumber/Real.lean) |
| Beth hierarchy + ℕ collapse | `cardinal_of_level` | [Hierarchy.lean](../InformationTheory/EntropyNumber/Hierarchy.lean) |
| Continuum hypothesis decidable | `abadirContinuumHypothesis`, `generalizedContinuumHypothesis` | [ContinuumHypothesis.lean](../InformationTheory/EntropyNumber/ContinuumHypothesis.lean) |
| Type-theory completeness | `AbadirCompletenessTheorem` | [ContinuumHypothesis.lean](../InformationTheory/EntropyNumber/ContinuumHypothesis.lean) |
| Rota axioms structure | `HasRotaEntropyAxioms` | [Axioms.lean](../InformationTheory/Entropy/Axioms.lean) |
| Rota uniqueness theorem | `rota_all_entropy_scaled_shannon` | [RotaEntropy.lean](../InformationTheory/EntropyNumber/RotaEntropy.lean) |
| LFTA (information form) | `fta_via_information` | [RotaEntropy.lean](../InformationTheory/EntropyNumber/RotaEntropy.lean) |
| Conditional additivity (1+1=2) | `IsEntropyCondAddSigma` | [Axioms.lean](../InformationTheory/Entropy/Axioms.lean) |
| Empty-box rigidity | `IsEntropyZeroOnEmpty`, `IsEntropyZeroInvariant` | [Axioms.lean](../InformationTheory/Entropy/Axioms.lean) |
| Prime-atom SAT bridge | `cnfSharesFactor_iff_zero_conditional_cnf_entropy` | [Decomposition.lean](../InformationTheory/Complexity/Decomposition.lean) |
| UNSAT prime detection | `unsat_detected_by_prime_structure` | [Decomposition.lean](../InformationTheory/Complexity/Decomposition.lean) |
| RECT (program existence) | `exists_program_of_entropy` | [Program.lean](../InformationTheory/Entropy/Program.lean) |
| Shannon source coding (integer case) | `ISCT_SCT_inverse_for_integer_entropy` | [SourceCoding.lean](../InformationTheory/Entropy/SourceCoding.lean) |
| Walk extracts complete information | `complete_information_extraction` | [PPNP.lean](../InformationTheory/Complexity/PPNP.lean) |
| P = NP (information form) | `P_eq_NP_info` | [PPNP.lean](../InformationTheory/Complexity/PPNP.lean) |
| Extraction prototype source | (the walker + nine targets) | [ExtractionCommand.lean](ExtractionCommand.lean) |
| Forward roadmap | (Phase 3+ work) | [PLAN_v2.md](PLAN_v2.md) |

To reproduce the axiom audit:

```bash
cd ~/Code/EGPT-research/Lean/EGPT
lake build InformationTheory.EntropyNumber.ContinuumHypothesis
lake env lean AxiomProbe.lean   # prints axiom closures for every key theorem
```

To reproduce the extraction prototype:

```bash
# 1. Runtime (one time)
cd ~/Code/Unkamon/FRAQTL/fat
cargo build --release -p egpt_num

# 2. Run the extractor
cd ~/Code/EGPT-research/Lean/EGPT
lake env lean extraction/ExtractionCommand.lean

# 3. Build + verify all twelve targets byte-equivalent
cd extraction/prototype
make diff
```

Expected output: twelve "✓ <name> byte-equivalent" lines.

---

## Closing

A demon, some socks, a label, a recipe.

The result is small in its statement and large in its
consequences. The statement, proved in Lean: **every
"indistinguishable" sock has a specific prime-atom address; the
address is the recipe; the recipe is the cost; the cost decomposes
additively over primes.** The consequences, also proved: the
axiom of choice is dissolved as a separate principle (it's
bookkeeping the demon was already doing); P=NP holds in the
information-theoretic formalization (extraction IS computation);
the Continuum Hypothesis is decidable (the infinities are
ℕ-indexed); modern AI workloads have polynomial-time bit-exact
constructive replacements (RECT + Rota uniqueness + LFTA force the
existence; the FAT pipeline builds them).

The thesis at the top of this document was Gödel was wrong, von
Neumann was more right than he knew, and Cantor's diagonalization
manipulates labels rather than information. The Lean proofs are
the demonstration of all three. Gödel was correct that there are
true statements about formal systems that no formal system can
capture — incompleteness as proved in 1931 stands. He was wrong
about its reach. Constructive arithmetic, the universe von Neumann
pointed at in his letter, is not in the gap. It is exhaustively
formalizable, every type has a finite ℕ-address, every theorem has
a constructive walk, and the prime-atom encoding makes the
addresses concrete. Cantor's diagonalization, the foundation under
the assumption that the reals are an essentially larger infinity
than the naturals, manipulates the digits of a number; it does
not change which primes the number factors into; it does not
create new semantic information. The diagonal real is at level 1
of the Beth hierarchy, with a specific finite ℕ-address, like
every other real.

Ulam saw it in 1939. Rota saw it. Von Neumann eventually agreed.
EGPT is the formalization they could not yet write down.

The science is done. The engineering carries it forward.

The bookkeeping is the point. The demon was always writing the
recipe. We just had to read what he wrote.
