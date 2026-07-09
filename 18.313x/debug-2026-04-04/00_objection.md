# Step 0: Team Godel's Objection

**Submitted by:** Godel (main thread) + Georg (user)
**Mode:** game
**Round:** OPENING

---

## The Constructive Extraction Gap

**Summary:** The proof of `P_eq_NP_info` claims constructivity (no `Classical.choice`), which by Curry-Howard should entail an extractable polynomial-time algorithm for SAT. But no such algorithm has been demonstrated. The only code that allegedly resolved the smuggled-search problem (`computeTableauDecidable`) was deleted. What remains requires a candidate assignment as input. The attempt to exhibit the algorithm (Walk.lean) failed on counterexamples.

**Specific citations:**

1. `P_eq_NP_info` (PPNP.lean:791) uses only `propext` and `Quot.sound` — fully constructive. By the propositions-as-types correspondence, this proof term IS a program.

2. `computeTableauDecidable` (VerifierDecidableWS.lean) — the function that took only `cnf` with no witness parameter — was **deleted**. C44 acknowledges this.

3. `computeTableau?` (Tableau.lean:251) takes `(cnf : SyntacticCNF k) (candidate : Vector Bool k)` — it requires a candidate assignment. It is a polynomial VERIFIER, not a polynomial SOLVER.

4. Walk.lean v2 failed (F8: counterexample `not x0 or x2, not x1 or not x2`). Walk.lean v3 failed (F9: Test 7). Walk.lean is NOT imported by the proof chain (C41).

5. The defense's IVT analogy (IN33) is inapposite: the IVT is a classical existence proof; `P_eq_NP_info` claims to be constructive. A constructive proof of P=NP should extract to a polynomial SAT solver, not merely assert one exists.

**The challenge:** Either exhibit the polynomial algorithm that the constructive proof term encodes, or explain why a constructive proof of P=NP does not entail an extractable polynomial SAT solver — which would undermine the claim that "the address IS the map."

**Targeted consensus points:** C38 (smuggled-search resolved — but the resolution was deleted), C40 (polynomial bound on reading — but no demonstrated reader), C41 (Walk.lean is engineering — but this deflects the constructive extraction question).
