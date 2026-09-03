import Mathlib.Logic.Equiv.Defs -- For Equiv
import Mathlib.Logic.Equiv.Basic   -- Equiv API
import Mathlib.Logic.Equiv.Nat     -- intEquivNat, natSumNatEquivNat, …
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Real.Cardinality
import Mathlib.Control.Random
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Finset.Basic
import Archive.Basic

open List


namespace EGPT


/-!
# EGPT Number Theory: Numbers Are Physics
The core axiom of EGPT is that particles move according to a RandomWalk - as they move forward in time step by step, they make a "coin flip" decision to move up or down such as heads = move up, tails = move down. If each heads/tails outcome is recorded we can use binary string of 1's and 0's to capture their path. In Lean we use List Bool as the fundamental type for this binary recording. When the path is walked the next step is independent of history (except the last state/position) - the next step depends only on the current position and the next coin flip. In probability theory each step on the path is said to be "event" in an independent and identically distributed (IID) process, the path formation is called a "memoryless stochastic process" (aka a Markov Process), and the resultant path is called a Markov Chain (or Random Walk).

In short, to describe particle movement and interactions the core encoding we use is a `List Bool`.
-/

def PathCompress_AllTrue (L : List Bool) : Prop := ∀ x ∈ L, x = true
abbrev ParticlePath := { L : List Bool // PathCompress_AllTrue L }


class IIDParticleSource (α : Type) where
  stream : ℕ → α

class CanonicalIIDParticleSource extends IIDParticleSource (List Bool) where
  -- The canonical IID source is one that produces a symmetric and sorted path.
  -- This means that the order of choices does not matter, only the counts of `true` and `false`.
  -- For example, `[true, true, false, false]` is the canonical representation of the path `[true, false, true, false]`.
  toCanonical : ∀ (n : ℕ), stream n = (List.replicate n true ++ List.replicate n false).mergeSort (fun a b => !a && b)

/-- The canonical representation of a particle path sampled from an IIDParticleSource is symmetric and sorted with 1s first. For example `[true, true, false, false]` is the canonical representation of the path `[true, false, true, false]`. This means that the order of choices does not matter, only the counts of `true` and `false` do. -/
def CannonicalSymmetricParticlePath := List Bool

/-- A non-canonical particle path is just the list of movements describing a random walk -/
abbrev RandomWalkPath := List Bool


/-- Calculates the number of `true` choices (e.g., "up-steps") in a path. -/
def numOnes (p_path : RandomWalkPath) : ℕ :=
  p_path.count true

abbrev ParticlePosition := ℤ
/--
Calculates the "position" of a particle after `t` steps,
defined as (#trues - #falses).
-/
def calcParticlePosition (initial_pos : ℤ) (p_path : RandomWalkPath) : ℤ :=
  let ones := numOnes p_path
  let path_len := p_path.length
  let zeros := path_len - ones
  let mag_initial := Int.natAbs initial_pos
  let (ones', zeros') :=
    if initial_pos >= 0 then
      (ones + mag_initial, zeros)
    else
      (ones, zeros + mag_initial)
  (ones' : ℤ) - (zeros' : ℤ)




def RandomWalkFromPosition (pos : ParticlePosition): RandomWalkPath :=
  let sign_bit := decide (pos >= 0)
  let magnitude := Int.natAbs pos
  List.append [sign_bit] (List.replicate magnitude true)

/-- A single instruction/choice, represented by a Bool.
    Corresponds to one "bit" of choice from an i.i.d. source
    or one step in a binary decision tree. -/
def ComputerInstruction := Bool

/-- A sequence of choices/instructions forming the "program" or "path description".
    This is conceptually the Turing Machine's input tape. -/
def ComputerTape := List ComputerInstruction

/-- A computer program is represented as a tape of binary instructions. -/
abbrev ComputerProgram := ComputerTape

/-- Program length is tape length by definition. -/
@[simp] theorem ComputerProgram.length_eq (prog : ComputerProgram) : prog.length = (prog : ComputerTape).length := rfl

/-- Concatenating two programs yields a program with additive length. -/
@[simp] theorem ComputerProgram.append_length (p q : ComputerProgram) :
    (List.append p q).length = p.length + q.length := by
  simp

-- EGPT — Electronic Graph Paper Theory
-- Copyright (C) 2026 Essam Abadir
-- Licensed under the DeSciX Community Source Code License (DCSL) v1.0.
-- See LICENSE and DeSciX_Community_License_v1.pdf in the repository root.
-- Provided WITHOUT ANY WARRANTY. See the DCSL for details.
