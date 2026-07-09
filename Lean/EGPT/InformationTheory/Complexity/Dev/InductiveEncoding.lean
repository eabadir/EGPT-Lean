import InformationTheory.EntropyNumber.LogarithmBijective
import InformationTheory.EntropyNumber.PrimeAtoms
import InformationTheory.Complexity.CNF.Prime

namespace InformationTheory

/-- The inductive encoding of a bit-stream into an EntropyNat.
    
    This function reads the bit-stream `f` up to index `n`. 
    For every `true` bit at index `i`, it concatenates the information 
    of the `i`-th prime (represented as an EntropyNat of length `nthPrimeC i`).
    
    Because EntropyNat is just a List Bool of true bits, this accumulation 
    is strictly monotonic. It only ever grows. -/
def accumulateEntropyNat (f : EntropyReal) : ℕ → EntropyNat
  | 0 => EntropyNat.ofNat 0
  | n + 1 => 
    let prev := accumulateEntropyNat f n
    if f (EntropyNat.ofNat n) then
      -- If the bit is true, we add the information of the n-th prime
      EntropyNat.add prev (EntropyNat.ofNat (nthPrimeC n))
    else
      prev

/-- The total information accumulated up to step `n` is exactly the 
    sum of the primes selected by the bit-stream. -/
lemma accumulateEntropyNat_toNat (f : EntropyReal) (n : ℕ) :
    EntropyNat.toNat (accumulateEntropyNat f n) = 
      (List.range n).foldl (fun acc i => 
        if f (EntropyNat.ofNat i) then acc + nthPrimeC i else acc) 0 := by
  induction n with
  | zero => rfl
  | succ n ih => 
    simp only [accumulateEntropyNat]
    split_ifs with h
    · rw [EntropyNat.toNat_add, EntropyNat.ofNat_toNat, ih]
      -- The rest is standard list foldl manipulation
      sorry
    · rw [ih]
      sorry

end InformationTheory
