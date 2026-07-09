-- Aggregator: bijection-chain tour (CNF → Polynomial → Matrix legs).
-- Load-bearing P=NP capstones do not require this module; import it for
-- the full `{propext, Quot.sound}` Equiv tower and operational fixtures.
import InformationTheory.Isomorphisms.CNF.CNFPolynomialSystem
import InformationTheory.Isomorphisms.CNF.CNFAsEntropyNat
import InformationTheory.Isomorphisms.CNF.CNFPolynomialRoots
import InformationTheory.Isomorphisms.Polynomial.PolynomialAsNat
import InformationTheory.Isomorphisms.Polynomial.RealPolynomialAsReal
import InformationTheory.Isomorphisms.Polynomial.StandardRealPolynomialAsReal
import InformationTheory.Isomorphisms.Polynomial.PolynomialDense
import InformationTheory.Isomorphisms.Polynomial.PolynomialValueRep
import InformationTheory.Isomorphisms.Polynomial.PolynomialSystemAsNat
import InformationTheory.Isomorphisms.Polynomial.RealPolynomialSystemAsReal
import InformationTheory.Isomorphisms.Matrix.RealMatrixAsReal
import InformationTheory.Isomorphisms.Matrix.StandardRealMatrixAsReal
import InformationTheory.Isomorphisms.Polynomial.OperationalBijectionChain
import InformationTheory.Isomorphisms.Matrix.PolynomialMatrixAsNat
import InformationTheory.Isomorphisms.Matrix.GemmInputAsNatPair
import InformationTheory.Isomorphisms.Matrix.RealMatrixPrimeFactorization
import InformationTheory.Isomorphisms.Matrix.MatrixPolynomialRoots
import InformationTheory.Isomorphisms.BijectionFixtures
