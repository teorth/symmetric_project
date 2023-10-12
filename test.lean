import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric

open MvPolynomial

-- the k^th elementary symmetric polynomial in n real variables

def esymm (n : ℕ) (k : N): MvPolynomial (fin n) ℝ := 
  MvPolynomial.esymm (fin n) ℝ k

#check fin 





