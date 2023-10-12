import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric

open MvPolynomial

-- real_esymm n k is the k^th elementary symmetric polynomial in n real variables
noncomputable def real_esymm (n : ℕ) (k : ℕ): MvPolynomial (Fin n) ℝ := 
  esymm (Fin n) ℝ k

variable {n : ℕ}
variable {x : Fin n → ℝ}

-- S_0(x) = 1
example : eval x (real_esymm n 0) = 1 := by 
  simp [real_esymm]

-- alternate proof:
--  rw [real_esymm, esymm_zero, ← C_1, eval_C]





