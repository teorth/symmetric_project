import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
--import Mathlib.RingTheory.MvPolynomial.Basic
--import Mathlib.RingTheory.MvPolynomial.Symmetric
import Mathlib.Algebra.BigOperators.Basic

import SymmetricProject.binomial

--open MvPolynomial
open Finset
open BigOperators

-- real_esymm n k is the k^th elementary symmetric polynomial in n real variables (but it is convenient to define x_i for all i)
def real_esymm (n : ℕ) (k : ℕ) (x : ℕ → ℝ): ℝ := ∑ A in set_binom n k, (∏ i in A, x i)

-- theorem real_esymm_explicit (n : ℕ) (k : ℕ) (x : (Fin n) → ℝ): eval x (real_esymm n k) = ∑ A in set_binom n k, (∏ i in A, x i) := by
--  sorry

--theorem esymm_recursion (n : ℕ) (k : ℕ) (x : Fin (n+1) → ℝ) (x': Fin n → ℝ) (h: ∀ m : Fin n, x m = x' m): eval x (real_esymm (n+1) (k+1)) = eval x' (real_esymm n (k+1)) + (x n) * (eval x' (real_esymm n k))
-- := by
--  rw [real_esymm, esymm_eq_sum_monomial]--
--  sorry


-- S_0(x) = 1
-- example : eval x (real_esymm n 0) = 1 := by 
--  simp [real_esymm]





