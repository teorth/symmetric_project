-- basic facts about the expression "esymm n k x" (or $S_{n,k}(x)$) - the k^th elementary symmetric polynomial of the first n variables of an infinite sequence x of real variables

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Init.Order.Defs
import Init.Data.Nat.Basic

-- I have ended up not using the mathlib library for symmetric polynomials due to various technical type casting / functional programming issues .  A future project would be refactor the arguments here using that library.

--import Mathlib.RingTheory.MvPolynomial.Basic
--import Mathlib.RingTheory.MvPolynomial.Symmetric
--open MvPolynomial

-- basic facts about the set "set_binom n k" (or $\binom{[n]}{k}$) of k-element subsets of $[n] = \{0, \dots, n-1\}$.
import SymmetricProject.binomial

open Finset
open BigOperators

-- "esymm n k" is the k^th elementary symmetric polynomial $S_{n,k}(x)$ in the first n of an infinite number $x_1, x_2, \dots$ of real variables.  We define this polynomial directly as a sum of monomials, instead of using MvPolynomial.esymm
def esymm (n : ℕ) (k : ℕ) (x : ℕ → ℝ): ℝ := ∑ A in set_binom n k, (∏ i in A, x i)

-- TODO: replace the reals by a more general commutative ring R
-- TODO: relate this function to MvPolynomial.esymm

-- The Pascal identity for esymm:
-- $$S_{n+1,k+1}(x) = S_{n,k+1}(x) + S_{n,k}(x) x_n$$

theorem esymm_pascal (n : ℕ) (k : ℕ) (x : ℕ → ℝ): esymm (n+1) (k+1) x = esymm n (k+1) x + (esymm n k x) * x n := by
  let X := esymm (n+1) (k+1) x
  let Y := esymm n (k+1) x
  let Z := esymm n k x
  show X = Y + Z * x n
  have h : X = esymm (n+1) (k+1) x := by rfl
  rw [esymm, set_pascal, sum_disjUnion (set_pascal_disjoint n k)] at h
  let monom := fun (A:Finset ℕ) => (∏ i in A, x i)
    
  let W := ∑ A in image (insert n) (set_binom n k), monom A

  have h2: X = Y + W := by 
    rw [h]
    simp [esymm]
  rw [h2]
  congr
  clear h h2 X Y 

  have h3 : W = ∑ A in (set_binom n k), monom (insert n A) := by
    apply sum_image
    apply insert_binom_inj n k

  rw [h3]
  dsimp [esymm]
  rw [sum_mul]
  clear Z W monom h3
  
  have h4 : ∀ A ∈ set_binom n k, ∏ i in insert n A, x i = (∏ i in A, x i) * x n := by
    intro A hA
    rw [prod_insert (set_binom_no_n n k A hA)]
    ring
  rw [sum_congr rfl h4]
  
