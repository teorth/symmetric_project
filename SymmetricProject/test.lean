import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic

-- I have ended up not using the mathlib library for symmetric polynomials due to various technical type casting / functional programming issues .  A future project would be refactor the arguments here using that library.

--import Mathlib.RingTheory.MvPolynomial.Basic
--import Mathlib.RingTheory.MvPolynomial.Symmetric
--open MvPolynomial


-- basic facts about the set "set_binom n k" (or $\binom{[n]}{k}$) of k-element subsets of $[n] = \{0, \dots, n-1\}$.

import SymmetricProject.binomial

open Finset
open BigOperators

-- "esymm n k" is the k^th elementary symmetric polynomial $S_{n,k}(x)$ in the first n of an infinite number $x_1, x_2, \dots$ of real variables 

def esymm (n : ℕ) (k : ℕ) (x : ℕ → ℝ): ℝ := ∑ A in set_binom n k, (∏ i in A, x i)

-- TODO: relate this function to MvPolynomial.esymm

-- TODO: prove the recursive identity
-- $S_{n+1,k+1}(x) = S_{n,k+1}(x) + x_k S_{n,k}(x)$

-- TODO: Use this identity and induction on n to prove that
-- $\prod_{i=1}^n (z - x_i) = \sum_{k+l=n} (-1)^k S_{n,k}(x) z^l$






