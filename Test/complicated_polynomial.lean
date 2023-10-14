-- An overly complicated way to handle sums like $\sum_{k=0}^n (-1)^k S_{n,k}(x) z^{n-k}$

import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Init.Order.Defs
import Init.Data.Nat.Basic

-- basic facts about the expression "esymm n k x" (or $S_{n,k}(x)$) - the k^th elementary symmetric polynomial of the first n variables of an infinite sequence x of real variables
import SymmetricProject.esymm_basic


open Finset
open BigOperators


  
open Polynomial

-- TODO: Use Pascal identity and induction on n to prove that
-- $$\prod_{i=1}^n (z - x_i) = \sum_{k=0}^n (-1)^k S_{n,k}(x) z^{n-k}$$

-- first need a preliminary lemma that the expression
-- $$ \sum_{k ≤ n} 1_{n-k = l} f(k) $$
-- equals $f(n-l)$ when $l < n$ and $0$ otherwise.
lemma downsum (n : ℕ) (l : ℕ) (f : ℕ → ℝ) : ∑ k in range (n + 1), (if n-k = l then f k else 0) = if l ≤ n then f (n-l) else 0 := by
  rcases le_or_gt l n with h | h
  . simp [h] 
    have nln : n-l ∈ range (n+1) := by
      simp [h]
      have h2 : n-l ≤ n := by apply Nat.sub_le
      linarith
    rw [<- add_sum_erase _ _ nln]
    have nnl : n - (n - l) = l := by 
      have h2 : l + (n - l) = n := by 
        apply Nat.add_sub_of_le h
      nth_rewrite 1 [<- h2]
      simp
    simp [nnl]
    apply sum_eq_zero
    intros k hk
    simp 
    intro nkl
    have hnl : k ≠ n - l := by apply  ne_of_mem_erase hk
    have kln : k ∈ range (n+1) := by 
      apply mem_of_mem_erase hk
    rw [mem_range] at kln
    have kln' : k ≤ n := by linarith
    contrapose! hnl
    clear f nln nnl hk hnl kln
    have kln : l + k = n := by 
      rw [<- nkl]
      apply Nat.sub_add_cancel kln'
    rw [<- kln]
    symm
    apply Nat.add_sub_cancel_left
  have h' : ¬ l ≤ n := by linarith
  simp [h'] 
  apply sum_eq_zero
  intro k hk
  have h : ¬ n - k = l := by
    contrapose! h'
    rw [<- h']
    apply Nat.sub_le
  simp [h]

theorem esym_genfn (n : ℕ) (x : ℕ → ℝ): ∏ i in (range n), (X - C (x i)) = ∑ k in range (n+1), monomial (n-k) ((-1) ^ ↑k * esymm n k x) := by
  induction' n with n hn
  . simp [esymm, set_binom]
  rw [Nat.succ_eq_add_one, prod_range_succ, hn, <- coeff_inj, mul_sub, sum_mul]
  ext l
  simp [finset_sum_coeff, coeff_monomial]  
  simp [downsum]

  sorry  







