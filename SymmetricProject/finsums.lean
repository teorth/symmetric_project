import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric
import Mathlib.Algebra.BigOperators.Basic

open MvPolynomial
open Finset
open BigOperators

example (n : ℕ) : ∑ t in range n, 2*t + n = n * n := by
  induction' n with n hn
  simp
  simp [Finset.sum_range_succ, hn]
  rw [Nat.succ_eq_add_one]
  have h : (∑ t in range n, 2 * t) + 2 * n + (n + 1) = (∑ t in range n, 2 * t) + n + n + (n + 1) := by ring 
  rw [h, hn]
  ring
  
