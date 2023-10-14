-- This is not part of the project, but was written in order for to practice manipulation of finite sums in Lean.

import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic

open Finset
open BigOperators

-- as predicted, subtraction is somewhat of a pain to work with in the natural numbers, so rewriting everything in totally "positive" form is useful

example (n : ℕ) : ∑ t in range n, 2*t + n = n * n := by
  induction' n with n hn
  . simp
  simp [Finset.sum_range_succ]
  linarith
  

--example (A : Finset ℕ) (f: ℕ → ℕ) : ∑ n in image succ A, f n = ∑ n in A, f (succ n) := by
--  apply sum_image
--  intros x hx y hy hxy
  