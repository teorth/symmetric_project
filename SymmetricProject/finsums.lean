-- This is not part of the project, but was written in order for to practice manipulation of finite sums in Lean.

import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic.Linarith

open Finset
open BigOperators

example (n : ℕ) : ∑ t in range n, 2*t + n = n * n := by
  induction' n with n hn
  · simp
  · simp [Finset.sum_range_succ]
    linarith


