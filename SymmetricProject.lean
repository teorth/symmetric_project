import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import SymmetricProject.binomial
import SymmetricProject.esymm_basic
import SymmetricProject.esymm_generating
import SymmetricProject.roots_deriv
import SymmetricProject.attainable

/- hack to avoid the real powers bug -/
local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

open Finset

/- The purpose of this project is to formalize the results in https://arxiv.org/abs/2310.05328 , hereafter referred to as "the paper".  In particular, to prove the following result: -/


theorem main_theorem : ∃ C : ℝ, (C > 0) ∧ ∀ n : ℕ, ∀ s : ℕ → ℝ, attainable n s → ∀ l ∈ range (n+1), ∀ k ∈ range l, k ≥ 1 →  (s l)^((1:ℝ)/l) ≤ C * ((l:ℝ)/k)^((1:ℝ)/2) * (((s k)^((1:ℝ)/k)) + ((s (k+1))^((1:ℝ)/(k+1))) ) := by
  sorry

