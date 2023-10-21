import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Init.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real


/- hack to avoid the real powers bug -/
local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

/- The purpose of this file is to prove the some "cheap" Stirling bounds for factorial and binomial coefficients.
-/

open Real
open Nat

lemma factorial_le {n : ℕ} : factorial n ≤ n^n := by
  sorry

lemma factorial_ge {n : ℕ} : factorial n ≥ n^n / exp n := by
  sorry

lemma choose_le {n : ℕ} {k : ℕ} (h : k ≤ n) : choose n k ≤ n^k / factorial k := by
  sorry

lemma choose_ge {n : ℕ} {k : ℕ} (h : k ≤ n) : choose n k ≥ n^k / k^k := by
  sorry
