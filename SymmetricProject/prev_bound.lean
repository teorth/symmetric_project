import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Init.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import SymmetricProject.esymm_basic
import SymmetricProject.attainable

/- hack to avoid the real powers bug -/
local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

/- The purpose of this file is to prove the bound

|s_l|^(1/2) ≪ l^(1/2) max |s_k|^(1/k), |s_{k+1}|^(1/k+1)

established by Gopalan-Yehudayoff.
-/

open Real
open Nat
open Finset
open BigOperators

/- the preliminary bound
|s_n|^(1/n) ≤ 2n max( |s_1|, |s_2|^(1/2))
-/
lemma prelim_bound {n l : ℕ} {s : ℕ → ℝ} (h1 : n > 2) (h5 : attainable n s) : |s n|^((1:ℝ)/n) ≤ ((2:ℝ) * n)^((1:ℝ)/2) * max |s 1| (|s 2|^((1:ℝ)/2))  := by
  rcases h5 with ⟨ x, hx ⟩
  calc
    |s n|^((1:ℝ)/n) = (abs (∏ j in range n, x j^2)^((1:ℝ)/n))^((1:ℝ)/2) := by
      rw [<- rpow_mul, mul_comm, rpow_mul]
      congr
      rw [<- abs_rpow_of_nonneg, <- finset_prod_rpow]

      sorry
      all_goals {positivity}
    _ ≤ (abs (∑ j in range n, x j^2) / n)^((1:ℝ)/2) := by
      sorry
    _ ≤ (((esymm n 1 x)^2 + 2 * abs (esymm n 2 x))/n)^((1:ℝ)/2) := by
      sorry
    _ ≤ ((2:ℝ) * n)^((1:ℝ)/2) * max |s 1| (|s 2|^((1:ℝ)/2)) := by
      sorry
