import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Init.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.MeanInequalities
import SymmetricProject.esymm_basic
import SymmetricProject.attainable
import SymmetricProject.stirling
import SymmetricProject.positivity_ext

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
lemma prelim_bound {n : ℕ} {s : ℕ → ℝ} (h1 : n > 2) (h2 : attainable n s) : |s n|^((n:ℝ)⁻¹) ≤ ((2:ℝ) * n)^((2:ℝ)⁻¹) * max |s 1| (|s 2|^((2:ℝ)⁻¹))  := by
  set X := max |s 1| (|s 2|^((2:ℝ)⁻¹))
  rcases h2 with ⟨ x, hx ⟩
  calc
    |s n|^((n:ℝ)⁻¹) = (abs (∏ j in range n, x j^2)^((n:ℝ)⁻¹))^((2:ℝ)⁻¹) := by
      rw [<- rpow_mul, mul_comm, rpow_mul]
      congr
      have := hx n (by linarith)
      simp at this
      rw [<- abs_rpow_of_nonneg, <- finset_prod_rpow, <- this, abs_prod, abs_prod]
      apply prod_congr rfl
      intro i _
      rw [<-sq_abs, (show |x i|^(2:ℕ) = |x i|^(2:ℝ) by norm_cast), <-rpow_mul]
      simp
      . positivity
      . intro i _; positivity
      . positivity
      . positivity
      . positivity
    _ ≤ (abs (∑ j in range n, x j^2) / n)^((2:ℝ)⁻¹) := by
      apply rpow_le_rpow
      . positivity
      . rw [abs_prod, abs_of_nonneg (by positivity), <- finset_prod_rpow, sum_div]
        have : ∑ j in range n, x j^2 / n = ∑ j in range n, ((n:ℝ)⁻¹)* |x j^2| := by
          congr
          ext j
          field_simp
        rw [this]
        apply geom_mean_le_arith_mean_weighted
        . intro i _; positivity
        . rw [sum_const]; simp; field_simp
        . intro i _; positivity
        . intro i _; positivity
      positivity
    _ ≤ (((esymm n 1 x)^2 + 2 * abs (esymm n 2 x))/n)^((2:ℝ)⁻¹) := by
      gcongr
      rw [newton_two]
      apply le_trans (abs_sub _ _) _
      gcongr
      . simp
      rw [abs_mul]
      simp
    _ ≤ ((2:ℝ) * n)^((2:ℝ)⁻¹) * X := by
      rw [hx 1 (by linarith), hx 2 (by linarith), <- rpow_le_rpow_iff _ _ (show 0 < 2 by norm_num), <- rpow_mul, mul_rpow, <-rpow_mul]
      simp
      rw [div_le_iff, (show (2:ℝ) * n * (X ^ 2) * n = (X * n)^2 + (n * X)^2 by ring), <- sq_abs (s 1 * n), abs_mul]
      simp
      gcongr
      . apply le_max_left
      . rw [mul_pow, abs_mul, mul_comm |s 2| _, <-mul_assoc]
        gcongr
        . have := choose_le (show 2 ≤ n by linarith)
          rw [(show 2! = 2 by norm_num)] at this
          simp
          field_simp at this
          linarith
        rw [<- rpow_le_rpow_iff _ _ (show 0 < (2:ℝ)⁻¹ by norm_num), (show X^(2:ℕ) = X^(2:ℝ) by norm_cast), <- rpow_mul]
        simp
        all_goals {positivity}
      all_goals {positivity}

/- the reversed preliminary bound
|s_n|^(1/n) ≤ max( (2n)^{1/2(n-1)} |s_{n-1}|^{1/n-1}, (2n)^{2/2(n-2)} |s_{n-2}|^(1/n-2))
-/
lemma prelim_bound_rev {n : ℕ} {s : ℕ → ℝ} (h1 : n > 2) (h2 : attainable n s) : |s n|^((n:ℝ)⁻¹) ≤ max (((2:ℝ) * n)^((1:ℝ)/(2*(n-1))) * |s (n-1)|^((n-1:ℝ)⁻¹)) (( (2:ℝ)*n)^((2:ℝ)/(2*(n-2))) * |s (n-2)|^((n-2:ℝ)⁻¹))  := by
  by_cases hsn : s n = 0
  . simp [hsn]
    left
    rw [zero_rpow]
    all_goals {positivity}
  let s' := fun k ↦ s (n - k) / s n
  have bound := prelim_bound h1 (attainable_reflect h2 hsn)
  have hs0 := attainable_zero_eq_one h2
  rw [<-div_le_iff'] at bound
  . simp [hs0] at bound ⊢
    clear h2 hs0 s'
    rw [abs_div, abs_div, abs_inv, <-rpow_neg_one, <-rpow_mul, div_rpow] at bound
    simp at bound
    . rcases bound with bound | bound
      . left
        have h1' : (0:ℝ) < (n:ℝ)- 1 := by
          rw [lt_sub_iff_add_lt]; simp; linarith
        have : (0:ℝ) < (n-1:ℝ)⁻¹ := by
          rwa [inv_pos]
        rw [div_le_div_iff] at bound
        nth_rewrite 2 [<- rpow_one |s n|] at bound
        rw [<-rpow_add, <-rpow_le_rpow_iff _ _ this, <-rpow_mul, mul_rpow] at bound
        convert bound using 1
        . congr
          have : 0 < (n:ℝ) * ((n:ℝ)-1) := by
            apply mul_pos; linarith; assumption
          field_simp [this]; ring
        rw [mul_comm, <- rpow_mul]
        congr 2
        ring
        all_goals {positivity}
      right
      have h1' : (0:ℝ) < (n:ℝ)- 2 := by
        rw [lt_sub_iff_add_lt]; norm_cast
      have : (0:ℝ) < 2*(n-2:ℝ)⁻¹ := by
        positivity
      rw [div_le_div_iff, <-rpow_add,<-rpow_le_rpow_iff _ _ this, <-rpow_mul, mul_rpow] at bound
      convert bound using 1
      . congr
        field_simp [this]; ring
      rw [mul_comm, <- rpow_mul, <- rpow_mul]
      congr 2
      . field_simp [h1']
      field_simp [h1']
      all_goals {positivity}
    all_goals {positivity}
  positivity
