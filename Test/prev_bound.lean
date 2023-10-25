import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Init.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import SymmetricProject.esymm_basic
import SymmetricProject.attainable
import SymmetricProject.stirling
import SymmetricProject.positivity_ext
import SymmetricProject.prev_bound_1

set_option maxHeartbeats 400000

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



/-- the bound two displays after (2.1) --/
lemma iterated_rev {n k : ℕ} {s : ℕ → ℝ} (h2 : attainable n s) (h3 : k+3 ≤ n) (h4 : 0 < k): |s n|^((n:ℝ)⁻¹) ≤ max (((2:ℝ) * n)^((Real.log (n-1) - Real.log (n-k-1))*(n-k)/(2*k)) * |s k|^((k:ℝ)⁻¹)) (( (2:ℝ)*n)^((Real.log (n-1) - Real.log (n-(k+1:ℕ)-1))*(n-(k+1))/(2*(k+1))) * |s (k+1)|^(((k+1:ℕ):ℝ)⁻¹)) := by
  have : n > (0:ℝ) := by norm_cast; linarith
  by_cases hsn: s n = 0
  . simp [hsn]
    left
    rw [zero_rpow]
    all_goals {positivity}
  let s' := fun k ↦ s (n - k) / s n
  have bound := iterated (attainable_reflect h2 hsn) h3
  simp [attainable_zero_eq_one h2] at bound ⊢
  rw [abs_inv, abs_div, abs_div, div_rpow, div_rpow, inv_rpow, mul_div, mul_div] at bound
  . rcases bound with bound | bound
    . left
      have h0 : n - (n-k) = k := by
        suffices : k + (n-k) = n
        . nth_rewrite 1 [<-this]
          apply Nat.add_sub_cancel
        apply Nat.add_sub_of_le
        linarith
      have h5 : 0 < (n:ℝ)-k := by
        simp; norm_cast; linarith
      have : 0 < ((n:ℝ)-k)/k := div_pos h5 (show (0:ℝ) < k by norm_cast)
      rw [le_div_iff, inv_mul_eq_div, <-rpow_sub, <- rpow_le_rpow_iff _ _ this, <-rpow_mul, mul_rpow, <-rpow_mul, <-rpow_mul, h0] at bound
      . convert bound using 2
        . field_simp; ring
        . congr 1; field_simp
        congr 1; field_simp
      all_goals {positivity}
    right -- could possibly shorten this proof by judicious use of swap, let, all_goals, and try
    have h0 : n - (n-(k+1)) = k+1 := by
      suffices : k+1 + (n-(k+1)) = n
      . nth_rewrite 1 [<-this]
        apply Nat.add_sub_cancel
      apply Nat.add_sub_of_le
      linarith
    have h5 : 0 < (n:ℝ)-(k+1) := by
      simp; norm_cast; linarith
    have : 0 < ((n:ℝ)-(k+1))/(k+1) := div_pos h5 (show (0:ℝ) < k+1 by norm_cast; linarith)
    rw [le_div_iff, inv_mul_eq_div, <-rpow_sub, <- rpow_le_rpow_iff _ _ this, <-rpow_mul, mul_rpow, <-rpow_mul, <-rpow_mul, h0] at bound
    . convert bound using 2
      . field_simp; ring
      . congr 1; field_simp
      congr 1; field_simp
    all_goals {positivity}
  all_goals {positivity}
