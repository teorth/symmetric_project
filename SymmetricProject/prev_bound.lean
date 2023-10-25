import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Init.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.ContinuousOn
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
      all_goals {intros; positivity}
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
        swap; rw [sum_const]; simp; field_simp
        all_goals { intros; positivity }
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

/-- If 0 < a < b, then 2(b-a)/(a+b) ≤ log b - log a -/
lemma log_jensen {a b : ℝ} (ha : 0 < a) (hb : a < b) : 2 * ((b-a) / (a+b)) ≤ log b - log a := by
  set x := (b-a) / (a+b)
  have hx0 : 0 < x := by
    apply div_pos; linarith; linarith
  have hx1 : x < 1 := by
    rw [div_lt_iff]; linarith; linarith
  let f := fun (t:ℝ) ↦ log (1 + t) - log (1 - t)
  have : log b - log a = f x := by
    simp
    have : a+b > 0 := by linarith
    rw [sub_eq_sub_iff_add_eq_add, <- log_mul, <- log_mul]
    . congr 1
      field_simp; ring
    all_goals{(try field_simp); linarith}
  rw [this]
  have : ∃ c, c ∈ Set.Ioo 0 x ∧ deriv f c = (f x - f 0) / (x - 0) := by
    apply exists_deriv_eq_slope
    . assumption
    . apply ContinuousOn.sub
      all_goals{
        apply ContinuousOn.log
        apply Continuous.continuousOn
        continuity
        intro y hy
        simp at hy
        linarith
      }
    apply DifferentiableOn.sub
    all_goals{
      apply DifferentiableOn.log
      apply Differentiable.differentiableOn
      apply Differentiable.const_add
      (try apply Differentiable.neg)
      simp
      intro y hy
      simp at hy
      linarith
    }
  rcases this with ⟨ c, ⟨ hc, mean ⟩ ⟩
  symm at mean
  rw [div_eq_iff, sub_eq_iff_eq_add] at mean
  rw [mean]
  simp at hc ⊢
  rcases hc with ⟨ hc1, hc2 ⟩
  have hc3 : 1 - c > 0 := by linarith
  gcongr
  . rw [deriv_sub, deriv.log, deriv.log, deriv_const_add, deriv_const_sub, deriv_id'']
    . field_simp
      rw [le_div_iff]
      ring_nf; simp
      all_goals {positivity}
    . rw [differentiableAt_const_sub_iff]; simp
    . positivity
    . rw [differentiableAt_const_add_iff]; simp
    . positivity
    . apply DifferentiableAt.log
      . rw [differentiableAt_const_add_iff]; simp
      positivity
    apply DifferentiableAt.log
    . rw [differentiableAt_const_sub_iff]; simp
    positivity
  linarith

/-- Annoyingly, this version of the bound (which telescopes nicely) is only useful for n>3.  -/
lemma prelim_bound_rev' {n : ℕ} {s : ℕ → ℝ} (h1 : n > 3) (h2 : attainable n s) : |s n|^((n:ℝ)⁻¹) ≤ max (((2:ℝ) * n)^((Real.log (n-1) - Real.log (n-2))/2) * |s (n-1)|^((n-1:ℝ)⁻¹)) (( (2:ℝ)*n)^((Real.log (n-1) - Real.log (n-3))/2) * |s (n-2)|^((n-2:ℝ)⁻¹)) := by
  apply le_trans (prelim_bound_rev (show n>2 by linarith) h2) _
  have h1' : (3:ℝ) < (n:ℝ) := by norm_cast
  apply max_le_max
  all_goals {
    apply mul_le_mul_of_nonneg_right
    rw [Real.rpow_le_rpow_left_iff]
    (try rw [le_div_iff])
    apply le_trans _ (log_jensen _ _)
    field_simp
    rw [div_le_div_iff]
    . ring_nf; linarith
    . linarith
    . linarith
    . linarith
    . linarith
    . linarith
    . (try linarith); (try positivity)
    (try positivity)
  }

/-- could also use Int.coe_nat_sub here -/
lemma nat_sub_eq_real_sub {a b : ℕ} (h: b ≤ a) : (a - b:ℕ) = (a:ℝ) - (b:ℝ) := by
  rw [eq_sub_iff_add_eq]
  norm_cast
  exact Nat.sub_add_cancel h

/-- inequality (2.1) from the paper, corrected to only hold for k+3 ≤ n --/
lemma iterated {n k : ℕ} {s : ℕ → ℝ} (h2 : attainable n s) (h3 : k+3 ≤ n) : |s n|^((n:ℝ)⁻¹) ≤ max (((2:ℝ) * n)^((Real.log (n-1) - Real.log (n-k-1))/2) * |s (n-k)|^((n-k:ℝ)⁻¹)) (( (2:ℝ)*n)^((Real.log (n-1) - Real.log (n-(k+1:ℕ)-1))/2) * |s (n-(k+1))|^((n-(k+1:ℕ):ℝ)⁻¹)) := by
  let f := fun (m:ℕ) ↦ ((2:ℝ) * n)^((Real.log (n-1) - Real.log (n-m-1))/2) * |s (n-m)|^((n-m:ℝ)⁻¹)
  show |s n|^((n:ℝ)⁻¹) ≤ max (f k) (f (k+1))
  induction' k with m hm
  . simp
  have hm := hm (show m+3 ≤ n by linarith)
  simp at hm
  rcases hm with hm | hm
  . have := attainable_truncate n (n-m) s (Nat.sub_le n m) h2
    have h3 : m + 4 ≤ n := by rw [Nat.succ_eq_add_one] at h3; linarith
    have h4 : n-m > 3 := calc
      n-m ≥ m + 4 - m := Nat.sub_le_sub_right h3 m
      _ = 4 := Nat.add_sub_cancel_left m 4
      _ > 3 := by norm_num
    have := prelim_bound_rev' h4 this
    apply le_trans hm _
    have h5 : 0 < (2:ℝ) * n := by norm_cast; linarith
    have h6 : 0 < (((2:ℝ) * n) ^ ((Real.log (n - 1) - Real.log (n - m - 1)) / 2)) := by positivity
    rw [<-mul_le_mul_left h6] at this
    rw [nat_sub_eq_real_sub (show m ≤ n by linarith)] at this
    apply le_trans this _
    rw [mul_max_of_nonneg]
    clear hm this h5 h6
    have h7 : n > 0 := by linarith
    . apply max_le_max
      . simp; ring_nf
        have h8 : n - succ m = n - m - 1 := by
          symm
          apply Nat.sub_eq_of_eq_add
          apply Nat.sub_eq_of_eq_add
          rw [Nat.succ_eq_add_one, add_assoc, add_comm 1 m, Nat.sub_add_cancel]
          linarith
        rw [h8]
        apply mul_le_mul_of_nonneg_right
        . simp
          rw [<-le_div_iff', <- rpow_sub]
          ring_nf; simp
          apply rpow_le_rpow
          . simp; linarith
          . simp
          . simp
            rw [Real.log_le_log]
            . linarith
            all_goals {
              simp
              rw [_root_.lt_sub_iff_add_lt]
              norm_cast; linarith
            }
          . simp; assumption
          . positivity
        positivity
      simp; ring_nf
      have h8 : n - (1+succ m) = n - m - 2 := by
        symm
        apply Nat.sub_eq_of_eq_add
        apply Nat.sub_eq_of_eq_add
        rw [Nat.succ_eq_add_one, (show 1+(m+1)=m+2 by ring), add_assoc, add_comm 2 m, Nat.sub_add_cancel]
        linarith
      rw [h8]
      apply mul_le_mul_of_nonneg_right
      . simp
        rw [<-le_div_iff', <- rpow_sub]
        ring_nf; simp
        apply rpow_le_rpow
        . simp; linarith
        . simp
        . simp; rw [Real.log_le_log]
          . linarith
          all_goals {
            simp; rw [_root_.lt_sub_iff_add_lt]
            norm_cast; linarith
          }
        . simp; assumption
        . positivity
      positivity
    positivity
  simp
  left
  exact hm

/-- the bound two displays after (2.1) --/
lemma iterated_rev {n k : ℕ} {s : ℕ → ℝ} (h2 : attainable n s) (h3 : k+3 ≤ n) : |s n|^((n:ℝ)⁻¹) ≤ max (((2:ℝ) * n)^((Real.log (n-1) - Real.log (n-k-1))*(n-k)/(2*k)) * |s k|^((k:ℝ)⁻¹)) (( (2:ℝ)*n)^((Real.log (n-1) - Real.log (n-(k+1:ℕ)-1))*(n-(k+1))/(2*(k+1))) * |s (k+1)|^(((k+1:ℕ):ℝ)⁻¹)) := by
  have : n > (0:ℝ) := by norm_cast; linarith
  by_cases hsn: s n = 0
  . simp [hsn]
    left
    rw [zero_rpow]
    all_goals {positivity}
  let s' := fun k ↦ s (n - k) / s n
  have bound := iterated (attainable_reflect h2 hsn) h3
  simp [attainable_zero_eq_one h2] at bound
  rw [abs_inv, abs_div, abs_div, div_rpow, div_rpow, inv_rpow] at bound
  . sorry
  sorry
