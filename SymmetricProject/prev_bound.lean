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
import SymmetricProject.Tactic.Rify

/- hack to avoid the real powers bug -/
local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

/- The purpose of this file is to prove the bound

|s_l|^(1/2) ≪ l^(1/2) max |s_k|^(1/k), |s_{k+1}|^(1/k+1)

established by Gopalan-Yehudayoff.
-/

open Real
open Nat hiding log
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
        all_goals positivity
      all_goals positivity

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
        all_goals positivity
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
      all_goals positivity
    all_goals positivity
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
lemma prelim_bound_rev' {n : ℕ} {s : ℕ → ℝ} (h1 : n > 3) (h2 : attainable n s) : |s n|^((n:ℝ)⁻¹) ≤ max (((2:ℝ) * n)^((log (n-1) - log (n-2))/2) * |s (n-1)|^((n-1:ℝ)⁻¹)) (( (2:ℝ)*n)^((log (n-1) - log (n-3))/2) * |s (n-2)|^((n-2:ℝ)⁻¹)) := by
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
lemma iterated {n k : ℕ} {s : ℕ → ℝ} (h2 : attainable n s) (h3 : k+3 ≤ n) : |s n|^((n:ℝ)⁻¹) ≤ max (((2:ℝ) * n)^((log (n-1) - log (n-k-1))/2) * |s (n-k)|^((n-k:ℝ)⁻¹)) (( (2:ℝ)*n)^((log (n-1) - log (n-(k+1:ℕ)-1))/2) * |s (n-(k+1))|^((n-(k+1:ℕ):ℝ)⁻¹)) := by
  let f := fun (m:ℕ) ↦ ((2:ℝ) * n)^((log (n-1) - log (n-m-1))/2) * |s (n-m)|^((n-m:ℝ)⁻¹)
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
    have h6 : 0 < (((2:ℝ) * n) ^ ((log (n - 1) - log (n - m - 1)) / 2)) := by positivity
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
            rw [log_le_log]
            . linarith
            all_goals {
              simp; rw [_root_.lt_sub_iff_add_lt]
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
        . simp; rw [log_le_log]
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

/-- the bound two displays after (2.1).  Thanks to Kyle Miller for speeding up the convert code which was unusually slow. --/
lemma iterated_rev {n k : ℕ} {s : ℕ → ℝ} (h2 : attainable n s) (h3 : k+3 ≤ n) (h4 : 0 < k): |s n|^((n:ℝ)⁻¹) ≤ max (((2:ℝ) * n)^((log (n-1) - log (n-k-1))*(n-k)/(2*k)) * |s k|^((k:ℝ)⁻¹)) (( (2:ℝ)*n)^((log (n-1) - log (n-(k+1:ℕ)-1))*(n-(k+1))/(2*(k+1))) * |s (k+1)|^(((k+1:ℕ):ℝ)⁻¹)) := by
  have : n > (0:ℝ) := by norm_cast; linarith
  by_cases hsn: s n = 0
  . simp [hsn]
    left
    rw [zero_rpow]
    all_goals positivity
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
      . convert (config := {closePost := false}) bound using 2
        . rfl
        . field_simp; ring
        . congr 1; field_simp
        congr 1; field_simp
      all_goals positivity
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
    . convert (config := {closePost := false}) bound using 2
      . rfl
      . field_simp; ring
      . congr 1; field_simp
      congr 1; field_simp
    all_goals positivity
  all_goals positivity

lemma root_self {x:ℝ} (h: x > 0) : x^(x⁻¹) ≤ Real.exp (Real.exp 1)⁻¹ := by
  rw [<- log_le_iff_le_exp, log_rpow, inv_mul_le_iff, <-sub_le_sub_iff_right 1]
  . have := log_le_sub_one_of_pos (show 0 < (x * (Real.exp 1)⁻¹) by positivity)
    convert this using 1
    rw [log_mul]
    . simp; ring
    all_goals positivity
  all_goals positivity

/-- The Gopalan-Yehudayoff bound for n ≥ 8. --/
lemma prev_bound_large_n {n k : ℕ} {s : ℕ → ℝ} (h2 : attainable n s) (h3 : k+1 ≤ n) (h4 : 0 < k) (h5 : 8 ≤ n): |s n|^((n:ℝ)⁻¹) ≤ (rexp ((rexp 1)⁻¹ * 4))  * ((2:ℝ) * n)^((2:ℝ)⁻¹) * max (|s k|^((k:ℝ)⁻¹))  (|s (k+1)|^(((k+1:ℕ):ℝ)⁻¹)) := by
  rcases le_or_gt (2*k) n with h6 | h6
  . have : ∃ k' : ℕ, 2 * k' ≤ n + 2 ∧ |s n|^((n:ℝ)⁻¹) ≤ ((2:ℝ)*n)^((log (n-1) - log (n-k'-1))*(n-k')/(2*k')) * |s k'|^((k':ℝ)⁻¹) ∧ |s k'|^((k':ℝ)⁻¹) ≤ max (|s k|^((k:ℝ)⁻¹))  (|s (k+1)|^(((k+1:ℕ):ℝ)⁻¹)) ∧ (0:ℝ) < k' := by
      have h3' : k+3 ≤ n := by linarith
      have bound := iterated_rev h2 h3' h4
      simp at bound
      rcases bound with bound | bound
      . use k
        constructor
        . linarith
        . constructor
          . exact bound
          constructor
          . simp
          norm_cast
      use k+1
      constructor
      . linarith
      . constructor
        . simp
          exact bound
        constructor
        . simp
        norm_cast; linarith
    rcases this with ⟨ k', hk', bound, hs, h4' ⟩
    have h7 : 0 < (n:ℝ) - (k':ℝ) - 1 := by
      rw [_root_.lt_sub_iff_add_lt, _root_.lt_sub_iff_add_lt]
      norm_cast
      linarith
    have h8: 0 < (n:ℝ) - 1 := by
      rw [_root_.lt_sub_iff_add_lt]
      norm_cast
      linarith
    apply bound.trans
    apply le_trans _ ((_root_.mul_le_mul_left _).2 hs)
    gcongr
    rw [<-log_div]
    have : log (((n:ℝ) -1) / ((n:ℝ) - (k':ℝ) - 1)) * ((n:ℝ)-k') / (2*k')  ≤ (2:ℝ)⁻¹ + ((2:ℝ)*n)⁻¹ * 4 := by
      have : log (((n:ℝ) -1) / ((n:ℝ) - (k':ℝ) - 1)) ≤ (((n:ℝ) -1) / ((n:ℝ) - (k':ℝ) - 1)) - 1 := by
        apply log_le_sub_one_of_pos
        positivity
      apply le_trans ((div_le_div_right _).2 (mul_le_mul_of_nonneg_right this _)) _
      . positivity
      . rw [_root_.le_sub_iff_add_le]
        norm_cast
        linarith
      clear s h2 k h3 h4 h6 bound hs this
      have : ((n:ℝ)-1)/((n:ℝ)-(k':ℝ)-1) - 1 = (k':ℝ) / ((n:ℝ)-(k':ℝ)-1) := by
        field_simp
      rw [this, <-_root_.sub_le_iff_le_add']
      field_simp
      rw [div_le_div_iff, <-sub_nonneg]
      ring_nf
      suffices : 0 ≤ 4 * (k':ℝ) * (3 * (n:ℝ) - 4  - 4 * (k':ℝ))
      . convert this using 1
        ring
      apply mul_nonneg
      . positivity
      . rw [sub_nonneg, _root_.le_sub_iff_add_le]
        norm_cast; linarith
      all_goals positivity
    apply le_trans ((rpow_le_rpow_left_iff _).2 this) _
    . norm_cast; linarith
    rw [rpow_add, mul_comm (rexp ((rexp 1)⁻¹ * 4)) _, rpow_mul, (show rexp ((rexp 1)⁻¹ * 4) = (rexp (rexp 1)⁻¹)^(4:ℝ) by apply exp_mul)]
    gcongr
    apply root_self
    . norm_cast; positivity
    . norm_cast; positivity
    . norm_cast; positivity
    all_goals positivity
  rw [le_iff_lt_or_eq] at h3
  rcases h3 with h3 | h3
  . have h3' : (n-(k+1)) + 3 ≤ n := by
      zify [h3.le] at *
      linarith
    have bound := iterated h2 h3'
    apply bound.trans
    clear h2 h3' bound
    have h3' : n - (k+1) + 1 ≤ n := by zify [h3]; linarith
    have h3'' : n - (k+1) ≤ n := by zify [h3]; linarith
    have h5' : 0 < (n:ℝ) - 1 := by
      rify at *; linarith
    have h7: n - (n - (k+1)) = k+1 := by
      zify [h3, h3''] at *
      linarith
    have h8: n - (n - (k+1) + 1) = k := by
      zify [h3, h3'] at *
      linarith
    have h9 : (n:ℝ) - (n - (k+1) : ℕ) = k+1 := by
      zify [h3, h3'] at *
      linarith
    have h10 : (n:ℝ) - (n - (k+1) + 1 : ℕ) = k := by
      zify [h3, h3'] at *
      linarith
    rw [h7, h8, h9, h10, mul_assoc, mul_max_of_nonneg, <- one_mul (max _ _), max_comm]
    apply mul_le_mul
    . simp; positivity
    have (k' : ℕ) (h : k ≤ k') : ((2:ℝ)*n)^((log ((n:ℝ)-1) - log ((k':ℝ) - 1))/2) ≤ ((2:ℝ) * n) ^ (2:ℝ)⁻¹ := by
      have : 0 < (k':ℝ) - 1 := by rw [_root_.lt_sub_iff_add_lt]; norm_cast; linarith
      rw [rpow_le_rpow_left_iff]
      field_simp
      gcongr
      rw [<-log_div, log_le_iff_le_exp, div_le_iff']
      suffices : (n:ℝ) - 1 ≤ ((n:ℝ)/2 - 1) * Real.exp 1
      . apply this.trans
        gcongr
        rw [div_le_iff]; norm_cast; linarith
        positivity
      field_simp
      rw [le_div_iff]
      ring_nf
      suffices : rexp 1 * 2 - 2 ≤ (n:ℝ) * (rexp 1 - 2)
      . rw [mul_sub] at this; linarith
      have : rexp 1 * 2 - 2 ≤ 8 * (rexp 1 - 2) := by
        have := quadratic_le_exp_of_nonneg (show 0 ≤ 1 by norm_num)
        linarith
      apply this.trans
      apply mul_le_mul_of_nonneg_right
      . norm_cast
      . have := add_one_le_exp_of_nonneg (show 0 ≤ 1 by norm_num);
        linarith
      . norm_num
      . assumption
      . positivity
      . positivity
      . positivity
      . norm_cast; linarith
    apply max_le_max
    . apply mul_le_mul_of_nonneg_right
      apply this k (show k ≤ k by linarith)
      positivity
    rw [(show (k+1:ℕ) = (k:ℝ)+1 by norm_cast)]
    apply mul_le_mul_of_nonneg_right
    rw [(show (k:ℝ)+1 = (k+1:ℕ) by norm_cast)]
    apply this (k+1) (show k ≤ k+1 by linarith)
    all_goals positivity
  rw [(show |s n|^((n:ℝ)⁻¹) = 1 * 1 * |s n|^((n:ℝ)⁻¹) by ring)]
  gcongr
  . simp; positivity
  . apply one_le_rpow
    . norm_cast; linarith
    positivity
  simp; right
  rw [h3, (show (k:ℝ) + 1 = n by norm_cast)]

-- We know the next big proof will be based on a trichotomy, so let's get that out of the way
-- by stating and proving the next two lemmas.
lemma Nat.succ_le_or_eq_of_le {k n : ℕ } (h : k ≤ n) : k + 1 ≤ n ∨ k = n  :=
  h.lt_or_eq.casesOn (fun h ↦ Or.inl h) fun h ↦ Or.inr h

lemma Nat.trichotomy_of_le {k n : ℕ } (h : k ≤ n) : k + 2 ≤ n ∨ n = k + 1 ∨ n = k := by
  rcases Nat.succ_le_or_eq_of_le h with h | rfl
  · rcases Nat.succ_le_or_eq_of_le h with h | rfl
    · exact Or.inl h
    · exact Or.inr <| Or.inl rfl
  · exact Or.inr <| Or.inr rfl

/-- The Gopalan-Yehudayoff bound in general --/
lemma prev_bound : ∃ C : ℝ, ∀ n : ℕ, ∀ k : ℕ, ∀ s : ℕ → ℝ, (attainable n s) → (k+1 ≤ n) → (0 < k) → |s n|^((n:ℝ)⁻¹) ≤ C * (n:ℝ)^((2:ℝ)⁻¹) * max (|s k|^((k:ℝ)⁻¹))  (|s (k+1)|^(((k+1:ℕ):ℝ)⁻¹)) := by
  use max (rexp ((rexp 1)⁻¹ * 4) * (2:ℝ)^((2:ℝ)⁻¹) ) ((2:ℝ) * (7:ℝ)^((2:ℝ)⁻¹))
  intro n k s h2 h3 h4
  rcases le_or_gt 8 n with h5 | h5
  · -- Case `n ≤ 8`
    apply (prev_bound_large_n h2 h3 h4 h5).trans
    rw [mul_rpow, ← mul_assoc]
    gcongr
    · simp
    all_goals positivity
  ·  -- Case `n > 8`
    have h9 : ((2:ℝ) * n)^(1:ℝ) ≤ 2 * (7:ℝ)^((2:ℝ)⁻¹) * (n:ℝ)^((2:ℝ)⁻¹) := by
      rw [rpow_one, mul_assoc]
      gcongr
      rw [← rpow_le_rpow_iff _ _ (show 0 < 2 by norm_num), mul_rpow, ← rpow_mul, ← rpow_mul,
          (show (n:ℝ)^(2:ℝ) = n * n by norm_cast; ring)]
      simp
      gcongr
      norm_cast; linarith
      all_goals positivity
    rcases Nat.trichotomy_of_le h3 with h3 | rfl | rfl
    · -- Case `k + 3 ≤ n`
      apply (iterated_rev h2 h3 h4).trans
      -- Send everything to `ℝ`, calling `N` and `K` the numbers `n` and `k` seen as reals numbers.
      have n_nonneg : 0 ≤ n := n.zero_le -- Make sure we won't forget that `0 ≤ N`.
      rify at *
      generalize (n : ℝ) = N at *
      generalize (k : ℝ) = K at *
      have : ∀ K' ≤ K+1, 0 < K' → (2*N)^ ((log (N - 1) - log (N - K' - 1)) * (N - K') / (2 * K')) ≤
                                    2 * (7:ℝ)^((2:ℝ)⁻¹) * N^((2:ℝ)⁻¹) := by
        intro K' hK' hK''
        apply le_trans _ h9
        -- Premptively state that everything that will go in a division or log is positive.
        have h6 : 0 < N - K' := by linarith
        have h7 : 0 < N - K' - 1 := by linarith
        have h8 : 0 < N - 1 := by linarith
        have h10 : 0 < (N - 1) / (N - K' - 1) := by positivity
        rw [← log_div (by linarith) (by linarith)]
        gcongr
        · linarith
        · field_simp [div_le_iff] -- Note you can provide extra lemmas to `field_simp`
          rw [← le_div_iff h6]
          · apply (log_le_sub_one_of_pos h10).trans
            field_simp [div_le_div_iff]
            rw [mul_comm 2 _, mul_assoc]
            gcongr
            linarith
      rw [mul_max_of_nonneg]
      -- Now apply `gcongr` a lot more than in original version
      · gcongr
        . apply (this K (by linarith) h4).trans
          gcongr
          exact? says apply le_max_right
        · apply (this (K+1) le_rfl (by linarith)).trans
          gcongr
          exact? says apply le_max_right
      positivity
    · -- Case `n = k + 2`, except we got rid of `n` and work only with `k + 2`.
      apply (prelim_bound_rev (by linarith) h2).trans
      -- Send everything to `ℝ`, calling `K` the number `k` seen as a real number.
      change 1 ≤ k at h4 -- Don't forget that `0 < k` really means `1 ≤ k` before going real.
      rify at *
      generalize (k : ℝ) = K at *
      -- clean-up all stupid expressions appearing
      rw [show K + 1 + 1 = K+2 by ring, show K + 2 - 1 = K + 1 by ring, show K + 2 - 2 = K by ring,
          show k + 1 + 1 - 2 = k by simp, show k + 1 + 1 - 1 = k + 1 by simp] at *
      -- Premptively prove positivity of things appearing in denominators
      have : 0 < K + 1 := by linarith
      rw [max_comm, mul_max_of_nonneg]
      -- Now apply `gcongr` a lot more than in original version
      · gcongr
        all_goals
          rw [max_mul_of_nonneg]
          · simp
            right
            apply le_trans _ h9
            gcongr
            · linarith
            · field_simp [div_le_iff]
              linarith
          . positivity
      · positivity
    · -- Case `n = k + 1`, except we got rid of `n` and work only with `k + 1`.
      rw [← one_mul (|s (k+1)| ^ (((k+1:ℕ):ℝ)⁻¹)), ← one_mul 1]
      gcongr
      . simp; left; rw [← one_mul 1]; gcongr
        . simp; positivity
        . apply one_le_rpow; norm_num; positivity
      . apply one_le_rpow; simp; positivity
      simp
