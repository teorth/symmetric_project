import Mathlib
import Mathlib.Tactic


import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Finset
open BigOperators
open Real

/- A Jensen inequality for the function x -> log(exp x + a) for any positive a. -/
lemma logexp_jensen {n : ℕ} {a : ℝ} {x : ℕ → ℝ} {h_1 : 0 < n} {h_2: 0 < a}  : ∑ i in range n, ((1:ℝ)/n) * log (exp (x i) + a) ≥ log (exp (∑ i in range n, ((1:ℝ)/n) * x i) + a) := by
  let g := fun (x:ℝ) ↦ exp x + a
  let f := fun (x:ℝ) ↦ log (g x)
  show ∑ i in range n, ((1:ℝ)/n) * f ( x i ) ≥ f (∑ i in range n, ((1:ℝ)/n) * x i)

  have g_diff : Differentiable ℝ g := by
    apply Differentiable.add
    . apply Differentiable.exp
      apply differentiable_id
    apply differentiable_const

  have g_diff_at (x : ℝ): DifferentiableAt ℝ g x := by
      apply Differentiable.differentiableAt g_diff

  have hg_pos (x : ℝ): g x > 0 := by
    show exp x + a > 0
    linarith [exp_pos x]

  have hg_nonzero (x : ℝ): g x ≠ 0 := by
    linarith [hg_pos x]

  have hg' : deriv g = rexp := by
    ext x
    simp

  have f_diff : Differentiable ℝ f := by
    apply Differentiable.log g_diff
    intro x
    show exp x + a ≠ 0
    linarith [exp_pos x]

  have hf' : deriv f = (fun x ↦ 1 - a / (g x)) := by
    ext x
    rw [deriv.log (g_diff_at x) (hg_nonzero x), hg']
    field_simp [hg_nonzero x]

  have f'_diff : Differentiable ℝ (deriv f) := by
    rw [hf']
    apply Differentiable.sub
    . apply differentiable_const
    apply Differentiable.div
    . apply differentiable_const
    . exact g_diff
    exact hg_nonzero

  have hf'' : deriv (deriv f) = (fun x ↦ a * (exp x) / (g x)^2) := by
    ext x
    rw [hf', deriv_const_sub]
    have hc : DifferentiableAt ℝ (fun (_:ℝ) ↦ a) x := by
      apply Differentiable.differentiableAt
      apply differentiable_const
    rw [deriv_div hc (g_diff_at x) (hg_nonzero x), hg', deriv_const]
    field_simp [hg_nonzero x]

  have convex : ConvexOn ℝ Set.univ f := by
    apply convexOn_of_deriv2_nonneg
    . exact convex_univ
    . apply Continuous.continuousOn
      apply Differentiable.continuous f_diff
    . apply Differentiable.differentiableOn f_diff
    . apply Differentiable.differentiableOn f'_diff
    intro x _
    simp [hf'']
    positivity
  apply ConvexOn.map_sum_le convex
  . intro _ _
    apply div_nonneg
    . norm_num
    norm_cast
    linarith
  . rw [sum_const]
    simp
    field_simp
  intro i _
  simp
