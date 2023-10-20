import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! The purpose of this file is to establish [Theorem 1.3 of the paper].  Namely, if $(s_0,\dots s_n)$ is attainable, r>0, and 1 ≤ l ≤ n, then
$$ ∑_{m=0}^l \binom{l}{m} |s_m| r^m ≥ (1 + |s_l|^{2/l} r^2)^{l/2}$$
and
$$ ∑_{m=0}^l \binom{l}{m} |s_m| r^{l-m} ≥ (|s_l|^{2/l} + r^2)^{l/2}. $$
-/


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

  have hg_nonzero (x : ℝ): g x ≠ 0 := by
    show exp x + a ≠ 0
    linarith [exp_pos x]

  have hg' : deriv g = rexp := by
    ext x
    simp

  have f_diff : Differentiable ℝ f := by
    apply Differentiable.log g_diff
    exact hg_nonzero

  have hf' : deriv f = (fun x ↦ 1 + (- a) / (g x)) := by
    ext x
    rw [deriv.log (g_diff_at x) (hg_nonzero x), hg']
    field_simp [hg_nonzero x]

  have convex : ConvexOn ℝ Set.univ f := by
    apply MonotoneOn.convexOn_of_deriv
    . exact convex_univ
    . apply Continuous.continuousOn
      apply Differentiable.continuous f_diff
    . apply Differentiable.differentiableOn f_diff
    apply Monotone.monotoneOn
    rw [hf']
    apply Monotone.const_add
    rw [monotone_iff_forall_lt]
    intro x y
    intro h
    field_simp [hg_nonzero x, hg_nonzero y]
    rw [<- neg_le_neg_iff]
    field_simp
    gcongr
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
