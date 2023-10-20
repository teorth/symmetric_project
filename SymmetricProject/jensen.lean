import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial

import SymmetricProject.esymm_basic
import SymmetricProject.esymm_generating
import SymmetricProject.attainable


/-! The purpose of this file is to establish [Theorem 1.3 of the paper].  Namely, if $(s_0,\dots s_n)$ is attainable, r>0, and 1 ≤ l ≤ n, then
$$ ∑_{m=0}^l \binom{l}{m} |s_m| r^m ≥ (1 + |s_l|^{2/l} r^2)^{l/2}$$
and
$$ ∑_{m=0}^l \binom{l}{m} |s_m| r^{l-m} ≥ (|s_l|^{2/l} + r^2)^{l/2}. $$
-/


open Finset
open BigOperators
open Real
open Polynomial

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

theorem new_inequality (n l : ℕ) (s : ℕ → ℝ) (r : ℝ) (h1: attainable n s) (h2 : l ≤ n) (h3: l ≥ 1) (h4: r > 0) : ∑ m in range (l+1), (Nat.choose l m) * abs (s m) * r^(l-m) ≥ (( abs (s l) )^(2 / l) + r^2)^(l / 2) := by

-- first reduce to the l=n case

  have h5: attainable l s := attainable_truncate n l s h2 h1
  clear h1 h2 n

  rcases em (s l = 0) with h6 | h6
  . rw [h6]
    have h7 : (2:ℝ)/l ≠ 0 := by positivity
    rw [Finset.sum_range_succ']

    have h8 : (r^2)^(l/2) = r^l := by
      rw [← rpow_mul]
      . congr
        field_simp
        ring
      linarith

    simp at h8
    simp [Real.zero_rpow h7, attainable_zero_eq_one l s h5, h8]
    apply sum_nonneg
    intro i hi
    positivity

  have h7 : abs (s l) > 0 := by positivity
  rcases h5 with ⟨x, h5⟩

  have h8 : ∀ i ∈ range l, x i ≠ 0 := by
    contrapose! h6
    rcases h6 with ⟨ i, ⟨ hi, hx ⟩⟩
    have h7 : l ≤ l := by linarith
    have h8 := h5 l h7
    rw [esymm_prod l x] at h8
    simp at h8
    rw [<- h8]
    apply prod_eq_zero hi hx

  have h9 : ∏ i in (range l), (X - C (x i)) = ∑ k in range (l+1), monomial (l-k) ((-1) ^ ↑k * (Nat.choose l k) * (s k)) := by
    rw [esymm_genfn l x]
    apply sum_congr rfl
    intro k hk
    have hk' : k ≤ l := by simp at hk; linarith
    rw [h5 k hk']
    congr 1
    rw [mul_assoc]
    congr 1
    . norm_cast
    ring
  let ir := Complex.I * (r:ℂ)

  have h10 := by congrm (eval₂ Complex.ofReal ir $h9)
  clear h6 h9 h5
  simp [eval₂_finset_prod, eval₂_finset_sum] at h10


  sorry


-- theorem new_inequality (n l : ℕ) (s : ℕ → ℝ) (r : ℝ) (h1: attainable n s) (h2 : l ∈ range (n+1)) (h3: l ≥ 1) : ∑ m in range (l+1), (Nat.choose l m) * abs (s m) * r^(l-m) ≥ (( abs (s l) )^((2:ℝ) / l) + r^2)^(l / (2:ℝ)) := by
--  sorry

--theorem new_inequality' (n l : ℕ) (s : ℕ → ℝ) (r : ℝ) (h1: attainable n s) (h2 : l ∈ range (n+1)) (h3: l ≥ 1) : ∑ m in range (l+1), (Nat.choose l m) * abs (s m) * r^m ≥ (1 + abs (s l)^((2:ℝ)/l) * r^2)^(l/(2:ℝ)) := by
--  sorry


-- $$ ∑_{m=0}^l \binom{l}{m} |s_m| r^{l-m} ≥ (|s_l|^{2/l} + r^2)^{l/2}. $$
