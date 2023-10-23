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


/-! The purpose of this file is to establish [Theorem 1.3 of the paper].
-/


open Finset
open BigOperators
open Real
open Polynomial

/- A Jensen inequality for the function x -> log(exp x + a) for any positive a. -/
lemma logexp_jensen {n : ℕ} {a : ℝ} {x : ℕ → ℝ} {h_1 : 0 < n} {h_2: 0 < a}  : ∑ i in range n, ((1:ℝ)/n) * log (exp (x i) + a) ≥ log (exp (∑ i in range n, ((1:ℝ)/n) * x i) + a) := by
  let g := fun x ↦ rexp x + a

  have g_diff : Differentiable ℝ g := by simp; apply Differentiable.exp; simp

  have hg_nonzero (x : ℝ): g x ≠ 0 := by dsimp; linarith [exp_pos x]

  have hf' : deriv (fun x ↦ log (g x)) = fun x ↦ 1 - a / (g x) := by
    ext x
    rw [deriv.log (Differentiable.differentiableAt g_diff) (hg_nonzero x)]
    field_simp [hg_nonzero x]

  apply ConvexOn.map_sum_le
  . apply MonotoneOn.convexOn_of_deriv convex_univ (Continuous.continuousOn (Differentiable.continuous (Differentiable.log g_diff hg_nonzero))) (Differentiable.differentiableOn (Differentiable.log g_diff hg_nonzero))
    apply Monotone.monotoneOn
    rw [hf', monotone_iff_forall_lt]
    intro x y hxy; dsimp; gcongr
  . intro _ _; positivity
  . rw [sum_const]; simp; field_simp
  intro i _; simp

/--
If $(s_0,\dots s_n)$ is attainable, r>0, and 1 ≤ l ≤ n, then
$$ ∑_{m=0}^l \binom{l}{m} |s_m| r^m ≥ (1 + |s_l|^{2/l} r^2)^{l/2}$$
-/
theorem new_inequality (n l : ℕ) (s : ℕ → ℝ) (r : ℝ) (h1: attainable n s) (h2 : l ≤ n) (h3: l ≥ 1) (h4: r > 0) : ∑ m in range (l+1), (Nat.choose l m) * abs (s m) * r^(l-m : ℕ) ≥ (( abs (s l) )^(2 / l) + r^2)^(l / 2) := by

-- first reduce to the l=n case

  have h5: attainable l s := attainable_truncate n l s h2 h1
  clear h1 h2 n

  by_cases h6 :s l = 0
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
    simp [Real.zero_rpow h7, attainable_zero_eq_one h5, h8]
    apply sum_nonneg
    intro i _
    positivity

  have h7 : abs (s l) > 0 := by positivity
  rcases h5 with ⟨x, h5⟩

  have h7a := esymm_prod l x
  simp [h5 l (by observe : l ≤ l)] at h7a

  have h8 : ∀ i ∈ range l, x i ≠ 0 := by
    contrapose! h6
    rcases h6 with ⟨ i, ⟨ hi, hx ⟩⟩
    rw [h7a]
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
  have h11 : |r| = r := by
    rw [abs_of_pos h4]
  have h12 := AbsoluteValue.sum_le Complex.abs (range (l+1)) (fun k ↦ (-1) ^ k * (Nat.choose l k) * (s k) * ir ^ (l - k : ℕ))
  simp [<-h10, h11] at h12
  clear h10 h11
  suffices : ∏ k in range l, Complex.abs (ir - x k) ≥ (|s l| ^ (2 / l) + r ^ 2) ^ (l / 2)
  . simp at this
    simp
    linarith

  have h13 : ∀ k ∈ range l, 0 < Complex.abs (ir - x k) := by
    intro k _
    apply AbsoluteValue.pos
    by_contra h13
    have h14 := by congrm Complex.im $h13
    simp at h14
    linarith

  rw [ge_iff_le, <- Real.log_le_log, Real.log_rpow, Real.log_prod]
  . clear h12
    have h15 : ∑ i in range l, log (Complex.abs (ir - (x i))) = (1:ℝ)/2 * ∑ i in range l, log (r^2 + (x i)^2) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      field_simp
      rw [mul_comm, <-log_rpow (h13 i hi)]
      congr
      norm_cast
      rw [<-Complex.normSq_eq_abs, (show ir - x i = (-x i:ℝ) + r * Complex.I by simp; ring), Complex.normSq_add_mul_I]
      ring
    rw [h15]
    clear h13 h15 ir

    let y := (fun (i: ℕ) ↦ log (x i^2))
    have h16 : ∀ i ∈ range l, x i^2 = exp (y i) := by
      intro i hi
      rw [exp_log]
      have h8a : x i ≠ 0 := h8 i hi
      norm_cast
      positivity

    suffices : ∑ i in range l, (1:ℝ)/l * log (exp (y i) + r ^ 2) ≥ log (|s l| ^ ((2:ℝ) / l) + r ^ 2)
    . rw [<- mul_le_mul_left (show 0 < (2:ℝ)/l by positivity)]
      calc (2:ℝ) / l * (l / 2 * log (|s l| ^ ((2:ℝ) / l) + r ^ 2)) = log (|s l| ^ ((2:ℝ) / l) + r ^ 2) := by field_simp; ring
        _ ≤ ∑ i in range l, 1 / ↑l * log (exp (y i) + r ^ 2) := by linarith
        _ = ∑ i in range l, 1 / ↑l * log (r ^ 2 + x i ^ 2) := by apply sum_congr rfl; intro i hi; rw [h16 i hi]; rw [add_comm]
        _ = (2:ℝ) / l * (1 / 2 * ∑ i in range l, log (r ^ 2 + x i ^ 2)) := by rw [<- mul_sum]; field_simp; ring

    have h17 : |s l|^((2:ℝ)/l) = exp (∑ i in range l, ((1:ℝ)/l) * y i) := calc
      |s l|^((2:ℝ)/l) = |s l^2|^((1:ℝ)/l) := by
        rw [(show (2:ℝ)/l = 2 * ((1:ℝ)/l) by ring), rpow_mul]
        . congr
          norm_cast
          rw [abs_pow]
        positivity
      _ = |∏ i in range l, x i^2|^((1:ℝ)/l) := by
        congr 2
        rw [h7a]
        norm_cast
        rw [prod_pow]
      _ = |∏ i in range l, exp (y i)|^((1:ℝ)/l) := by
        congr 2
        apply prod_congr rfl
        intro i hi
        rw [h16 i hi]
      _ = exp (∑ i in range l, ((1:ℝ)/l) * y i) := by
        rw [<- exp_sum, abs_of_pos, <-exp_mul, <-mul_sum]
        . congr 1
          field_simp
        apply exp_pos
    rw [h17]
    apply logexp_jensen
    . linarith
    positivity
  . intro k hk
    linarith [h13 k hk]
  . positivity
  . positivity
  apply prod_pos
  exact h13

/--
If $(s_0,\dots s_n)$ is attainable, r>0, and 1 ≤ l ≤ n, then
$$ ∑_{m=0}^l \binom{l}{m} |s_m| r^{l-m} ≥ (|s_l|^{2/l} + r^2)^{l/2}. $$
-/
theorem new_inequality' (n l : ℕ) (s : ℕ → ℝ) (r : ℝ) (h1: attainable n s) (h2 : l ≤ n) (h3: l ≥ 1) (h4 : r > 0) : ∑ m in range (l+1), (Nat.choose l m) * abs (s m) * r^m ≥ (1 + abs (s l)^((2:ℝ)/l) * r^2)^(l/(2:ℝ)) := calc
  ∑ m in range (l+1), (Nat.choose l m) * abs (s m) * r^m = r^l * ∑ m in range (l+1), (Nat.choose l m) * abs (s m) * (1/r)^(l-m : ℕ) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro m hm
    rw [mul_comm (r^(l:ℝ)) _, mul_assoc _ _ (r^(l:ℝ))]
    congr
    field_simp
    rw [<-pow_add]
    congr
    rw [add_comm, Nat.sub_add_cancel]
    simp at hm; linarith
  _ ≥ r^l * (( abs (s l) )^(2 / l) + (1/r)^2)^(l / 2) := by
    rw [ge_iff_le, mul_le_mul_left, <-ge_iff_le]
    . apply new_inequality n l s (1/r) h1 h2 h3
      . positivity
    positivity
  _ = (1 + abs (s l)^((2:ℝ)/l) * r^2)^(l/(2:ℝ)) := by
    have h5 : r^l = (r^2)^(l/2) := by
      rw [<- rpow_mul]
      . congr
        field_simp
        ring
      linarith
    rw [h5, <- mul_rpow]
    . congr
      field_simp
      ring
    . positivity
    positivity
