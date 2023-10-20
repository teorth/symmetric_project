import Mathlib
import Mathlib.Tactic


import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Finset
open BigOperators
open Real

example {n : ℕ} {a : ℝ} {x : ℕ → ℝ} {h_1 : 0 < n} {h_2: 0 < a}  : ∑ i in range n, ((1:ℝ)/n) * log (exp (x i) + a) ≥ log (exp (∑ i in range n, ((1:ℝ)/n) * x i) + a) := by
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
    have hc : DifferentiableAt ℝ (fun (x:ℝ) ↦ a) x := by
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
    . sorry
    sorry
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


/--
theorem convexOn_of_deriv2_nonneg{D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D)) (hf'' : DifferentiableOn ℝ (deriv f) (interior D)) (hf''_nonneg : ∀ (x : ℝ), x ∈ interior D → 0 ≤ deriv^[2] f x) :
ConvexOn ℝ D f

theorem ConvexOn.map_sum_le{𝕜 : Type u_1} {E : Type u_2} {β : Type u_4} {ι : Type u_5} [LinearOrderedField 𝕜] [AddCommGroup E] [OrderedAddCommGroup β] [Module 𝕜 E] [Module 𝕜 β] [OrderedSMul 𝕜 β] {s : Set E} {f : E → β} {t : Finset ι} {w : ι → 𝕜} {p : ι → E} (hf : ConvexOn 𝕜 s f) (h₀ : ∀ (i : ι), i ∈ t → 0 ≤ w i) (h₁ : (Finset.sum t fun i => w i) = 1) (hmem : ∀ (i : ι), i ∈ t → p i ∈ s) :
f (Finset.sum t fun i => w i • p i) ≤ Finset.sum t fun i => w i • f (p i)

-/



  example : Finset.range 2 = {0,1} := by
    ext a
    simp
    constructor
    . intro ha
      have ha' : a ≤ 1 := by linarith [ha]
      rcases a with a | a
      . norm_num
      rw [Nat.succ_eq_add_one]
      rw [Nat.succ_eq_add_one] at ha'
      have ha'' : a = 0 := by linarith
      right
      rw [ha'']
    intro ha
    rcases ha with h | h
    . norm_num [h]
    norm_num [h]

example : Finset.range 2 = {0,1} := by
  simp



example (a : ℝ) : 0 ≤ a^2 := by
  simp
  positivity

example (a b c: ℕ) (ha: a ≤ c) (hb: b ≤ c) (h:c-a=c-b) : a = b := by
  linarith [Nat.sub_add_cancel ha, Nat.sub_add_cancel hb]

example (n m : ℕ) : (n-m:ℕ) = if m ≤ n then (n:ℤ)-(m:ℤ) else (0:ℤ) := by
  split
  . have h : m ≤ n := by assumption
    symm; rw [sub_eq_iff_eq_add]
    suffices : n = (n-m) + m
    . nth_rewrite 1 [this]
      simp
    rw [Nat.sub_add_cancel h]

  suffices : (n - m) = 0
  . zify at this; assumption
  rw [Nat.sub_eq_zero_iff_le]
  linarith


example (X complicated_expression_1 complicated_expression_2 complicated_expression_3 bound_1 bound_2 bound_3: ℕ)
    (h: X ≤ complicated_expression_1 + complicated_expression_2 + complicated_expression_3)
    (b1 : complicated_expression_1 ≤ bound_1)
    (b2 : complicated_expression_2 ≤ bound_2)
    (b3 : complicated_expression_3 ≤ bound_3) :
    X ≤ bound_1 + bound_2 + bound_3 :=
  calc X ≤ _ := h
    _ ≤ bound_1 + bound_2 + bound_3 := by gcongr


example (complicated_expression_1 complicated_expression_2 : Nat) (f : Nat → Nat)
    (h : complicated_expression_1 = complicated_expression_2) :
    f complicated_expression_1 = f complicated_expression_2 := by
  have h' := by congrm(f $h)
  exact h'
