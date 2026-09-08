import Mathlib
import Mathlib.Tactic
import SymmetricProject.Tactic.RwIneq

open Real


/- In this file the power notation will always mean the base and exponent are real numbers. -/
local macro_rules | `($x ^ $y)   => `(HPow.hPow ($x : ℝ) ($y : ℝ))

/- In this file the division  notation will always mean division of real numbers. -/
local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))

/- In this file, inversion will always mean inversion of real numbers. -/
local macro_rules | `($x ⁻¹)   => `(Inv.inv ($x : ℝ))

-- the binary entropy density on [0,1]. Defined piecewise at 0 so the value
-- does not depend on Real.log 0 being the junk value 0.
noncomputable def h : ℝ → ℝ := fun x => if x = 0 then 0 else -x * log x

/-- The off-zero formula, `h x = -x log x`. Used to move derivatives off the `if`. -/

lemma h_nonneg {x : ℝ} (h1 : 0 ≤ x) (h2 : x ≤ 1) : 0 ≤ h x := by
  unfold h
  split_ifs with hx
  . simp
  -- x ≠ 0, so this is -x log x, and log x ≤ 0 on (0,1]
  rw [neg_mul_comm]
  apply mul_nonneg h1
  simp
  exact log_nonpos h1 h2

/-- a sublemma needed to get an upper bound for h. -/
lemma log_le {x:ℝ} (hx: 0 ≤ x) : log x ≤ x / rexp 1 := by
  rw [le_iff_lt_or_eq] at hx
  rcases hx with hx | hx
  . rw [<-sub_le_sub_iff_right 1]
    convert (log_le_sub_one_of_pos (show 0 < (x * (Real.exp 1)⁻¹) by positivity)) using 1
    rw [log_mul]
    . simp; ring
    all_goals positivity
  simp [<-hx]

/-- an upper bound for h that can help prove continuity at 0. -/
lemma h_le {x : ℝ} (hx : 0 ≤ x) : h x ≤ 2 * (sqrt x) / rexp 1 := by
  unfold h
  rw [le_iff_lt_or_eq] at hx
  rcases hx with hx | hx
  . have hx0 : x ≠ 0 := by linarith
    simp [hx0]
    rw [neg_mul_comm, <- log_inv, <- sq_sqrt (show 0 ≤ x⁻¹ by positivity), log_pow, <-mul_assoc, <- le_div_iff']
    convert log_le (show 0 ≤ sqrt x⁻¹ by positivity) using 1
    field_simp
    nth_rewrite 3 [<- sq_sqrt (show 0 ≤ x by positivity)]
    ring
    positivity
  simp [<-hx]

/-- To prove continuity of h we will need a version of the squeeze test. -/
lemma squeeze {α : Type*} [TopologicalSpace α] {β : Type*} [TopologicalSpace β] [LinearOrder β] [OrderTopology β] {f g h : α → β} {x : α} (hfg : f x = g x) (hgh : g x = h x) (lower : ∀ y : α, f y ≤ g y) (upper : ∀ y : α, g y ≤ h y) (f_cont : ContinuousAt f x) (h_cont : ContinuousAt h x) : ContinuousAt g x := by
  rw [continuousAt_iff_lower_upperSemicontinuousAt] at f_cont h_cont ⊢
  dsimp [LowerSemicontinuousAt, UpperSemicontinuousAt] at f_cont h_cont ⊢
  rw [hfg] at f_cont
  rw [<-hgh] at h_cont
  constructor
  . intro a ha
    apply Filter.Eventually.mono (f_cont.1 a ha)
    intro x hx
    exact lt_of_lt_of_le hx (lower x)
  intro a ha
  apply Filter.Eventually.mono (h_cont.2 a ha)
  intro x hx
  exact LE.le.trans_lt (upper x) hx

/-- actually we need the squeeze test restricted to a subdomain. -/
lemma squeezeWithin {α : Type*} [TopologicalSpace α] {β : Type*} [TopologicalSpace β] [LinearOrder β] [OrderTopology β] {f g h : α → β} {s : Set α} {x : α} (hx : x ∈ s) (hfg : f x = g x) (hgh : g x = h x) (lower : ∀ y ∈ s, f y ≤ g y) (upper : ∀ y ∈ s, g y ≤ h y) (f_cont : ContinuousWithinAt f s x) (h_cont : ContinuousWithinAt h s x) : ContinuousWithinAt g s x := by
  rw [continuousWithinAt_iff_continuousAt_restrict _ hx] at f_cont h_cont ⊢
  set f' := Set.restrict s f
  set g' := Set.restrict s g
  set h' := Set.restrict s h
  set x' : s := ⟨ x, hx ⟩
  apply squeeze (show f' x' = g' x' by simpa) (show g' x' = h' x' by simpa) _ _ f_cont h_cont
  . intro y; simp [lower y]
  intro y; simp [upper y]

/-- Finally, the continuity of h. -/
lemma h_cont : ContinuousOn h (Set.Icc 0 1) := by
  dsimp [ContinuousOn]
  intro x hx
  simp at hx; rcases hx with ⟨ hx1, hx2 ⟩
  rw [le_iff_lt_or_eq] at hx1
  rcases hx1 with hx1 | hx1
  . unfold h
    have hx0 : x ≠ 0 := by linarith
    simp [hx0]
    apply ContinuousWithinAt.mul
    . apply Continuous.continuousWithinAt
      continuity
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_log
    linarith
-- the tricky case : continuity at zero!
  rw [<- hx1]
  let f := fun _ : ℝ ↦ (0:ℝ)
  let g := fun x : ℝ ↦ (2 * sqrt x) / rexp 1
  have f_cont : ContinuousWithinAt f (Set.Icc 0 1) 0 := by
    apply continuousWithinAt_const
  have g_cont : ContinuousWithinAt g (Set.Icc 0 1) 0 := by
    apply Continuous.continuousWithinAt
    continuity
  apply squeezeWithin _ _ _ _ _ f_cont g_cont
  . simp
  . simp [h]
  . simp [h]
  -- squeeze between 0 and the explicit upper bound, both continuous at 0 on [0,1]
  . intro y hy; simp at hy ⊢
    exact h_nonneg hy.1 hy.2
  intro y hy; simp at hy ⊢
  exact h_le hy.1

/-- The entropy function off zero, used to compute derivatives. -/
noncomputable def h_mul (x : ℝ) : ℝ := -x * log x

lemma h_eq_mul {x : ℝ} (hx : x ≠ 0) : h x = h_mul x := by
  simp [h, h_mul, hx]

lemma h_of_pos {x : ℝ} (hx : 0 < x) : h x = -x * log x := by
  rw [h_eq_mul hx.ne']; rfl

lemma h_zero : h 0 = 0 := by simp [h]

/-- The differentiability of h. -/
lemma h_diff : DifferentiableOn ℝ h (Set.Ioo 0 1) := by
  -- On (0,1) the piecewise definition agrees with -x log x, which is differentiable there.
  apply DifferentiableOn.congr (g := h_mul)
  · unfold h_mul
    apply DifferentiableOn.mul
    . apply DifferentiableOn.neg
      apply differentiableOn_id
    apply DifferentiableOn.log
    . apply differentiableOn_id
    intro x hx; simp at hx
    linarith [hx.1]
  intro x hx
  have hx0 : x ≠ 0 := by simp at hx; linarith [hx.1]
  exact h_eq_mul hx0

/-- The derivative of h. -/
lemma h_deriv {x : ℝ} (hx: 0 < x) : deriv h x = - log x + (- 1) := by
  have hne : x ≠ 0 := hx.ne'
  -- derivatives see a neighbourhood, so replace h by h_mul off a neighbourhood of 0.
  have heq : deriv h x = deriv h_mul x := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [eventually_ne_nhds hne] with y hy
    exact h_eq_mul hy
  rw [heq]
  unfold h_mul
  rw [deriv_mul]
  . rw [deriv_neg]
    rw [deriv_log]
    field_simp [hx]
  . apply Differentiable.differentiableAt
    apply differentiable_neg
  apply DifferentiableAt.log
  . exact differentiableAt_id'
  linarith

/-- The concavity of h. -/
lemma h_concave : ConcaveOn ℝ (Set.Icc 0 1) h := by
  apply AntitoneOn.concaveOn_of_deriv
  . apply convex_Icc
  . exact h_cont
  . rw [interior_Icc]; exact h_diff
  rw [interior_Icc]
  have : Set.EqOn (fun x ↦ - log x + (- 1)) (deriv h) (Set.Ioo 0 1) := by
    intro x hx; rw [h_deriv hx.1]
  apply AntitoneOn.congr _ this
  apply AntitoneOn.add_const
  apply MonotoneOn.neg
  have : (Set.Ioo (0:ℝ) 1) ⊆ (Set.Ioi (0:ℝ)) := by
    intro x hx
    simp at hx ⊢
    exact hx.1
  exact MonotoneOn.mono (StrictMonoOn.monotoneOn strictMonoOn_log) this


