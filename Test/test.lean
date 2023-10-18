import Mathlib
import Mathlib.Tactic







example (a b c : ℝ) (h : a/c = b/c) (h' : c ≠ 0) : a = b := by
  field_simp at h
  assumption


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
    rfl

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
