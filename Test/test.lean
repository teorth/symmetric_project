import Mathlib
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Ring

open Finset
open BigOperators



example (a b : ℕ) : a + b = b + a := by
  generalize h : a + b = x
  set c := b + a
  rw [<- h]
  observe k : a = a
  observe l : a ≤ a
  observe m : a ≤ a + 1
  wlog h : a < 0
  . rw [Nat.add_comm]
  rw [Nat.add_comm]

example (n : ℕ ) (f g : ℕ → ℕ) (h : ∀ x ∈ range n, f x = g x) : ∀ x ∈ range n, 1 + f x = 1 + g x := by
  have hc (x : ℕ) (hx : x ∈ range n): ?Q := by
    let h0 := h x hx
    have h1 := by congrm (1 + $h0)
    exact h1
  assumption


example (a: ℝ) : Differentiable ℝ (fun (x:ℝ) ↦ (Real.exp x + a)) := by
    simp
    apply Differentiable.exp
    simp

example (a b c : ℝ) (h: c * a ≤ c * b) (h2 : c > 0): a ≤ b := by
  exact (mul_le_mul_left h2).mp h


example (a b c d : ℝ) (h1 : a / (c^2 + d^2) = b / (c^2 + d^2)) (h2: c ≠ 0) (h3 : d ≠ 0) : a = b := by
  have h4 : c^2+d^2 ≠ 0 := by
    have h5 : 0 < c^2 := by norm_cast; rw [sq_pos_iff c]; assumption
    have h6 : 0 < d^2 := by norm_cast; rw [sq_pos_iff d]; assumption
    linarith
  rw [div_left_inj' h4] at h1
  exact h1

example (a b c d : ℝ) (h1 : a*(c-d) = b*(c-d)) (h2 : c ≠ d): a = b := by
  have h3 : c-d ≠ 0 := by contrapose! h2; linarith
  field_simp [h3] at h1
  assumption


example (a b c d : ℝ) (h1 : a/(c-d) = b/(c-d)) (h2 : c ≠ d): a = b := by
  have h3 : c-d ≠ 0 := by contrapose! h2; linarith
  field_simp at h1
  assumption





example (f : ℕ → ℕ → ℕ) (a b c : ℕ) (h: a = b) : f c a = f c b := by
  congrm f c $h


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
