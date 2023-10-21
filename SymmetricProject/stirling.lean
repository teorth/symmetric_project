import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Init.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real


/- hack to avoid the real powers bug -/
local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

/- The purpose of this file is to prove the some "cheap" Stirling bounds for factorial and binomial coefficients.
-/

open Real
open Nat
open Finset
open BigOperators

lemma factorial_le {n : ℕ} : n ! ≤ n^n := by
  induction' n with m hm
  . simp
  rw [factorial_succ, Nat.pow_succ, succ_eq_add_one, mul_comm]
  gcongr
  apply le_trans hm
  gcongr
  linarith

lemma factorial_ge {n : ℕ} : n ! ≥ n^n / exp n := by
  have h := calc
    exp n ≥ ∑ k in range (n+1), (n:ℝ)^k / k ! := by
      rw [ge_iff_le]
      apply Real.sum_le_exp_of_nonneg
      positivity
    _ ≥ (n:ℝ)^n/n ! := by
      rw [sum_range_succ]
      simp
      apply sum_nonneg
      intro k _
      positivity
  apply_fun (fun (X:ℝ) =>  X * (n ! / exp n)) at h
  . have h1 : (n !: ℝ) ≠ 0 := by positivity
    have h2 : exp n ≠ 0 := by positivity
    field_simp at h
    rw [ge_iff_le]
    convert h using 1
    . congr
      norm_cast
    field_simp
    ring
  rw [monotone_iff_forall_lt]
  intro a b hab
  gcongr

lemma choose_eq {n : ℕ} {k : ℕ} (h : k ≤ n) : choose n k = (∏ j in range k, (1 - (j:ℝ)/n)) * n^k / k ! := by
  have : choose n k = (descFactorial n k : ℝ) / k ! := by
    rw [descFactorial_eq_factorial_mul_choose]
    field_simp [(observe : k! ≠ 0)]
  rw [this]
  congr
  have : n ^ k = ∏ j in range k, (n:ℝ) := by
    rw [prod_const, card_range]
    norm_cast
  rw [this, <- prod_mul_distrib, descFactorial_eq_prod_range]
  rw [(show ∏ i in range k, (n-i) = ∏ i in range k, ((n - i : ℕ) : ℝ) by norm_cast)]
  apply prod_congr rfl
  intro j hj
  simp at hj
  have hn : n ≠ 0 := by linarith
  field_simp
  symm
  rw [sub_eq_iff_eq_add]
  norm_cast
  rw [Nat.sub_add_cancel]
  linarith



lemma choose_le {n : ℕ} {k : ℕ} (h : k ≤ n) : choose n k ≤ n^k / k ! := by
  sorry

lemma choose_ge {n : ℕ} {k : ℕ} (h : k ≤ n) : choose n k ≥ n^k / k^k := by
  sorry
