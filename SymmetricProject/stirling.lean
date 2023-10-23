import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Init.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import SymmetricProject.positivity_ext


/- hack to avoid the real powers bug -/
local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

/- The purpose of this file is to prove the some "cheap" Stirling bounds for factorial and binomial coefficients.
-/

open Real
open Nat
open Finset
open BigOperators

/-- n! is upper bounded by n^n -/
lemma factorial_le {n : ℕ} : n ! ≤ n^n := by
  induction' n with m hm
  . simp
  rw [factorial_succ, Nat.pow_succ, succ_eq_add_one, mul_comm]
  gcongr
  apply le_trans hm
  gcongr
  linarith

/-- n! is lower bounded by n^n/e^n -/
lemma factorial_ge {n : ℕ} : n ! ≥ n^n / exp n := by
  have h := calc
    exp n ≥ ∑ k in range (n+1), (n:ℝ)^k / k ! := by
      rw [ge_iff_le]
      apply Real.sum_le_exp_of_nonneg
      positivity
    _ ≥ (n:ℝ)^n/n ! := by
      rw [sum_range_succ]
      simp
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

/-- choose n k can be written as a product --/
lemma choose_eq {n : ℕ} {k : ℕ} (h : k ≤ n) : choose n k = (∏ j in range k, (1 - (j:ℝ)/n)) * n^k / k ! := by
  have : choose n k = (descFactorial n k : ℝ) / k ! := by
    rw [descFactorial_eq_factorial_mul_choose]
    have hk : k ! ≠ 0 := by positivity
    field_simp [hk]
    ring
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
  field_simp [(show n ≠ 0 by linarith)]
  symm
  rw [sub_eq_iff_eq_add]
  norm_cast
  rw [Nat.sub_add_cancel]
  linarith

/-- choose n k is bounded above by n^k/k! -/
lemma choose_le {n : ℕ} {k : ℕ} (h : k ≤ n) : choose n k ≤ (n:ℝ)^k / k ! := by
  have h1 : (n:ℝ)^k/k ! = (∏ j in range k, (1:ℝ)) * n^k / (k !:ℝ) := by rw [prod_const_one]; norm_cast; simp
  rw [h1, choose_eq h]
  show (∏ j in range k, (1 - (j:ℝ) / n)) * (n ^ k : ℕ) / (k !:ℝ) ≤ (∏ j in range k, (1:ℝ)) * (n ^ k : ℕ) / (k !:ℝ)
  gcongr with i hi
  . intro i hi
    simp at hi; field_simp
    rw [div_le_iff]
    . simp; linarith
    norm_cast; linarith [hi, h]
  simp at hi; field_simp; positivity

/-- choose n k is bounded below by n^k/k^k -/
lemma choose_ge {n : ℕ} {k : ℕ} (h : k ≤ n) : choose n k ≥ (n:ℝ)^k / (k:ℝ)^k := by
  suffices : (k:ℝ)^k * choose n k ≥  (choose k k) * n^k
  . simp at this
    rw [ge_iff_le, div_le_iff, mul_comm]
    . exact this
    induction' k with m _
    . simp
    positivity

  rw [choose_eq h, choose_eq (show k ≤ k by linarith)]
  field_simp
  rw [<-mul_assoc, mul_comm ((k:ℝ)^k) _]
  gcongr with i hi
  . intro i hi
    simp at hi; field_simp
    rw [div_le_iff]
    . simp; linarith
    norm_cast; linarith [hi, h]
  simp at hi; norm_cast; linarith


lemma choose_le' {n : ℕ} {k : ℕ} (h : k ≤ n) (h2 : 0 < k): (choose n k : ℝ)^((1:ℝ) / k) ≤ (exp 1) * n / k := by
  replace h2 : 0 < (k:ℝ) := by norm_cast
  rw [<- rpow_le_rpow_iff _ _ h2, <- rpow_mul, div_rpow, mul_rpow, (show 1/(k:ℝ) * k = 1 by field_simp), exp_one_rpow]
  . simp
    apply (le_trans (choose_le h) _)
    rw [div_le_div_iff]
    . calc
        (n:ℝ)^k * (k:ℝ)^k = (rexp k) * (n:ℝ)^k * ((k:ℝ)^k / (rexp k)) := by field_simp; ring
        _ ≤ (rexp k) * (n:ℝ)^k * k ! := by
          gcongr
          rw [<-ge_iff_le, (show (k:ℝ)^k = (k^k :ℕ) by norm_cast)]
          apply factorial_ge
    all_goals {positivity}
  all_goals { positivity }

lemma choose_ge' {n : ℕ} {k : ℕ} (h : k ≤ n) (h2 : 0 < k) : (choose n k : ℝ)^((1:ℝ) / k) ≥  n / k := by
  replace h2 : 0 < (k:ℝ) := by norm_cast
  rw [ge_iff_le, <- rpow_le_rpow_iff _ _ h2, <- rpow_mul, div_rpow, (show 1/(k:ℝ) * k = 1 by field_simp)]
  . simp
    rw [<-ge_iff_le]
    apply choose_ge h
  all_goals {positivity}
