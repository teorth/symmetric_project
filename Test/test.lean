import Mathlib
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Ring
import SymmetricProject.Tactic.RwIneq

open Finset
open BigOperators
open Real
open Nat


/- In this file the power notation will always mean the base and exponent are real numbers. -/
local macro_rules | `($x ^ $y)   => `(HPow.hPow ($x : ℝ) ($y : ℝ))

/- In this file the division  notation will always mean division of real numbers. -/
local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))

/- In this file, inversion will always mean inversion of real numbers. -/
local macro_rules | `($x ⁻¹)   => `(Inv.inv ($x : ℝ))





lemma lem1 {a b c d: ℝ} : (a*b)*(c*d)= (b*d) * (a*c) := by ring

lemma lem9a {A s t : ℝ} (h : 0 < A) : A^s * (A⁻¹)^t = A^(s-t) := by
  rw [<- rpow_neg_one, <- rpow_mul (show 0 ≤ A by positivity), <-rpow_add h]
  congr 1
  ring

lemma lem9c { k' mR nR A : ℝ } (h2: 0 < mR) (hnk': 0 < nR - k') (hkm': 0 < k' - mR) (hA: 1 ≤ A):  A ^ ((k' - mR) / (nR - k') * (nR - mR) - k' * (nR - mR) / (nR - k')) ≤ A^(-mR) := by
    gcongr
    . assumption
    field_simp [h2, hnk', hkm']
    rw [div_le_iff hnk', (show (k'-mR)*(nR-mR) - k' * (nR-mR) = -(mR * (nR-mR)) by ring), neg_le_iff_add_nonneg]
    ring_nf
    have : 0 ≤ mR * (k'-mR) := by positivity
    convert this using 1
    ring

lemma lem3 {a b c : ℝ} (h: c>0) : c*a ≤ b ↔ a ≤ b * c⁻¹ := by
  constructor
  . intro this
    rw [<- le_div_iff' h] at this
    convert this using 1
  intro this
  rw [<- le_div_iff' h]
  convert this using 1

set_option maxHeartbeats 400000 in
lemma lem9d { kR k' mR nR A NR sm : ℝ } (h1: kR > 10) (h2 : 0 < mR) (h3 : mR < kR) (h5 : nR ≤ NR) (hA: 1 ≤ A) (hk : 3 * kR < 2 * nR) (hk': kR ≤ k') (hk'': k' ≤ kR + 1) (bound: |sm| * (nR / k') ^ (2⁻¹ * (k' * (nR - mR) / (nR - k'))) ≤ A ^ ((k' - mR) / (nR - k') * (nR - mR)) * ((nR - mR) / (k' - mR)) ^ ((k' - mR) / (2 * (nR - k')) * (nR - mR)) * (A⁻¹ * rexp NR⁻¹) ^ (k' * (nR - mR) / (nR - k'))) : |sm| ≤ rexp (mR / (k' - mR) * ((k' - mR) / (2 * (nR - k')) * (nR - mR))) * rexp 4 * A ^ (-mR) * (nR / k') ^ (-mR * (nR - mR) / (2 * (nR - k'))) := by
  have hA' : 0 < A := by linarith
  have hn' : 0 < nR := by linarith
  have h5' : 0 < NR := by linarith
  have hnk' : 0 < nR - k' := by linarith
  have hkm' : 0 < k' - mR := by linarith
  have hk0' : 0 < k' := by linarith
  have hnm : 0 < nR - mR := by linarith

  rw [mul_rpow, lem1, lem9a hA'] at bound
  have tmp := lem9c h2 hnk' hkm' hA
  rw_ineq [tmp] at bound
  have : (nR-mR) / (k'-mR) ≤ (nR/k') * (k'/(k'-mR)) := by
    rw [(show (nR/k') * (k'/(k'-mR)) = nR / (k'-mR) by field_simp [hk0', hkm'])]
    gcongr
    linarith
  rw_ineq [this] at bound; clear this
  have {a b c d e : ℝ} : a * b * c * d * e = b * c * d * (a*e) := by ring
  rw [mul_rpow, mul_comm, lem3, this, <-inv_rpow, lem9a] at bound; clear this
  have : (k'-mR) / (2*(nR-k')) * (nR-mR) - 2⁻¹ * (k'*(nR-mR) / (nR-k')) = -mR*(nR-mR) / (2 * (nR-k')) := by
    field_simp [hk0', hnk', hkm']
    ring
  rw [this, <-exp_mul] at bound; clear this
  have ratio : nR / (nR-k') ≤ 4 := by
    rw [div_le_iff]; linarith; positivity
  have this := calc
    (NR⁻¹ * (k' * (nR-mR) / (nR-k'))) = (k'/NR) * ((nR-mR)/(nR-k')) := by field_simp [hnk', h5']
    _ ≤ 1 * (nR / (nR-k')) := by
      gcongr
      . rw [div_le_iff]; linarith; positivity
      linarith
    _ ≤ 4 := by linarith
  set Y := NR⁻¹ * (k' * (nR-mR) / (nR-k')) with hY
  rw_ineq [this] at bound; clear this Y hY
  have this : k' / (k'-mR) ≤ exp (mR / (k'-mR)) := by
    have : k' / (k'-mR) = mR / (k'-mR) + 1 := by field_simp [hkm']
    rw [this]
    apply add_one_le_exp
  rw_ineq [this] at bound; clear this
  rw [<-exp_mul] at bound
  . assumption
  all_goals positivity
