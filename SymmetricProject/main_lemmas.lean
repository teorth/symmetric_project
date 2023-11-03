import Mathlib.Analysis.SpecialFunctions.Pow.Real
import SymmetricProject.prev_bound
import SymmetricProject.stirling
import SymmetricProject.Tactic.Rify
import SymmetricProject.Tactic.RwIneq

/- In this file the power notation will always mean the base and exponent are real numbers. -/
local macro_rules | `($x ^ $y)   => `(HPow.hPow ($x : ℝ) ($y : ℝ))

/- In this file the division  notation will always mean division of real numbers. -/
local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))

/- In this file, inversion will always mean inversion of real numbers. -/
local macro_rules | `($x ⁻¹)   => `(Inv.inv ($x : ℝ))

/- The purpose of this file is to prove some easy lemmas used in the main arguments
-/

open Real

/-- If a ≤ bc and dc ≤ e then ad ≤ bc.  Sort of an le_trans with multiplicative factors. --/
lemma lem0 {a b c d e : ℝ} (h1: a ≤ b * c) (h2: d * c ≤ e) (h3 : 0 ≤ d) (h4 : 0 ≤ b): a * d ≤ b * e := by
  replace h1 := mul_le_mul_of_nonneg_right h1 h3
  replace h2 := mul_le_mul_of_nonneg_left h2 h4
  linarith

/-- A specific rearrangement of a quadruple product that was a bit complicated to do directly from mul_comm and mul_assoc. --/
lemma lem1 {a b c d: ℝ} : (a*b)*(c*d)= (b*d) * (a*c) := by ring

/-- A version of div_le_iff where we use a * c⁻¹ instead of a/c.  --/
lemma lem2 {a b c : ℝ} (h: c>0) : a ≤ b*c ↔ a * c⁻¹ ≤ b := by
  constructor
  . intro this
    rw [<- div_le_iff h] at this
    convert this using 1
  intro this
  rw [<- div_le_iff h]
  convert this using 1

/-- A version of le_div_iff where we use b * c⁻¹ instead of b/c.  --/
lemma lem3 {a b c : ℝ} (h: c>0) : c*a ≤ b ↔ a ≤ b * c⁻¹ := by
  constructor
  . intro this
    rw [<- le_div_iff' h] at this
    convert this using 1
  intro this
  rw [<- le_div_iff' h]
  convert this using 1

/-- a^b ≤ c iff a ≤ c^{b⁻¹}.  --/
lemma lem4 {a b c : ℝ} (ha: 0 ≤ a) (hb : 0 < b) (h: a^b ≤ c) : a ≤ c^b⁻¹ := by
  replace h := rpow_le_rpow (by positivity) h (show 0 ≤ b⁻¹ by positivity)
  convert h using 1
  rw [<- rpow_mul ha, mul_inv_cancel (by positivity)]
  simp


/-- If 1 ≤ N then e^(1/N) ≤ e -/
lemma lem5 {N : ℕ} (h : 1 ≤ N) : rexp N⁻¹ ≤ rexp 1 := by
  rify at h
  have : (0:ℝ) < N := by linarith
  gcongr
  rw [inv_le this]
  simpa; norm_num

/-- the main calculation needed to handle the bounded k case. -/
lemma lem6 {n k N : ℕ} {C s A : ℝ} (h1 : 1 ≤ C * n^2⁻¹ * |s|^k⁻¹) (h2: (n/k)^2⁻¹ * |s|^k⁻¹ ≤ A⁻¹ * rexp N⁻¹) (hA: 0 < A) (hk : 0 < k) (hN: 1 ≤ N) : A ≤ k^2⁻¹ * C * rexp 1 := by
  have hn : 0 < n := by
    contrapose! h1
    replace h1 := (show n = 0 by linarith)
    simp [h1]
  have hC : 0 < C := by
    contrapose! h1
    have := mul_nonpos_of_nonpos_of_nonneg h1 (show 0 ≤ n^2⁻¹ by positivity)
    have := mul_nonpos_of_nonpos_of_nonneg this (show 0 ≤ |s|^k⁻¹ by positivity)
    linarith
  have h3 : A⁻¹ * rexp N⁻¹ ≤ A⁻¹ * rexp 1 := mul_le_mul_of_nonneg_left (lem5 hN) (show 0 ≤ A⁻¹ by positivity)
  replace h2 := h2.trans h3
  have bound := lem0 h1 h2 (by positivity) (by positivity)
  rw [mul_comm A⁻¹ _, <- mul_assoc, <- lem3 (by positivity), one_mul, <-le_div_iff (by positivity)] at bound
  convert bound using 1
  rw [div_rpow, div_div_eq_mul_div]
  field_simp [hk,hn]
  ring
  all_goals positivity

lemma lem7a { a b c d : ℝ } (h1: a ≤ c) (h2: b ≤ d) (h3: 1 ≤ a) (h4: 0 ≤ b) : a^b ≤ c^d := by
  have : a^b ≤ a^d := rpow_le_rpow_of_exponent_le h3 h2
  apply this.trans
  exact rpow_le_rpow (by linarith) h1 (by linarith)

/-- The main calculation needed to handle the k > 2n/3 case. -/
lemma lem7 {n k N : ℕ} {A : ℝ} (h1 : k ≥ 10) (h2 : k+1 ≤ n) (h3: 3*k ≥ 2*n) (hN: 1 ≤ N) (hA: 0 < A) (bound: 1*(n/k)^2⁻¹ ≤ A^(((n:ℝ)-k)/k) * (n/((n:ℝ)-k))^((n-k)/(2*k)) * (A⁻¹ * rexp N⁻¹)) : A ≤ (rexp (rexp 1)⁻¹ * rexp 1)^2 := by --placeholder
  have hk : k ≤ n := by linarith
  have hk' : 0 < k := by linarith
  have hk'': 0 < (k:ℝ) := by norm_cast
  have hn : 0 < n := by linarith
  have hn' : 0 < (n:ℝ) := by norm_cast
  have hkn : k/n ≤ 1 := by
    rw [div_le_iff]; norm_cast; simpa; positivity
  have hN' : rexp N⁻¹ ≤ rexp 1 := lem5 hN
  have h11: 0 < n - (k:ℝ) := by rify at h2; linarith
  have h12: ((n - (k:ℝ)) / k + -1) * (-1) = (2*(k:ℝ) - n) / k := by field_simp [hk'']; ring
  have h13: 0 < 2*(k:ℝ) - n := by rify at h1 h2 h3; linarith

  rw [lem1, <-rpow_neg_one A, <- rpow_add, lem2, one_mul, lem3, <- inv_rpow _ 2⁻¹, inv_div] at bound
  rw_ineq [hN', hkn] at bound
  rw [<- rpow_neg_one, <-rpow_mul] at bound
  rw [h12] at bound
  replace bound := lem4 (by positivity) (by positivity) bound
  apply bound.trans
  clear N hN hN' A hA bound h12
  apply lem7a
  . simp
    have h14 : (n - (k:ℝ)) / (2*k) = (n / (n-(k:ℝ)))⁻¹ * (n / (2*k)) := by
      rw [inv_div]
      field_simp [hn, hk', h11]
    rw [h14, rpow_mul]
    gcongr
    . rw [<- rpow_one (rexp (rexp 1)⁻¹) ]
      apply lem7a
      . exact root_self (by positivity)
      . rw [div_le_iff]; linarith; positivity
      . apply one_le_rpow
        . rw [le_div_iff]; linarith; positivity
        positivity
      positivity
    positivity
  . rw [inv_le, le_div_iff]; field_simp; rify at h1 h2 h3; linarith; all_goals positivity
  . simp
    nth_rewrite 1 [(show (1:ℝ)=(1:ℝ)*1 by norm_num)]
    gcongr
    . apply one_le_rpow
      . rw [le_div_iff]; linarith; positivity
      positivity
    exact one_le_exp (by norm_num)
  all_goals positivity

lemma lem8a { n : ℕ } (h: 0 < n) : n = n^(1/2) * n^(1/2) := by
  rw [<- rpow_add]
  norm_num
  norm_cast

lemma lem8b: rexp 4^(1/2) = (rexp 1) * (rexp 1) := by
  rw [<-exp_mul, <-exp_add]
  congr 1
  norm_num

/-- the main calculation needed to establish (4.6)-/
lemma lem8 { k m n N : ℕ } {s : ℕ → ℝ } {A : ℝ} (h1 : 0 < k) (h2 : k ≤ m) (h3 : m ≤ n) (h4 : n ≤ N) (hA: 0 < A) (bound : |s m|^m⁻¹ ≤ A * max ((m/k)^2⁻¹ * |s k|^k⁻¹) ((m/(k+1))^2⁻¹ * |s (k+1)|^(k+1)⁻¹) ) (h6: (n/k)^2⁻¹ * |s k|^k⁻¹ ≤ A⁻¹ * rexp N⁻¹) (h6': (n/(k+1))^2⁻¹ * |s (k+1)|^(k+1)⁻¹ ≤ A⁻¹ * rexp N⁻¹) : (Nat.choose n m) * |s m| ≤ ((exp 4) * n / m)^(m/2) := by
  have hn : 0 < n := by linarith
  have hm : 0 < m := by linarith
  have hn' : 0 < n^(1/2) := by positivity
  have hm' : 0 < m^(1/2) := by positivity
  rw [mul_max_of_nonneg _ _ (by positivity)] at bound
  simp at bound
  have : |s m|^(1/m) ≤ m^(1/2) * (rexp 1) / n^(1/2) := by
    rcases bound with bound | bound
    . rw [<-mul_assoc] at bound
      replace bound := lem0 bound h6 (by positivity) (by positivity)
      rw [lem1, mul_inv_cancel, mul_comm, lem3, <-inv_rpow, inv_div, div_rpow, div_rpow] at bound
      rw_ineq [lem5 (show 1 ≤ N by linarith)] at bound
      field_simp at bound
      exact bound
      all_goals positivity
    rw [<-mul_assoc] at bound
    replace bound := lem0 bound h6' (by positivity) (by positivity)
    rw [lem1, mul_inv_cancel, mul_comm, lem3, <-inv_rpow, inv_div, div_rpow, div_rpow] at bound
    rw_ineq [lem5 (show 1 ≤ N by linarith)] at bound
    field_simp at bound
    exact bound
    all_goals positivity

  rw [<- rpow_le_rpow_iff _ _ (show 0 < 1/m by positivity), mul_rpow, <-rpow_mul, (show m/2 * (1/m) = (1/2) by field_simp [hm]; ring), div_rpow]
  calc
    (Nat.choose n m)^(1/m) * |s m|^(1/m) ≤ (exp 1) * n / m * |s m|^(1/m) := by
      gcongr
      exact choose_le' h3 hm
    _ ≤ (rexp 1) * n / m * (m^(1/2) * (rexp 1) / n^(1/2) ) := by
      gcongr
    _ = ((rexp 4) * n)^(1/2) / m^(1/2) := by
      rw [mul_rpow]
      field_simp [hn', hm', hm]
      rw [lem8b]
      nth_rewrite 1 [lem8a hn]
      nth_rewrite 3 [lem8a hm]
      ring
      all_goals positivity
  all_goals positivity


lemma lem9a {A s t : ℝ} (h : 0 < A) : A^s * (A⁻¹)^t = A^(s-t) := by
  rw [<- rpow_neg_one, <- rpow_mul (show 0 ≤ A by positivity), <-rpow_add h]
  congr 1
  ring

lemma lem9b {kR mR nR NR A sm sk sk1 : ℝ} (hnm : 0 < nR - mR) (hnk : 0 < nR - (kR+1)) (hnk1 : 0 < nR - kR) (hkm : 0 < kR - mR) (hkm1 : 0 < kR + 1 - mR) (hk0 : 0 < kR) (hk1 : 0 < kR+1) (hA' : 0 < A) (hn' : 0 < nR) (bound: |sm| ^ ((nR - mR)⁻¹) ≤ max (A ^ ((kR - mR) / (nR - kR)) * ((nR - mR) / (kR-mR)) ^ ((kR-mR) / (2 * (nR - kR))) * |sk| ^ (nR - kR)⁻¹)  (A ^ ((kR + 1 - mR) / (nR - (kR + 1))) *((nR - mR) / (kR + 1 - mR)) ^ ((kR + 1 - mR) / (2 * (nR - (kR + 1)))) * |sk1| ^ (nR - (kR + 1))⁻¹)) (h6: (nR/kR)^2⁻¹ * |sk|^kR⁻¹ ≤ A⁻¹ * rexp NR⁻¹) (h6': (nR/(kR+1))^2⁻¹ * |sk1|^(kR+1)⁻¹ ≤ A⁻¹ * rexp NR⁻¹) : ∃ k':ℝ, kR ≤ k' ∧ k' ≤ kR+1 ∧ |sm| * (nR/k')^(2⁻¹ * (k'*(nR-mR)/(nR-k'))) ≤ A^((k'-mR)/(nR-k') * (nR-mR)) * ((nR-mR)/(k'-mR))^((k'-mR)/(2*(nR-k')) * (nR-mR)) * (A⁻¹* rexp NR⁻¹)^(k' * (nR-mR) / (nR-k')) := by
  rw [le_max_iff] at bound
  rcases bound with bound | bound
  . use kR
    constructor; linarith
    constructor; linarith
    replace bound := rpow_le_rpow (by positivity) bound (show 0 ≤ nR - mR by linarith)
    replace h6 := rpow_le_rpow (by positivity) h6 (show 0 ≤ kR * (nR-mR) / (nR - kR) by positivity)
    rw [<-rpow_mul, mul_rpow, mul_rpow, <- rpow_mul, <- rpow_mul, <- rpow_mul, inv_mul_cancel] at bound
    have : kR⁻¹ * (kR * (nR-mR) / (nR-kR)) = (nR-kR)⁻¹ * (nR-mR) := by field_simp [hk0, hnk1, hnm]; ring
    rw [mul_rpow, <-rpow_mul, <-rpow_mul, this] at h6
    replace bound := lem0 bound h6 (by positivity) (by positivity)
    rwa [rpow_one] at bound
    all_goals positivity
  use kR+1
  constructor; linarith
  constructor; linarith
  replace bound := rpow_le_rpow (by positivity) bound (show 0 ≤ nR - mR by linarith)
  replace h6' := rpow_le_rpow (by positivity) h6' (show 0 ≤ (kR+1) * (nR-mR) / (nR - (kR+1)) by positivity)
  rw [<-rpow_mul, mul_rpow, mul_rpow, <- rpow_mul, <- rpow_mul, <- rpow_mul, inv_mul_cancel] at bound
  have : (kR+1)⁻¹ * ((kR+1) * (nR-mR) / (nR-(kR+1))) = (nR-(kR+1))⁻¹ * (nR-mR) := by field_simp [hk1, hnk, hnm]; ring
  rw [mul_rpow, <-rpow_mul, <-rpow_mul, this] at h6'
  replace bound := lem0 bound h6' (by positivity) (by positivity)
  rwa [rpow_one] at bound
  all_goals positivity

lemma lem9c { k' mR nR A : ℝ } (h2: 0 < mR) (hnk': 0 < nR - k') (hkm': 0 < k' - mR) (hA: 1 ≤ A):  A ^ ((k' - mR) / (nR - k') * (nR - mR) - k' * (nR - mR) / (nR - k')) ≤ A^(-mR) := by
    gcongr
    . assumption
    field_simp [h2, hnk', hkm']
    rw [div_le_iff hnk', (show (k'-mR)*(nR-mR) - k' * (nR-mR) = -(mR * (nR-mR)) by ring), neg_le_iff_add_nonneg]
    ring_nf
    have : 0 ≤ mR * (k'-mR) := by positivity
    convert this using 1
    ring

set_option maxHeartbeats 400000 in
-- The main calculation needed to establish (4.7) -/
lemma lem9 {k m n N : ℕ} {A : ℝ} {s : ℕ → ℝ} (h1: k > 10) (h2 : 0 < m) (h3 : m < k) (h4 : k+2 ≤ n) (h5 : n ≤ N) (hA: 1 ≤ A) (hk : 3 * k < 2 * n) (bound: |s m| ^ ((n:ℝ) - m)⁻¹ ≤ max (A ^ (((k:ℝ) - ↑m) / ((n:ℝ) - k)) * (((n:ℝ) - m) / ((k:ℝ) - m)) ^ (((k:ℝ) - m) / (2 * ((n:ℝ) - k))) * |s k| ^ ((n:ℝ) - k)⁻¹) (A ^ (((k:ℝ) + 1 - m) / ((n:ℝ) - ((k:ℝ) + 1))) *(((n:ℝ) - m) / ((k:ℝ) + 1 - m)) ^ (((k:ℝ) + 1 - m) / (2 * ((n:ℝ) - (k + 1)))) * |s (k + 1)| ^ ((n:ℝ) - (k + 1))⁻¹)) (h6: (n/k)^2⁻¹ * |s k|^k⁻¹ ≤ A⁻¹ * rexp N⁻¹) (h6': (n/(k+1))^2⁻¹ * |s (k+1)|^(k+1)⁻¹ ≤ A⁻¹ * rexp N⁻¹) : (Nat.choose n m) * |s m| ≤ (10 * k / (A * m))^m * (n / k)^(m/2) := by
  rify at *
  set nR := (n:ℝ)
  set mR := (m:ℝ)
  set kR := (k:ℝ)
  set NR := (N:ℝ)
  have hnm : 0 < nR - mR := by linarith
  have hA' : 0 < A := by linarith
  have hn' : 0 < nR := by linarith
  have h5' : 0 < NR := by linarith

  have := lem9b hnm (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hA' hn' bound h6 h6'
  clear bound h6 h6'
  rcases this with ⟨ k', hk', hk'', bound ⟩
  rw [mul_rpow, lem1, lem9a hA'] at bound
  have hnk' : 0 < nR - k' := by linarith
  have hkm' : 0 < k' - mR := by linarith
  have hk0' : 0 < k' := by linarith
  have h7 := lem9c h2 hnk' hkm' hA
  set X := A ^ ((k' - mR) / (nR - k') * (nR - mR) - k' * (nR - mR) / (nR - k')) with hX
--  rw_ineq [h7] at bound; clear h7
  have : (nR-mR) / (k'-mR) ≤ (nR/k') * (k'/(k'-mR)) := by
    rw [(show (nR/k') * (k'/(k'-mR)) = nR / (k'-mR) by field_simp [hk0', hkm'])]
    gcongr
    linarith
  rw_ineq [this] at bound; clear this
  have {a b c d e : ℝ} : a * b * c * d * e = b * c * d * (a*e) := by ring
  rw [mul_rpow, mul_comm, lem3, this, <-inv_rpow, lem9a] at bound; clear this
  have : (k'-mR) / (2*(nR-k')) * (nR-m) - 2⁻¹ * (k'*(nR-mR) / (nR-k')) = -mR*(nR-mR) / (2 * (nR-k')) := by
    field_simp [hk0', hnk', hkm']
    ring
  rw [this, <-exp_mul] at bound; clear this
  have ratio : nR / (nR-k') ≤ 4 := by
    rw [div_le_iff]; linarith; positivity
  have this := calc
    (N⁻¹ * (k' * (nR-mR) / (nR-k'))) = (k'/N) * ((nR-mR)/(nR-k')) := by field_simp [hnk', h5']
    _ ≤ 1 * (nR / (nR-k')) := by
      gcongr
      . rw [div_le_iff]; linarith; positivity
      linarith
    _ ≤ 4 := by linarith
  set Y := N⁻¹ * (k' * (nR-mR) / (nR-k')) with hY
  rw_ineq [this] at bound; clear this Y hY
  have this : k' / (k'-mR) ≤ exp (mR / (k'-mR)) := by
    have : k' / (k'-mR) = mR / (k'-mR) + 1 := by field_simp [hkm']
    rw [this]
    apply add_one_le_exp
  rw_ineq [this] at bound; clear this
  rw [<-exp_mul] at bound
  have this := calc
    mR / (k'-mR) * ((k' - mR) / (2 * (nR-k')) * (nR-mR)) = (mR / (2 * (nR-k')) * (nR-m)) := by field_simp [hkm', hnk']; ring
    _ ≤ mR / (2 * (nR-k')) * nR := by gcongr; linarith
    _ = mR * (nR / (nR-k')) / 2 := by field_simp [hnk']; ring
    _ ≤ mR * 4 / 2 := by gcongr
    _ = 2 * mR := by ring
  set Y := mR / (k'-mR) * ((k' - mR) / (2 * (nR-k')) * (nR-mR)) with hY
  rw_ineq [this] at bound; clear this Y hY
  rw [rpow_le_rpow_iff _ _ (show 0 < mR⁻¹ by positivity)] at bound ⊢
  rw [mul_rpow, mul_rpow, mul_rpow, mul_rpow]
  
  . sorry
  all_goals positivity
