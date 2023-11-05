import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.CompleteLattice
import Mathlib.Algebra.BigOperators.Ring
import SymmetricProject.attainable
import SymmetricProject.prev_bound
import SymmetricProject.jensen
import SymmetricProject.main_lemmas
import SymmetricProject.Tactic.RwIneq

/- In this file the power notation will always mean the base and exponent are real numbers. -/
local macro_rules | `($x ^ $y)   => `(HPow.hPow ($x : ℝ) ($y : ℝ))

/- In this file the division  notation will always mean division of real numbers. -/
local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))

/- In this file, inversion will always mean inversion of real numbers. -/
local macro_rules | `($x ⁻¹)   => `(Inv.inv ($x : ℝ))

/- The purpose of this file is to prove the main theorem, following the arguments in Section 4 of the paper.
-/

open Real

/-- We first need a set of potential upper bounds A. --/
 def upper_bounds (N:ℕ) := { A : ℝ | 1 ≤ A ∧ ∀ k l n : ℕ, ∀ s : ℕ → ℝ, 0 < k → k ≤ l → l ≤ n →
   n ≤ N → attainable n s →
   |s l|^l⁻¹ ≤ A * max ((l / k)^2⁻¹ * |s k|^k⁻¹) ((l/(k+1))^2⁻¹ * |s (k+1)|^(k+1)⁻¹) }

/-- The first task is to prove that the set of potential upper bounds is nonempty. This follows from the Gopalan-Yehudayoff bound. --/
lemma upper_bounds_nonempty (N:ℕ) : Set.Nonempty (upper_bounds N) := by
  rcases prev_bound with ⟨ C , ⟨ hC, bound⟩ ⟩
  suffices : max 1 (C * N^2⁻¹) ∈ upper_bounds N
  . exact Set.nonempty_of_mem this
  dsimp [upper_bounds]
  constructor
  . simp
  intro k l n s h1 h2 h3 h4 h5
  by_cases h6 : k = l
  . rw [<-one_mul (|s l|^l⁻¹)]
    gcongr
    . simp
    have h7: l ≠ 0 := by linarith
    rw [h6]
    simp [h7]
  have h7 : k+1 ≤ l := by contrapose! h6; linarith
  replace bound := bound l k s (attainable_truncate n l s h3 h5) h7 h1
  apply bound.trans
  gcongr
  . simp; right
    gcongr
    linarith
  . nth_rewrite 1 [<-one_mul (|s k|^(k⁻¹))]
    gcongr
    apply one_le_rpow
    . rw [le_div_iff]; norm_cast; simpa; positivity
    positivity
  nth_rewrite 1 [<-one_mul (|s (k+1)|^(_)⁻¹)]
  rify
  gcongr
  apply one_le_rpow
  . rw [le_div_iff]; norm_cast; simpa; positivity
  positivity

lemma upper_bounds_lower (N:ℕ) : BddBelow (upper_bounds N) := by
  rw [bddBelow_def]
  use 1
  intro A hA
  dsimp [upper_bounds] at hA
  exact hA.left

/-- Now we can define the best constant. --/
noncomputable def best_constant (N:ℕ) := sInf (upper_bounds N)

/-- The best constant is at least one. -/
lemma one_le_best (N:ℕ) : 1 ≤ best_constant N := by
  simp [best_constant]
  apply le_csInf (upper_bounds_nonempty N)
  intro A hA
  exact hA.left

/-- The best constant is a bound. (4.1) in the paper -/
lemma best_constant_bounds { k l n N : ℕ } { s : ℕ → ℝ } (h1 : 0 < k) (h2 : k ≤ l) (h3 : l ≤ n) (h4 : n ≤ N) (h5 : attainable n s) : |s l|^l⁻¹ ≤ best_constant N * max ((l / k )^2⁻¹ * |s k|^k⁻¹) ((l / (k+1) )^2⁻¹ * |s (k+1)|^(k+1)⁻¹) := by
  set Q := max ((l / k )^2⁻¹ * |s k|^k⁻¹) ((l / (k+1) )^2⁻¹ * |s (k+1)|^(k+1)⁻¹)
  set X := |s l|^l⁻¹

  have (ε : ℝ) (hε : 0 < ε) : X ≤ (best_constant N+ε) * Q := by
    have := Real.lt_sInf_add_pos (upper_bounds_nonempty N) hε
    rcases this with ⟨ A, hA, hA' ⟩
    dsimp [upper_bounds] at hA
    have := hA.right k l n s h1 h2 h3 h4 h5
    apply this.trans
    gcongr
    simp [best_constant]
    linarith
  rcases le_or_gt Q 0 with hQ | hQ
  . replace := this 1 (show 0 < 1 by norm_num)
    apply this.trans
    rw [add_mul]
    linarith
  contrapose! this
  use (X - best_constant N * Q) / (2 * Q)
  constructor
  . have : 0 < X - best_constant N * Q := by linarith
    positivity
  have h6 : (X + best_constant N * Q) / 2 < X := by linarith
  convert h6 using 1
  generalize hQ' : Q = Q'
  field_simp [(show 2*Q' ≠ 0 by linarith)]
  ring

/-- Anything less than the best constant isn't a bound.  Implements some convenient normalizations.  Essentially (4.3) in the paper -/
lemma cant_beat_best_constant {N : ℕ} {A : ℝ} (hN: 1 ≤ N) (hA : A < best_constant N) : ∃ k n : ℕ, ∃ s : ℕ → ℝ, (0 < k) ∧ (k ≤ n) ∧ (n ≤ N) ∧ (attainable n s) ∧ |s n| = 1 ∧ 1 ≥ A * max ((n / k )^(2⁻¹) * |s k|^(k⁻¹)) ((n / (k+1) )^(2⁻¹) * |s (k+1)|^((k+1:ℝ)⁻¹)) := by
  rcases le_or_gt A 1 with hA' | hA'
  . use 1, 1, (fun _ ↦ 1)
    constructor; norm_num
    constructor; norm_num
    constructor; exact hN
    constructor; exact attainable_one 1
    simp
    have : max 1 (((1:ℝ) + 1)⁻¹ ^ 2⁻¹) = 1 := by
      simp
      apply rpow_le_one
      all_goals norm_num
    rw [this]
    linarith
  simp [best_constant] at hA
  have not_bound : ¬ A ∈ upper_bounds N := by
    contrapose! hA
    apply csInf_le (upper_bounds_lower N) hA
  simp [upper_bounds] at not_bound
  replace not_bound := not_bound (show 1 ≤ A by linarith)
  rcases not_bound with ⟨ k, l, n, s, h1, h2, h3, h4, h5, h6 ⟩
  have : 0 < |s l| := by
    contrapose! h6
    simp at h6
    rw [h6]
    simp
    rw [Real.zero_rpow (show l⁻¹ ≠ 0 by simp; linarith)]
    positivity
  let s' := (fun m : ℕ ↦ (|s l|^(-l⁻¹))^m * s m)
  use k, l, s'
  constructor; assumption
  constructor; assumption
  constructor; linarith
  constructor
  . convert attainable_scaling l s (|s l|^(-l⁻¹)) (attainable_truncate n l s h3 h1)
    exact rpow_nat_cast _ _
  constructor
  . dsimp
    rw [(show (|s l| ^ (-l⁻¹)) ^ (l:ℕ) = (|s l| ^ (-l⁻¹)) ^ (l:ℝ) by norm_cast), <-rpow_mul, abs_mul, abs_rpow_of_nonneg, abs_abs, neg_mul, inv_mul_cancel, rpow_neg_one, inv_mul_cancel]
    . positivity
    . norm_cast; linarith
    . positivity
    positivity
  rw [ge_iff_le, <-mul_le_mul_right (show 0 < |s l|^l⁻¹ by positivity), mul_assoc, max_mul_of_nonneg, mul_assoc, mul_assoc, le_iff_lt_or_eq]
  left; simp
  convert h6 using 4
  . rw [abs_mul, mul_rpow, abs_pow, ← rpow_nat_cast, <-rpow_mul, abs_rpow_of_nonneg, mul_comm, mul_inv_cancel, abs_abs, rpow_one, <- mul_assoc, <-rpow_add]
    . simp
    all_goals positivity
  rw [ ← rpow_nat_cast]
  rify
  rw [abs_mul, mul_rpow, abs_rpow_of_nonneg, <-rpow_mul, abs_rpow_of_nonneg, mul_comm, mul_inv_cancel, abs_abs, rpow_one, <- mul_assoc, <-rpow_add]
  . simp
  all_goals positivity

/-- a reversed version of the bound from the best constant. (4.2) in the paper -/
lemma best_constant_bounds_rev { k l n N : ℕ } { s : ℕ → ℝ } (h1 : 0 < k) (h2 : k+2 ≤ l) (h3 : l ≤ n) (h4 : n ≤ N) (h5 : attainable n s) : |s l|^l⁻¹ ≤ max ((best_constant N)^(k/(l-(k:ℝ))) * (l/ k )^(k/(2*(l-(k:ℝ)))) * |s (l-k)|^((l-(k:ℝ))⁻¹)) ((best_constant N)^((k+1)/(l-(k+1:ℝ))) * (l/ (k+1) )^((k+1)/(2*(l-(k+1:ℝ)))) * |s (l-(k+1))|^((l-(k+1:ℝ))⁻¹)) := by
  have h6 : 0 ≤ best_constant N := by linarith [one_le_best N]
  by_cases h7 : s l = 0
  . rw [h7, abs_zero, zero_rpow]
    . positivity
    simp; linarith
  have h8 := attainable_zero_eq_one h5
  replace h5 := attainable_truncate n l s h3 h5
  replace h5 := attainable_reflect h5 h7
  set s' : ℕ → ℝ := (fun m ↦ (s (l-m)) / (s l))
  have bound := best_constant_bounds h1 (show k ≤l by linarith) (show l ≤ l by linarith) (show l ≤ N by linarith) h5
  rw [mul_max_of_nonneg _ _ h6] at bound
  simp [h8, abs_mul, mul_rpow, abs_inv, inv_rpow, div_eq_mul_inv] at bound
  simp
  have h3' : 0 < (l:ℝ) := by norm_cast; linarith
  rcases bound with bound | bound
  . left
    rw [<-mul_assoc, <-mul_assoc, <-div_le_iff, <- rpow_neg_one, <- rpow_neg_one (|s l| ^ (k⁻¹)), <- rpow_mul, <- rpow_mul, <- rpow_sub] at bound
    have h9 : 0 < ((l:ℝ) - k) := by
      rify at h2; linarith
    have h10 : 0 < k / ((l:ℝ) - k) := by
      positivity
    have h1' : 0 < (k:ℝ) := by norm_cast
    have h11 : (l⁻¹ * (-1) - k⁻¹ * (-1)) * (k/ ((l:ℝ) - k)) = l⁻¹ := by
      field_simp [h9, h1', h3']; ring
    have h11' : k⁻¹ * (k / ((l:ℝ) - k)) = ((l:ℝ)-(k:ℝ))⁻¹ := by
      field_simp [h9, h1', h3']
    rw [<-rpow_le_rpow_iff _ _ h10, <- rpow_mul, mul_rpow, mul_rpow, <-rpow_mul, h11, h11'] at bound
    convert bound using 3
    rw [div_eq_mul_inv, mul_rpow, mul_rpow, <-inv_rpow, <- rpow_mul, <- rpow_mul]
    congr 2
    . field_simp [h9]
    . field_simp [h9]
    all_goals positivity
  right
  rw [<-mul_assoc, <-mul_assoc, <-div_le_iff, <- rpow_neg_one, <- rpow_neg_one (|s l| ^ (((k:ℝ)+1)⁻¹)), <- rpow_mul, <- rpow_mul, <- rpow_sub] at bound
  have h9 : 0 < ((l:ℝ) - (k+1)) := by
    rify at h2; linarith
  have h10 : 0 < (k+1) / ((l:ℝ) - (k+1)) := by
    positivity
  have h1' : 0 < (k:ℝ)+1 := by norm_cast; linarith
  have h11 : (l⁻¹ * (-1) - (k+1)⁻¹ * (-1)) * ((k+1) / ((l:ℝ) - (k+1))) = l⁻¹ := by
    field_simp [h9, h1', h3']; ring
  have h11' : (k+1)⁻¹ * ((k+1) / ((l:ℝ) - (k+1))) = (l-((k:ℝ)+1))⁻¹ := by
    field_simp [h9, h1', h3']
  rw [<-rpow_le_rpow_iff _ _ h10, <- rpow_mul, mul_rpow, mul_rpow, <-rpow_mul, <-rpow_mul, h11, h11'] at bound
  convert bound using 3
  rw [div_eq_mul_inv, mul_rpow, mul_rpow]
  congr 2
  . field_simp [h9]
  . field_simp [h9]
  all_goals positivity

set_option maxHeartbeats 400000 in
/-- a doubly reversed version of the bound from the best constant. The equation after (4.6) in the paper -/
lemma best_constant_bounds_rev' { k m n N : ℕ } { s : ℕ → ℝ } (h1 : m < k) (h2 : k+2 ≤ n) (h4 : n ≤ N) (h5 : attainable n s) (h6 : |s n| = 1): |s m|^(((n:ℝ)-m)⁻¹) ≤ max ((best_constant N)^(((k:ℝ)-m)/((n:ℝ)-(k:ℝ))) * (((n:ℝ) - m) / ((k:ℝ) - m) )^(((k:ℝ)-m)/(2*((n:ℝ)-k))) * |s k|^((n-(k:ℝ))⁻¹)) ((best_constant N)^(((k:ℝ)+1-m)/(n-((k:ℝ)+1))) * (((n:ℝ) - m) / ((k:ℝ)+1 - m) )^(((k:ℝ)+1-m)/(2*((n:ℝ)-(k+1)))) * |s (k+1)|^((n-((k:ℝ)+1))⁻¹)) := by
  have h8 : s n ≠ 0 := by
    contrapose! h6; rw [h6]; norm_cast
  replace h5 := attainable_reflect h5 h8
  have h9 : m < n := by linarith
  have bound := best_constant_bounds_rev (show 0 < k-m by zify [h1]; zify at h1; linarith) (show k-m+2 ≤ n-m by zify [h1, h9]; zify at h1 h2; linarith) (Nat.sub_le n m) h4 h5
  simp [abs_div, div_rpow, h6] at bound
  have h10 : n - (n-m) = m := by zify [Nat.sub_le n m, h9]; linarith
  have h11 : k-m < n-m := by zify [h1, h9]; zify at h1 h2; linarith
  have h12 : (n-m)-(k-m) = n-k := by zify [h11, h9,h1, (show k ≤ n by linarith)]; linarith
  have h13 : n - (n-k) = k := by zify [Nat.sub_le n k, (show k ≤ n by linarith)]; linarith
  have h11' : k-m+1 < n-m := by zify [h1, h9]; zify at h1 h2; linarith
  have h12' : (n-m)-(k-m+1) = n-(k+1) := by zify [h11', h9,h1, (show k+1 ≤ n by linarith)]; linarith
  have h13' : n - (n-(k+1)) = k+1 := by zify [Nat.sub_le n (k+1), (show k+1 ≤ n by linarith)]; linarith
  have h14: (n-m:ℕ) = n - (m:ℝ) := by rify [h9]
  have h15: (k-m:ℕ) = k - (m:ℝ) := by rify [h1]
  rw [h10, h12, h13, h12', h13',h14,h15] at bound
  simp
  rcases bound with bound | bound
  . left
    convert (config := {closePost := false})  bound using 1
    rw [(show (n-(m:ℝ)) - (k-(m:ℝ)) = n - (k:ℝ) by ring)]
    congr 2
    rw [div_rpow]
    . rify at h9; linarith
    rify at h1; linarith
  right
  convert (config := {closePost := false})  bound using 1
  rw [(show (n-(m:ℝ)) - (k-(m:ℝ)+1) = n - ((k:ℝ)+1) by ring)]
  congr 4
  all_goals ring


open Finset
open BigOperators

set_option maxHeartbeats 400000 in
/-- A form of the main theorem. --/
theorem uniform_bound : ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → best_constant N ≤ C := by
  rcases prev_bound with ⟨ C_prev, hC_prev, bound_prev ⟩
  use max (exp 1) (max (11^2⁻¹ * C_prev * exp 1) (max ((((exp (exp 1)⁻¹) * exp 1))^2) (160 * exp 7)))
  intro N hN
  simp
  let A := rexp (-N⁻¹) * best_constant N
  have hBest := one_le_best N
  have hA : A < best_constant N := by
    suffices : rexp (-N⁻¹) * best_constant N < 1 * best_constant N
    . simpa
    gcongr
    simp; linarith
  have hA' : 0 < A := by positivity
  have hBest' : 0 < best_constant N := by positivity
  have cant := cant_beat_best_constant hN hA
  rcases cant with ⟨ k, n, s, h1, h2, h3, h4, h5, h6 ⟩
  have hn : (n:ℝ) ≠ 0 := by norm_cast; linarith
  rw [ge_iff_le] at h6
  replace h6 := mul_le_mul_of_nonneg_left h6 (show 0 ≤ A⁻¹ by positivity)
  rw [<-mul_assoc, inv_mul_cancel (show A ≠ 0 by positivity)] at h6
  simp [<- exp_neg] at h6
  rcases h6 with ⟨h6, h6'⟩
  by_cases h7 : k = n
  . left
    simp [h7, h5, div_self hn] at h6
    field_simp at h6
    rw [le_div_iff hBest', one_mul] at h6
    apply h6.trans
    rw [show 1/N = N⁻¹ by field_simp]
    exact lem5 hN
  by_cases h8 : k+1 = n
  . left
    have : (k:ℝ)+1 = n := by norm_cast
    simp [h8, this, h5, div_self hn] at h6'
    field_simp at h6'
    rw [le_div_iff hBest', one_mul] at h6'
    apply h6'.trans
    rw [show 1/N = N⁻¹ by field_simp]
    exact lem5 hN
  right
  replace h7 : k+1 ≤ n := by contrapose! h7; linarith
  replace h8 : k+2 ≤ n := by contrapose! h8; linarith
  have hn' : 0 < n^2⁻¹ := by positivity
  by_cases h9 : k ≤ 10
  . replace bound_prev := bound_prev n k s h4 h7 h1
    rw [mul_max_of_nonneg] at bound_prev
    simp [h5] at bound_prev
    left
    rcases bound_prev with bound_prev | bound_prev
    . have := lem6 bound_prev h6 hBest' h1 hN
      apply this.trans
      gcongr
      norm_cast
      linarith
    . rw [(show (k:ℝ)+1 = (k+1:ℕ) by norm_cast)] at h6' bound_prev
      have := lem6 bound_prev h6' hBest' (show 0 < k+1 by linarith) hN
      apply this.trans
      gcongr
      norm_cast
      linarith
    positivity
  right
  replace h9 : k > 10 := by contrapose! h9; linarith
  by_cases h10 : 3 * k ≥ 2 * n
  . left
    have h1' : 0 < n-(k+1) := by
      rify [h7] at h8 ⊢; linarith
    have h2' : n-(k+1)+2 ≤ n := by
      rify [h7] at h9 ⊢; linarith
    have bound := best_constant_bounds_rev h1' h2' (show n ≤ n by linarith) h3 h4
    have h3' : n - (n-(k+1)) = k+1 := by
      rify [Nat.sub_le n (k+1), h7]; linarith
    have h4' : n - (n-(k+1) + 1) = k := by
      have : n-(k+1)+1 = n-k := by
        rify [h2, h7]; linarith
      rw [this]
      rify [Nat.sub_le n k, h2]; linarith
    rify [h2, h7] at bound
    have h5' : n - ((k:ℝ)+1) + 1 = n - (k:ℝ) := by ring
    have h7': 0 < n - ((k:ℝ)+1) := by rify at h8; linarith
    have h8': 0 < n - (k:ℝ) := by  linarith
    simp [h5, h3', h4', h5'] at bound
    have hN0 : 0 < (N:ℝ) := by norm_cast
    rcases bound with bound | bound
    . replace bound := lem0 bound h6' (by positivity) (by positivity)
      rw [(show (k:ℝ)+1 = (k+1:ℕ) by norm_cast)] at bound
      have := lem7 (by linarith) (by linarith) (by linarith) hN hBest' bound
      simp at this
      assumption
    replace bound := lem0 bound h6 (by positivity) (by positivity)
    have := lem7 (by linarith) (by linarith) (by linarith) hN hBest' bound
    simp at this
    assumption
  right
  have eq46 {m : ℕ} (h11: k ≤ m) (h12: m ≤ n) : (Nat.choose n m) * |s m| ≤ ((exp 4) * n / m)^(m/2) := by
    have bound := best_constant_bounds h1 h11 h12 h3 h4
    exact lem8 h1 h11 h12 h3 hBest' bound h6 h6'
  have eq47 {m : ℕ} (h12: m < k) : (Nat.choose n m) * |s m| ≤ ((rexp 7) * (k+1) / ((best_constant N)*m))^m * (n/(k+1))^(m/2) := by
    rcases eq_or_lt_of_le (Nat.zero_le m) with h11 | h11
    . rw [<-h11]
      simp [attainable_zero_eq_one h4]
    have bound := best_constant_bounds_rev' h12 h8 h3 h4 h5
    replace bound := lem9 h9 h11 h12 h8 h3 hBest (by linarith) bound h6 h6'
    exact bound
  -- now the endgame after (4.7) begins
  let δ := 1/20 -- placeholder
  let r := δ * ((k+1)/n)^(2⁻¹)
  have bound := new_inequality' n n s r h4 (show n ≤ n by linarith) (show n ≥ 1 by linarith) (show r > 0 by positivity)
  rw [h5, ge_iff_le] at bound
  clear bound_prev h4 h5 h6 h6' h2 h7 A hA hA' hn' hN h3
  rify at h1 h8 h9 h10
  have : exp (δ^2 * (k+1) / (2*n) ) ≤ 1 + 1^(2/n) * r^2 := by
    have : δ ^ 2 * (k+1) / (2*n) = r^2 / 2 := by
      dsimp
      rw [mul_rpow, <-rpow_mul, (show 2⁻¹ * 2 = 1 by norm_num)]
      field_simp [hn, h1]; left; ring
      all_goals positivity
    rw [(show 1^(2/n) * r^2 = r^2 by simp), this]
    apply lem10
    . positivity
    simp
    rw [abs_of_nonneg, (show 1 = 1 * 1^2⁻¹ by simp)]
    gcongr
    . norm_num
    . rw [div_le_iff]; simp; linarith; positivity
    positivity
  rw_ineq [<-this] at bound; clear this
  rw [lem11 (show k ≤ n+1 by rify; linarith)] at bound
  have eq47a : ∑ m in range k, (Nat.choose n m) * |s m| * r^m ≤ ∑ m in range k, ((rexp 7) * (k+1) / ((best_constant N)*m))^m * (n/(k+1))^(m/2) * r^m := by
    apply Finset.sum_le_sum
    intro m hm
    simp at hm
    rw [mul_le_mul_right]
    . exact eq47 hm
    positivity
  have eq46a : ∑ m in range (n+1-k), (Nat.choose n (k+m)) * |s (k+m)| * r^(k+m) ≤ ∑ m in range (n+1-k), ((exp 4) * n / (k+m))^((k+m)/2) * r^(k+m) := by
    apply Finset.sum_le_sum
    intro m hm
    simp at hm
    have : m+1 ≤ n+1-k := by linarith
    rify [show k ≤ n+1 by rify; linarith] at this
    have h : k+m ≤ n := by rify; linarith
    have h2 : k ≤ k+m := by linarith
    rw [mul_le_mul_right]
    . have := eq46 h2 h
      simp at this
      assumption
    positivity
  have eq47b : ∑ m in range k, (Nat.choose n m) * |s m| * r^m ≤ exp ((rexp 7) * δ * (k+1) / (best_constant N) ) := by
    apply eq47a.trans
    have := lem12 k (best_constant N) ((rexp 7) * (k+1)) (n/(k+1)) r (show 0 < best_constant N by linarith) (show 0 < (rexp 7) * (k+1) by positivity) (show 0 < n/(k+1) by positivity) (show 0 < r by positivity)
    convert this using 3
    dsimp
    have h { a b c d e : ℝ} : a*b*c*(d*e) = a*d*b*(c*e) := by ring
    rw [h, <- mul_rpow]
    have h2 : 0 < (k:ℝ)+1 := by linarith
    field_simp [hn, h2]
    all_goals positivity
  have eq46b : ∑ m in range (n+1-k), (Nat.choose n (k+m)) * |s (k+m)| * r^(k+m) ≤ 2 * 2^(-k) := by
    apply eq46a.trans
    apply le_trans _ (lem14 (n+1-k) k)
    apply Finset.sum_le_sum
    intro m hm
    rw [(show (k+m)/2 = 2⁻¹ * (k+m) by field_simp), rpow_mul, <-mul_rpow]
    apply rpow_le_rpow
    . positivity
    dsimp
    exact lem13 h9 hn
    all_goals positivity
--  `rw_ineq [eq46b, eq47b] at bound` timed out here, working manually instead
  have bound2 : rexp (δ ^ 2 * (k + 1) / (2 * n)) ^ (n / 2) ≤ rexp (rexp 7 * δ * (k + 1) / best_constant N) + 2 * 2 ^ (-k) := by
    apply bound.trans
    gcongr
    convert eq46b
    norm_cast
  dsimp at bound2
  clear eq46 eq47 eq46a eq46b eq47a eq47b bound r h10 h8 s hBest δ
  exact lem16 h9 hn bound2
