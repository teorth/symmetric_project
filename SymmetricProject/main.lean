import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.CompleteLattice
import SymmetricProject.attainable
import SymmetricProject.prev_bound

/- hack to avoid the real powers bug -/
local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

/- The purpose of this file is to prove the main theorem, following the arguments in Section 4 of the paper.
-/

open Real

/-- We first need a set of potential upper bounds A. --/
 def upper_bounds (N:ℕ) := { A : ℝ | 1 ≤ A ∧ ∀ k l n : ℕ, ∀ s : ℕ → ℝ, (0 < k) → (k ≤ l) → (l ≤ n) → (n ≤ N) → (attainable n s) → |s l|^((l:ℝ)⁻¹) ≤ A * max (((l:ℝ) / k )^((2:ℝ)⁻¹) * |s k|^((k:ℝ)⁻¹)) (((l:ℝ) / (k+1) )^((2:ℝ)⁻¹) * |s (k+1)|^((k+1:ℝ)⁻¹)) }

/-- The first task is to prove that the set of potential upper bounds is nonempty. This follows from the Gopalan-Yehudayoff bound. --/
lemma upper_bounds_nonempty (N:ℕ) : Set.Nonempty (upper_bounds N) := by
  rcases prev_bound with ⟨ C , ⟨ hC, bound⟩ ⟩
  suffices : max 1 (C * (N:ℝ)^(2:ℝ)⁻¹) ∈ upper_bounds N
  . exact Set.nonempty_of_mem this
  dsimp [upper_bounds]
  constructor
  . simp
  intro k l n s h1 h2 h3 h4 h5
  by_cases h6 : k = l
  . rw [<-one_mul (|s l|^((l:ℝ)⁻¹))]
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
  . nth_rewrite 1 [<-one_mul (|s k|^((k:ℝ)⁻¹))]
    gcongr
    apply one_le_rpow
    . rw [le_div_iff]; norm_cast; simpa; positivity
    positivity
  nth_rewrite 1 [<-one_mul (|s (k+1)|^(((k+1:ℕ):ℝ)⁻¹))]
  rw [show (k:ℝ)+1 = (k+1:ℕ) by norm_cast]
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
lemma best_constant_bounds { k l n N : ℕ } { s : ℕ → ℝ } (h1 : 0 < k) (h2 : k ≤ l) (h3 : l ≤ n) (h4 : n ≤ N) (h5 : attainable n s) : |s l|^((l:ℝ)⁻¹) ≤ best_constant N * max (((l:ℝ) / k )^((2:ℝ)⁻¹) * |s k|^((k:ℝ)⁻¹)) (((l:ℝ) / (k+1) )^((2:ℝ)⁻¹) * |s (k+1)|^((k+1:ℝ)⁻¹)) := by
  set Q := max (((l:ℝ) / k )^((2:ℝ)⁻¹) * |s k|^((k:ℝ)⁻¹)) (((l:ℝ) / (k+1) )^((2:ℝ)⁻¹) * |s (k+1)|^((k+1:ℝ)⁻¹))
  set X := |s l|^((l:ℝ)⁻¹)

  have (ε : ℝ) (hε : 0 < ε) : X ≤ (best_constant N+ε) * Q := by
    have := Real.lt_sInf_add_pos (upper_bounds_nonempty N) hε
    rcases this with ⟨ A, ⟨ hA, hA' ⟩ ⟩
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
lemma cant_beat_best_constant {N : ℕ} {A : ℝ} (hN: 1 ≤ N) (hA : A < best_constant N) : ∃ k n : ℕ, ∃ s : ℕ → ℝ, (0 < k) ∧ (k ≤ n) ∧ (n ≤ N) ∧ (attainable n s) ∧ |s n| = 1 ∧ 1 ≥ A * max (((n:ℝ) / k )^((2:ℝ)⁻¹) * |s k|^((k:ℝ)⁻¹)) (((n:ℝ) / (k+1) )^((2:ℝ)⁻¹) * |s (k+1)|^((k+1:ℝ)⁻¹)) := by
  rcases le_or_gt A 1 with hA' | hA'
  . use 1, 1, (fun _ ↦ 1)
    constructor; norm_num
    constructor; norm_num
    constructor; exact hN
    constructor; exact attainable_one 1
    simp
    have : max 1 (((1:ℝ) + 1)⁻¹ ^ (2:ℝ)⁻¹) = 1 := by
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
  rcases not_bound with ⟨ k, ⟨ l, ⟨ n, ⟨ s, ⟨ h1, ⟨ h2, ⟨ h3, ⟨ h4, ⟨ h5, h6 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  have : 0 < |s l| := by
    contrapose! h6
    simp at h6
    rw [h6]
    simp
    rw [Real.zero_rpow (show (l:ℝ)⁻¹ ≠ 0 by simp; linarith)]
    positivity
  let s' := (fun m ↦ (|s l|^(-(l:ℝ)⁻¹))^m * s m)
  use k, l, s'
  constructor; assumption
  constructor; assumption
  constructor; linarith
  constructor
  . exact attainable_scaling l s (|s l|^(-(l:ℝ)⁻¹)) (attainable_truncate n l s h3 h1)
  constructor
  . dsimp
    rw [(show (|s l| ^ (-(l:ℝ)⁻¹)) ^ (l:ℕ) = (|s l| ^ (-(l:ℝ)⁻¹)) ^ (l:ℝ) by norm_cast), <-rpow_mul, abs_mul, abs_rpow_of_nonneg, abs_abs, neg_mul, inv_mul_cancel, rpow_neg_one, inv_mul_cancel]
    . positivity
    . norm_cast; linarith
    . positivity
    positivity
  rw [ge_iff_le, <-mul_le_mul_right (show 0 < |s l|^((l:ℝ)⁻¹) by positivity), mul_assoc, max_mul_of_nonneg, mul_assoc, mul_assoc, le_iff_lt_or_eq]
  left; simp
  convert h6 using 4
  . rw [abs_mul, mul_rpow, (show (|s l| ^ (-(l:ℝ)⁻¹)) ^ (k:ℕ) = (|s l| ^ (-(l:ℝ)⁻¹)) ^ (k:ℝ) by norm_cast), abs_rpow_of_nonneg, <-rpow_mul, abs_rpow_of_nonneg, mul_comm, mul_inv_cancel, abs_abs, rpow_one, <- mul_assoc, <-rpow_add]
    . simp
    all_goals positivity
  rw [abs_mul, mul_rpow, (show (|s l| ^ (-(l:ℝ)⁻¹)) ^ (k+1:ℕ) = (|s l| ^ (-(l:ℝ)⁻¹)) ^ (k+1:ℝ) by norm_cast), abs_rpow_of_nonneg, <-rpow_mul, abs_rpow_of_nonneg, mul_comm, mul_inv_cancel, abs_abs, rpow_one, <- mul_assoc, <-rpow_add]
  . simp
  all_goals positivity

/-- a reversed version of the bound from the best constant. (4.2) in the paper -/
lemma best_constant_bounds_rev { k l n N : ℕ } { s : ℕ → ℝ } (h1 : 0 < k) (h2 : k+2 ≤ l) (h3 : l ≤ n) (h4 : n ≤ N) (h5 : attainable n s) : |s l|^((l:ℝ)⁻¹) ≤ max ((best_constant N)^((k:ℝ)/((l:ℝ)-(k:ℝ))) * ((l:ℝ) / k )^((k:ℝ)/(2*((l:ℝ)-k))) * |s (l-k)|^((l-(k:ℝ))⁻¹)) ((best_constant N)^((k+1:ℝ)/((l:ℝ)-(k+1:ℝ))) * ((l:ℝ) / (k+1) )^((k+1:ℝ)/(2*((l:ℝ)-(k+1:ℝ)))) * |s (l-(k+1))|^((l-(k+1:ℝ))⁻¹)) := by
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
    rw [<-mul_assoc, <-mul_assoc, <-div_le_iff, <- rpow_neg_one, <- rpow_neg_one (|s l| ^ ((k:ℝ)⁻¹)), <- rpow_mul, <- rpow_mul, <- rpow_sub] at bound
    have h9 : 0 < ((l:ℝ) - k) := by
      rify at h2; linarith
    have h10 : 0 < (k:ℝ) / ((l:ℝ) - k) := by
      positivity
    have h1' : 0 < (k:ℝ) := by norm_cast
    have h11 : ((l:ℝ)⁻¹ * (-1) - (k:ℝ)⁻¹ * (-1)) * ((k:ℝ) / ((l:ℝ) - k)) = (l:ℝ)⁻¹ := by
      field_simp [h9, h1', h3']; ring
    have h11' : (k:ℝ)⁻¹ * ((k:ℝ) / ((l:ℝ) - k)) = ((l:ℝ)-(k:ℝ))⁻¹ := by
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
  have h10 : 0 < ((k:ℝ)+1) / ((l:ℝ) - (k+1)) := by
    positivity
  have h1' : 0 < (k:ℝ)+1 := by norm_cast; linarith
  have h11 : ((l:ℝ)⁻¹ * (-1) - ((k:ℝ)+1)⁻¹ * (-1)) * (((k:ℝ)+1) / ((l:ℝ) - (k+1))) = (l:ℝ)⁻¹ := by
    field_simp [h9, h1', h3']; ring
  have h11' : ((k:ℝ)+1)⁻¹ * (((k:ℝ)+1) / ((l:ℝ) - (k+1))) = ((l:ℝ)-((k:ℝ)+1))⁻¹ := by
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
lemma best_constant_bounds_rev' { k m n N : ℕ } { s : ℕ → ℝ } (h1 : m < k) (h2 : k+2 ≤ n) (h4 : n ≤ N) (h5 : attainable n s) (h6 : |s n| = 1): |s m|^(((n:ℝ)-m)⁻¹) ≤ max ((best_constant N)^(((k:ℝ)-m)/((n:ℝ)-(k:ℝ))) * (((n:ℝ) - m) / ((k:ℝ) - m) )^(((k:ℝ)-m)/(2*((n:ℝ)-k))) * |s k|^((n-(k:ℝ))⁻¹)) ((best_constant N)^(((k:ℝ)+1-m)/((n:ℝ)-((k:ℝ)+1))) * (((n:ℝ) - m) / ((k:ℝ)+1 - m) )^(((k:ℝ)+1-m)/(2*((n:ℝ)-(k+1)))) * |s (k+1)|^((n-((k:ℝ)+1))⁻¹)) := by
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
  have h14: (n-m:ℕ) = (n:ℝ) - (m:ℝ) := by rify [h9]
  have h15: (k-m:ℕ) = (k:ℝ) - (m:ℝ) := by rify [h1]
  rw [h10, h12, h13, h12', h13',h14,h15] at bound
  simp
  rcases bound with bound | bound
  . left
    convert (config := {closePost := false})  bound using 1
    rw [(show ((n:ℝ)-(m:ℝ)) - ((k:ℝ)-(m:ℝ)) = (n:ℝ) - (k:ℝ) by ring)]
    congr 2
    rw [div_rpow]
    . rify at h9; linarith
    rify at h1; linarith
  right
  convert (config := {closePost := false})  bound using 1
  rw [(show ((n:ℝ)-(m:ℝ)) - ((k:ℝ)-(m:ℝ)+1) = (n:ℝ) - ((k:ℝ)+1) by ring)]
  congr 4
  all_goals ring





/-- A form of the main theorem. --/
theorem uniform_bound : ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → best_constant N ≤ C := by
  use 100 -- placeholder
  intro N hN
  let A := rexp (-(N:ℝ)⁻¹) * best_constant N
  have hA : A < best_constant N := by
    sorry
  have cant := cant_beat_best_constant hN hA
  rcases cant with ⟨ k, ⟨ n, ⟨ s, ⟨ h1, ⟨ h2, ⟨ h3, ⟨ h4, ⟨ h5, h6 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  by_cases h7 : k = n
  . sorry
  by_cases h8 : k+1 = n
  . sorry
  by_cases h9 : k ≤ 10 -- placeholder
  . sorry
  by_cases h10 : 3 * k ≥ 2 * n
  . sorry
  have eq46 {m : ℕ} (h11: k ≤ m) (h12: m ≤ n) : (Nat.choose n m) * |s m| ≤ ((10:ℝ) * n / m)^((m:ℝ)/2) := by -- placeholder
    sorry
  have eq47 {m : ℕ} (h11: 0 < m) (h12: m < k) : (Nat.choose n m) * |s m| ≤ (10 * k / (A*m))^((m:ℝ)) * ((n:ℝ)/k)^((m:ℝ)/2) := by -- placeholder
    sorry
  let δ := (100:ℝ)⁻¹ -- placeholder
  let r := δ * ((k:\R)/n)^((2:ℝ)⁻¹)
  sorry
