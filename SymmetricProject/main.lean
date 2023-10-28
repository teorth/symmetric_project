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

/-- The best constant is a bound. -/
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

/-- Anything less than the best constant isn't a bound. -/
lemma cant_beat_best_constant {N : ℕ} {A : ℝ} (hN: 1 ≤ N) (hA : A < best_constant N) : ∃ k l n : ℕ, ∃ s : ℕ → ℝ, (0 < k) ∧ (k ≤ l) ∧ (l ≤ n) ∧ (n ≤ N) ∧ (attainable n s) ∧ |s l|^((l:ℝ)⁻¹) ≥ A * max (((l:ℝ) / k )^((2:ℝ)⁻¹) * |s k|^((k:ℝ)⁻¹)) (((l:ℝ) / (k+1) )^((2:ℝ)⁻¹) * |s (k+1)|^((k+1:ℝ)⁻¹)) := by
  rcases le_or_gt A 1 with hA' | hA'
  . use 1, 1, 1, (fun _ ↦ 1)
    constructor; norm_num
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
  use k, l, n, s
  constructor; assumption
  constructor; assumption
  constructor; assumption
  constructor; assumption
  constructor; assumption
  linarith







/-- A form of the main theorem. --/
theorem uniform_bound : ∃ C : ℝ, ∀ N : ℕ, best_constant N ≤ C := by
  sorry
