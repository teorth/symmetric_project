import Mathlib.Analysis.SpecialFunctions.Pow.Real
import SymmetricProject.attainable
import SymmetricProject.prev_bound

/- hack to avoid the real powers bug -/
local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

/- The purpose of this file is to prove the main theorem, following the arguments in Section 4 of the paper.
-/

open Real

/-- We first need a set of potential upper bounds A. --/
 def upper_bounds (N:ℕ) := { A : ℝ | ∀ k l n : ℕ, ∀ s : ℕ → ℝ, (0 < k) → (k ≤ l) → (l ≤ n) → (n ≤ N) → (attainable n s) → |s l|^((l:ℝ)⁻¹) ≤ A * max (((l:ℝ) / k )^((2:ℝ)⁻¹) * |s k|^((k:ℝ)⁻¹)) (((l:ℝ) / (k+1) )^((2:ℝ)⁻¹) * |s (k+1)|^((k+1:ℝ)⁻¹)) }

/-- The first task is to prove that the set of potential upper bounds is nonempty. This follows from the Gopalan-Yehudayoff bound. --/
lemma upper_bounds_nonempty (N:ℕ) : Set.Nonempty (upper_bounds N) := by
  rcases prev_bound with ⟨ C , ⟨ hC, bound⟩ ⟩
  suffices : max 1 (C * (N:ℝ)^(2:ℝ)⁻¹) ∈ upper_bounds N
  . exact Set.nonempty_of_mem this
  dsimp [upper_bounds]
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



  sorry

/-- The first task is to introduce the quantity A_N. It degenerates to 0 for N=0 (by the Lean conventions for inf) but (because of the Gopalan-Yehudayoff bound) will be meaningful for N>0. --/
noncomputable def best_constant (N:ℕ) := sInf (upper_bounds N)
