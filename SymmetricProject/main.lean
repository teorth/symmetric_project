import Mathlib.Analysis.SpecialFunctions.Pow.Real
import SymmetricProject.Attainable
import SymmetricProject.prev_bound

/- hack to avoid the real powers bug -/
local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

/- The purpose of this file is to prove the main theorem, following the arguments in Section 4 of the paper.
-/

open Real

/-- We first need a set of potential upper bounds A. --/
 def upper_bounds (N:ℕ) := { A : ℝ | ∀ k l n : ℕ, ∀ s : ℕ → ℝ, (0 < k) → (k ≤ l) → (l ≤ n) → (n ≤ N) → (attainable n s) → |s l|^((l:ℝ)⁻¹) ≤ A * max (((l:ℝ) / k )^((2:ℝ)⁻¹) * |s k|^((k:ℝ)⁻¹)) (((l:ℝ) / (k+1) )^((2:ℝ)⁻¹) * |s (k+1)|^((k+1:ℝ)⁻¹)) }

/-- The first task is to prove that the set of potential upper bounds is nonempty. --/
lemma upper_bounds_nonempty (N:ℕ) (h : 0 < N): Set.Nonempty (upper_bounds N) := by

  sorry

/-- The first task is to introduce the quantity A_N. It degenerates to 0 for N=0 (by the Lean conventions for inf) but (because of the Gopalan-Yehudayoff bound) will be meaningful for N>0. --/
noncomputable def best_constant (N:ℕ) := sInf (upper_bounds N)
