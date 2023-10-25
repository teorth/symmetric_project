import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Init.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.ContinuousOn
import SymmetricProject.esymm_basic
import SymmetricProject.attainable
import SymmetricProject.stirling
import SymmetricProject.positivity_ext

theorem extracted_1 {n k : ℕ} {s : ℕ → ℝ} (h2 : attainable n s) (h3 : k + 3 ≤ n) (h4 : 0 < k) (this_1 : ↑n > 0)
  (hsn : ¬s n = 0)
  (bound :
    |s n| ^ ((((n:ℝ) - (k + 1))⁻¹ - (n:ℝ)⁻¹) * ((↑n - (↑k + 1)) / (↑k + 1))) ≤
      (2 * ↑n) ^ ((Real.log (↑n - 1) - Real.log (↑n - (↑k + 1) - 1)) / 2 * ((↑n - (↑k + 1)) / (↑k + 1))) *
        |s (k + 1)| ^ (((n:ℝ) - (k + 1))⁻¹ * ((n:ℝ) - (k + 1)) / (↑k + 1)))
  (h0 : n - (n - (k + 1)) = k + 1) (h5 : 0 < ↑n - (↑k + 1)) (this : 0 < (↑n - (↑k + 1)) / (↑k + 1)) :
  |s n| ^ (↑n)⁻¹ ≤
    (2 * ↑n) ^ ((Real.log (↑n - 1) - Real.log (↑n - (↑k + 1) - 1)) * (↑n - (↑k + 1)) / (2 * (↑k + 1))) *
      |s (k + 1)| ^ ((k:ℝ) + 1)⁻¹ := by
    convert bound using 2
    sorry
