import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import SymmetricProject.attainable
import SymmetricProject.main


/- In this file the power notation will always mean the base and exponent are real numbers. -/
local macro_rules | `($x ^ $y)   => `(HPow.hPow ($x : ℝ) ($y : ℝ))

/- In this file the division  notation will always mean division of real numbers. -/
local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))

/- In this file, inversion will always mean inversion of real numbers. -/
local macro_rules | `($x ⁻¹)   => `(Inv.inv ($x : ℝ))

open Finset

/- The main result of https://arxiv.org/abs/2310.05328 -/
theorem main_theorem : ∃ C : ℝ, (C > 0) ∧ ∀ n : ℕ, ∀ s : ℕ → ℝ, attainable n s → ∀ l ∈ range (n+1), ∀ k ∈ range l, k ≥ 1 →  |s l|^l⁻¹ ≤ C * (max ((l/k)^2⁻¹ * |s k|^k⁻¹) ((l/(k+1))^2⁻¹ * |s (k+1)|^(k+1)⁻¹))  := by
  rcases uniform_bound with ⟨C, hC⟩
  use C
  have hC' : 0 < C := by
    have := one_le_best 1
    replace hC := hC 1 (show 1 ≤ 1 by rfl)
    linarith
  constructor; assumption
  intro n s hs l hl k hk hk'
  simp at hl hk
  replace hC := hC n (show 1 ≤ n by linarith)
  apply (best_constant_bounds (show 0 < k by linarith) (show k ≤ l by linarith) (show l ≤ n by linarith) (show n ≤ n by linarith) hs).trans
  have := one_le_best n
  gcongr
