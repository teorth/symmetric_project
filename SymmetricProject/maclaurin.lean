import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Finset.Fin
import Mathlib.Data.Fintype.Fin
import SymmetricProject.newton
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Proof of the Maclaurin inequality - monotone decreasing nature of s_k^{1/k} when the s_k are non-negative. -/

open Finset


/- hack to avoid the real powers bug -/
local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)


theorem maclaurin (n l : ℕ) (s : ℕ → ℝ) (h1 : attainable n s) (h2 : ∀ i : ℕ, 0 ≤ s i) (h3 : l ∈ range (n+1)) : ∀ k:ℕ, k ≤ l ∧ 0 < k → (s l)^(1/l) ≤ (s k)^(1/k) := by
  -- first reduce to the case l = k+1
  suffices : ∀ m ∈ range n, m ≥ 1 → (s (m+1))^(1 / (m+1)) ≤ (s m)^(1 / m)
  . sorry

  intro k hk hk'

  have newton : ∀ i ∈ range k, s i * s (i+2) ≤ s (i+1)^2 := by
    sorry
  
/- divide into cases depending on whether s_k vanishes -/

  let vanish := ∃ i ∈ range (k+2), s i = 0

  rcases em vanish with vanishes | nonvanishes
  . sorry

    have hs_prop : ∀ j ∈ range (k+2), j ≥ i → s j = 0 := by
      -- induct
      sorry

    -- conclude

  -- look to see if there is existing tools on convexity / log convexity / monotonicity esp in discrete settings

  def d i := s (i+1) / s i

  have hd_pos : ∀ i ∈ range k+1, d i > 0 := by
    sorry
  
  have hd_mono : ∀ i ∈ range k, d_i > d (i+1) := by
    sorry

  have hd_mono' : ∀ i ∈ range (k+1), ∀ j ∈ range i, d_j > d_i := by
    sorry

  have hds : ∀ i ∈ range (k+1), s i = ∏ j ∈ range i, d i := by
    sorry

  have hdd : d_k^k < ∏ j ∈ range k, d_j := by
    sorry

  -- conclude with real power laws  
  sorry