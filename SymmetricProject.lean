import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

import SymmetricProject.binomial
import SymmetricProject.esymm_basic
import SymmetricProject.esymm_generating
import SymmetricProject.roots_deriv
import SymmetricProject.attainable
import SymmetricProject.jensen

/- the newton and maclaurin files are strictly speaking not needed for the main project, but are of independent interest.  If anyone wishes to convert those files to a  proof of the Newton and Maclaurin inequalities that would be suitable for contributing to the mathlib, be my guest.
-/

/- To do:

* Write a README
* Formalize the rest of Section 2 (current work in progress at prev_bound)
* Formalize the main argument in Section 4
* After the main theorem is formalized, ask for a crowdsourced effort to create MathLib support for the Newton and Maclaurin inequalities, and perhaps also some of the helper lemmas about elementary symmetric polynomials and Finset.mempowersetLen

-/

/- hack to avoid the real powers bug -/
local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

open Finset

/- The purpose of this project is to formalize the results in https://arxiv.org/abs/2310.05328 , hereafter referred to as "the paper".  In particular, to prove the following result: -/
theorem main_theorem : ∃ C : ℝ, (C > 0) ∧ ∀ n : ℕ, ∀ s : ℕ → ℝ, attainable n s → ∀ l ∈ range (n+1), ∀ k ∈ range l, k ≥ 1 →  (s l)^((1:ℝ)/l) ≤ C * ((l:ℝ)/k)^((1:ℝ)/2) * (max ((s k)^((1:ℝ)/k)) ((s (k+1))^((1:ℝ)/(k+1))) ) := by
  sorry
