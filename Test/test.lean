import Mathlib
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Ring
import SymmetricProject.Tactic.RwIneq

open Finset
open BigOperators
open Real
open Nat

example {a b c d e: ℝ} (h: a ≤ (Real.exp c)*b) (h1 : c ≤ 1) : false := by
  rw_ineq [h1] at h

  sorry
