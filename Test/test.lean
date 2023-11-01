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



example {a b c : ℕ  } (ha : 0 < a) (hc : a < c) : 2 * a ≤ 3 * c  := by
  rw_ineq [(show 2 ≤ 3 by norm_num), hc] at ⊢
  . norm_num
  linarith
