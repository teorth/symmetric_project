import Mathlib.Analysis.SpecialFunctions.Pow.Real

/- In this file the power notation will always mean the base and exponent are real numbers. -/
local macro_rules | `($x ^ $y)   => `(HPow.hPow ($x : ℝ) ($y : ℝ))

/- In this file the division  notation will always mean division of real numbers. -/
local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))

/- In this file, inversion will always mean inversion of real numbers. -/
local macro_rules | `($x ⁻¹)   => `(Inv.inv ($x : ℝ))

/- The purpose of this file is to prove some easy lemmas used in the main arguments
-/

open Real

/-- If a ≤ bc and dc ≤ e then ad ≤ bc.  Sort of an le_trans with multiplicative factors. --/
lemma lem0 {a b c d e : ℝ} (h1: a ≤ b * c) (h2: d * c ≤ e) (h3 : 0 ≤ d) (h4 : 0 ≤ b): a * d ≤ b * e := by
  replace h1 := mul_le_mul_of_nonneg_right h1 h3
  replace h2 := mul_le_mul_of_nonneg_left h2 h4
  linarith

/-- A specific rearrangement of a quadruple product that was a bit complicated to do directly from mul_comm and mul_assoc. --/
lemma lem1 {a b c d: ℝ} : (a*b)*(c*d)= (b*d) * (a*c) := by ring

/-- A version of div_le_iff where we use a * c⁻¹ instead of a/c.  --/
lemma lem2 {a b c : ℝ} (h: c>0) : a ≤ b*c ↔ a * c⁻¹ ≤ b := by
  constructor
  . intro this
    rw [<- div_le_iff h] at this
    convert this using 1
  intro this
  rw [<- div_le_iff h]
  convert this using 1

/-- A version of le_div_iff where we use b * c⁻¹ instead of b/c.  --/
lemma lem3 {a b c : ℝ} (h: c>0) : c*a ≤ b ↔ a ≤ b * c⁻¹ := by
  constructor
  . intro this
    rw [<- le_div_iff' h] at this
    convert this using 1
  intro this
  rw [<- le_div_iff' h]
  convert this using 1

/-- a^b ≤ c iff a ≤ c^{b⁻¹}.  --/
lemma lem4 {a b c : ℝ} (ha: 0 ≤ a) (hb : 0 < b) (h: a^b ≤ c) : a ≤ c^b⁻¹ := by
  replace h := rpow_le_rpow (by positivity) h (show 0 ≤ b⁻¹ by positivity)
  convert h using 1
  rw [<- rpow_mul ha, mul_inv_cancel (by positivity)]
  simp
