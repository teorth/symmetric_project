import Mathlib

open Real

/-- Bounding a monomial x^a by an exponential exp (b*x) with the optimal constant of  (a/eb)^a.  -/
lemma poly_le_exp {x a b:ℝ} (hx: x > 0) (ha : a > 0) (hb: b > 0) : x^a ≤ exp (b*x) * ( a / ((exp 1) * b) )^a := by
  rw [<- log_le_log, log_rpow, log_mul, log_rpow, log_div, log_mul, log_exp, log_exp]
  ring_nf
  suffices : a * log x - a * log a + a * log b ≤ b * x - a
  . linarith
  rw [<- mul_sub, <-mul_add, <-log_div, <- log_mul, (show b * x - a = a * (x / a * b - 1) by field_simp; ring)]
  gcongr
  apply log_le_sub_one_of_pos
  all_goals positivity
