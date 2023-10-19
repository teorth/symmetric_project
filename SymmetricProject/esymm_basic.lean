import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Init.Order.Defs
import Init.Data.Nat.Basic
import SymmetricProject.binomial

/-!
Basic facts about the expression "esymm n k x" (or $S_{n,k}(x)$) - the k^th elementary symmetric polynomial of the first n variables of an infinite sequence x of real variables

I have ended up not using the mathlib library for symmetric polynomials due to various technical type casting / functional programming issues .  A future project would be refactor the arguments here using that library.

Thanks to Patrick Massot for optimizations and suggestions.
-/

--import Mathlib.RingTheory.MvPolynomial.Basic
--import Mathlib.RingTheory.MvPolynomial.Symmetric
--open MvPolynomial

open Finset
open BigOperators

/-- "esymm n k" is the k^th elementary symmetric polynomial $S_{n,k}(x)$ in the first n of an infinite number $x_1, x_2, \dots$ of real variables.

We define this polynomial directly as a sum of monomials, instead of using MvPolynomial.esymm -/
def esymm (n : ℕ) (k : ℕ) (x : ℕ → ℝ): ℝ := ∑ A in set_binom n k, (∏ i in A, x i)

-- TODO: replace the reals by a more general commutative ring R
-- TODO: relate this function to MvPolynomial.esymm

/-- S_{n,0}(x)=1 -/
@[simp]
lemma esymm_zero_eq_one (n : ℕ) (x : ℕ → ℝ) : esymm n 0 x = 1 := by
  simp [esymm, set_binom]

/-- S_{n,k}(x)=0 if k>n -/
lemma esymm_eq_zero {n k : ℕ} (x : ℕ → ℝ) (h : n < k) : esymm n k x = 0 := by
  simp [esymm, set_binom_empty h]


/-- S_{n,n}(x) = \prod_{i=0}^{n-1} x_i -/
lemma esymm_prod (n : ℕ) (x: ℕ → ℝ): esymm n n x = ∏ i in range n, x i := by
  simp [esymm]
  -- Note how this proof benefits from the added simp lemma `set_binom_self`

/-- S_{n,k}(ax) = a^k S_{n,k}(x) -/
lemma esymm_mul (n k : ℕ) (x : ℕ → ℝ) (a : ℝ) : esymm n k (a * x ·) = a^k * esymm n k x := by
  unfold esymm
  rw [mul_sum]
  apply sum_congr rfl
  intro A hA
  simp [prod_mul_distrib, set_binom_card hA] -- again, adding a lemma earlier makes things easier

-- Note: the combination `sum_image (sdiff_binom_inj _ _)` appear in the next two proofs, hence it could
-- be stated as a lemma.

/-- If S_{n,n}(x) is non-zero, then
$$ S_{n,k}(1/x) = S_{n,n-k}(x) / S_{n,n}(x) $$
for all 0 ≤ k ≤ n
-/
lemma esymm_reflect (n : ℕ) (k : ℕ) (x : ℕ → ℝ) (h : esymm n n x ≠ 0) (hkn : k ≤ n) : esymm n k (1 / x) = esymm n (n-k) x / esymm n n x := by
  field_simp
  rw [esymm_prod, esymm, esymm, sum_mul, ← sdiff_binom_image n k hkn, sum_image (sdiff_binom_inj n k)]
  apply sum_congr rfl
  intro A hA
  have hAn := set_binom_subset hA
  replace hA : ∀ i ∈ A, x i ≠ 0 := by
    rw [esymm_prod, prod_ne_zero_iff] at h
    tauto
  calc (∏ i in A, (1 / x) i) * (∏ i in range n, x i)
    = (∏ i in A, (1 / x) i) * ((∏ i in range n \ A, x i) * ∏ i in A,  x i) := by rw [prod_sdiff hAn]
  _ = (∏ i in A, (1 / x) i) * (∏ i in A,  x i) * (∏ i in range n \ A, x i) := by ring
  _ = ∏ i in range n \ A, x i := by field_simp [prod_ne_zero_iff.2 hA]

/-- The Pascal identity for esymm:

$$S_{n+1,k+1}(x) = S_{n,k+1}(x) + S_{n,k}(x) x_n$$
-/
theorem esymm_pascal (n : ℕ) (k : ℕ) (x : ℕ → ℝ) :
    esymm (n+1) (k+1) x = esymm n (k+1) x + esymm n k x * x n := by
  rw [esymm, set_pascal, sum_disjUnion (set_pascal_disjoint n k)]
  congr
  simp only [sum_image (insert_binom_inj _ _), esymm, sum_mul]
  apply sum_congr rfl
  intro A hA
  rw [prod_insert (set_binom_no_n hA)]
  ring

/-- S_{n,1}(x) = \sum_{i=0}^{n-1} x_i -/
lemma esymm_sum (n : ℕ) (x: ℕ → ℝ): esymm n 1 x = ∑ i in range n, x i := by
  induction' n with m ih
  . exact esymm_eq_zero x (show 1 > 0 by norm_num)
  · simp [ih, esymm_pascal, sum_range_succ]

/-- If n > 0 and the x_i are positive, then S_{n,k}(x) is positive for k <= n. -/
lemma esymm_pos (n k : ℕ) (x: ℕ → ℝ) (h1: k ≤ n) (h2: ∀ i ∈ range n, 0 < x i ) : 0 < esymm n k x := by
  unfold esymm
  apply sum_pos
  . intros A hA
    apply prod_pos
    . intro i hi
      exact h2 i (set_binom_subset hA hi)
  use range k
  simpa [set_binom, mem_powersetLen]
