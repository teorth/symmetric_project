import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Init.Order.Defs
import Init.Data.Nat.Basic
import SymmetricProject.binomial

-- basic facts about the expression "esymm n k x" (or $S_{n,k}(x)$) - the k^th elementary symmetric polynomial of the first n variables of an infinite sequence x of real variables


-- I have ended up not using the mathlib library for symmetric polynomials due to various technical type casting / functional programming issues .  A future project would be refactor the arguments here using that library.

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

-- S_{n,0}(x)=1
lemma esymm_zero_eq_one (n : ℕ) (x : ℕ → ℝ) : esymm n 0 x = 1 := by
  simp [esymm, set_binom]

-- S_{n,k}(x)=0 if k>n
lemma esymm_eq_zero (n : ℕ) (k : ℕ) (x : ℕ → ℝ) : (k > n) → esymm n k x = 0 := by
  intro h
  simp [esymm, set_binom_empty h]


-- S_{n,n}(x) = \prod_{i=0}^{n-1} x_i
lemma esymm_prod (n : ℕ) (x: ℕ → ℝ): esymm n n x = (∏ i in range n, x i) := by
  simp [esymm, set_binom]
  have h : powersetLen n (range n) = { range n } := by
    rw [<- powersetLen_self]
    congr
    exact (card_range n).symm
  rw [h]
  apply sum_singleton

-- S_{n,k}(ax) = a^k S_{n,k}(x)
lemma esymm_mul (n : ℕ) (k : ℕ) (x : ℕ → ℝ) (a : ℝ) : esymm n k (fun i => a * x i) = a^k * esymm n k x := by
  simp [esymm]
  rw [mul_sum]
  apply sum_congr rfl
  intro A hA
  rw [prod_mul_distrib]
  congr
  simp
  congr
  simp [set_binom, mem_powersetLen] at hA
  tauto

/-- If S_{n,n}(x) is non-zero, then
$$ S_{n,k}(1/x) = S_{n,n-k}(x) / S_{n,n}(x) $$
for all 0 ≤ k ≤ n
-/

lemma esymm_reflect (n : ℕ) (k : ℕ) (x : ℕ → ℝ) (h : esymm n n x ≠ 0) (hkn : k ≤ n) : esymm n k (fun i => 1 / x i) = esymm n (n-k) x / esymm n n x := by
  have hi : ∀ i : ℕ, i < n → x i ≠ 0 := by
    rw [esymm_prod, prod_ne_zero_iff] at h
    intro i hi
    apply h i
    simp
    assumption
  rw [eq_div_iff h, esymm_prod, esymm, esymm, sum_mul]
  clear h
  rw [<- sdiff_binom_image n k hkn]
  rw [sum_image (sdiff_binom_inj n k)]
  apply sum_congr rfl
  intro A hA
  simp [set_binom, mem_powersetLen] at hA
  rcases hA with ⟨ hAn, cardA ⟩
  clear k cardA hkn
  rw [<- prod_sdiff hAn, mul_comm, mul_assoc]
  nth_rewrite 2 [<- mul_one (∏ i in range n \ A, x i)]
  congr
  rw [<- prod_mul_distrib]
  calc
    ∏ i in A, x i * (1 / x i) = ∏ i in A, 1 := by
      apply prod_congr rfl
      intro i hia
      have hi' : i < n := by
        rw [<- mem_range]
        exact hAn hia
      exact mul_one_div_cancel (hi i hi')
    _ = 1 := by
      exact prod_const_one



/-- The Pascal identity for esymm:

$$S_{n+1,k+1}(x) = S_{n,k+1}(x) + S_{n,k}(x) x_n$$
-/
theorem esymm_pascal (n : ℕ) (k : ℕ) (x : ℕ → ℝ): esymm (n+1) (k+1) x = esymm n (k+1) x + (esymm n k x) * x n := by
  let X := esymm (n+1) (k+1) x
  let Y := esymm n (k+1) x
  let Z := esymm n k x
  show X = Y + Z * x n
  have h : X = esymm (n+1) (k+1) x := by rfl
  rw [esymm, set_pascal, sum_disjUnion (set_pascal_disjoint n k)] at h
  let monom := fun (A:Finset ℕ) => (∏ i in A, x i)

  let W := ∑ A in image (insert n) (set_binom n k), monom A

  have h2: X = Y + W := by
    rw [h]
    simp [esymm]
  rw [h2]
  congr
  clear h h2 X Y

  have h3 : W = ∑ A in (set_binom n k), monom (insert n A) := by
    apply sum_image
    apply insert_binom_inj n k

  rw [h3]
  dsimp [esymm]
  rw [sum_mul]
  clear Z W monom h3

  have h4 : ∀ A ∈ set_binom n k, ∏ i in insert n A, x i = (∏ i in A, x i) * x n := by
    intro A hA
    rw [prod_insert (set_binom_no_n hA)]
    ring
  rw [sum_congr rfl h4]


-- S_{n,1}(x) = \sum_{i=0}^{n-1} x_i
lemma esymm_sum (n : ℕ) (x: ℕ → ℝ): esymm n 1 x = (∑ i in range n, x i) := by
  induction' n with m ih
  . apply esymm_eq_zero 0 1 x (show 1 > 0 by norm_num)
  rw [(show 1 = 0+1 by norm_num), Nat.succ_eq_add_one, esymm_pascal m 0]
  rw [(show 0+1=1 by norm_num), ih, esymm_zero_eq_one m x, one_mul, sum_range_succ]
