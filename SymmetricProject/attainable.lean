import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Coeff
import Mathlib.Data.Polynomial.Derivative
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Ring
import SymmetricProject.esymm_basic
import SymmetricProject.esymm_generating
import SymmetricProject.roots_deriv

/-! this file sets up the concept of an attainable sequence - a tuple of real numbers that can be attained as elementary symmetric means.  It also establishes [Lemma 2.1 of the paper], which is a key tool in what follows. -/

open Finset
open BigOperators
open Polynomial
open Nat

/-- attainable n s holds if there exists a sequence of real numbers x such that
$$ S_k(x) = s_k \binom{n}{k}$$
for all $0 \leq k \leq n$.
-/
def attainable (n : ℕ) (s : ℕ → ℝ) : Prop := ∃ (x : ℕ → ℝ), ∀ k : ℕ, k ≤ n → esymm n k x = (s k) * (choose n k)

/- Any attainable sequence starts at one. -/
lemma attainable_zero_eq_one (n : ℕ) (s : ℕ → ℝ) : attainable n s → s 0 = 1 := by
  intro h
  rcases h with ⟨ x, hx ⟩
  have h0: 0 ≤ n := by linarith
  have esymm0 := hx 0 h0
  simp [esymm_zero_eq_one] at esymm0
  symm
  assumption

/- An attainable sequence can be scaled. [Lemma 2.1(i) in the paper] -/
lemma attainable_scaling (n : ℕ) (s : ℕ → ℝ) (a : ℝ) : attainable n s → attainable n (fun k => (a ^ k) * (s k) ) := by
  intro h
  rcases h with ⟨ x, hx ⟩
  use fun k => a * (x k)
  intro k hk
  simp
  rw [esymm_mul]
  simp [hx k hk]
  ring

/-- An attainable sequence can be reflected if its final entry is non-zero. [Lemma 2.1(ii) in the paper]-/
lemma attainable_reflect (n : ℕ) (s : ℕ → ℝ) : attainable n s → s n ≠ 0 → attainable n fun k ↦ s (n - k) / s n := by
  intro h hn
  rcases h with ⟨ x, hx ⟩
  use 1/x
  intro k hk
  rw [esymm_reflect]
  have hnk : n-k ≤ n := sub_le ..
  rw [hx (n-k) hnk, hx n le_rfl]
  simp [choose_symm hk]
  ring
  . contrapose! hn
    simpa [hx n le_rfl] using hn
  assumption


/- If a polynomial $\sum_{k=0}^n a_k z^{n-k}$ vanishes, then all its coefficients vanish.
-/
lemma compare_coeff (n : ℕ) (a: ℕ → ℝ) (h: ∑ k in range (n + 1), monomial (n - k) (a k) = 0) : ∀ k : ℕ, k ≤ n → a k = 0 := by
  intro m hm
  have h' := by congrm(coeff $h (n-m))
  clear h
  rw [finset_sum_coeff, coeff_zero] at h'
  let f : ℕ → ℝ := fun k => if k = m then a m else 0
  have h'' : ∑ b in range (n+1), f b = 0 := by
    rw [<- h']
    apply sum_congr rfl
    intro b hb
    rw [coeff_monomial]
    simp
    have iff : b = m ↔ n-b = n-m := by
      constructor
      . intro bm
        simp [bm]
      intro nbm
      have hb' : b ≤ n := by simp at hb; linarith
      have hm' := Nat.sub_add_cancel hm
      have hb'' := Nat.sub_add_cancel hb'
      linarith [nbm, hm', hb'']

    rcases em (b=m) with bm | bm
    . have nbm : n-b = n-m := by rw [<-iff]; assumption
      simp [bm, nbm]
    have nbm : n-b ≠ n-m := by contrapose! bm; rw [iff]; assumption
    simp [bm, nbm]
  have h''': m ∈ range (n+1) := by
    simp
    linarith
  rw [<- add_sum_erase _ _ h'''] at h''
  simp at h''
  assumption

/- the hardest part (iii) of [Lemma 2.1 of the paper]: if a sequence is attainable, then so is its truncation.-/
lemma attainable_truncate (n : ℕ) (l : ℕ) (s : ℕ → ℝ) (hln : l ≤ n) : attainable n s → attainable l s := by
-- first use induction to reduce to the case where l = n+1
  revert hln l
  induction' n with n ih
  . intro l hln
    simp at hln
    simp [hln]
  intro l hln
  rcases le_or_gt l n with hln' | hln'
  . suffices : attainable (succ n) s → attainable n s
    . intro h
      exact (ih l hln') (this h)
    clear ih l hln hln'
    -- now the main argument begins
    intro h
    rcases h with ⟨ x, hx ⟩

    let P : Polynomial ℝ := ∏ i in (range (succ n)), (X - C (x i))

    have hP : P = ∑ k in range ((succ n)+1), monomial ((succ n)-k) ((-1) ^ ↑k * esymm (succ n) k x) := by
      apply esymm_genfn
    have hy : ∃ (y : ℕ → ℝ), derivative P = (C ((succ n):ℝ)) * (∏ k in range ((succ n)-1), (X - C (y k))) := by
      apply real_roots_deriv

    rcases hy with ⟨ y, hy ⟩
    use y
    rw [succ_sub_one, succ_eq_add_one, esymm_genfn, hP, derivative_sum] at hy

    clear P hP
    have h : ∑ b in range (succ n + 1), derivative ((monomial (succ n - b)) ((-1) ^ b * esymm (succ n) b x)) = ∑ b in range (succ n + 1), (monomial (succ n - b - 1)) ((succ n - b) * (-1) ^ b * s b * ↑(Nat.choose (succ n) b)) := by
      apply sum_congr rfl
      intro b hb
      rw [derivative_monomial]
      simp at hb
      rw [lt_add_one_iff, <- succ_eq_add_one] at hb
      congr! 1
      rw [hx b hb, succ_eq_add_one]
      rw [mul_comm, <-mul_assoc, <-mul_assoc]
      congr
      symm
      rw [sub_eq_iff_eq_add]
      suffices : n+1 = n + 1 - b + b
      . nth_rewrite 1 [this]
        simp
      symm
      apply Nat.sub_add_cancel
      rw [succ_eq_add_one] at hb
      exact hb
    rw [h] at hy
    clear h
    rw [succ_eq_add_one, mul_sum] at hy
    simp at hy
    rw [Finset.sum_range_succ] at hy
    have tmp : ((n:ℝ) + 1 - ↑(n + 1)) = 0 := by
      simp
    rw [tmp] at hy
    simp at hy
    rw [<-sub_eq_zero, <-sum_sub_distrib] at hy
    have hy' : ∑ x in range (n + 1),
    monomial (n - x) ((↑n + 1 - ↑x) * (-1) ^ x * s x * ↑(Nat.choose (n + 1) x) - (↑n + 1) * (-1) ^ x * esymm n x y) = 0 := by
      rw [<- hy]
      apply sum_congr rfl
      intro b hb
      have tmp : n + 1 - b - 1 = n - b := by
        simp at hb
        have hb' : b ≤ n := by linarith
        rw [Nat.sub_add_comm hb']
        simp
      rw [tmp]
      simp
      rw [mul_assoc, <-C_mul_monomial]
      congr
      . simp
    clear tmp hy hx
    have h :  ∀ k : ℕ, k ≤ n → (↑n + 1 - ↑k) * (-1) ^ k * s k * ↑(Nat.choose (n + 1) k) - (↑n + 1) * (-1) ^ k * esymm n k y = 0 := by
       apply compare_coeff n _ hy'
    clear hy'
    intro k hk
    have h' := h k hk
    rw [sub_eq_zero] at h'

    have h'' : (-1)^k * ((↑n + 1 - ↑k) * ↑(Nat.choose (n + 1) k) * s k) = (-1)^k * ((↑n + 1) * esymm n k y) := by
      have : (-1) ^ k * ((↑n + 1) * esymm n k y) = (↑n + 1) * (-1) ^ k * esymm n k y := by ring
      rw [this, <- h']
      ring

    clear h h'

    have h3: (-1:ℝ)^k ≠ 0 := by
      have : (-1:ℝ) ≠ 0 := by norm_num
      exact pow_ne_zero k this
    have h4 := mul_left_cancel₀ h3 h''
    clear h3 h''

    have h5 : ((n:ℝ) + 1 - (k:ℝ)) * (Nat.choose (n + 1) k) = (n + 1) * (Nat.choose n k) := by
      let m := n + 1 - k
      have : ((n:ℝ) + 1 - k) = m :=  by
        rw [sub_eq_iff_eq_add]
        let r := m+k
        have : n + 1 = r := by
          simp
          have : k ≤ n+1 := by linarith
          rw [Nat.sub_add_cancel this]
        have : (n:ℝ) + 1 = r := by
          rw [<- this]
          simp
        rw [this]
        simp
      rw [this]
      let u := m * (Nat.choose (n+1) k)
      have : (m:ℝ) * (Nat.choose (n+1) k) = u := by simp
      rw [this]
      have : u = (n+1) * (Nat.choose n k) := by
        rw [mul_comm, Nat.choose_mul_succ_eq]
        simp
        ring
      rw [this]
      simp
    rw [h5, mul_assoc] at h4
    have h6 : ((n:ℝ) + 1) ≠ 0 := by
      have : n + 1 ≥ 1 := by linarith
      by_contra hn
      have : (n:ℝ) + 1 ≥ 1 := by
        simp [this]
      linarith
    have h7 := mul_left_cancel₀ h6 h4
    clear h4 h5 h6
    rw [<- h7]
    ring

  have hln'' : l = succ n := by
    have : l ≤ n ∨ l = succ n := of_le_succ hln
    linarith
  rw [hln'']
  tauto
