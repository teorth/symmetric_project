import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Finset.Fin
import Mathlib.Data.Fintype.Fin
import SymmetricProject.newton
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Proof of the Maclaurin inequality - monotone decreasing nature of s_k^{1/k} when the s_k are non-negative. -/

open Finset
open BigOperators

/- hack to avoid the real powers bug -/
local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)


/- if f(i+1) ≤ f(i) for all i in range(n), then f(l) ≤ f(i) for all 0 ≤ i ≤ n -/
lemma monotone_decr {n : ℕ} {f : ℕ → ℝ} (h : ∀ k ∈ range n, f (k+1) ≤ f k) : ∀ l ∈ range (n+1), ∀ k ∈ range (l+1), f l ≤ f k := by
/- it could be possible with some effort to prove this from monotone_nat_of_le_succ, but this requires modifying the function f outside of range(n+1).  Seems easier to just directly induct. -/
  intro l hl
  induction' l with m hm
  . simp 
  have hm2 : m ∈ range (n+1) := by 
    simp
    simp [Nat.succ_eq_add_one] at hl
    linarith
  have hm3 := hm hm2
  clear hm hm2
  intro k hk
  rcases em (k = m+1) with hk2 | hk2
  . rw [Nat.succ_eq_add_one, hk2]
  simp [Nat.succ_eq_add_one] at hk
  have hk3 : k ≤ m + 1 := by linarith [hk]
  have hk4 : k < m + 1 := by contrapose! hk2; linarith 
  simp at hm3
  have hk5 := hm3 k hk4
  rw [Nat.succ_eq_add_one]
  simp [Nat.succ_eq_add_one] at hl
  simp at h
  have hk7 := h m hl
  linarith

theorem maclaurin (n k l : ℕ) (s : ℕ → ℝ) (h1 : attainable n s) (h2 : ∀ i : ℕ, 0 < s i) (h3 : l ∈ range (n+1)) (h4 : k ∈ range (l+1)) (h5 : k > 0): (s l)^((1:ℝ)/l) ≤ (s k)^((1:ℝ)/k) := by
  -- first reduce to the case l = k+1
  suffices : ∀ m ∈ range n, m ≥ 1 → (s (m+1))^((1:ℝ) / (m+1)) ≤ (s m)^((1:ℝ) / m)
  . let g := fun (m: ℕ) => if m=0 then s 1 else (s m)^((1:ℝ)/m)
    have hg : ∀ k ∈ range n, g (k+1) ≤ g k := by
      intro k hk
      rcases em (k = 0) with hk2 | hk2
      . simp [hk2]
      simp [hk2]
      have hk3 : k ≥ 1 := by contrapose! hk2; linarith 
      have h := this k hk hk3
      simp at h
      assumption
    have hg2 := monotone_decr hg l h3 k h4
    have h6 : k ≠ 0 := by linarith
    simp at h4
    have h7 : l ≠ 0 := by linarith
    simp [h6, h7] at hg2
    simp
    assumption 

  intro k hk hk'

  have h0 : s 0 = 1 := attainable_zero_eq_one n s h1
  
  have newton : ∀ i ∈ range k, s i * s (i+2) ≤ s (i+1)^2 := by
    intro i hi
    simp at hi
    simp at hk
    have h : i+2 ≤ n := by linarith
    exact newton_identity n i h s h1
  simp at newton
  clear h4 h5 h3 h1

  let d i := s (i+1) / s i

  have hd_pos : ∀ i ∈ range (k+1), d i > 0 := by
    intro i hi
    dsimp
    exact div_pos (h2 (i + 1)) (h2 i)
  
  have hd_mono : ∀ i ∈ range k, d (i+1) ≤ d i := by
    intro i hi
    simp at hi
    have sss := newton i hi
    dsimp
    rw [(show i+1+1 = i+2 by ring)]
    have h3 := h2 i
    have h4 := h2 (i+1)
    have h5 : 0 < (s i) * (s (i+1)) := by 
      apply Real.mul_pos h3 h4
    calc s (i+2) / s (i+1) = (s i * s (i+2)) / (s i * (s (i+1))) := by 
          field_simp [h3,h4]
          ring
      _ ≤ s (i+1)^2 / (s i * (s (i+1))) := by 
          exact (div_le_div_right h5).mpr sss
      _ = s (i+1) / s i := by 
        field_simp [h3, h4]
        ring
 
  have hd_mono' : ∀ i ∈ range (k+1), ∀ j ∈ range (i+1), d i ≤ d j := by
    apply monotone_decr hd_mono
  
  have hds : ∀ i ∈ range (k+2), s i = (∏ j in range i, d j) := by
    intro i hi
    induction' i with m hm
    . simp [h0]
    simp at hi
    have hi2 : m ∈ range (k+2) := by simp; linarith
    rw [prod_range_succ, <- hm hi2, Nat.succ_eq_add_one]
    dsimp
    have h2m := h2 m
    field_simp [h2m]
    ring

  have hdd : d k^k ≤ ∏ j in range k, d j := by
    rw [pow_eq_prod_const]
    have hk'' : k ∈ range (k+1) := by simp
    have h0 : ∀ j ∈ range k, 0 ≤ d k := by
      intro j _
      have dk := hd_pos k hk''
      linarith
    have h1 : ∀ j ∈ range k, d k ≤ d j := by
      intro j hj
      have hj' : j ∈ range (k+1) := by 
        simp; simp at hj; linarith
      exact hd_mono' k hk'' j hj'
    exact prod_le_prod h0 h1

  have h2k := h2 k
  have h2k' := h2 (k+1)
  clear hk h0 newton hd_pos hd_mono hd_mono' 
  have kkk : (0:ℝ) < k * (k+(1:ℝ)) := by
    have hk'': (k:ℝ) ≥ 1 := by
      exact Nat.one_le_cast.mpr hk'
    apply mul_pos
    linarith [hk'']
    linarith [hk'']
    
  by_contra hs
  simp at hs
  have ht : 0 ≤ s k := by linarith
  have ht' : 0 ≤  s (k+1) := by linarith
  have hu : 0 ≤ (s k)^((1:ℝ) / k) := by 
    apply Real.rpow_nonneg_of_nonneg ht
  have hu' : 0 ≤ (s (k+1))^((1:ℝ) /(k+1)) := by   
    apply Real.rpow_nonneg_of_nonneg ht'
  simp at hu
  simp at hu'
  have hs' := Real.rpow_lt_rpow hu hs kkk 
  rw [<- Real.rpow_mul ht, <- Real.rpow_mul ht'] at hs'
  contrapose! hs'
  have h: (k:ℝ)⁻¹ * ((k:ℝ) * ((k:ℝ) + 1)) = (k:ℝ) + 1 := by 
    field_simp
    ring
  have h': ((k:ℝ) + 1)⁻¹ * ((k:ℝ) * ((k:ℝ) + 1)) = (k:ℝ) := by 
    field_simp
  rw [h, h'] 
  simp 
  have hs'' : s k^((k:ℝ)+1) = s k^(k+1) := by 
    let m := k+1
    have hm : k+1 = m := by rfl
    have hm' : (k:ℝ)+1 = m := by simp
    rw [hm, hm']
    exact Real.rpow_nat_cast (s k) m
    
  have hw : k ∈ range (k+2) := by simp
  have hw' : k+1 ∈ range (k+2) := by simp
  rw [hs'', hds k hw, hds (k+1) hw', prod_range_succ, mul_pow, pow_succ, <- hds k hw]
  have hx : (s k)^k > 0 := by 
    exact pow_pos (h2 k) k
  suffices : d k^k ≤ s k
  . rw [mul_comm (s k)]
    exact (mul_le_mul_left hx).mpr this
  rw [hds k hw]
  assumption





