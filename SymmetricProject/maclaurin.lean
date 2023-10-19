import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Finset.Fin
import Mathlib.Data.Fintype.Fin
import SymmetricProject.newton
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Order.Basic

/-! Proof of the Maclaurin inequality - monotone decreasing nature of s_k^{1/k} when the s_k are non-negative.

Proof follows the sketch in LaTeX/symmetric.tex
-/

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

theorem maclaurin (n k l : ℕ) (s : ℕ → ℝ) (h1 : attainable n s) (h2 : ∀ i ∈ range (n+1), 0 < s i) (h3 : l ∈ range (n+1)) (h4 : k ∈ range (l+1)) (h5 : k > 0): (s l)^((1:ℝ)/l) ≤ (s k)^((1:ℝ)/k) := by
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
    simp at hi
    simp at hk
    have h : i ∈ range (n+1) := by simp; linarith
    have h' : i+1 ∈ range (n+1) := by simp; linarith
    exact div_pos (h2 (i + 1) h') (h2 i h)

  have hd_mono : ∀ i ∈ range k, d (i+1) ≤ d i := by
    intro i hi
    simp at hi
    simp at hk
    have sss := newton i hi
    dsimp
    have h : i ∈ range (n+1) := by simp; linarith
    have h' : i+1 ∈ range (n+1) := by simp; linarith
    rw [(show i+1+1 = i+2 by ring)]
    have h3 := h2 i h
    have h4 := h2 (i+1) h'
    calc s (i+2) / s (i+1) = (s i * s (i+2)) / (s i * (s (i+1))) := by
          field_simp
          ring
      _ ≤ s (i+1)^2 / (s i * (s (i+1))) := by gcongr
      _ = s (i+1) / s i := by
        field_simp
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
    have hm2 : m ∈ range (n+1) := by
      simp
      simp at hk
      simp [Nat.succ_eq_add_one] at hi
      linarith
    have hm3 := h2 m hm2
    field_simp
    ring

  have hdd : d k^k ≤ ∏ j in range k, d j := by
    rw [pow_eq_prod_const]
    have hk'' : k ∈ range (k+1) := by simp
    gcongr with j hj
    · intro j _
      have dk := hd_pos k hk''
      linarith
    · have hj' : j ∈ range (k+1) := by
        simp; simp at hj; linarith
      exact hd_mono' k hk'' j hj'

  simp at hk
  have hk3 : k ∈ range (n+1) := by simp; linarith
  have hk3' : k+1 ∈ range (n+1) := by simp; linarith

  have h2k := h2 k hk3
  have h2k' := h2 (k+1) hk3'
  clear hk h0 newton hd_pos hd_mono hd_mono'
  have kkk : (0:ℝ) < k * (k+(1:ℝ)) := by positivity

  by_contra hs
  simp at hs
  have ht : 0 ≤ s k := by linarith
  have ht' : 0 ≤  s (k+1) := by linarith
  have hu : 0 ≤ (s k)^((1:ℝ) / k) := by positivity
  simp at hu
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
  have hs'' : s k^((k:ℝ)+1) = s k^(k+1) := by norm_cast

  have hw : k ∈ range (k+2) := by simp
  have hw' : k+1 ∈ range (k+2) := by simp
  rw [hs'', hds k hw, hds (k+1) hw', prod_range_succ, mul_pow, pow_succ, <- hds k hw]
  rw [mul_comm (s k)]
  gcongr
  rw [hds k hw]
  assumption


-- Now we develop the limiting argument to extend Maclaurin's inequality to non-negative variables

open Topology

def Rplus := {x : ℝ | x > 0}

lemma lim_of_le {f g : ℝ → ℝ} (hf : ContinuousWithinAt f Rplus 0) (hg : ContinuousWithinAt g Rplus 0) (h : ∀ x ∈ Rplus, f x ≤ g x) : f 0 ≤ g 0 := by
  apply ContinuousWithinAt.closure_le _ hf hg h
  . -- proving that 0 is in the closure of Rplus.  Presumably this is already in MathLib?
    rw [Real.mem_closure_iff]
    intro ε hε
    use ε/2
    constructor
    . simp [Rplus]
      positivity
    simp
    rw [abs_lt]
    constructor
    . linarith
    linarith

theorem maclaurin' (n k l : ℕ) (x : ℕ → ℝ) (h1 : ∀ i ∈ range n, x i ≥ 0) (h2 : l ∈ range (n+1)) (h3 : k ∈ range (l+1)) (h4 : k > 0): (esymm n l x / Nat.choose n l)^((1:ℝ)/l) ≤ (esymm n k x / Nat.choose n k)^((1:ℝ)/k) := by
  set x_eps := fun (ε : ℝ) (k : ℕ) ↦ x k + ε with hx_eps
  set s_eps := fun (ε : ℝ) (k : ℕ) ↦ esymm n k (x_eps ε) / Nat.choose n k with hs_eps

  have hs1 : ∀ ε ∈ Rplus, attainable n (s_eps ε) := by
    intro ε hε
    simp [Rplus] at hε
    unfold attainable
    use x_eps ε
    intro k hk
    simp [hs_eps, hx_eps]
    have nkp : Nat.choose n k > 0 := by
      apply Nat.choose_pos
      linarith
    field_simp

  have hs2: ∀ ε ∈ Rplus, ∀ i ∈ range (n+1), 0 < s_eps ε i := by
    intro ε hε i hi
    simp at hi
    simp [Rplus] at hε
    simp [hs_eps]
    have nkp : (Nat.choose n i:ℝ) > 0 := by
      norm_cast
      apply Nat.choose_pos
      linarith
    suffices : 0 < esymm n i (x_eps ε)
    . show 0 < (esymm n i (x_eps ε)) / (Nat.choose n i)
      positivity
    apply esymm_pos
    . linarith
    intro i hi
    dsimp
    linarith [h1 i hi]

  have hmac : ∀ ε ∈ Rplus, (s_eps ε l)^((1:ℝ)/l) ≤ (s_eps ε k)^((1:ℝ)/k) := by
    intro ε hε
    apply maclaurin _ _ _ _ (hs1 ε hε) (hs2 ε hε) h2 h3 h4

  have h0 : ∀ k : ℕ, s_eps 0 k = esymm n k x / (Nat.choose n k) := by
    intro k
    simp [hs_eps]

  rw [<- h0 l, <- h0 k]

  have h5 : l>0 := by simp at h3; linarith

  set f := fun (ε : ℝ) => (s_eps ε l)^((1:ℝ)/l) with hf
  set g := fun (ε : ℝ) => (s_eps ε k)^((1:ℝ)/k) with hg

  replace hmac : ∀ ε ∈ Rplus, f ε ≤ g ε := by
    intro ε hε
    rw [hf, hg]
    apply hmac
    assumption

  suffices : f 0 ≤ g 0
  . rw [hf, hg] at this
    assumption

  have h6 : k ∈ range (n+1) := by
    simp
    simp at h2
    simp at h3
    linarith

  clear h1 h0 h3 hs1

  have cts : ∀ m ∈ range (n+1), m>0 → ContinuousWithinAt (fun (ε : ℝ) ↦ (s_eps ε m)^((1:ℝ)/m) ) Rplus 0 := by
    intro m hm hm2
    let F := fun (y:ℝ) ↦ y^((1:ℝ)/m)
    let G := fun (ε : ℝ) ↦ s_eps ε m
    have hF : (fun (ε : ℝ) ↦ (s_eps ε m)^((1:ℝ)/m)) = F ∘ G := by
      ext ε
      congr
    rw [hF]

    have hmap : Set.MapsTo G Rplus Rplus := by
      intro ε hε
      exact hs2 ε hε m hm

    apply ContinuousWithinAt.comp _ _ hmap
    . rw [(show G 0 = 0 by simp)]
      sorry
    sorry

  apply lim_of_le _ _ hmac
  . exact cts l h2 h5
  exact cts k h6 h4
