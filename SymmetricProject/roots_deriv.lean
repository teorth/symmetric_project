import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Coeff
import Mathlib.Data.Polynomial.Derivative
import Mathlib.Data.Polynomial.Eval
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.Order.WithBot

-- The purpose of this file is to establish that the derivative of a real-rooted polynomial is also real-rooted. 

open Finset
open BigOperators
open Polynomial

-- A lemma to convert multiset products to finset products.  Thanks to Yael Dilles for the code.
-- But the "non-evil" thing to do is to not use finsets at all and just use multisets, i.e. do not try to order the roots.
lemma multiset_prod_to_finset {β : Type u} {α : Type v}[CommMonoid β] [Ring α] (A : Multiset α) (f : α → β) :
    ∃ (a : ℕ → α), Multiset.prod (Multiset.map f A) =
      Finset.prod (Finset.range (Multiset.card A)) (fun i => f (a i)) := by
  induction' A using Multiset.induction with n A ih
  · exact ⟨0, by simp⟩
  · obtain ⟨a, ha⟩ := ih
    refine ⟨Function.update a (Multiset.card A) n, ?_⟩
    simp only [Multiset.map_cons, Multiset.prod_cons, ha, Multiset.card_cons, Finset.range_succ,
      Finset.mem_range, lt_self_iff_false, ne_eq, not_false_eq_true, Finset.prod_insert,
      Function.update_same]
    have h (a : β) (b : β) (c : β) : a = b → c*a = c*b := by intro h; rw [h]
    apply h _ _ _
    refine Finset.prod_congr rfl fun x hx ↦ ?_
    rw [Function.update_noteq (Finset.mem_range.1 hx).ne]

-- Fundamental theorem of algebra in finset form
lemma finset_ftoa (P : Polynomial ℝ) : ∃ (z : ℕ → ℂ ), map Complex.ofReal P = C (P.leadingCoeff : ℂ) * ∏ k in range P.natDegree, (X - C (z k)) := by
  let n := P.natDegree
  let f := fun (a : ℂ) => X - C a
  let P_C := map Complex.ofReal P
  let Roots := roots P_C
  have splitsP : Splits Complex.ofReal P := by
    apply IsAlgClosed.splits_codomain
  have cardRoots : Multiset.card Roots = n := by
    rw [<- natDegree_eq_card_roots splitsP]  
  have h : P_C = Polynomial.map Complex.ofReal P := rfl
  rw [<- h]
  rw [eq_prod_roots_of_splits splitsP] at h
  have tmp : ∃ (a : ℕ → ℂ), Multiset.prod (Multiset.map f Roots) = Finset.prod (Finset.range (Multiset.card Roots)) (fun k => f (a k)) := by
    apply multiset_prod_to_finset
  rcases tmp with ⟨ z, hz⟩ 
  rw [hz, cardRoots] at h
  use z
  rw [h]
  simp



theorem real_roots_deriv (n : ℕ) (x : ℕ → ℝ) : ∃ (y : ℕ → ℝ), derivative (∏ k in range n, (X - C (x k))) = (C (n:ℝ)) * (∏ k in range (n-1), (X - C (y k))) := by
  rcases n with _ | m
  . simp
  rw [Nat.succ_eq_add_one]
  simp 

  let P := ∏ k in range (m+1), (X - C (x k))
  let P' := derivative P

  have hP' : P' = derivative P := by rfl
  rw [<- hP']
  clear hP'

  have degP : P.degree = m+1 := by
    rw [degree_prod]
    simp [degree_X_sub_C]
  have monicP : Monic P := by
    apply monic_prod_of_monic
    intro k hk
    simp [monic_X_sub_C]
  have Pne0 : P ≠ 0 := by 
    contrapose! monicP
    simp [monicP]  
  have ndegP : P.natDegree = m+1 := by
    rw [<- degree_eq_iff_natDegree_eq Pne0]
    exact degP
  have coeffP' : coeff P' m = m+1 := by
    rw [coeff_derivative]
    nth_rewrite 1 [<- ndegP]
    rw [Monic.coeff_natDegree monicP]
    ring
  have mne : (m:ℝ) + 1 ≠ 0 := by
    apply ne_of_gt
    apply Nat.cast_add_one_pos
  have P'ne0 : P' ≠ 0 := by
    contrapose! coeffP'
    simp [coeffP']
    contrapose! mne
    linarith
  have ndegP' : P'.degree = P'.natDegree := by
    apply degree_eq_natDegree
    exact P'ne0
  have degP' : P'.degree = m := by
    apply degree_eq_of_le_of_coeff_ne_zero
    . rw [ndegP']
      have ndegP' : P'.natDegree ≤ m+1-1 := by  
        rw [<- ndegP]
        apply natDegree_derivative_le P
      rw [Nat.add_sub_cancel, <- WithBot.coe_le_coe] at ndegP'
      exact ndegP'     
    rw [coeffP']
    exact mne
  rw [degP', Nat.cast_inj] at ndegP'
  have leadP' : leadingCoeff P' = m+1 := by
    rw [<-coeff_natDegree, <- ndegP', coeffP']
  have splitsP' : Splits Complex.ofReal P' := by
    apply IsAlgClosed.splits_codomain
  let P'_C := map Complex.ofReal P'

  have ftoa : ∃ (z : ℕ → ℂ ), P'_C = C (P'.leadingCoeff : ℂ) * ∏ k in range P'.natDegree, (X - C (z k)) := by
    apply finset_ftoa
  
  rcases ftoa with ⟨z, hz⟩
  rw [leadP', <- ndegP'] at hz
  
  -- we have factored P' into a product of linear factors, now we need to show that the roots are real

  have eachRootReal : ∀ (k : ℕ), (k ∈ range m) → (z k).im = 0 := by
    intro k hk
    sorry

  have realRoots : ∃ (y : ℕ → ℝ), ∀ (k : ℕ), (k ∈ range m) → z k = y k := by
    let y : ℕ → ℝ := fun k => if (k ∈ range m) then (z k).re else 0
    use y
    intro k hk
    apply Complex.ext
    . simp at hk
      simp [hk]
    apply eachRootReal
    exact hk
  clear eachRootReal

  rcases realRoots with ⟨y, hy⟩
  use y
  
  clear degP monicP Pne0 ndegP coeffP' mne P'ne0 ndegP' degP' leadP' splitsP'
  
  have pmapInj : Function.Injective (Polynomial.map Complex.ofReal) := by
    apply Polynomial.map_injective
    exact Complex.ofReal_injective

  apply pmapInj

  have hPC : P'_C = map Complex.ofReal P' := rfl
  rw [<- hPC, hz]
  simp
  left
  clear x P P' P'_C hz pmapInj hPC
  rw [Polynomial.map_prod]
  apply prod_congr rfl
  intro k hk
  rw [hy k hk]
  simp


