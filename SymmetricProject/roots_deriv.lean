import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Coeff
import Mathlib.Data.Polynomial.Derivative
import Mathlib.Data.Polynomial.Eval
import Mathlib.Data.Polynomial.Splits
import Mathlib.Order.WithBot
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial

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

  have splitP : Splits (RingHom.id ℝ) P := by
    apply splits_prod
    intro k hk
    apply splits_X_sub_C
  
  rw [splits_iff_card_roots, ndegP] at splitP

  let RootsP' := roots P'

  have manyRoots : m+1 ≤ Multiset.card RootsP' + 1 := by
    rw [<- splitP]
    apply card_roots_le_derivative
  
  simp at manyRoots

  have numRoots : Multiset.card RootsP' = m := by
    apply le_antisymm
    . rw [ndegP']
      apply card_roots'
    apply manyRoots
    
  clear degP monicP Pne0 ndegP splitP manyRoots

  have splitP' : Multiset.card RootsP' = m := numRoots

  rw [ndegP', <-splits_iff_card_roots, splits_iff_exists_multiset] at splitP'
  
  rcases splitP' with ⟨ R , hR⟩
  simp [leadP'] at hR

  have h : ∃ (y : ℕ → ℝ), Multiset.prod (Multiset.map (fun x => X - C x) R) = Finset.prod (Finset.range (Multiset.card R)) (fun i => X - C (y i)) := by
    apply multiset_prod_to_finset

-- Multiset.prod (Multiset.map (fun x => X - ↑C x) R)

  sorry
