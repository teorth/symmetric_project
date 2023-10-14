import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic

open Finset

-- "set_binom n k" is the set $\binom{[n]}{k}$) of k-element subsets of $[n] = \{0, \dots, n-1\}$

def set_binom (n : ℕ) (k : ℕ) : Finset (Finset ℕ) :=
  powersetLen k (range n)

-- elements of set_binom n k do not contain n.

lemma set_binom_no_n (n : ℕ) (k : ℕ) (A: Finset ℕ) : A ∈ (set_binom n k) → ¬ n ∈ A := by
  intro h
  simp [set_binom, mem_powersetLen] at h
  intro nA
  have nn : n ∈ range n := h.1 nA
  have nn' : ¬ n ∈ range n := by simp 
  contradiction


-- Pascal's identity in set form: $\binom{[n+1]}{k+1}$ is the *disjoint* union of $\binom{[n]}{k+1}$ and the image of $\binom{[n]}{k}$ under the insertion map $A \mapsto A \cup \{n\}$.  First, a proof of disjointness:

def set_pascal_disjoint (n : ℕ) (k : ℕ) : Disjoint (set_binom n (k+1)) (image (insert n) (set_binom n k)) := (by
  simp [disjoint_iff_ne]
  intro A hA B hB hAB
  clear hB
  apply set_binom_no_n n (k+1) A hA
  rw [hAB]
  apply mem_insert_self
  )


-- Then, the set identity:
theorem set_pascal (n : ℕ) (k : ℕ) : set_binom (n+1) (k+1) = disjUnion (set_binom n (k+1)) (image (insert n) (set_binom n k)) (set_pascal_disjoint n k) := by
  simp [set_pascal_disjoint, set_binom, range, powersetLen_succ_insert] 


-- To use this, also need the image (insert n) map to be injective on set_binom n k

theorem insert_binom_inj (n : ℕ) (k : ℕ) : (∀ (A : Finset ℕ), A ∈ (set_binom n k) → ∀ (B : Finset ℕ), B ∈ (set_binom n k) → (insert n A = insert n B) → A = B) := by
  intro A hA B hB hAB
  rw [<-erase_insert (set_binom_no_n n k A hA), <-erase_insert (set_binom_no_n n k B hB), hAB]

#check insert_binom_inj