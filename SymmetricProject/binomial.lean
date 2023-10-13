import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic

open Finset

-- set_binom n k is the set of k-element subsets of {0,...,n-1}
def set_binom (n : ℕ) (k : ℕ) : Finset (Finset ℕ) :=
  powersetLen k (range n)

-- Pascal's identity in set form: set_binom (n+1) (k+1) is the *disjoint* union of set_binom n (k+1) and image (insert n) (set_binom n k).  First, a proof of disjointness:

def set_pascal_disjoint (n : ℕ) (k : ℕ) := disjUnion (set_binom n (k+1)) (image (insert n) (set_binom n k)) (by
  simp [disjoint_iff_ne, set_binom]
  intro A hA B hB AnB 
  rw [mem_powersetLen, AnB] at hA
  have nn : n ∈ range n := hA.1 (mem_insert_self n B)
  have nn' : ¬ n ∈ range n := by simp [not_mem_range_self]

  contradiction 
  )
  
-- Then, the set identity:
theorem set_pascal (n : ℕ) (k : ℕ) : set_binom (n+1) (k+1) = set_pascal_disjoint n k := by
  simp [set_pascal_disjoint, set_binom, range, powersetLen_succ_insert] 



