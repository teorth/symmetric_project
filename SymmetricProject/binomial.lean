import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Finset.Fin
import Mathlib.Data.Fintype.Fin
import Init.Data.Nat.Basic

/-! Basic facts about the set "set_binom n k" (or $\binom{[n]}{k}$) of k-element subsets of $[n] = \{0, \dots, n-1\}$. 

Thanks to Patrick Massot for some optimizations and suggestions.
-/



open Finset

/-- `set_binom n k` is the set $\binom{[n]}{k}$ of k-element subsets of $[n] = \{0, \dots, n-1\}$ -/
def set_binom (n : ℕ) (k : ℕ) : Finset (Finset ℕ) :=
  powersetLen k (range n)

/-- Variant of `set_binom` remembering that everything is `< n`. -/
def set_binom' (n : ℕ) (k : ℕ) : Finset (Finset (Fin n)) :=
  powersetLen k univ

-- The next two lemmas should be in Mathlib, but seem to be missing.
@[simp]
theorem Finset.mapEmbedding_card : (Finset.mapEmbedding f s).card = s.card := by
  simp [Finset.mapEmbedding]

@[simp]
theorem Finset.mem_mapEmbedding : x ∈ Finset.mapEmbedding f s ↔ ∃ y ∈ s, f y = x :=
  Finset.mem_map

abbrev Finset.mapFinVal (n : ℕ) : Finset (Fin n) ↪ Finset ℕ := (Finset.mapEmbedding Fin.valEmbedding).toEmbedding

-- code here provided by Scott Morrison
example : Finset.map (Finset.mapFinVal n) (set_binom' n k) = set_binom n k := by
  -- This feels more complicated than it ought to be!
  simp only [set_binom, set_binom']
  ext s
  simp? [mem_powersetLen] says simp only [gt_iff_lt, mem_map, mem_powersetLen, subset_univ, true_and,
      RelEmbedding.coe_toEmbedding, le_eq_subset, card_range]
  constructor
  · rintro ⟨s, c, rfl⟩
    rw [Finset.mapEmbedding_card] -- why does this not work by simp?! (Perhaps a bug, it should.)
    simp [c]
    intro a h
    rw [Finset.mem_mapEmbedding] at h
    rcases h with ⟨y, _, rfl⟩
    simp
  · rintro ⟨h, rfl⟩
    refine ⟨Finset.attachFin s ?_, ?_⟩
    · intro m w
      specialize h w
      simp_all
    simp? says simp only [card_attachFin, true_and]
    ext m
    rw [Finset.mem_mapEmbedding] -- why does this not work by simp?!
    simp? says simp only [mem_attachFin, Fin.valEmbedding_apply]
    constructor
    · rintro ⟨y, m, rfl⟩
      assumption
    · intro mem
      specialize h mem
      use ⟨m, by simpa using h⟩

-- shorter proof provided by Arend Mellendiijk
example : Finset.map (Finset.mapFinVal n) (set_binom' n k) = set_binom n k := by
  rw[set_binom, set_binom', ←Finset.powersetLen_map,Fin.map_valEmbedding_univ, Nat.Iio_eq_range]

/-- set_binom n k is empty when k > n -/
lemma set_binom_empty {n k : ℕ} (h : n < k) : set_binom n k = ∅ := by
  apply powersetLen_empty
  rwa [card_range]

/-- Elements of set_binom n k do not contain n. -/
lemma set_binom_no_n {n k : ℕ} {A : Finset ℕ} (h : A ∈ set_binom n k) : ¬ n ∈ A := by
  simp [set_binom, mem_powersetLen] at h
  intro nA
  have nn : n ∈ range n := h.1 nA
  simp at nn

/-- Pascal's identity in set form: $\binom{[n+1]}{k+1}$ is the *disjoint* union of $\binom{[n]}{k+1}$ and the image of $\binom{[n]}{k}$ under the insertion map $A \mapsto A \cup \{n\}$.

First, a proof of disjointness: -/
lemma set_pascal_disjoint (n : ℕ) (k : ℕ) : Disjoint (set_binom n (k+1)) (image (insert n) (set_binom n k)) := by
  simp [disjoint_iff_ne]
  rintro A hA B - rfl
  apply set_binom_no_n hA
  simp

-- Then, the set identity:
theorem set_pascal (n : ℕ) (k : ℕ) : set_binom (n+1) (k+1) = disjUnion (set_binom n (k+1)) (image (insert n) (set_binom n k)) (set_pascal_disjoint n k) := by
  simp [set_pascal_disjoint, set_binom, range, powersetLen_succ_insert]


-- To use this, also need the image (insert n) map to be injective on set_binom n k
lemma insert_binom_inj (n : ℕ) (k : ℕ) :
    ∀ A ∈ set_binom n k, ∀ B ∈ set_binom n k, insert n A = insert n B → A = B := by
  rintro A hA B hB hAB
  rw [← erase_insert (set_binom_no_n hA), ← erase_insert (set_binom_no_n hB), hAB]


-- complement (in range n) is injective on set_binom n k
lemma sdiff_binom_inj (n : ℕ) (k : ℕ) :
    ∀ A ∈ set_binom n k, ∀ B ∈ set_binom n k, sdiff (range n) A = sdiff (range n) B → A = B := by
  intro A hA B hB hAB
  have hAn : range n \ (range n \ A) = A := by
    simp [set_binom, mem_powersetLen] at hA
    apply Finset.sdiff_sdiff_eq_self hA.1
  have hBn : range n \ (range n \ B) = B := by
    simp [set_binom, mem_powersetLen] at hB
    apply Finset.sdiff_sdiff_eq_self hB.1
  rw [← hAn, ← hBn, hAB]

-- complement (in range n) maps set_binom n k to set_binom n (n-k) if k ≤ n
lemma sdiff_binom_image (n : ℕ) (k : ℕ) (h : k ≤ n) :
    image (sdiff (range n)) (set_binom n k) = set_binom n (n-k) := by
  ext A
  simp [set_binom, mem_powersetLen]
  constructor
  . rintro ⟨B, ⟨hBn, cardB⟩, rfl⟩
    constructor
    . apply sdiff_subset
    · rw [card_sdiff hBn, card_range, cardB]
  · rintro ⟨hA, cardA⟩
    let B := sdiff (range n) A
    use B
    constructor
    . constructor
      . apply sdiff_subset
      · rw [card_sdiff hA, card_range, cardA]
        exact? says exact Nat.sub_sub_self h
    · exact Finset.sdiff_sdiff_eq_self hA
