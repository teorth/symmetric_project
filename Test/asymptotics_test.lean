import Mathlib

open Filter Asymptotics Set

noncomputable section

def F (n : ℕ) (k : ℕ) : ℕ := 10 * n * k  -- toy example only
def G (n : ℕ) (k : ℕ) : ℕ := ↑(n^2 + k^2) -- toy example only

lemma est1 : ∃ C : ℕ, ∀ n : ℕ, ∀ k : ℕ, (n ≤ k) → F n k ≤ C * G n k := by
  -- 10 * n * k ≤ 10 * k^2 ≤ 10 * (n^2 + k^2)
  refine ⟨10, fun n k hnk ↦ ?_⟩
  have h1 : F n k ≤ 10 * k ^ 2 := by
    simp only [F]
    have : n * k ≤ k * k := Nat.mul_le_mul_right k hnk
    simpa [pow_two, mul_assoc] using Nat.mul_le_mul_left 10 this
  have h2 : 10 * k ^ 2 ≤ 10 * G n k := by
    simp only [G]
    exact Nat.mul_le_mul_left 10 (Nat.le_add_left (k ^ 2) (n ^ 2))
  exact h1.trans h2

lemma est2 : ∃ C : ℕ, ∀ n : ℕ, ∀ k : ℕ, (n > k) → F n k ≤ C * G n k := by
  -- 10 * n * k < 10 * n^2 ≤ 10 * (n^2 + k^2)
  refine ⟨10, fun n k hnk ↦ ?_⟩
  have hnk' : k ≤ n := Nat.le_of_lt hnk
  have h1 : F n k ≤ 10 * n ^ 2 := by
    simp only [F]
    have : n * k ≤ n * n := Nat.mul_le_mul_left n hnk'
    simpa [pow_two, mul_comm n k, mul_assoc] using Nat.mul_le_mul_left 10 this
  have h2 : 10 * n ^ 2 ≤ 10 * G n k := by
    simp only [G]
    exact Nat.mul_le_mul_left 10 (Nat.le_add_right (n ^ 2) (k ^ 2))
  exact h1.trans h2

lemma est1' : ((↑) ∘ ↿F : ℕ × ℕ → ℤ) =O[𝓟 {x | x.1 ≤ x.2}] ((↑) ∘ ↿G : ℕ × ℕ → ℤ) := by
  rcases est1 with ⟨C, hC⟩
  simp [isBigO_principal]
  refine ⟨C, by exact_mod_cast hC⟩

lemma est2' : ((↑) ∘ ↿F : ℕ × ℕ → ℤ) =O[𝓟 {x | x.1 > x.2}] ((↑) ∘ ↿G : ℕ × ℕ → ℤ) := by
  rcases est2 with ⟨C, hC⟩
  simp [isBigO_principal]
  refine ⟨C, by exact_mod_cast hC⟩

example : ((↑) ∘ ↿F : ℕ × ℕ → ℤ) =O[⊤] ((↑) ∘ ↿G : ℕ × ℕ → ℤ) := by
  convert est1'.sup est2'
  rw [← principal_univ, sup_principal, principal_eq_iff_eq, eq_comm, eq_univ_iff_forall]
  exact fun x ↦ le_or_gt x.1 x.2
