import Mathlib

open Filter Asymptotics Set

noncomputable section

def F (n : ℕ) (k : ℕ) : ℕ := 10 * n * k  -- toy example only
def G (n : ℕ) (k : ℕ) : ℕ := ↑(n^2 + k^2) -- toy example only

lemma est1 : ∃ C : ℕ, ∀ n : ℕ, ∀ k : ℕ, (n ≤ k) → F n k ≤ C * G n k := by
  sorry -- argue that 10 * n * k ≤  10 * k^2 ≤ 10 * (n^2 + k^2)

lemma est2 : ∃ C : ℕ, ∀ n : ℕ, ∀ k : ℕ, (n > k) → F n k ≤ C * G n k := by
  sorry -- argue that 10 * n * k < 10 * n^2 ≤ 10 * (n^2 + k^2)

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
