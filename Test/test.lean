import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.List.FinRange



namespace List
variable {ι α : Type*} [AddCommMonoid α]

lemma sum_map_get : ∀ l : List α, ((finRange l.length).map l.get).sum = l.sum
  | [] => rfl
  | a :: l => by
    simp only [length_cons, finRange_succ_eq_map, map_cons, get_cons_zero, map_map,
      sum_cons]
    rw [←sum_map_get l]
    congr


