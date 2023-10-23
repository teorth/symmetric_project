import Mathlib.Tactic.Positivity.Core
import Mathlib.Algebra.BigOperators.Order

/-!
# Extensions to positivity

To help it handle sums and products
-/
open Finset
open BigOperators

open Qq
open Mathlib.Meta.Positivity Lean Meta

@[positivity Finset.sum _ _] def evalSum : PositivityExt where eval {u β2} zβ pβ e := do
  -- let ⟨v, l, r⟩ ← inferTypeQ' <| (Expr.getAppArgs (← withReducible (whnf e))).get! 1
  let .app (.app (.app (.app (.app _ (β : Q(Type u))) (α : Q(Type u))) (_ : Q(AddCommMonoid $β)))
    (s : Q(Finset $α))) (b : Q($α → $β)) ← withReducible (whnf e) | throwError "not sum"
  haveI' : $β =Q $β2 := ⟨⟩
  haveI' : $e =Q Finset.sum $s $b := ⟨⟩
  let (lhs, _, (rhs : Q($β))) ← lambdaMetaTelescope b
  let rb ← core zβ pβ rhs

  let so : Option Q(Finset.Nonempty $s) ← do -- TODO if i make a typo it doesn't complain.?
    try {
      let _ ← synthInstanceQ (q(Fintype $α) : Q(Type u))
      let _ ← synthInstanceQ (q(Nonempty $α) : Q(Prop))
      match s with
      | ~q(@univ _ $fi) => pure (some q(Finset.univ_nonempty (α := $α)))
      | _ => pure none }
    catch _ => do
      let .some fv ← findLocalDeclWithType? q(Finset.Nonempty $s) | pure none
      pure (some (.fvar fv))

  match rb, so with
  | .nonnegative pb, _ => do
    let pα' ← synthInstanceQ (q(OrderedAddCommMonoid $β) : Q(Type u))
    assertInstancesCommute
    let pr : Q(∀ (i : $α), 0 ≤ $b i) ← mkLambdaFVars lhs pb
    pure (.nonnegative q(@sum_nonneg.{u, u} $α $β $pα' $b $s (fun i _ => $pr i)))
  | .positive pb, .some (fi : Q(Finset.Nonempty $s)) => do
    let pα' ← synthInstanceQ (q(OrderedCancelAddCommMonoid $β) : Q(Type u))
    assertInstancesCommute
    let pr : Q(∀ (i : $α), 0 < $b i) ← mkLambdaFVars lhs pb
    pure (.positive q(@sum_pos.{u, u} $α $β $pα' $b $s (fun i _ => $pr i) $fi))
  | _, _ => pure .none


/-- for now simply copy sum to prod version -/
@[positivity Finset.prod _ _] def evalProd : PositivityExt where eval {u β2} zβ pβ e := do
  -- let ⟨v, l, r⟩ ← inferTypeQ' <| (Expr.getAppArgs (← withReducible (whnf e))).get! 1
  let .app (.app (.app (.app (.app _ (β : Q(Type u))) (α : Q(Type u))) (_ : Q(CommMonoid $β)))
    (s : Q(Finset $α))) (b : Q($α → $β)) ← withReducible (whnf e) | throwError "not prod"
  haveI' : $β =Q $β2 := ⟨⟩
  haveI' : $e =Q Finset.prod $s $b := ⟨⟩
  let (lhs, _, (rhs : Q($β))) ← lambdaMetaTelescope b
  let rb ← core zβ pβ rhs

  match rb with
  | .nonnegative pb => do
    let pα' ← synthInstanceQ (q(OrderedCommSemiring $β) : Q(Type u))
    assertInstancesCommute
    let pr : Q(∀ (i : $α), 0 ≤ $b i) ← mkLambdaFVars lhs pb
    pure (.nonnegative q(@prod_nonneg.{u, u} $α $β $pα' $b $s (fun i _ => $pr i)))
  | .positive pb => do
    let pα' ← synthInstanceQ (q(StrictOrderedCommSemiring $β) : Q(Type u))
    let pα'' ← synthInstanceQ (q(Nontrivial $β) : Q(Prop))
    assertInstancesCommute
    let pr : Q(∀ (i : $α), 0 < $b i) ← mkLambdaFVars lhs pb
    pure (.positive q(@prod_pos.{u, u} $α $β $pα' $pα'' $b $s (fun i _ => $pr i)))
  | _ => pure .none

section tests

/-
set_option trace.Tactic.positivity true

lemma oops (n : ℕ) (a : ℕ → ℤ): 0 ≤ ∑ j in range n, a j^2 := by
  positivity

#print axioms oops

#check sum_pos

lemma oops' (n : ℕ) (a : ℕ → ℤ): 0 ≤ ∑ j : Fin 8, ∑ i in range n, a j^2 + i ^ 2 := by
  positivity


lemma oops'' (n : ℕ) (a : ℕ → ℤ): 0 < ∑ j : Fin (n + 1), (a j^2 + 1) := by
  positivity

lemma oops''' (n : ℕ) (a : ℕ → ℤ): 0 < ∑ j in ({1} : Finset ℕ), (a j^2 + 1) := by
  have : Finset.Nonempty {1} := singleton_nonempty 1
  positivity

-/
end tests
