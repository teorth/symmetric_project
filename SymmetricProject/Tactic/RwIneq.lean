import Mathlib.Data.Complex.Exponential

open Lean Meta Elab Term Tactic

/-- Returns a version of `target` where any occurence of `old` as a function argument has
been replaced by `new`. Comparison with `old` is up to defEq. -/
def Lean.Expr.subst (target old new : Expr) : MetaM Expr := do
  if ← isDefEq target old then
    return new
  else
    match target with
    | Expr.app fn arg    => return (Expr.app fn (← arg.subst old new))
    | _                  => return target

/-- Given expressions `orig : r a b` and `subst : s x y` for some relations
`r` and `s`, build the expression `r b c` where `c` is obtained from `b` by replacing
any occurence of `x` in a function application argument by `y`. -/
def Lean.Expr.substInRel (orig subst : Expr) : MetaM (Option Expr) := do
  let some (relo, _lo, ro) := (← getCalcRelation? orig) | return none
  let some (_rels, ls, rs) := (← getCalcRelation? subst) | return none
  return some (← mkAppM' relo #[ro, (← ro.subst ls rs)])

def gcongrDefaultDischarger (g : MVarId) : MetaM PUnit :=Term.TermElabM.run' do
  let [] ← Tactic.run g <| evalTactic (Unhygienic.run `(tactic| gcongr_discharger)) | failure

/-- Rewrite in the relation assumption `h : r a b` using `subst : s x y` to produce `h : r a c`
where `c` is obtained from `b` by replacing any occurence of `x` in a function application argument
by `y`. This new relation `h` is proven from `trans h h'` where `h' : r b c` is proven by `gcongr`
using the list of given identifiers for newly introduced variables.
Returns the list of new goals. -/
def Lean.MVarId.rwIneq (g : MVarId) (h : Name) (subst : Expr)
    (names : List (TSyntax ``binderIdent)) : MetaM (List MVarId) := do
  let decl ← (← getLCtx).findFromUserName? h
  let some newIneq := ← Lean.Expr.substInRel decl.type subst
    | throwError "Could not create the new relation."
  let mvar ← mkFreshExprMVar newIneq
  let (success, _, newGoals) ← mvar.mvarId!.gcongr none names gcongrDefaultDischarger
  if success then
    let g ← g.clear decl.fvarId
    let (_, newGoal) ← g.note decl.userName (← mkAppM `Trans.trans #[.fvar decl.fvarId, mvar])
    return newGoal::newGoals.toList
  else
    throwError "The `gcongr` tactic called by `rw_ineq` failed."

/-- `rw_ineq e at h` rewrite in the relation assumption `h : r a b` using `e : s x y` to replace `h`
with `r a c` where `c` is obtained from `b` by replacing any occurence of `x` in a function
application argument by `y`. This may generate new goals including new objects that can
be named using the `with` clause.

```
open Real

example (x y z w u : ℝ) (bound : x * exp y ≤ z + exp w) (h : w ≤ u) :  x * exp y ≤ z + exp u := by
  rw_ineq h at bound
  exact bound
```
-/
elab "rw_ineq" e:term "at " h:ident withArg:((" with " (colGt binderIdent)+)?) : tactic =>
  withMainContext do
  let mainGoal ← getMainGoal
  let subst ← inferType (← Lean.Elab.Term.elabTerm e none)
  let names := (withArg.raw[1].getArgs.map TSyntax.mk).toList
  replaceMainGoal (← mainGoal.rwIneq h.getId subst names)

/-- `rwa_ineq e at h` rewrite in the relation assumption `h : r a b` using `e : s x y` to replace `h`
with `r a c` where `c` is obtained from `b` by replacing any occurence of `x` in a function
application argument by `y`. Then tries to close the main goal using `assumption`.
This may generate new goals including new objects that can be named using the `with` clause.

```
open Real

example (x y z w u : ℝ) (bound : x * exp y ≤ z + exp w) (h : w ≤ u) :  x * exp y ≤ z + exp u := by
  rwa_ineq h at bound
```
-/
elab "rwa_ineq" e:term "at " h:ident withArg:((" with " (colGt binderIdent)+)?) : tactic =>
  withMainContext do
  let mainGoal ← getMainGoal
  let subst ← inferType (← Lean.Elab.Term.elabTerm e none)
  let names := (withArg.raw[1].getArgs.map TSyntax.mk).toList
  replaceMainGoal (← mainGoal.rwIneq h.getId subst names)
  (← getMainGoal).assumption

open Real

example (x y z w u : ℝ) (bound : x * exp y ≤ z + 2*exp w) (h : w ≤ u) :
    x * exp y ≤ z + 2*exp u := by
  rw_ineq h at bound
  exact bound

example (x y z w u : ℝ) (bound : x * exp y < z + 2*exp w) (h : w < u) :
    x * exp y < z + 2*exp u := by
  rwa_ineq h at bound

-- Test where a side condition is not automatically discharged.
example (x y z w u : ℝ) (bound : x * exp y < z + x^2*exp w) (h : w < u) (hx : 2*x > 2) :
    x * exp y < z + x^2*exp u := by
  rwa_ineq h at bound
  apply pow_pos
  linarith
