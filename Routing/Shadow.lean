/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Routing.Route
public meta import Lean.Elab.Tactic

/-!
A route is *shadowed* when an earlier one with the same method matches every path it does, so it
can never be dispatched. `RouteIndex.of` (`Trie.lean`) takes a proof that no route in its table is,
and `routes_unshadowed` supplies it for a table known at compile time.
-/

public section

namespace Routing

open Std.Http (Method)

/-- What decides whether a route is reachable. Leaving out the handler lets `routes_unshadowed`
check a table whose handlers close over a value known only at run time. -/
@[expose] def Route.key (r : Route result) : Method × List PathSeg :=
  (r.method, r.segs)

namespace Internal

/-- Whether `a` matches every segment `b` matches. A `Nat` capture matches no `unlinkable`
segment, so a `String` capture covers it. -/
@[expose] def segCovers : PathSeg → PathSeg → Bool
  | .lit a _, .lit b _ => a == b
  | .capture _ .string, .lit b _ => !unlinkable b
  | .capture _ .string, .capture _ _ => true
  | .capture _ .nat, .capture _ .nat => true
  | .capture _ .nat, .lit b _ => (parseNat? b).isSome
  | _, _ => false

/-- Whether `a` matches every path `b` matches. Both tolerate a trailing `""` alike (`dispatch`), so
neither can cover a pattern of another length. -/
@[expose] def covers : List PathSeg → List PathSeg → Bool
  | [], [] => true
  | a :: as, b :: bs => segCovers a b && covers as bs
  | _, _ => false

/-- Whether no route in `keys` is shadowed by an earlier one. -/
@[expose] def unshadowed : List (Method × List PathSeg) → Bool
  | [] => true
  | (m, segs) :: rest =>
    rest.all (fun (m', segs') => !(m == m' && covers segs segs')) && unshadowed rest

theorem unshadowed_append (l₁ l₂ : List (Method × List PathSeg))
    (h : unshadowed (l₁ ++ l₂) = true) : unshadowed l₁ = true ∧ unshadowed l₂ = true := by
  induction l₁ with
  | nil => simpa [unshadowed] using h
  | cons k t ih =>
    obtain ⟨m, segs⟩ := k
    simp only [List.cons_append, unshadowed, List.all_append, Bool.and_eq_true] at h ⊢
    exact ⟨⟨h.1.1, (ih h.2).1⟩, (ih h.2).2⟩

/-- A line for each shadowed route in `keys`, naming the route that shadows it. -/
def shadowReport : List (Method × List PathSeg) → List String
  | [] => []
  | (m, segs) :: rest =>
    (rest.filter fun (m', segs') => m == m' && covers segs segs').map (fun (_, segs') =>
      s!"{m} {renderPattern segs'} is unreachable behind {m} {renderPattern segs}") ++
      shadowReport rest

end Internal

/-- Closes `Internal.unshadowed keys = true` by evaluating it, reporting each shadowed route if it
is false. A handler may mention a local value, but a method or pattern may not, since then the table
is only known at run time; see `RouteIndex.ofChecked`. -/
syntax (name := routesUnshadowed) "routes_unshadowed" : tactic

open Lean Elab Tactic Meta

private meta unsafe def shadowReportOfUnsafe (keys : Expr) : MetaM (List String) :=
  evalExpr (List String) (mkApp (mkConst ``List [.zero]) (mkConst ``String))
    (mkApp (mkConst ``Internal.shadowReport) keys)

@[implemented_by shadowReportOfUnsafe]
private meta opaque shadowReportOf (keys : Expr) : MetaM (List String)

@[tactic routesUnshadowed] meta def evalRoutesUnshadowed : Tactic := fun _ => do
  let goal ← getMainGoal
  let some (_, lhs, _) := (← instantiateMVars (← goal.getType)).eq?
    | throwError "routes_unshadowed: expected a goal `Internal.unshadowed keys = true`"
  let_expr Internal.unshadowed keys := lhs
    | throwError "routes_unshadowed: expected a goal `Internal.unshadowed keys = true`"
  -- Reducing drops the handlers, which are all a local value can usually reach.
  let keys ← if keys.hasFVar then reduce keys else pure keys
  if keys.hasFVar || keys.hasMVar then
    throwError "routes_unshadowed: a route's method or pattern is only known at run time; \
      build the table with `RouteIndex.ofChecked`"
  match ← shadowReportOf keys with
  | [] => pure ()
  | lines => throwError "{String.intercalate "\n" lines}"
  let goal ← goal.replaceTargetDefEq
    (← mkEq (mkApp (mkConst ``Internal.unshadowed) keys) (mkConst ``true))
  replaceMainGoal [goal]
  evalTactic (← `(tactic| native_decide))

end Routing
