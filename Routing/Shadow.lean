/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Routing.Route
public meta import Lean.Elab.Tactic

/-!
A route is *shadowed* when something tried before it takes every request a link to it makes, so no
link reaches it: an earlier route with the same method, or in a `Router`, an earlier router's
slash redirect or mount root (`Internal.Taker`). `RouteIndex.of` (`Trie.lean`) and
`Router.toHandler` take a proof that no route is, and `routes_unshadowed` supplies it for a table
known at compile time.
-/

public section

namespace Routing

open Std.Http (Method)

namespace Internal

/-- Something that takes a request before the routes after it, in the order a `Router` tries
them. -/
inductive Taker where
  /-- A route, the one kind whose own reachability is checked. -/
  | route (method : Method) (segs : List PathSeg)
  /-- A router's redirect of a request matching `segs` to the same path with a slash added. -/
  | redirect (method : Method) (segs : List PathSeg)
  /-- A router's mount root, which takes every request under it, whatever its method. -/
  | root (segs : List String)

/-- Whether `a` matches every segment `b` matches. A `Nat` capture matches no `unlinkable`
segment, so a `String` capture covers it. -/
@[expose] def segCovers : PathSeg → PathSeg → Bool
  | .lit a _, .lit b _ => a == b
  | .capture _ .string, .lit b _ => !unlinkable b
  | .capture _ .string, .capture _ _ => true
  | .capture _ .nat, .capture _ .nat => true
  | .capture _ .nat, .lit b _ => (parseNat? b).isSome
  | _, _ => false

@[expose] def isEmptyLit : PathSeg → Bool
  | .lit s _ => s.isEmpty
  | .capture .. => false

/-- Whether `a` matches every path `b` matches exactly, so every path a link to `b` gives. No link
ends with the extra `""` that `dispatch` tolerates, so a route reached only through one counts as
unreachable, and `a` can take `b`'s final empty literal as that `""`. -/
@[expose] def covers : List PathSeg → List PathSeg → Bool
  | [], [] => true
  | [], [b] => isEmptyLit b
  | a :: as, b :: bs => segCovers a b && covers as bs
  | _, _ => false

/-- Whether every path `b` matches starts with `pre`. -/
@[expose] def coversPrefix : List String → List PathSeg → Bool
  | [], _ => true
  | s :: pre, .lit t _ :: b => s == t && coversPrefix pre b
  | _, _ => false

/-- Whether `t` takes every request a link to a route `method segs` makes. -/
@[expose] def Taker.blocks : Taker → Method → List PathSeg → Bool
  | .route m a, method, segs | .redirect m a, method, segs => m == method && covers a segs
  | .root pre, _, segs => coversPrefix pre segs

/-- Whether `u` is a route that `t`, coming before it, leaves unreachable. -/
@[expose] def Taker.shadows (t : Taker) : Taker → Bool
  | .route method segs => t.blocks method segs
  | _ => false

/-- Whether no route in `takers` is shadowed by an earlier taker. -/
@[expose] def unshadowed : List Taker → Bool
  | [] => true
  | t :: rest => rest.all (!t.shadows ·) && unshadowed rest

theorem unshadowed_append (l₁ l₂ : List Taker)
    (h : unshadowed (l₁ ++ l₂) = true) : unshadowed l₁ = true ∧ unshadowed l₂ = true := by
  induction l₁ with
  | nil => simpa [unshadowed] using h
  | cons t rest ih =>
    simp only [List.cons_append, unshadowed, List.all_append, Bool.and_eq_true] at h ⊢
    exact ⟨⟨h.1.1, (ih h.2).1⟩, (ih h.2).2⟩

/-- `some a` when `segs` is `a` followed by an empty literal, so a request matching `a` without its
trailing slash is redirected. `a` itself must not end with one, or the redirect would not take
every request `a` matches. -/
@[expose] def redirectFrom? (segs : List PathSeg) : Option (List PathSeg) :=
  match segs.getLast? with
  | some last =>
    let a := segs.dropLast
    if isEmptyLit last && !(a.getLast?.any isEmptyLit) then some a else none
  | none => none

def Taker.describe : Taker → String
  | .route m segs => s!"{m} {renderPattern segs}"
  | .redirect m segs =>
    s!"the redirect from {m} {renderPattern segs} to {renderPattern (segs ++ [.lit ""])}"
  | .root segs => s!"the router mounted at /{String.intercalate "/" segs}"

/-- A line for each shadowed route in `takers`, naming each taker that shadows it. -/
def shadowReport : List Taker → List String
  | [] => []
  | t :: rest =>
    ((rest.filter t.shadows).map fun u => s!"{u.describe} is unreachable behind {t.describe}") ++
      shadowReport rest

end Internal

@[expose] def Route.key (r : Route result) : Internal.Taker :=
  .route r.method r.segs

/-- The redirect `r` causes, if any (`Internal.redirectFrom?`). -/
@[expose] def Route.redirect? (r : Route result) : Option Internal.Taker :=
  (Internal.redirectFrom? r.segs).map (.redirect r.method)

/-- Closes `Internal.unshadowed keys = true` by evaluating it, reporting each shadowed route if it
is false. A handler may mention a local value, but a method or pattern may not, since then the table
is only known at run time; see `RouteIndex.ofChecked`. Dropping a handler means reducing the table,
so one defined in another module must be `@[expose]`d. -/
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
    -- A definition another module doesn't expose reaches this one as an axiom, with no body.
    let env ← getEnv
    let hidden := keys.find? fun e => e.hasFVar && e.getAppFn.constName?.any fun c =>
      env.find? c matches some (.axiomInfo _)
    if let some c := hidden.bind (·.getAppFn.constName?) then
      throwError "routes_unshadowed: `{c}` is defined in another module without `@[expose]`, so \
        its routes can't be checked here; expose it"
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
