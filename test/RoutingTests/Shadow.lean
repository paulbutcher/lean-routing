/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Routing.Router
import Routing.RouteTable

namespace Routing

open Std Http Server

route_table ShadowApp
  [ list := "/todos",
    create := "/todos",
    new := "/todos/new",
    item := "/todos/:id:Nat",
    byName := "/todos/:name:String",
    first := "/todos/1",
    padded := "/todos/01" ]

private def ok : Result := fun _ => Response.ok.text "ok"

-- One path under two methods is fine, and so is a literal ahead of a capture that would take it.
private def restHandler : StatelessHandler :=
  toHandler
    [ .get ShadowApp.patterns.list ok,
      .post ShadowApp.patterns.create ok,
      .get ShadowApp.patterns.new ok,
      .get ShadowApp.patterns.item fun _ => ok,
      .get ShadowApp.patterns.byName fun _ => ok ]

-- A `Nat` capture takes only canonical digits.
private def paddedHandler : StatelessHandler :=
  toHandler [ .get ShadowApp.patterns.item fun _ => ok, .get ShadowApp.patterns.padded ok ]

-- A handler may close over a value known only at run time.
private def greeter (greeting : String) : StatelessHandler :=
  toHandler [ .get ShadowApp.patterns.list fun _ => Response.ok.text greeting ]

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: GET /todos/new is unreachable behind GET /todos/:name:String
GET /todos/1 is unreachable behind GET /todos/:name:String
GET /todos/:id:Nat is unreachable behind GET /todos/:name:String
-/
#guard_msgs in
private def shadowedHandler : StatelessHandler :=
  toHandler
    [ .get ShadowApp.patterns.byName fun _ => ok,
      .get ShadowApp.patterns.new ok,
      .get ShadowApp.patterns.first ok,
      .post ShadowApp.patterns.first ok,
      .get ShadowApp.patterns.item fun _ => ok ]

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: routes_unshadowed: a route's method or pattern is only known at run time; build the table with `RouteIndex.ofChecked`
-/
#guard_msgs in
private def runtimeMethod (method : Method) : StatelessHandler :=
  toHandler [ route method ShadowApp.patterns.list ok ]

private def checkedRoutes (method : Method) : List (Route String) :=
  [ .get ShadowApp.patterns.list "list", route method ShadowApp.patterns.create "create" ]

#guard (RouteIndex.ofChecked (checkedRoutes .post)).toBool
#guard match RouteIndex.ofChecked (checkedRoutes .get) with
  | .error e => e == "GET /todos is unreachable behind GET /todos"
  | .ok _ => false

private def apiRouter : Router :=
  { routes := [ .get ShadowApp.patterns.first ok ] }

-- A router tries its own routes before its sub-routers'.
private def siteRouter (inner : Router) : Router :=
  { routes := [ .get ShadowApp.patterns.item fun _ => ok ], routers := [ inner ] }

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: GET /todos/1 is unreachable behind GET /todos/:id:Nat
-/
#guard_msgs in
private def siteHandler : StatelessHandler := (siteRouter apiRouter).toHandler

private def apiFirst : Router := { routers := [ apiRouter, siteRouter {} ] }

#guard (apiFirst.toHandlerChecked).toBool
#guard !((siteRouter apiRouter).toHandlerChecked).toBool


namespace Internal

theorem unlinkable_of_parseNat? {p : String} (h : (parseNat? p).isSome) : unlinkable p = false := by
  simp only [parseNat?, Option.isSome_filter] at h
  cases hp : p.toNat? with
  | none => simp [hp] at h
  | some n =>
    simp only [hp, Option.any_some, beq_iff_eq] at h
    subst h
    have hd : '.' ∉ Nat.toDigits 10 n := fun hm =>
      absurd (Nat.isDigit_of_mem_toDigits (by decide) (by decide) hm) (by decide)
    simp only [unlinkable, dotSegment, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    refine ⟨?_, ?_, ?_⟩ <;> intro he <;> have := congrArg String.toList he <;>
      simp [Nat.toList_repr] at this <;> simp_all

/-- The paths `dispatch` accepts, whatever the handler. -/
def Accepts : List PathSeg → List String → Prop
  | [], [] => True
  | [], [""] => True
  | .lit s _ :: rest, p :: ps => s = p ∧ Accepts rest ps
  | .capture _ .nat :: rest, p :: ps => (parseNat? p).isSome ∧ Accepts rest ps
  | .capture _ .string :: rest, p :: ps => unlinkable p = false ∧ Accepts rest ps
  | _, _ => False

theorem dispatch_isSome_iff :
    ∀ (segs : List PathSeg) (h : HandlerType segs r) (path : List String),
      (dispatch segs h path).isSome ↔ Accepts segs path
  | [], _, [] => by simp [dispatch, Accepts]; rfl
  | [], _, [p] => by by_cases hp : p = "" <;> simp [dispatch, Accepts, hp]; rfl
  | [], _, _ :: _ :: _ => by simp [dispatch, Accepts]
  | .lit s _ :: rest, h, [] => by simp [dispatch, Accepts]
  | .lit s _ :: rest, h, p :: ps => by
    by_cases hs : s = p
    · simp [dispatch, Accepts, hs, dispatch_isSome_iff rest h ps]
    · simp [dispatch, Accepts, hs]
  | .capture _ .nat :: rest, h, [] => by simp [dispatch, Accepts]
  | .capture _ .nat :: rest, h, p :: ps => by
    cases hn : parseNat? p with
    | none => simp [dispatch, Accepts, hn]
    | some n => simp [dispatch, Accepts, hn, dispatch_isSome_iff rest (h n) ps]
  | .capture _ .string :: rest, h, [] => by simp [dispatch, Accepts]
  | .capture _ .string :: rest, h, p :: ps => by
    cases hu : unlinkable p
    · simp [dispatch, Accepts, hu, dispatch_isSome_iff rest (h p) ps]
    · simp [dispatch, Accepts, hu]

theorem accepts_of_covers : ∀ (a b : List PathSeg) (path : List String),
    covers a b = true → Accepts b path → Accepts a path
  | [], [], _, _, hb => hb
  | x :: xs, y :: ys, p :: ps, hc, hb => by
    simp only [covers, Bool.and_eq_true] at hc
    have ih := accepts_of_covers xs ys ps hc.2
    match x, y, hc.1 with
    | .lit _ _, .lit _ _, hs => simp_all [segCovers, Accepts]
    | .capture _ .string, .lit _ _, hs => simp_all [segCovers, Accepts]
    | .capture _ .string, .capture _ .string, _ => simp_all [segCovers, Accepts]
    | .capture _ .string, .capture _ .nat, _ =>
      simp only [Accepts] at hb ⊢
      exact ⟨unlinkable_of_parseNat? hb.1, ih hb.2⟩
    | .capture _ .nat, .capture _ .nat, _ => simp_all [segCovers, Accepts]
    | .capture _ .nat, .lit _ _, hs => simp_all [segCovers, Accepts]
  | [], _ :: _, _, hc, _ | _ :: _, [], _, hc, _ => by simp [covers] at hc
  | _ :: _, y :: _, [], _, hb => by cases y with
    | lit => simp [Accepts] at hb
    | capture _ k => cases k <;> simp [Accepts] at hb

end Internal

/-- A route the check reports is unreachable: whatever it would match, the route reported as
shadowing it matches too. -/
theorem Route.tryDispatch_of_covers (a b : Route α) (hm : a.method = b.method)
    (hc : Internal.covers a.segs b.segs = true) (method : Method) (path : List String)
    (hb : (b.tryDispatch method path).isSome) : (a.tryDispatch method path).isSome := by
  unfold Route.tryDispatch at hb ⊢
  rw [hm]
  split at hb
  · simp only [↓reduceIte, *, Internal.dispatch_isSome_iff] at hb ⊢
    exact Internal.accepts_of_covers _ _ _ hc hb
  · simp at hb

end Routing
