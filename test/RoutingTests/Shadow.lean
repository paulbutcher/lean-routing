/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RoutingStd
import Routing.RouteTable
import RoutingTests.RoundTrip

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

private def ok : Result .std := fun _ => Response.ok.text "ok"

-- One path under two methods is fine, and so is a literal ahead of a capture that would take it.
private def restHandler : StatelessHandler .std :=
  toHandler
    [ .get ShadowApp.patterns.list ok,
      .post ShadowApp.patterns.create ok,
      .get ShadowApp.patterns.new ok,
      .get ShadowApp.patterns.item fun _ => ok,
      .get ShadowApp.patterns.byName fun _ => ok ]

-- A `Nat` capture takes only canonical digits.
private def paddedHandler : StatelessHandler .std :=
  toHandler [ .get ShadowApp.patterns.item fun _ => ok, .get ShadowApp.patterns.padded ok ]

-- A handler may close over a value known only at run time.
private def greeter (greeting : String) : StatelessHandler .std :=
  toHandler [ .get ShadowApp.patterns.list fun _ => Response.ok.text greeting ]

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: GET /todos/new is unreachable behind GET /todos/:name:String
GET /todos/1 is unreachable behind GET /todos/:name:String
GET /todos/:id:Nat is unreachable behind GET /todos/:name:String
-/
#guard_msgs in
private def shadowedHandler : StatelessHandler .std :=
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
private def runtimeMethod (method : Method) : StatelessHandler .std :=
  toHandler [ route method ShadowApp.patterns.list ok ]

private def checkedRoutes (method : Method) : List (Route String) :=
  [ .get ShadowApp.patterns.list "list", route method ShadowApp.patterns.create "create" ]

#guard (RouteIndex.ofChecked (checkedRoutes .post)).toBool
#guard match RouteIndex.ofChecked (checkedRoutes .get) with
  | .error e => e == "GET /todos is unreachable behind GET /todos"
  | .ok _ => false

private def apiRouter : Router .std :=
  { routes := [ .get ShadowApp.patterns.first ok ] }

-- A router tries its own routes before its sub-routers'.
private def siteRouter (inner : Router .std) : Router .std :=
  { routes := [ .get ShadowApp.patterns.item fun _ => ok ], routers := [ inner ] }

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: GET /todos/1 is unreachable behind GET /todos/:id:Nat
-/
#guard_msgs in
private def siteHandler : StatelessHandler .std := (siteRouter apiRouter).toHandler

private def apiFirst : Router .std := { routers := [ apiRouter, siteRouter {} ] }

#guard (apiFirst.toHandlerChecked).toBool
#guard !((siteRouter apiRouter).toHandlerChecked).toBool

private def todosMount : Entry .std := .mount (.mk ["todos"]) [ .get [] ok ]

private def listRouter : Router .std := { routes := [ .get ShadowApp.patterns.list ok ] }

private def itemRouter : Router .std := { routes := [ .get ShadowApp.patterns.item fun _ => ok ] }

-- A router takes every request under its mount roots, and redirects `/todos` to its `/todos/`.
/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: GET /todos is unreachable behind the redirect from GET /todos to /todos/
GET /todos is unreachable behind the router mounted at /todos
GET /todos/:id:Nat is unreachable behind the router mounted at /todos
-/
#guard_msgs in
private def siblingHandler : StatelessHandler .std :=
  Router.toHandler { routers := [ { routes := [ todosMount ] }, listRouter, itemRouter ] }

-- A router's own redirects come before its sub-routers, but its mount roots don't.
/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: GET /todos is unreachable behind the redirect from GET /todos to /todos/
-/
#guard_msgs in
private def parentHandler : StatelessHandler .std :=
  Router.toHandler { routes := [ todosMount ], routers := [ listRouter ] }

private def parentWithItem : StatelessHandler .std :=
  Router.toHandler { routes := [ todosMount ], routers := [ itemRouter ] }

-- The link `/todos/` reaches `GET /todos`, which takes the trailing slash `dispatch` tolerates.
/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: GET /todos/ is unreachable behind GET /todos
-/
#guard_msgs in
private def slashHandler : StatelessHandler .std :=
  toHandler [ .get ShadowApp.patterns.list ok, .get [.lit "todos", .lit ""] ok ]

private def slashFirst : StatelessHandler .std :=
  toHandler [ .get [.lit "todos", .lit ""] ok, .get ShadowApp.patterns.list ok ]


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

theorem parseNat?_empty : parseNat? "" = none := by
  cases h : parseNat? "" with
  | none => rfl
  | some n =>
    have := unlinkable_of_parseNat? (p := "") (by simp [h])
    exact absurd this (by decide)

theorem method_beq_self (m : Method) : (m == m) = true := by cases m <;> rfl

/-- Whether `seg` matches the segment `p`. -/
def SegOk : PathSeg → String → Prop
  | .lit s _, p => s = p
  | .capture _ .nat, p => (parseNat? p).isSome
  | .capture _ .string, p => unlinkable p = false

/-- The paths `dispatch` accepts, whatever the handler. -/
def Accepts : List PathSeg → List String → Prop
  | [], [] => True
  | [], [""] => True
  | seg :: rest, p :: ps => SegOk seg p ∧ Accepts rest ps
  | _, _ => False

/-- `Accepts` without the trailing `""` that `dispatch` tolerates. -/
def Exact : List PathSeg → List String → Prop
  | [], [] => True
  | seg :: rest, p :: ps => SegOk seg p ∧ Exact rest ps
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
    · simp [dispatch, Accepts, SegOk, hs, dispatch_isSome_iff rest h ps]
    · simp [dispatch, Accepts, SegOk, hs]
  | .capture _ .nat :: rest, h, [] => by simp [dispatch, Accepts]
  | .capture _ .nat :: rest, h, p :: ps => by
    cases hn : parseNat? p with
    | none => simp [dispatch, Accepts, SegOk, hn]
    | some n => simp [dispatch, Accepts, SegOk, hn, dispatch_isSome_iff rest (h n) ps]
  | .capture _ .string :: rest, h, [] => by simp [dispatch, Accepts]
  | .capture _ .string :: rest, h, p :: ps => by
    cases hu : unlinkable p
    · simp [dispatch, Accepts, SegOk, hu, dispatch_isSome_iff rest (h p) ps]
    · simp [dispatch, Accepts, SegOk, hu]

theorem accepts_iff : ∀ (a : List PathSeg) (p : List String),
    Accepts a p ↔ Exact a p ∨ ∃ q, p = q ++ [""] ∧ Exact a q
  | [], [] => by simp [Accepts, Exact]
  | [], [x] => by
    constructor
    · intro h
      have : x = "" := by by_cases hx : x = "" <;> simp_all [Accepts]
      exact .inr ⟨[], by simp [this], trivial⟩
    · rintro (h | ⟨q, hq, h⟩)
      · exact h.elim
      · cases q with
        | nil => simp at hq; simp [Accepts, hq]
        | cons _ _ => simp [Exact] at h
  | [], _ :: _ :: _ => by
    simp only [Accepts, Exact, false_or, false_iff, not_exists, not_and]
    intro q hq h
    cases q with
    | nil => simp at hq
    | cons _ _ => simp [Exact] at h
  | _ :: _, [] => by simp [Accepts, Exact]
  | seg :: rest, p :: ps => by
    simp only [Accepts, Exact, accepts_iff rest ps]
    constructor
    · rintro ⟨hs, h | ⟨q, hq, h⟩⟩
      · exact .inl ⟨hs, h⟩
      · exact .inr ⟨p :: q, by simp [hq], hs, h⟩
    · rintro (⟨hs, h⟩ | ⟨q, hq, h⟩)
      · exact ⟨hs, .inl h⟩
      · cases q with
        | nil => simp [Exact] at h
        | cons q₀ q' =>
          simp only [List.cons_append, List.cons.injEq] at hq
          obtain ⟨rfl, rfl⟩ := hq
          exact ⟨h.1, .inr ⟨q', rfl, h.2⟩⟩

theorem accepts_of_exact {a : List PathSeg} {p : List String} (h : Exact a p) : Accepts a p :=
  (accepts_iff a p).2 (.inl h)

theorem exact_append_empty : ∀ (a : List PathSeg) (h) (q : List String),
    Exact a q → Exact (a ++ [.lit "" h]) (q ++ [""])
  | [], _, [], _ => by simp [Exact, SegOk]
  | _ :: rest, h, _ :: qs, he => ⟨he.1, exact_append_empty rest h qs he.2⟩
  | [], _, _ :: _, he | _ :: _, _, [], he => he.elim

theorem segOk_isEmptyLit {seg : PathSeg} (h : SegOk seg "") : isEmptyLit seg = true := by
  match seg with
  | .lit s _ => simp_all [SegOk, isEmptyLit]
  | .capture _ .nat => simp [SegOk, parseNat?_empty] at h
  | .capture _ .string => simp [SegOk, unlinkable] at h

theorem exact_getLast : ∀ (a : List PathSeg) (q : List String), Exact a q →
    a.getLast?.any isEmptyLit = false → q.getLast? ≠ some ""
  | [], [], _, _ => by simp
  | [seg], [p], he, ha => by
    intro hp
    simp only [List.getLast?_singleton, Option.some.injEq] at hp
    subst hp
    simp [segOk_isEmptyLit he.1] at ha
  | _ :: s :: rest, _ :: p :: ps, he, ha => by
    simpa using exact_getLast (s :: rest) (p :: ps) he.2 (by simpa using ha)
  | [], _ :: _, he, _ | _ :: _, [], he, _ | [_], _ :: _ :: _, he, _ => by simp_all [Exact]
  | _ :: _ :: _, [_], he, _ => by simp_all [Exact]

theorem digitChar_of_isDigit {c : Char} (h : c.isDigit = true) :
    ∃ d < 10, Nat.digitChar d = c := by
  have hc : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
    simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq, UInt32.le_iff_toNat_le] at h
    exact ⟨h.1, h.2⟩
  refine ⟨c.toNat - 48, by omega, ?_⟩
  rw [← Char.toNat_inj, Nat.toNat_digitChar_of_lt_ten (by omega)]
  omega

theorem eq_zero_of_head_toDigits (n : Nat) (h : (Nat.toDigits 10 n).head? = some '0') : n = 0 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [Nat.toDigits_eq_ite (by decide)] at h
    split at h
    · simpa using h
    · rename_i hn
      have hne := Nat.toDigits_ne_nil (b := 10) (n := n / 10)
      obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hne
      rw [hcs, List.cons_append, List.head?_cons] at h
      have := ih (n / 10) (by omega) (by rw [hcs]; exact h)
      omega

theorem canonicalDigits_iff_props (cs : List Char) : canonicalDigits cs = true ↔
    cs ≠ [] ∧ cs.all Char.isDigit = true ∧ (cs.head? = some '0' → cs = ['0']) := by
  match cs with
  | [] => simp [canonicalDigits]
  | [c] =>
    simp only [canonicalDigits, ne_eq, List.cons_ne_nil, not_false_eq_true, List.all_cons,
      List.all_nil, Bool.and_true, List.head?_cons, Option.some.injEq, true_and]
    constructor
    · intro h; exact ⟨h, fun hc => by simp [hc]⟩
    · exact fun h => h.1
  | c :: d :: rest =>
    simp only [canonicalDigits, bne_iff_ne, ne_eq, Bool.and_eq_true,
      List.cons_ne_nil, not_false_eq_true, List.all_cons, List.head?_cons, Option.some.injEq,
      List.cons.injEq, and_false, imp_false, true_and]
    constructor
    · rintro ⟨⟨h0, hc⟩, hd⟩; exact ⟨⟨hc, hd⟩, h0⟩
    · rintro ⟨⟨hc, hd⟩, h0⟩; exact ⟨⟨h0, hc⟩, hd⟩

theorem canonicalDigits_iff (cs : List Char) :
    canonicalDigits cs = true ↔ ∃ n, Nat.toDigits 10 n = cs := by
  rw [canonicalDigits_iff_props]
  constructor
  · intro hp
    induction hk : cs.length using Nat.strongRecOn generalizing cs with
    | ind k ih =>
      rcases List.eq_nil_or_concat cs with rfl | ⟨ds, c, rfl⟩
      · exact absurd rfl hp.1
      obtain ⟨-, hall, h0⟩ := hp
      simp only [List.concat_eq_append] at hall h0 hk
      simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true,
        Bool.and_eq_true] at hall
      obtain ⟨d, hd, rfl⟩ := digitChar_of_isDigit hall.2
      cases ds with
      | nil => exact ⟨d, by simp [Nat.toDigits_of_lt_base hd]⟩
      | cons e es =>
        have he : e ≠ '0' := fun he => by simpa using h0 (by simp [he])
        obtain ⟨m, hm⟩ := ih _ (by simp [← hk]) (e :: es)
          ⟨by simp, hall.1, fun h => absurd (by simpa using h) he⟩ rfl
        have hm0 : 0 < m := Nat.pos_of_ne_zero fun h =>
          he (by simp [h, Nat.toDigits_zero] at hm; exact hm.1.symm)
        refine ⟨10 * m + d, ?_⟩
        rw [List.concat_eq_append, ← Nat.toDigits_append_toDigits (by decide) hm0 hd, hm,
          Nat.toDigits_of_lt_base hd]
  · rintro ⟨n, rfl⟩
    refine ⟨Nat.toDigits_ne_nil, ?_, fun h => ?_⟩
    · simp only [List.all_eq_true]
      exact fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
    · rw [eq_zero_of_head_toDigits n h, Nat.toDigits_zero]

theorem canonicalDigits_toList (s : String) : canonicalDigits s.toList = (parseNat? s).isSome := by
  apply Bool.eq_iff_iff.2
  rw [canonicalDigits_iff]
  constructor
  · rintro ⟨n, hn⟩
    have : toString n = s := String.ext (by simp only [toString]; rw [Nat.toList_repr, hn])
    rw [← this, parseNat?_toString]; rfl
  · intro h
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 h
    refine ⟨n, ?_⟩
    rw [← toString_of_parseNat? hn]
    simp only [toString]
    rw [Nat.toList_repr]

theorem accepts_of_covers : ∀ (a b : List PathSeg) (path : List String),
    covers a b = true → Exact b path → Accepts a path
  | [], [], [], _, _ => trivial
  | [], [.lit s _], [p], hc, hb => by
    have : s = "" := by simpa [covers, isEmptyLit] using hc
    have : p = "" := by simp_all [Exact, SegOk]
    simp [Accepts, this]
  | x :: xs, y :: ys, p :: ps, hc, hb => by
    simp only [covers, Bool.and_eq_true] at hc
    refine ⟨?_, accepts_of_covers xs ys ps hc.2 hb.2⟩
    have hs := hb.1
    match x, y, hc.1 with
    | .lit _ _, .lit _ _, h => simp_all [segCovers, SegOk]
    | .capture _ .string, .lit _ _, h => simp_all [segCovers, SegOk]
    | .capture _ .string, .capture _ .string, _ => exact hs
    | .capture _ .string, .capture _ .nat, _ => exact unlinkable_of_parseNat? hs
    | .capture _ .nat, .capture _ .nat, _ => exact hs
    | .capture _ .nat, .lit _ _, h => simp_all [segCovers, SegOk, canonicalDigits_toList]
  | [], [.capture ..], _, hc, _ | [], _ :: _ :: _, _, hc, _ | _ :: _, [], _, hc, _ => by
    simp [covers, isEmptyLit] at hc
  | [], [], _ :: _, _, hb | [], [.lit ..], [], _, hb | _ :: _, _ :: _, [], _, hb => hb.elim
  | [], [.lit ..], _ :: _ :: _, _, hb => hb.2.elim


theorem prefix_of_coversPrefix : ∀ (pre : List String) (b : List PathSeg) (path : List String),
    coversPrefix pre b = true → Accepts b path → pre.isPrefixOf path = true
  | [], _, _, _, _ => by simp
  | s :: pre, .lit t _ :: b, p :: ps, hc, hb => by
    simp only [coversPrefix, Bool.and_eq_true, beq_iff_eq] at hc
    simp [List.isPrefixOf, hc.1, show t = p from hb.1, prefix_of_coversPrefix pre b ps hc.2 hb.2]
  | _ :: _, .lit _ _ :: _, [], _, hb => hb.elim
  | _ :: _, [], _, hc, _ | _ :: _, .capture .. :: _, _, hc, _ => by simp [coversPrefix] at hc

theorem redirectFrom?_eq_some {segs a : List PathSeg} (h : redirectFrom? segs = some a) :
    (∃ he, segs = a ++ [.lit "" he]) ∧ a.getLast?.any isEmptyLit = false := by
  unfold redirectFrom? at h
  dsimp only at h
  split at h
  · rename_i last hl
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      refine ⟨?_, hc.2⟩
      match last, hc.1 with
      | .lit s hs, he =>
        have : s = "" := by simpa [isEmptyLit] using he
        subst this
        obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.1 hl
        exact ⟨hs, by simp⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

end Internal

open Internal

theorem exact_pathOf : ∀ (segs : List PathSeg) (args : Args segs), Linkable segs args →
    Exact segs (pathOf segs args)
  | [], _, _ => trivial
  | .lit s _ :: rest, args, hl => ⟨rfl, exact_pathOf rest args hl⟩
  | .capture _ .nat :: rest, (n, args), hl =>
    ⟨by show (parseNat? (toString n)).isSome = true; rw [parseNat?_toString]; rfl,
      exact_pathOf rest args hl⟩
  | .capture _ .string :: rest, (_, args), hl => ⟨hl.1, exact_pathOf rest args hl.2⟩

/-- A route the check reports is unreachable by its links: the route reported as shadowing it,
with the same method, matches the path of every link to it. -/
theorem Route.tryDispatch_of_covers (a b : Route α) (hc : covers a.segs b.segs = true)
    (args : Args b.segs) (hl : Linkable b.segs args) :
    (a.tryDispatch a.method (pathOf b.segs args)).isSome := by
  simp only [Route.tryDispatch, method_beq_self, ↓reduceIte, dispatch_isSome_iff]
  exact accepts_of_covers _ _ _ hc (exact_pathOf _ args hl)


/-- The router holding `r` answers whatever a route its redirect is reported to shadow would match:
`r` matches it, or matches it with a slash added and the router redirects it there. -/
theorem Route.redirect_takes (r : Route α) {a : List PathSeg} (hr : redirectFrom? r.segs = some a)
    {path : List String} (h : Accepts a path) :
    (r.tryDispatch r.method path).isSome ∨
      (path.getLast? ≠ some "" ∧ (r.tryDispatch r.method (path ++ [""])).isSome) := by
  obtain ⟨⟨he, hs⟩, ha⟩ := redirectFrom?_eq_some hr
  simp only [Route.tryDispatch, method_beq_self, ↓reduceIte, dispatch_isSome_iff]
  rw [hs]
  rcases (accepts_iff a path).1 h with hx | ⟨q, rfl, hx⟩
  · exact .inr ⟨exact_getLast a path hx ha, accepts_of_exact (exact_append_empty a he path hx)⟩
  · exact .inl (accepts_of_exact (exact_append_empty a he q hx))

/-- A router takes whatever a route its mount root is reported to shadow would match. -/
theorem root_takes {root : List String} {b : List PathSeg} (hc : coversPrefix root b = true)
    {path : List String} (h : Accepts b path) : root.isPrefixOf path = true :=
  prefix_of_coversPrefix root b path hc h

namespace Internal

/-- What `t` takes, in the terms its check uses: a redirect takes what its `segs` match. -/
def Taker.Takes : Taker → Method → List String → Prop
  | .route m a, method, path | .redirect m a, method, path => m = method ∧ Accepts a path
  | .root pre, _, path => pre.isPrefixOf path = true

def litStrings : List PathSeg → List String :=
  List.filterMap fun | .lit s _ => some s | .capture .. => none

def Taker.strings : Taker → List String
  | .route _ a | .redirect _ a => litStrings a
  | .root pre => pre

/-- `K` and `N` are beyond every string in `L`: longer, and above any number one parses as. -/
structure Fresh (L : List String) (K N : Nat) : Prop where
  pos : 0 < K
  len : ∀ s ∈ L, s.length < K
  num : ∀ s ∈ L, ∀ n, parseNat? s = some n → n < N

def freshString (K : Nat) : String := String.ofList (List.replicate K 'a')

/-- A segment of the path `b` matches that no taker not covering `b` takes, given `K` and `N` fresh
for them. -/
def witSeg (K N : Nat) : PathSeg → String
  | .lit s _ => s
  | .capture _ .nat => toString N
  | .capture _ .string => freshString K

theorem freshString_length (K : Nat) : (freshString K).length = K := by
  simp [freshString]

theorem parseNat?_freshString {K : Nat} (hK : 0 < K) : parseNat? (freshString K) = none := by
  cases h : parseNat? (freshString K) with
  | none => rfl
  | some n =>
    have := congrArg String.toList (toString_of_parseNat? h)
    have ha : 'a' ∈ Nat.toDigits 10 n := by
      rw [← Nat.toList_repr]
      simp only [toString] at this
      rw [this]
      simp [freshString, List.mem_replicate]
      omega
    exact absurd (Nat.isDigit_of_mem_toDigits (by decide) (by decide) ha) (by decide)

theorem unlinkable_freshString {K : Nat} (hK : 0 < K) : unlinkable (freshString K) = false := by
  have hl := freshString_length K
  simp only [unlinkable, dotSegment, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  refine ⟨fun h => by simp [h] at hl; omega, fun h => ?_, fun h => ?_⟩ <;>
    have := congrArg String.toList h <;> simp [freshString] at this <;>
    have := congrArg List.head? this <;> cases K <;> simp_all [List.replicate_succ]

theorem segOk_witSeg {K N : Nat} (hK : 0 < K) (seg : PathSeg) : SegOk seg (witSeg K N seg) := by
  match seg with
  | .lit s _ => rfl
  | .capture _ .nat =>
    show (parseNat? (toString N)).isSome = true
    rw [parseNat?_toString]; rfl
  | .capture _ .string => exact unlinkable_freshString hK

theorem exact_map_witSeg {K N : Nat} (hK : 0 < K) :
    ∀ b : List PathSeg, Exact b (b.map (witSeg K N))
  | [] => trivial
  | seg :: rest => ⟨segOk_witSeg hK seg, exact_map_witSeg hK rest⟩

/-- A pattern whose literals `K` and `N` are fresh for, and that matches `b`'s generic path
exactly, covers `b` segment by segment. -/
theorem covers_of_exact {L : List String} {K N : Nat} (hf : Fresh L K N) :
    ∀ a b : List PathSeg, (∀ s ∈ litStrings a, s ∈ L) → Exact a (b.map (witSeg K N)) →
      covers a b = true
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hl, he => by
    have hl' : ∀ s ∈ litStrings xs, s ∈ L := fun s hs => hl s (by
      cases x <;> simp_all [litStrings])
    simp only [covers, Bool.and_eq_true]
    refine ⟨?_, covers_of_exact hf xs ys hl' he.2⟩
    have hs := he.1
    match x, y with
    | .lit s _, .lit t _ => simpa [segCovers, SegOk, witSeg] using hs
    | .lit s _, .capture _ .nat =>
      have hsL : s ∈ L := hl s (by simp [litStrings])
      simp only [SegOk, witSeg] at hs
      subst hs
      exact absurd (hf.num _ hsL N (parseNat?_toString N)) (Nat.lt_irrefl N)
    | .lit s _, .capture _ .string =>
      have hsL : s ∈ L := hl s (by simp [litStrings])
      simp only [SegOk, witSeg] at hs
      have := hf.len s hsL
      rw [hs, freshString_length] at this
      exact absurd this (Nat.lt_irrefl K)
    | .capture _ .nat, .lit t _ => simpa [segCovers, SegOk, witSeg, canonicalDigits_toList] using hs
    | .capture _ .nat, .capture _ .nat => rfl
    | .capture _ .nat, .capture _ .string =>
      simp [SegOk, witSeg, parseNat?_freshString hf.pos] at hs
    | .capture _ .string, .lit t _ => simpa [segCovers, SegOk, witSeg] using hs
    | .capture _ .string, .capture _ _ => rfl
  | [], _ :: _, _, he | _ :: _, [], _, he => he.elim

theorem exact_length : ∀ (a : List PathSeg) (p : List String), Exact a p → a.length = p.length
  | [], [], _ => rfl
  | _ :: rest, _ :: ps, he => by simp [exact_length rest ps he.2]
  | [], _ :: _, he | _ :: _, [], he => he.elim

theorem covers_append_empty (h) : ∀ a b : List PathSeg, a.length = b.length →
    covers a b = true → covers a (b ++ [.lit "" h]) = true
  | [], [], _, _ => rfl
  | _ :: xs, _ :: ys, hlen, hc => by
    simp only [covers, Bool.and_eq_true, List.cons_append] at hc ⊢
    exact ⟨hc.1, covers_append_empty h xs ys (by simpa using hlen) hc.2⟩
  | [], _ :: _, hlen, _ | _ :: _, [], hlen, _ => by simp at hlen

/-- A route or redirect that takes `b`'s generic path covers `b`: it matches the path exactly, or
with `b`'s final empty literal as the `""` that `dispatch` tolerates. -/
theorem covers_of_accepts {L : List String} {K N : Nat} (hf : Fresh L K N)
    (a b : List PathSeg) (hl : ∀ s ∈ litStrings a, s ∈ L)
    (h : Accepts a (b.map (witSeg K N))) : covers a b = true := by
  rcases (accepts_iff _ _).1 h with hx | ⟨q, hq, hx⟩
  · exact covers_of_exact hf a b hl hx
  · cases hg : b.getLast? with
    | none => simp_all
    | some last =>
      obtain ⟨b', rfl⟩ := List.getLast?_eq_some_iff.1 hg
      simp only [List.map_append, List.map_cons, List.map_nil] at hq
      obtain ⟨rfl, hw⟩ := List.append_inj' hq rfl
      simp only [List.cons.injEq, and_true] at hw
      match last, segOk_isEmptyLit (hw ▸ segOk_witSeg hf.pos last) with
      | .lit s hs, he =>
        have : s = "" := by simpa [isEmptyLit] using he
        subst this
        exact covers_append_empty hs a b' (by simpa using exact_length _ _ hx)
          (covers_of_exact hf a b' hl hx)

theorem coversPrefix_of_isPrefixOf {L : List String} {K N : Nat} (hf : Fresh L K N) :
    ∀ (pre : List String) (b : List PathSeg), (∀ s ∈ pre, s ∈ L) →
      pre.isPrefixOf (b.map (witSeg K N)) = true → coversPrefix pre b = true
  | [], _, _, _ => rfl
  | _ :: _, [], _, h => by simp at h
  | s :: pre, y :: ys, hl, h => by
    simp only [List.map_cons, List.isPrefixOf, Bool.and_eq_true, beq_iff_eq] at h
    have ih := coversPrefix_of_isPrefixOf hf pre ys (fun t ht => hl t (by simp [ht])) h.2
    have hsL : s ∈ L := hl s (by simp)
    match y, h.1 with
    | .lit t _, hs => simp_all [coversPrefix, witSeg]
    | .capture _ .nat, hs =>
      simp only [witSeg] at hs
      subst hs
      exact absurd (hf.num _ hsL N (parseNat?_toString N)) (Nat.lt_irrefl N)
    | .capture _ .string, hs =>
      simp only [witSeg] at hs
      have := hf.len s hsL
      rw [hs, freshString_length] at this
      exact absurd this (Nat.lt_irrefl K)

theorem shadows_eq_false_of_unshadowed {u : Taker} :
    ∀ (pre post : List Taker), unshadowed (pre ++ u :: post) = true → ∀ t ∈ pre,
      t.shadows u = false
  | [], _, _, _, ht => by simp at ht
  | t :: pre, post, h, t', ht => by
    simp only [List.cons_append, unshadowed, Bool.and_eq_true, List.all_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true] at h
    rcases List.mem_cons.1 ht with rfl | ht
    · exact h.1 u (by simp)
    · exact shadows_eq_false_of_unshadowed pre post h.2 t' ht

theorem le_sum_of_mem {f : String → Nat} : ∀ {L : List String} {s : String}, s ∈ L →
    f s ≤ (L.map f).sum
  | _ :: _, _, .head _ => by simp
  | _ :: _, _, .tail _ h => by have := le_sum_of_mem (f := f) h; simp; omega

/-- In a table that passes the check, every route has a path it matches exactly, as a link gives,
that nothing tried before it takes. So no route is unreachable behind several takers together
either. -/
theorem reachable_of_unshadowed (pre post : List Taker) (m : Method) (b : List PathSeg)
    (hu : unshadowed (pre ++ .route m b :: post) = true) :
    ∃ path, Exact b path ∧ ∀ t ∈ pre, ¬t.Takes m path := by
  let L := pre.flatMap Taker.strings
  obtain ⟨K, N, hf⟩ : ∃ K N, Fresh L K N :=
    ⟨1 + (L.map String.length).sum, 1 + (L.map fun s => (parseNat? s).getD 0).sum,
    { pos := by omega
      len := fun s hs => by have := le_sum_of_mem (f := String.length) hs; omega
      num := fun s hs n hn => by
        have := le_sum_of_mem (f := fun s => (parseNat? s).getD 0) hs
        simp only [hn, Option.getD_some] at this
        omega }⟩
  refine ⟨b.map (witSeg K N), exact_map_witSeg hf.pos b, fun t ht htakes => ?_⟩
  have hs := shadows_eq_false_of_unshadowed pre post hu t ht
  have hL : ∀ s ∈ t.strings, s ∈ L := fun s hs => List.mem_flatMap.2 ⟨t, ht, hs⟩
  match t, htakes with
  | .route m' a, ⟨hm, h⟩ | .redirect m' a, ⟨hm, h⟩ =>
    have := covers_of_accepts hf a b hL h
    subst hm
    simp_all [Taker.shadows, Taker.blocks]
  | .root root, h =>
    have := coversPrefix_of_isPrefixOf hf root b hL h
    simp_all [Taker.shadows, Taker.blocks]

end Internal

end Routing
