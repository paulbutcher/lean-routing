/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Routing.Router
import RoutingTests.Shadow
import RoutingTests.Trie

/-!
A router serves a request with the route that comes first among its takers (`Router.takers`), so
the check's order is the router's.
-/

namespace Routing

open Std Http
open Internal

variable {e : Engine}

theorem method_beq_iff (a b : Method) : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> decide

theorem tryMatch_isSome_iff (r : Route α) (m : Method) (p : List String) :
    (r.tryMatch m p).isSome ↔ r.key.Takes m p := by
  simp only [Route.tryMatch, Route.tryDispatch, Option.isSome_map, Route.key, Taker.Takes]
  split
  · rename_i hm
    simp [(method_beq_iff _ _).1 hm, dispatch_isSome_iff]
  · rename_i hm
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_and]
    exact fun h => absurd ((method_beq_iff _ _).2 h) hm

theorem matchTable_isSome_iff (l : List (Route α)) (m : Method) (p : List String) :
    (Routing.matchTable l m p).isSome ↔ ∃ r ∈ l, r.key.Takes m p := by
  induction l with
  | nil => simp [Routing.matchTable]
  | cons r rest ih =>
    simp only [Routing.matchTable, List.findSome?_cons] at ih ⊢
    cases hr : r.tryMatch m p with
    | some _ =>
      have := (tryMatch_isSome_iff r m p).1 (by simp [hr])
      simp only [Option.isSome_some, List.mem_cons, true_iff]
      exact ⟨r, .inl rfl, this⟩
    | none =>
      have : ¬r.key.Takes m p := fun h => by simpa [hr] using (tryMatch_isSome_iff r m p).2 h
      simp only [ih, List.mem_cons, exists_eq_or_imp]
      exact ⟨fun h => .inr h, fun h => h.resolve_left this⟩

theorem matchTable_first (m : Method) (p : List String) (b : List PathSeg) (hb : Accepts b p) :
    ∀ (l : List (Route α)) (pre post : List Taker),
      l.map Route.key = pre ++ .route m b :: post →
      (∀ t ∈ pre, ¬t.Takes m p) → (Routing.matchTable l m p).map (·.1) = some ⟨m, b⟩
  | [], pre, _, hl, _ => by cases pre <;> simp at hl
  | r :: rest, [], _, hl, _ => by
    simp only [List.map_cons, List.nil_append, List.cons.injEq] at hl
    have hk := hl.1
    simp only [Route.key, Taker.route.injEq] at hk
    have hs : (r.tryMatch m p).isSome := (tryMatch_isSome_iff r m p).2 (by
      simp [Route.key, Taker.Takes, hk.1, hk.2, hb])
    obtain ⟨⟨matched, res⟩, hmr⟩ := Option.isSome_iff_exists.1 hs
    have : matched = ⟨r.method, r.segs⟩ := by
      simp only [Route.tryMatch, Option.map_eq_some_iff, Prod.mk.injEq] at hmr
      obtain ⟨_, _, h, _⟩ := hmr
      exact h.symm
    simp [Routing.matchTable, hmr, this, hk.1, hk.2]
  | r :: rest, t :: pre, post, hl, hpre => by
    simp only [List.map_cons, List.cons_append, List.cons.injEq] at hl
    have hn : r.tryMatch m p = none := by
      cases h : r.tryMatch m p with
      | none => rfl
      | some _ =>
        exact absurd ((tryMatch_isSome_iff r m p).1 (by simp [h])) (hl.1 ▸ hpre t (by simp))
    simp only [Routing.matchTable, List.findSome?_cons, hn] at ⊢
    exact matchTable_first m p b hb rest pre post hl.2 (fun t ht => hpre t (by simp [ht]))

theorem exact_append_iff : ∀ (a a' : List PathSeg) (p p' : List String), a.length = p.length →
    (Exact (a ++ a') (p ++ p') ↔ Exact a p ∧ Exact a' p')
  | [], _, [], _, _ => by simp [Exact]
  | _ :: as, a', _ :: ps, p', hl => by
    simp only [List.cons_append, Exact, exact_append_iff as a' ps p' (by simpa using hl), and_assoc]
  | [], _, _ :: _, _, hl | _ :: _, _, [], _, hl => by simp at hl

/-- A request a router redirects to add a slash is one its own routes or redirect takers take. -/
theorem takes_of_redirect {own : List (Route α)} {m : Method} {p : List String}
    (hp : p.getLast? ≠ some "") (hm : (Routing.matchTable own m (p ++ [""])).isSome) :
    ∃ t ∈ own.map Route.key ++ own.filterMap Route.redirect?, t.Takes m p := by
  obtain ⟨c, hc, hct⟩ := (matchTable_isSome_iff own m _).1 hm
  simp only [Route.key, Taker.Takes] at hct
  rcases (accepts_iff _ _).1 hct.2 with he | ⟨q, hq, he⟩
  · have hlen := exact_length _ _ he
    obtain ⟨a, x, hax⟩ : ∃ a x, c.segs = a ++ [x] := by
      cases hg : c.segs.getLast? with
      | none => simp_all
      | some x => exact ⟨_, x, (List.getLast?_eq_some_iff.1 hg).choose_spec⟩
    rw [hax] at he hlen
    have ⟨hap, hx⟩ := (exact_append_iff a [x] p [""] (by simpa using hlen)).1 he
    have hxe := segOk_isEmptyLit hx.1
    have hal : a.getLast?.any isEmptyLit = false := by
      cases hg : a.getLast? with
      | none => rfl
      | some y =>
        obtain ⟨a₀, rfl⟩ := List.getLast?_eq_some_iff.1 hg
        cases hy : isEmptyLit y
        · simp [hy]
        · obtain ⟨p₀, y', rfl⟩ : ∃ p₀ y', p = p₀ ++ [y'] := by
            cases hp' : p.getLast? with
            | none =>
              simp only [List.getLast?_eq_none_iff] at hp'
              subst hp'
              exact absurd (exact_length _ _ hap) (by simp)
            | some y' => exact ⟨_, y', (List.getLast?_eq_some_iff.1 hp').choose_spec⟩
          have hlen₀ : a₀.length = p₀.length := by
            have := exact_length _ _ hap
            simpa using this
          have := ((exact_append_iff a₀ [y] p₀ [y'] hlen₀).1 hap).2.1
          match y, hy with
          | .lit s _, hy =>
            have : s = "" := by simpa [isEmptyLit] using hy
            subst this
            simp_all [SegOk]
    have hr : redirectFrom? c.segs = some a := by
      match x, hxe with
      | .lit s _, hxe =>
        have : s = "" := by simpa [isEmptyLit] using hxe
        subst this
        simp [redirectFrom?, hax, isEmptyLit, hal]
    refine ⟨.redirect c.method a, ?_, hct.1, accepts_of_exact hap⟩
    simp only [List.mem_append, List.mem_filterMap]
    exact .inr ⟨c, hc, by simp [Route.redirect?, hr]⟩
  · rw [← List.append_cancel_right hq] at he
    exact ⟨c.key, List.mem_append.2 (.inl (List.mem_map_of_mem hc)), hct.1, accepts_of_exact he⟩

/-- A request one of a router's own routes or redirect takers takes, it answers itself. -/
theorem answers_of_takes {own : List (Route α)} {m : Method} {p : List String} {t : Taker}
    (ht : t ∈ own.map Route.key ++ own.filterMap Route.redirect?) (h : t.Takes m p) :
    (Routing.matchTable own m p).isSome ∨
      (p.getLast? ≠ some "" ∧ (Routing.matchTable own m (p ++ [""])).isSome) := by
  simp only [List.mem_append, List.mem_map, List.mem_filterMap] at ht
  rcases ht with ⟨c, hc, rfl⟩ | ⟨c, hc, hr⟩
  · exact .inl ((matchTable_isSome_iff own m p).2 ⟨c, hc, h⟩)
  · simp only [Route.redirect?, Option.map_eq_some_iff] at hr
    obtain ⟨a, ha, rfl⟩ := hr
    obtain ⟨rfl, hp⟩ := h
    have hrm : ∀ q, (c.tryDispatch c.method q).isSome →
        (Routing.matchTable own c.method q).isSome :=
      fun q hq => (matchTable_isSome_iff own _ q).2
        ⟨c, hc, (tryMatch_isSome_iff c _ q).1 (by simpa [Route.tryMatch] using hq)⟩
    rcases Route.redirect_takes c ha hp with h | ⟨hl, h⟩
    · exact .inl (hrm p h)
    · exact .inr ⟨hl, hrm _ h⟩

theorem wantsSlash_of_index {own : List (Route α)} (hu) {m : Method} {p : List String} :
    wantsSlash (RouteIndex.of own hu) m p =
      (p.getLast? != some "" && (Routing.matchTable own m (p ++ [""])).isSome) := by
  simp [wantsSlash, RouteIndex.matchTable_of]

theorem own_takes_iff {own : List (Route α)} (hu) (m : Method) (p : List String) :
    ((RouteIndex.of own hu).matchTable m p).isSome || wantsSlash (RouteIndex.of own hu) m p ↔
      ∃ t ∈ own.map Route.key ++ own.filterMap Route.redirect?, t.Takes m p := by
  rw [wantsSlash_of_index, RouteIndex.matchTable_of]
  constructor
  · intro h
    simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    rcases h with h | ⟨hp, h⟩
    · obtain ⟨c, hc, hct⟩ := (matchTable_isSome_iff own m p).1 h
      exact ⟨c.key, List.mem_append.2 (.inl (List.mem_map_of_mem hc)), hct⟩
    · exact takes_of_redirect hp h
  · rintro ⟨t, ht, h⟩
    rcases answers_of_takes ht h with h | ⟨hp, h⟩ <;> simp_all

theorem split_append {l₁ l₂ pre post : List Taker} {x : Taker}
    (h : l₁ ++ l₂ = pre ++ x :: post) :
    (∃ post₁, l₁ = pre ++ x :: post₁) ∨
      ∃ pre₂, pre = l₁ ++ pre₂ ∧ l₂ = pre₂ ++ x :: post := by
  rcases List.append_eq_append_iff.1 h with ⟨a', rfl, h₂⟩ | ⟨c', rfl, h₂⟩
  · exact .inr ⟨a', rfl, h₂⟩
  · cases c' with
    | nil => exact .inr ⟨[], by simp, by simpa using h₂.symm⟩
    | cons y c'' =>
      simp only [List.cons_append, List.cons.injEq] at h₂
      obtain ⟨rfl, _⟩ := h₂
      exact .inl ⟨c'', by simp⟩

mutual
theorem compile_takes_iff : ∀ (r : Router e) (h) (m : Method) (p : List String),
    (compile r h).takes m p = true ↔ ∃ t ∈ r.takers, t.Takes m p
  | { middlewares, routes, routers, fallback }, h, m, p => by
    have ih := compileAll_takes_iff routers
    simp only [compile, Router.takers, List.mem_append, List.mem_map, Bool.or_eq_true,
      List.any_eq_true]
    rw [← Bool.or_eq_true, own_takes_iff]
    constructor
    · rintro ((⟨t, ht, htt⟩ | ⟨root, hr, hp⟩) | hs)
      · exact ⟨t, by simp_all, htt⟩
      · exact ⟨.root root, .inr ⟨root, hr, rfl⟩, hp⟩
      · obtain ⟨t, ht, htt⟩ := (ih _ m p).1 (by simpa [List.any_eq_true] using hs)
        exact ⟨t, .inl (.inr ht), htt⟩
    · rintro ⟨t, (((ht | ht) | ht) | ⟨root, hr, rfl⟩), htt⟩
      · exact .inl (.inl ⟨t, by simp [ht], htt⟩)
      · exact .inl (.inl ⟨t, by simp [ht], htt⟩)
      · exact .inr (by simpa [List.any_eq_true] using (ih _ m p).2 ⟨t, ht, htt⟩)
      · exact .inl (.inr ⟨root, hr, htt⟩)

theorem compileAll_takes_iff : ∀ (rs : List (Router e)) (h) (m : Method) (p : List String),
    (compileAll rs h).any (·.takes m p) = true ↔ ∃ t ∈ Router.takersOf rs, t.Takes m p
  | [], _, _, _ => by simp [compileAll, Router.takersOf]
  | r :: rs, h, m, p => by
    simp only [compileAll, List.any_cons, Bool.or_eq_true, Router.takersOf, List.mem_append]
    rw [compile_takes_iff r, compileAll_takes_iff rs]
    constructor
    · rintro (⟨t, ht, h⟩ | ⟨t, ht, h⟩)
      · exact ⟨t, .inl ht, h⟩
      · exact ⟨t, .inr ht, h⟩
    · rintro ⟨t, ht | ht, h⟩
      · exact .inl ⟨t, ht, h⟩
      · exact .inr ⟨t, ht, h⟩
end

theorem not_route_mem_redirects {own : List (Route α)} {m : Method} {b : List PathSeg} :
    Taker.route m b ∉ own.filterMap Route.redirect? := by
  simp only [List.mem_filterMap, Route.redirect?, Option.map_eq_some_iff, not_exists, not_and]
  intro _ _ _ _ h
  cases h

mutual
theorem compile_served : ∀ (r : Router e) (h) (m : Method) (target : RequestTarget)
    (pre post : List Taker) (b : List PathSeg), r.takers = pre ++ .route m b :: post →
    Accepts b (decodedPath target) → (∀ t ∈ pre, ¬t.Takes m (decodedPath target)) →
      (compile r h).served m target = some ⟨m, b⟩
  | { middlewares, routes, routers, fallback }, h, m, target, pre, post, b, hr, hb, hpre => by
    simp only [Router.takers] at hr
    simp only [compile, RouteIndex.matchTable_of]
    rcases split_append hr with ⟨post₁, h₁⟩ | ⟨pre₂, rfl, h₂⟩
    · rcases split_append h₁ with ⟨post₂, h₂⟩ | ⟨pre₃, rfl, h₃⟩
      · rcases split_append h₂ with ⟨post₃, h₃⟩ | ⟨pre₄, rfl, h₄⟩
        · obtain ⟨⟨mr, res⟩, hmt, hmr⟩ := Option.map_eq_some_iff.1
            (matchTable_first m _ b hb _ pre post₃ h₃ hpre)
          simp only at hmr
          simp [hmt, hmr]
        · have : Taker.route m b ∈ (Entry.listToRoutes routes).filterMap Route.redirect? := by
            rw [h₄]; simp
          exact absurd this not_route_mem_redirects
      · have hown : ∀ t ∈ (Entry.listToRoutes routes).map Route.key ++
            (Entry.listToRoutes routes).filterMap Route.redirect?,
            ¬t.Takes m (decodedPath target) := fun t ht => hpre t (List.mem_append.2 (.inl ht))
        have hmt :
            Routing.matchTable (Entry.listToRoutes routes) m (decodedPath target) = none := by
          cases hm : Routing.matchTable (Entry.listToRoutes routes) m (decodedPath target) with
          | none => rfl
          | some _ =>
            obtain ⟨c, hc, hct⟩ := (matchTable_isSome_iff (Entry.listToRoutes routes) m
              (decodedPath target)).1 (by simp [hm])
            exact absurd hct (hown _ (List.mem_append.2 (.inl (List.mem_map_of_mem hc))))
        have hws : ∀ hu, wantsSlash (RouteIndex.of (Entry.listToRoutes routes) hu) m
            (decodedPath target) = false := fun hu => by
          cases hw :
              wantsSlash (RouteIndex.of (Entry.listToRoutes routes) hu) m (decodedPath target)
          · rfl
          · obtain ⟨t, ht, htt⟩ := (own_takes_iff hu m (decodedPath target)).1 (by simp [hw])
            exact absurd htt (hown t ht)
        have hs : unshadowed (Router.takersOf routers) = true :=
          (unshadowed_append _ _ (unshadowed_append _ _ (by rwa [Router.takers] at h)).1).2
        obtain ⟨c, hc, hcs⟩ := compileAll_served routers hs m target pre₃ post₁ b h₃ hb
          (fun t ht => hpre t (by simp [ht]))
        simp [hmt, slashRedirect?, hws, hc, hcs]
    · have : Taker.route m b ∈ (Entry.listRoots routes).map Taker.root := by rw [h₂]; simp
      simp at this

theorem compileAll_served : ∀ (rs : List (Router e)) (h) (m : Method) (target : RequestTarget)
    (pre post : List Taker) (b : List PathSeg), Router.takersOf rs = pre ++ .route m b :: post →
    Accepts b (decodedPath target) → (∀ t ∈ pre, ¬t.Takes m (decodedPath target)) →
      ∃ c, (compileAll rs h).find? (·.takes m (decodedPath target)) = some c ∧
        c.served m target = some ⟨m, b⟩
  | [], _, _, _, pre, _, _, hr, _, _ => by cases pre <;> simp [Router.takersOf] at hr
  | r :: rs, h, m, target, pre, post, b, hr, hb, hpre => by
    simp only [Router.takersOf] at hr
    simp only [compileAll, List.find?_cons]
    rcases split_append hr with ⟨post₁, h₁⟩ | ⟨pre₂, rfl, h₂⟩
    · have h₀ : unshadowed r.takers = true :=
        (unshadowed_append _ _ (by rwa [Router.takersOf] at h)).1
      have ht : ∀ h', (compile r h').takes m (decodedPath target) = true := fun h' =>
        (compile_takes_iff r h' m _).2
          ⟨.route m b, show Taker.route m b ∈ r.takers by rw [h₁]; simp, rfl, hb⟩
      exact ⟨compile r h₀, by simp [ht],
        compile_served r h₀ m target pre post₁ b h₁ hb hpre⟩
    · have ht : ∀ h', (compile r h').takes m (decodedPath target) = false := fun h' => by
        cases hc : (compile r h').takes m (decodedPath target)
        · rfl
        · obtain ⟨t, ht, htt⟩ := (compile_takes_iff r h' m _).1 hc
          exact absurd htt (hpre t (by simp [ht]))
      simp only [ht]
      exact compileAll_served rs _ m target pre₂ post b h₂ hb
        (fun t ht => hpre t (by simp [ht]))
end

/-- Every route in a router that passes the check is the one it serves a link to that route with.
-/
theorem Router.serves_link (r : Router e) (h : unshadowed r.takers = true) {pre post : List Taker}
    {m : Method} {b : List PathSeg} (hr : r.takers = pre ++ .route m b :: post) :
    ∃ path, Exact b path ∧ ∀ target, decodedPath target = path →
      (compile r h).served m target = some ⟨m, b⟩ := by
  obtain ⟨path, he, hpre⟩ := reachable_of_unshadowed pre post m b (hr ▸ h)
  exact ⟨path, he, fun target ht =>
    compile_served r h m target pre post b hr (ht ▸ accepts_of_exact he) (ht ▸ hpre)⟩

end Routing
