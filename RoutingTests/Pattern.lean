import Routing.Pattern

namespace Routing

#guard parsePattern "/" = some []
#guard parsePattern "/users" = some [.lit "users"]
#guard parsePattern "/users/:id:Nat" = some [.lit "users", .capture "id" .nat]
#guard parsePattern "/users/:id:Nat/posts/:slug:String"
  = some [.lit "users", .capture "id" .nat, .lit "posts", .capture "slug" .string]

-- malformed patterns fail via `none`
#guard parsePattern "" = none                          -- no leading '/'
#guard parsePattern "users/:id:Nat" = none             -- no leading '/'
#guard parsePattern "/users//id" = none                -- doubled '/' ⇒ empty segment
#guard parsePattern "/users/" = none                   -- trailing '/' ⇒ empty segment
#guard parsePattern "/users/:id:Bool" = none           -- unknown capture kind
#guard parsePattern "/users/:id" = none                -- missing capture kind
#guard parsePattern "/users/::Nat" = none              -- empty capture name

-- `parsePattern!` fails to *compile* on a malformed pattern (its `h` autoParam's `by decide`
-- fails against the literal), rather than returning a bogus value or panicking at runtime.
-- `#check_failure` is itself the assertion here: it's a build error if the term *doesn't* fail
-- to elaborate, so there's no fragile error-message text to pin down.
#check_failure parsePattern! "not-a-valid-pattern"

/-! ## Round-trip: `renderPattern` and `parsePattern` are mutual inverses
 -/

private theorem splitOnceColon_append (name tail : List Char)
    (h : ∀ c ∈ name, c ≠ ':') :
    splitOnceColon (name ++ ':' :: tail) = some (name, tail) := by
  induction name with
  | nil => simp [splitOnceColon]
  | cons c name' ih =>
    have hc : c ≠ ':' := h c (by simp)
    have hname' : ∀ c' ∈ name', c' ≠ ':' := fun c' hmem => h c' (by simp [hmem])
    show splitOnceColon ((c :: name') ++ ':' :: tail) = some (c :: name', tail)
    simp only [List.cons_append, splitOnceColon, if_neg hc]
    rw [ih hname']
    rfl

private theorem splitChars_noSlash : ∀ (cs : List Char), (∀ c ∈ cs, c ≠ '/') →
    splitChars cs = [cs]
  | [], _ => rfl
  | c :: cs', h => by
    have hc : c ≠ '/' := h c (by simp)
    have hcs' : ∀ c' ∈ cs', c' ≠ '/' := fun c' hmem => h c' (by simp [hmem])
    have ih := splitChars_noSlash cs' hcs'
    show splitChars (c :: cs') = [c :: cs']
    simp only [splitChars, if_neg hc, ih]

private theorem splitChars_append_slash : ∀ (cs rest : List Char),
    (∀ c ∈ cs, c ≠ '/') → splitChars (cs ++ '/' :: rest) = cs :: splitChars rest
  | [], rest, _ => by simp [splitChars]
  | c :: cs', rest, h => by
    have hc : c ≠ '/' := h c (by simp)
    have hcs' : ∀ c' ∈ cs', c' ≠ '/' := fun c' hmem => h c' (by simp [hmem])
    have ih := splitChars_append_slash cs' rest hcs'
    show splitChars ((c :: cs') ++ '/' :: rest) = (c :: cs') :: splitChars rest
    simp only [List.cons_append, splitChars, if_neg hc, ih]

private theorem splitChars_joinWithSlash : ∀ (css : List (List Char)),
    (∀ cs ∈ css, ∀ c ∈ cs, c ≠ '/') → css ≠ [] →
    splitChars (renderPattern.joinWithSlash css) = css
  | [], _, hne => absurd rfl hne
  | [cs], h, _ => by
    have hcs : ∀ c ∈ cs, c ≠ '/' := h cs (by simp)
    simpa [renderPattern.joinWithSlash] using splitChars_noSlash cs hcs
  | cs :: cs' :: rest, h, _ => by
    have hcs : ∀ c ∈ cs, c ≠ '/' := h cs (by simp)
    have hrest : ∀ cs'' ∈ (cs' :: rest), ∀ c ∈ cs'', c ≠ '/' :=
      fun cs'' hmem => h cs'' (by simp [hmem])
    have ih := splitChars_joinWithSlash (cs' :: rest) hrest (by simp)
    show splitChars (cs ++ '/' :: renderPattern.joinWithSlash (cs' :: rest)) = cs :: cs' :: rest
    rw [splitChars_append_slash cs _ hcs, ih]

private theorem parseSeg_toString (seg : PathSeg) (h : seg.WellFormed) :
    parseSeg seg.toString.toList = some seg := by
  cases seg with
  | lit s =>
    obtain ⟨hne, _hnoslash, hnocolon⟩ := h
    match hs : s.toList with
    | [] => exact absurd (String.toList_eq_nil_iff.mp hs) hne
    | c :: rest =>
      have hc : c ≠ ':' := by
        intro hcolon
        exact hnocolon (by simp [hs, hcolon])
      show parseSeg (c :: rest) = some (PathSeg.lit s)
      simp only [parseSeg, if_neg hc]
      rw [← hs, String.ofList_toList]
  | capture name kind =>
    obtain ⟨hne, hcond⟩ := h
    have hnocolon : ∀ c ∈ name.toList, c ≠ ':' := fun c hmem => (hcond c hmem).2
    show parseSeg (String.ofList (':' :: name.toList ++ ':' :: kind.name.toList)).toList
      = some (PathSeg.capture name kind)
    rw [String.toList_ofList]
    show parseSeg (':' :: (name.toList ++ ':' :: kind.name.toList)) = some (PathSeg.capture name kind)
    simp only [parseSeg, if_true]
    rw [splitOnceColon_append name.toList kind.name.toList hnocolon]
    have hnameNil : name.toList ≠ [] := fun heq => hne (String.toList_eq_nil_iff.mp heq)
    obtain ⟨c, cs, hname⟩ := List.exists_cons_of_ne_nil hnameNil
    have hname_ofList : String.ofList (c :: cs) = name := by rw [← hname, String.ofList_toList]
    simp only [hname, hname_ofList]
    cases kind with
    | nat => simp [CaptureKind.name]
    | string => simp [CaptureKind.name]

private theorem mapSegs_toString : ∀ (segs : List PathSeg), (∀ seg ∈ segs, seg.WellFormed) →
    mapSegs (segs.map (fun seg => seg.toString.toList)) = some segs
  | [], _ => rfl
  | seg :: segs', h => by
    have hseg : seg.WellFormed := h seg (by simp)
    have hsegs' : ∀ seg' ∈ segs', seg'.WellFormed := fun seg' hmem => h seg' (by simp [hmem])
    show mapSegs (seg.toString.toList :: segs'.map (fun seg => seg.toString.toList)) = some (seg :: segs')
    simp only [mapSegs, parseSeg_toString seg hseg, Option.bind_some,
      mapSegs_toString segs' hsegs', Option.map_some]

/-- **The round-trip property, and the main piece of formal verification for
`Routing/Pattern.lean`**: rendering a well-formed list of path segments back to a
pattern string, then parsing that string, recovers exactly the original
segments. -/
theorem parsePattern_renderPattern (segs : List PathSeg) (h : ∀ seg ∈ segs, seg.WellFormed) :
    parsePattern (renderPattern segs) = some segs := by
  have htoList : (renderPattern segs).toList
      = '/' :: renderPattern.joinWithSlash (segs.map (fun seg => seg.toString.toList)) := by
    unfold renderPattern
    rw [String.toList_ofList]
  rcases segs with _ | ⟨seg, segs'⟩
  · show parsePattern (renderPattern []) = some []
    have hs : (renderPattern ([] : List PathSeg)).toList = ['/'] := by rw [htoList]; rfl
    unfold parsePattern
    rw [hs]
    rfl
  · have hkindNoSlash : ∀ (kind : CaptureKind) c, c ∈ kind.name.toList → c ≠ '/' := by
      intro kind
      cases kind <;> decide
    have hcssNe : (seg :: segs').map (fun s => s.toString.toList) ≠ [] := by simp
    have hnoSlash : ∀ cs ∈ (seg :: segs').map (fun s => s.toString.toList),
        ∀ c ∈ cs, c ≠ '/' := by
      intro cs hcs c hc
      simp only [List.mem_map] at hcs
      obtain ⟨seg', hseg'mem, hseg'eq⟩ := hcs
      have hwf := h seg' hseg'mem
      cases seg' with
      | lit s =>
        obtain ⟨_, hnoslash, _⟩ := hwf
        subst hseg'eq
        exact hnoslash c hc
      | capture name kind =>
        obtain ⟨_, hcond⟩ := hwf
        subst hseg'eq
        simp only [PathSeg.toString, String.toList_ofList, List.mem_cons, List.mem_append] at hc
        rcases hc with (rfl | hc) | (rfl | hc)
        · decide
        · exact (hcond c hc).1
        · decide
        · exact hkindNoSlash kind c hc
    have hrest : renderPattern.joinWithSlash ((seg :: segs').map (fun s => s.toString.toList))
        ≠ [] := by
      cases segs' with
      | nil =>
        have hsegWF := h seg (by simp)
        have hne : seg.toString ≠ "" := by
          cases seg with
          | lit s => exact hsegWF.1
          | capture name kind => simp [PathSeg.toString]
        simp only [renderPattern.joinWithSlash, List.map_cons, List.map_nil]
        exact fun heq => hne (String.toList_eq_nil_iff.mp heq)
      | cons seg' segs'' =>
        simp [renderPattern.joinWithSlash]
    obtain ⟨c0, r0, hcr0⟩ := List.exists_cons_of_ne_nil hrest
    have hs : (renderPattern (seg :: segs')).toList = '/' :: c0 :: r0 := by
      rw [htoList, hcr0]
    show parsePattern (renderPattern (seg :: segs')) = some (seg :: segs')
    unfold parsePattern
    rw [hs]
    show mapSegs (splitChars (c0 :: r0)) = some (seg :: segs')
    rw [← hcr0, splitChars_joinWithSlash _ hnoSlash hcssNe, mapSegs_toString (seg :: segs') h]

end Routing
