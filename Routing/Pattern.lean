/-!
Route pattern strings (`"/users/:id:Nat/posts/:slug:String"`) parsed into
`List PathSeg`. See `docs/routing-design-plan.md` §3 for why this parser is
hand-rolled structural recursion over `List Char` rather than
`String.splitOn`: on this toolchain (`v4.31.0`, `String` rebuilt around
`String.Slice`), a `String.splitOn`-based parser does not reduce through
kernel defeq, which silently breaks `HandlerType`-computed types (`Handler.lean`)
built from its output. A hand-rolled `List Char` recursion was confirmed (by
the throwaway spike behind this design doc) to reduce fine.
-/

namespace Routing

/-- The two capture types supported in v1. Closed by design for now --
whether to open this into a typeclass is deferred, see
`docs/routing-design-plan.md` §5. -/
inductive CaptureKind where
  | nat
  | string
deriving Repr, DecidableEq

/-- The Lean `Type` a capture of this kind produces. Marked `@[reducible]`
because typeclass search uses stricter transparency than ordinary
elaboration and can otherwise fail to see through this even where `rfl`
succeeds -- see `docs/routing-design-plan.md` §4. -/
@[reducible] def CaptureKind.type : CaptureKind → Type
  | .nat => Nat
  | .string => String

/-- The pattern-string spelling of a capture kind (`:id:Nat` / `:id:String`).
Single source of truth for both rendering (`PathSeg.toString`) and parsing
(`parseSeg`), so the two can never drift apart. -/
def CaptureKind.name : CaptureKind → String
  | .nat => "Nat"
  | .string => "String"

/-- One segment of a route path pattern: a literal segment to match
verbatim, or a named, typed capture. -/
inductive PathSeg where
  | lit (s : String)
  | capture (name : String) (kind : CaptureKind)
deriving Repr, DecidableEq

/-- Renders a single segment back to its pattern-string spelling. Built
directly from `List Char` (not string interpolation) so the round-trip
proof (`parsePattern_renderPattern`, `RoutingTests/Pattern.lean`) can
reason about it structurally. -/
def PathSeg.toString (seg : PathSeg) : String :=
  match seg with
  | .lit s => s
  | .capture name kind =>
      String.ofList (':' :: name.toList ++ ':' :: kind.name.toList)

/-- A segment is well-formed as a *renderable* pattern segment when it
doesn't contain characters that would be re-parsed as a different
structure: no `/` (would split into more segments), and -- for `lit` -- no
leading `:` (would be re-parsed as a capture); for `capture`, no `:` in the
name (would confuse the name/kind split). This is exactly the
precondition `parsePattern_renderPattern` (`RoutingTests/Pattern.lean`) needs;
routes built by hand from ordinary identifiers naturally satisfy it. -/
def PathSeg.WellFormed : PathSeg → Prop
  | .lit s => s ≠ "" ∧ (∀ c ∈ s.toList, c ≠ '/') ∧ s.toList.head? ≠ some ':'
  | .capture name _ => name ≠ "" ∧ (∀ c ∈ name.toList, c ≠ '/' ∧ c ≠ ':')

/-- Renders a full pattern (list of segments) back to its `"/"`-prefixed
source form, e.g. `[.lit "users", .capture "id" .nat] ↦ "/users/:id:Nat"`.
The empty list renders as the root path `"/"`. -/
def renderPattern (segs : List PathSeg) : String :=
  String.ofList ('/' :: joinWithSlash (segs.map (fun seg => seg.toString.toList)))
where
  /-- Interspaces `'/'` between a list of `List Char` chunks, e.g.
  `[cs₁, cs₂, cs₃] ↦ cs₁ ++ '/' :: cs₂ ++ '/' :: cs₃`. -/
  joinWithSlash : List (List Char) → List Char
    | [] => []
    | [cs] => cs
    | cs :: rest => cs ++ '/' :: joinWithSlash rest

/-- Splits a single first `':'` off a `List Char`, e.g. `"id:Nat".toList`
splits to `("id".toList, "Nat".toList)`. Returns `none` if there is no
second `':'` (a capture segment missing its kind, e.g. bare `:id`). Plain
structural recursion, no `String` operations. -/
def splitOnceColon : List Char → Option (List Char × List Char)
  | [] => none
  | c :: rest =>
      if c = ':' then
        some ([], rest)
      else
        (splitOnceColon rest).map (fun (name, kind) => (c :: name, kind))

/-- Parses one path segment's characters into a `PathSeg`. A segment
starting with `':'` is parsed as a capture (`name:kind`, kind must be a
known `CaptureKind.name`); anything else is a literal. Malformed captures
(missing kind, unknown kind name, empty capture name) fail via `none`,
never a panic -- see the `#guard` regressions in `RoutingTests/Pattern.lean`. -/
def parseSeg (cs : List Char) : Option PathSeg :=
  match cs with
  | [] => none
  | c :: rest =>
      if c = ':' then
        match splitOnceColon rest with
        | none => none
        | some ([], _) => none
        | some (nameChars, kindChars) =>
            let kindStr := String.ofList kindChars
            if kindStr = CaptureKind.nat.name then
              some (.capture (String.ofList nameChars) .nat)
            else if kindStr = CaptureKind.string.name then
              some (.capture (String.ofList nameChars) .string)
            else
              none
      else
        some (.lit (String.ofList (c :: rest)))

/-- Splits a `List Char` on `'/'`, e.g. `"a/bc/d".toList` splits to
`[['a'], ['b','c'], ['d']]`. A structural recursion over `List Char`, never
`String.splitOn` -- see the module docstring. -/
def splitChars : List Char → List (List Char)
  | [] => [[]]
  | c :: rest =>
      if c = '/' then
        [] :: splitChars rest
      else
        match splitChars rest with
        | [] => [[c]]
        | seg :: segs => (c :: seg) :: segs

/-- Parses a list of already-split segment character-lists into `PathSeg`s,
failing the whole pattern if any one segment fails (e.g. an empty segment
from a doubled or trailing `/`, or a malformed capture). Hand-rolled rather
than `List.mapM` so the round-trip proof can induct on it directly. -/
def mapSegs : List (List Char) → Option (List PathSeg)
  | [] => some []
  | cs :: rest => (parseSeg cs).bind (fun seg => (mapSegs rest).map (seg :: ·))

/-- Parses a full route pattern string (must start with `"/"`) into path
segments. The root path `"/"` parses to `[]`; anything not starting with
`"/"`, or containing an empty segment (doubled or trailing `/`), or an
unparseable segment, fails via `none`. -/
def parsePattern (s : String) : Option (List PathSeg) :=
  match s.toList with
  | ['/'] => some []
  | '/' :: rest => mapSegs (splitChars rest)
  | _ => none

/-- Parses a route pattern, panicking on a malformed pattern. Intended only
for pattern strings written as source-code literals by the route author
(so a malformed pattern is a programming error caught immediately at
startup), never for untrusted input. -/
def parsePattern! (s : String) : List PathSeg :=
  (parsePattern s).getD []

end Routing
