import Routing.Pattern

/-!
Computing a handler's function type from a route pattern, and dispatching
a decoded request path against it. See `docs/routing-design-plan.md` §2:
the throwaway spike behind that design doc confirmed (by direct
compilation, not just reasoning about it) that `HandlerType` reduces
through ordinary kernel defeq (`rfl`) with **zero extra machinery** -- no
macro, no typeclass dispatch step -- which is what lets a wrong-arity
handler be rejected as an ordinary compile-time type error (the
`#guard_msgs` regression in `RoutingTests/Handler.lean`), the same way
Servant's type-level encoding does in Haskell, but without needing
DataKinds/type families to fake a type depending on a value.
-/

namespace Routing

/-- The Lean function type a handler for `segs` must have: one argument
per capture segment (typed via `CaptureKind.type`), literal segments
contribute nothing to the arity, and the whole thing returns `result`. -/
def HandlerType (segs : List PathSeg) (result : Type) : Type :=
  match segs with
  | [] => result
  | .lit _ :: rest => HandlerType rest result
  | .capture _ kind :: rest => kind.type → HandlerType rest result

/-- Matches a decoded request path (`List String`, e.g. from
`RequestTarget.path.toDecodedSegments`) against `segs`, applying `handler`
to the extracted, typed capture values as it goes. `none` on a literal
mismatch, a path segment that doesn't parse as the capture's type (e.g.
`"notanumber"` against a `.nat` capture), or an arity mismatch between
`segs` and the actual path. There's no automatic derivation for this step
(unlike Servant's `HasServer` instance search) -- it's a real, accepted
cost of not having macros do the work, per `docs/routing-design-plan.md`
§2. -/
def dispatch {result : Type} :
    (segs : List PathSeg) → HandlerType segs result → List String → Option result
  | [], h, [] => some h
  | .lit s :: rest, h, p :: ps => if s == p then dispatch rest h ps else none
  | .capture _ .nat :: rest, h, p :: ps => p.toNat?.bind (fun n => dispatch rest (h n) ps)
  | .capture _ .string :: rest, h, p :: ps => dispatch rest (h p) ps
  | _, _, _ => none

/-- The Lean type a reverse-routing function for `segs` produces: a `String` once every capture
has been supplied a value, one curried argument per capture segment beforehand -- the mirror image
of `HandlerType`, which computes a request *handler*'s argument types from the same `segs` value.
Marked `@[reducible]` for the same reason as `CaptureKind.type` (`Pattern.lean`): typeclass search
(here, `DecidableEq` for the `#guard` tests below) uses stricter transparency than ordinary
elaboration. -/
@[reducible] def LinkType : List PathSeg → Type
  | [] => String
  | .lit _ :: rest => LinkType rest
  | .capture _ kind :: rest => kind.type → LinkType rest

/-- Builds the `/`-joined path for `segs`, given the literal/rendered-capture parts collected so
far. Structural recursion over `segs`, mirroring `dispatch`, but producing a value (accumulating
`parts`) instead of consuming a `List String` of an incoming request's path. -/
def linkParts : (segs : List PathSeg) → List String → LinkType segs
  | [], parts => "/" ++ String.intercalate "/" parts
  | .lit s :: rest, parts => linkParts rest (parts ++ [s])
  | .capture _ .nat :: rest, parts => fun n => linkParts rest (parts ++ [toString n])
  | .capture _ .string :: rest, parts => fun s => linkParts rest (parts ++ [s])

/-- The reverse-routing function for a route pattern's segments: a `String`, or a function taking
one argument per capture (in order) and returning one, e.g. `linkFor (parsePattern! "/todos/:id:Nat")
: Nat → String`. -/
def linkFor (segs : List PathSeg) : LinkType segs := linkParts segs []

end Routing
