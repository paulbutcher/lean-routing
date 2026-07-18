import Routing.Pattern

/-!
Computing a handler's function type from a route pattern, and dispatching
a decoded request path against it. -/

namespace Routing

/-- The type a handler for `segs` must have. -/
def HandlerType (segs : List PathSeg) (result : Type) : Type :=
  match segs with
  | [] => result
  | .lit _ :: rest => HandlerType rest result
  | .capture _ kind :: rest => kind.type → HandlerType rest result

/-- Matches a decoded request path (`List String`, e.g. from
`RequestTarget.path.toDecodedSegments`) against `segs`, applying `handler`
to the extracted, typed capture values as it goes. -/
def dispatch {result : Type} :
    (segs : List PathSeg) → HandlerType segs result → List String → Option result
  | [], h, [] => some h
  | .lit s :: rest, h, p :: ps => if s == p then dispatch rest h ps else none
  | .capture _ .nat :: rest, h, p :: ps => p.toNat?.bind (fun n => dispatch rest (h n) ps)
  | .capture _ .string :: rest, h, p :: ps => dispatch rest (h p) ps
  | _, _, _ => none

/-- The Lean type a reverse-routing function for `segs` produces -/
@[reducible] def LinkType : List PathSeg → Type
  | [] => String
  | .lit _ :: rest => LinkType rest
  | .capture _ kind :: rest => kind.type → LinkType rest

/-- Builds the `/`-joined path for `segs`, given the literal/rendered-capture parts collected so
far. -/
def linkParts : (segs : List PathSeg) → List String → LinkType segs
  | [], parts => "/" ++ String.intercalate "/" parts
  | .lit s :: rest, parts => linkParts rest (parts ++ [s])
  | .capture _ .nat :: rest, parts => fun n => linkParts rest (parts ++ [toString n])
  | .capture _ .string :: rest, parts => fun s => linkParts rest (parts ++ [s])

/-- The reverse-routing function for a route pattern's segments: a `String`, or a function taking
one argument per capture (in order) and returning one, e.g.
`linkFor [.lit "todos", .capture "id" .nat] : Nat → String`. -/
def linkFor (segs : List PathSeg) : LinkType segs := linkParts segs []

end Routing
