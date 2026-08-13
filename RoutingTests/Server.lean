import Routing.Server

/-!
`matchTable`'s own tests (`Route.lean`, `Mount.lean`) are pure `#guard`s over `Route String`.
These run the real `toHandler` against a real `Request Body.Stream` instead, which is the only way
to check the half that `matchTable` can't show: that the `MatchedRoute` actually lands in the
request's and the response's `extensions`.
-/

namespace Routing

open Std Async
open Std Http Server

/-- What the handler saw on its own *request*, smuggled out on the response so a single
round-trip can check both publication directions at once. -/
private structure SeenByHandler where
  matched : Option MatchedRoute
deriving TypeName

private def userSegs : List PathSeg := [.lit "users", .capture "id" .nat]

private def serverRoutes : List (Route Result) :=
  [ .get userSegs (handler := fun (id : Nat) request => do
      let response ← Response.ok.text s!"user #{id}"
      return { response with
                extensions :=
                  response.extensions.insert
                    (SeenByHandler.mk (matchedRoute? request.extensions)) }) ]

private def runRequest (target : String) : IO (Option MatchedRoute × Option SeenByHandler) :=
  Async.block <| ContextAsync.run do
    let body ← Body.empty
    let request := (Request.get (RequestTarget.parse! target)).body body
    let response ← (toHandler serverRoutes).onRequest request
    return (matchedRoute? response.extensions, response.extensions.get SeenByHandler)

private def expected : MatchedRoute := { method := .get, segs := userSegs }

private def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"{label}")

#eval show IO Unit from do
  let (onResponse, seen) ← runRequest "/users/7"
  check s!"response should carry {repr expected}, got {repr onResponse}" (onResponse == some expected)
  check "handler should see the matched route on its request"
    (seen.map (·.matched) == some (some expected))

  -- Requirement: absence is the signal. A 404 carries no `MatchedRoute` at all, so a consumer
  -- can tell "no route matched" from "matched a route whose pattern is empty".
  let (onResponse, seen) ← runRequest "/nope"
  check s!"404 response should carry no MatchedRoute, got {repr onResponse}" (onResponse == none)
  check "404 should not reach a route handler" seen.isNone

end Routing
