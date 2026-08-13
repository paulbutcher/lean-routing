import Routing.Route

namespace Routing

-- Stands in for a `route_table`-generated `App.patterns` field.
private def userSegs : List PathSeg := [.lit "users", .capture "id" .nat]

private def noteSegs : List PathSeg := [.lit "notes", .capture "slug" .string]

private def testRoutes : List (Route String) :=
  [ .get ([] : List PathSeg) (handler := "home"),
    .get userSegs (handler := fun (id : Nat) => s!"user #{id}"),
    .post userSegs (handler := fun (id : Nat) => s!"created #{id}"),
    .put userSegs (handler := fun (id : Nat) => s!"updated #{id}"),
    .delete userSegs (handler := fun (id : Nat) => s!"deleted #{id}"),
    .get noteSegs (handler := fun (slug : String) => s!"note {slug}") ]

#guard dispatchTable testRoutes .get [] = some "home"
#guard dispatchTable testRoutes .get ["users", "7"] = some "user #7"
#guard dispatchTable testRoutes .post ["users", "7"] = some "created #7"
#guard dispatchTable testRoutes .put ["users", "7"] = some "updated #7"
#guard dispatchTable testRoutes .delete ["users", "7"] = some "deleted #7"
#guard dispatchTable testRoutes .get ["users", "nope"] = none
#guard dispatchTable testRoutes .get ["missing"] = none

-- `matchTable` returns what `dispatchTable` does, plus the pattern that produced it -- for a
-- static route, for a capture of each `CaptureKind`, and (with the method, which is what
-- distinguishes these four) for every method sharing one pattern.
#guard matchTable testRoutes .get [] = some ({ method := .get, segs := [] }, "home")
#guard matchTable testRoutes .get ["users", "7"] = some ({ method := .get, segs := userSegs }, "user #7")
#guard matchTable testRoutes .post ["users", "7"] = some ({ method := .post, segs := userSegs }, "created #7")
#guard matchTable testRoutes .put ["users", "7"] = some ({ method := .put, segs := userSegs }, "updated #7")
#guard matchTable testRoutes .delete ["users", "7"] = some ({ method := .delete, segs := userSegs }, "deleted #7")
#guard matchTable testRoutes .get ["notes", "hi"] = some ({ method := .get, segs := noteSegs }, "note hi")

-- The reported `segs` is the *pattern*, not the requested path: two different ids report the
-- same `segs`, which is exactly the low-cardinality property that makes it groupable.
#guard (matchTable testRoutes .get ["users", "7"]).map (·.1.segs)
     = (matchTable testRoutes .get ["users", "8"]).map (·.1.segs)

-- No match reports nothing at all -- absence is the signal, so a 404 can't be confused with a
-- route whose pattern happens to be empty (`segs = []` is the root route, matched above).
#guard matchTable testRoutes .get ["users", "nope"] = none
#guard matchTable testRoutes .get ["missing"] = none
#guard matchTable testRoutes .put ["notes", "hi"] = none

end Routing
