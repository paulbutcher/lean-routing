import Routing.Route

namespace Routing

-- `.get`/`.post`/etc. (`Route.lean`'s `route`/`.get`/`.post`/`.put`/`.delete`), taking
-- already-parsed segments directly -- what `routeTable!`'s generated `App.patterns`
-- (`RouteTable.lean`) is meant to feed them.
private def userSegs : List PathSeg := [.lit "users", .capture "id" .nat]

private def testRoutes : List (Route String) :=
  [ .get ([] : List PathSeg) (handler := "home"),
    .get userSegs (handler := fun (id : Nat) => s!"user #{id}"),
    .post userSegs (handler := fun (id : Nat) => s!"created #{id}"),
    .put userSegs (handler := fun (id : Nat) => s!"updated #{id}"),
    .delete userSegs (handler := fun (id : Nat) => s!"deleted #{id}") ]

#guard dispatchTable testRoutes .get [] = some "home"
#guard dispatchTable testRoutes .get ["users", "7"] = some "user #7"
#guard dispatchTable testRoutes .post ["users", "7"] = some "created #7"
#guard dispatchTable testRoutes .put ["users", "7"] = some "updated #7"
#guard dispatchTable testRoutes .delete ["users", "7"] = some "deleted #7"
#guard dispatchTable testRoutes .get ["users", "nope"] = none
#guard dispatchTable testRoutes .get ["missing"] = none

-- `.getPattern`/`.postPattern`/etc., for a one-off route not declared via `routeTable!`.
private def patternRoutes : List (Route String) :=
  [ .getPattern "/" (handler := "home"),
    .getPattern "/users/:id:Nat" (handler := fun (id : Nat) => s!"user #{id}"),
    .postPattern "/users/:id:Nat" (handler := fun (id : Nat) => s!"created #{id}") ]

#guard dispatchTable patternRoutes .get [] = some "home"
#guard dispatchTable patternRoutes .get ["users", "7"] = some "user #7"
#guard dispatchTable patternRoutes .post ["users", "7"] = some "created #7"

-- Negative-compile regression: a malformed pattern is an elaboration error at the route
-- definition
#check_failure Route.getPattern (result := String) "not-a-valid-pattern"

end Routing
