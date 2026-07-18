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

end Routing
