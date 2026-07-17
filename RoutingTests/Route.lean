import Routing.Route

namespace Routing

-- #guard tests: first match wins, method mismatch, path mismatch all fall through.
private def testRoutes : List (Route String) :=
  [ .get "/" "home",
    .get "/users/:id:Nat" (fun (id : Nat) => s!"user #{id}"),
    .post "/users/:id:Nat" (fun (id : Nat) => s!"created #{id}") ]

#guard dispatchTable testRoutes .get [] = some "home"
#guard dispatchTable testRoutes .get ["users", "7"] = some "user #7"
#guard dispatchTable testRoutes .post ["users", "7"] = some "created #7"
#guard dispatchTable testRoutes .get ["users", "nope"] = none
#guard dispatchTable testRoutes .delete ["users", "7"] = none
#guard dispatchTable testRoutes .get ["missing"] = none

end Routing
