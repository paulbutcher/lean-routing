import Routing.Route

namespace Routing

private def testRoutes : List (Route String) :=
  [ .get "/" (handler := "home"),
    .get "/users/:id:Nat" (handler := fun (id : Nat) => s!"user #{id}"),
    .post "/users/:id:Nat" (handler := fun (id : Nat) => s!"created #{id}") ]

#guard dispatchTable testRoutes .get [] = some "home"
#guard dispatchTable testRoutes .get ["users", "7"] = some "user #7"
#guard dispatchTable testRoutes .post ["users", "7"] = some "created #7"
#guard dispatchTable testRoutes .get ["users", "nope"] = none
#guard dispatchTable testRoutes .delete ["users", "7"] = none
#guard dispatchTable testRoutes .get ["missing"] = none

-- Negative-compile regression: a malformed pattern is an elaboration error at the route
-- definition
#check_failure Route.get (result := String) "not-a-valid-pattern"

end Routing
