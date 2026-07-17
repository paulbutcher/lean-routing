import Routing.RouteTable
import Routing.Route

namespace Routing

routeTable! RouteTableTest
  [ "/" as index,
    "/active" as active,
    "/todos/:id:Nat/edit" as edit ]

#guard RouteTableTest.patterns.index = []
#guard RouteTableTest.patterns.active = [.lit "active"]
#guard RouteTableTest.patterns.edit = [.lit "todos", .capture "id" .nat, .lit "edit"]
#guard RouteTableTest.links.index = "/"
#guard RouteTableTest.links.active = "/active"
#guard RouteTableTest.links.edit 7 = "/todos/7/edit"

-- A route built from `App.patterns` needs no pattern-string parsing of its own -- `HandlerType`
-- is computed straight from the already-parsed segments.
private def editRoute : Route String :=
  .get RouteTableTest.patterns.edit (handler := fun (id : Nat) => s!"edit #{id}")

#guard dispatchTable [editRoute] .get ["todos", "7", "edit"] = some "edit #7"
#guard dispatchTable [editRoute] .get ["todos", "notanumber", "edit"] = none

-- Negative-compile regression: declaring the same name twice is a command-time error, not a
-- silently-overwritten field.
/--
error: route name 'index' already declared at `index
-/
#guard_msgs in
routeTable! RouteTableTestDup
  [ "/" as index,
    "/elsewhere" as index ]

end Routing
