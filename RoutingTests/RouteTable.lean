import Routing.RouteTable

namespace Routing

routeTable! RouteTableTest
  [ "/" as index,
    "/active" as active,
    "/todos/:id:Nat/edit" as edit ]

-- #guard tests: the pattern and link structures' shapes and their values -- same shape
-- `Todo/Links.lean` proved by hand before this macro automated it.
#guard RouteTableTest.patterns.index = "/"
#guard RouteTableTest.patterns.active = "/active"
#guard RouteTableTest.patterns.edit = "/todos/:id:Nat/edit"
#guard RouteTableTest.links.index = "/"
#guard RouteTableTest.links.active = "/active"
#guard RouteTableTest.links.edit 7 = "/todos/7/edit"

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
