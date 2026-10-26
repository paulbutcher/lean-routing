/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Routing.RouteTable
import Routing.Route

namespace Routing

route_table RouteTableTest
  [ index := "/",
    active := "/active",
    edit := "/todos/:id:Nat/edit" ]

#guard RouteTableTest.patterns.index = []
#guard RouteTableTest.patterns.active = [.lit "active"]
#guard RouteTableTest.patterns.edit = [.lit "todos", .capture "id" .nat, .lit "edit"]
#guard RouteTableTest.links.index = "/"
#guard RouteTableTest.links.active = "/active"
#guard RouteTableTest.links.edit 7 = "/todos/7/edit"

-- A route built from `App.patterns` needs no pattern-string parsing of its own; `HandlerType`
-- is computed straight from the already-parsed segments.
private def editRoute : Route String :=
  .get RouteTableTest.patterns.edit (handler := fun (id : Nat) => s!"edit #{id}")

#guard dispatchTable [editRoute] .get ["todos", "7", "edit"] = some "edit #7"
#guard dispatchTable [editRoute] .get ["todos", "notanumber", "edit"] = none

route_table RouteTableDocTest
  [ edit := "/todos/:id:Nat/edit",
    dash := "/a-/b",
    tick := "/a`b``c" ]

route_table RouteTableDocMountTest
  [ docs := mount "/docs" RouteTableDocTest ]

-- Hovering over a generated field shows the row that declared it. `-/` cannot end a docstring it
-- is not written into, and a backtick in a pattern needs a longer fence.
#guard_msgs in
open Lean in
run_cmd do
  let env ← getEnv
  for (decl, expected) in [
      (``RouteTableDocTest.Patterns.edit, "`\"/todos/:id:Nat/edit\"`"),
      (``RouteTableDocTest.Links.edit, "`\"/todos/:id:Nat/edit\"`"),
      (``RouteTableDocTest.Links.dash, "`\"/a-/b\"`"),
      (``RouteTableDocTest.Links.tick, "```\"/a`b``c\"```"),
      (``RouteTableDocMountTest.Patterns.docs, "`mount \"/docs\" RouteTableDocTest`"),
      (``RouteTableDocMountTest.Links.docs, "`mount \"/docs\" RouteTableDocTest`")] do
    let actual ← findDocString? env decl
    unless actual == some expected do
      throwError "{decl}: expected {repr expected}, got {repr actual}"

#guard RouteTableDocTest.links.dash = "/a-/b"

-- Negative-compile regression: declaring the same name twice is a command-time error, not a
-- silently-overwritten field.
/--
error: route name 'index' already declared at `index
-/
#guard_msgs in
route_table RouteTableTestDup
  [ index := "/",
    index := "/elsewhere" ]

-- Negative-compile regression: a malformed pattern string is a command-time error at the row
-- that declares it (`segsSrcFor`, `RouteTable.lean`), not a silently-accepted bad route.
/--
error: invalid route pattern "not-a-valid-pattern"
-/
#guard_msgs in
route_table RouteTableTestInvalid
  [ bad := "not-a-valid-pattern" ]

end Routing
