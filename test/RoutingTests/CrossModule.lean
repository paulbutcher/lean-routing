/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import RoutingTests.CrossModule.Table
public import Routing.Route

/-!
Compiling is passing: neither declaration below checks unless the bodies generated in
`CrossModule/Table.lean` reach this module.
-/

namespace RoutingTests.CrossModule

open Routing

-- `HandlerType` computes the type this handler must have by reducing the pattern it is given.
def itemRoute : Route String :=
  .get App.patterns.leaf.item (handler := fun (slug : String) => s!"item {slug}")

-- Each field of a mount's `Links` is `linkFor` of the prefixed segments, checked against the
-- mounted table's own field type, which is `LinkType` of the unprefixed ones.
route_table Outer
  [ sub := mount "/sub" App,
    wrapped := mount "/wrapped" Wrapped ]
