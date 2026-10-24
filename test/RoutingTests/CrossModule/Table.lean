/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Routing.RouteTable
public import Routing.Trie

/-!
The tables `RoutingTests/CrossModule.lean` consumes. `HandlerType` and `LinkType` both reduce the
pattern value they are given, so what `route_table` generates here has to cross the module
boundary for a consumer to check at all.
-/

public section

namespace RoutingTests.CrossModule

open Routing

route_table Leaf
  [ index := "/",
    item := "/:slug:String" ]

route_table App
  [ home := "/",
    leaf := mount "/leaf" Leaf ]

-- A table inside an `@[expose] section` already gets the attribute from the section, so the
-- macro must not add one of its own, which would be a warning.
@[expose] section

route_table Wrapped
  [ index := "/" ]

end

-- `routes_unshadowed` needs these bodies, in another module, to drop handlers closing over a local.
def greetings (greeting : String) : List (Route String) :=
  [ .get Leaf.patterns.index greeting ]

@[expose] def exposedGreetings (greeting : String) : List (Route String) :=
  [ .get Leaf.patterns.index greeting ]
