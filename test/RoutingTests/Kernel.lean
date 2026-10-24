/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Routing

/-!
Tables proved by the kernel rather than `native_decide`, from a module, as a consumer that admits
only the standard axioms would prove them.
-/

public section

namespace RoutingTests.Kernel

open Routing Std.Http Server

route_table App
  [ list := "/todos",
    create := "/todos",
    new := "/todos/new",
    item := "/todos/:id:Nat",
    padded := "/todos/01" ]

def ok : Result := fun _ => Response.ok.text "ok"

def index : RouteIndex Result :=
  RouteIndex.of
    [ .get App.patterns.list ok, .post App.patterns.create ok, .get App.patterns.new ok,
      .get App.patterns.item fun _ => ok, .get App.patterns.padded ok ]
    (by decide +kernel)

def router : Router :=
  { routers := [ { routes := [ .get App.patterns.item fun _ => ok ] },
      { routes := [ .mount (.mk ["todos"]) [ .get [] ok ] ] } ] }

def handler : StatelessHandler := router.toHandler (by decide +kernel)

/-- info: 'RoutingTests.Kernel.index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms index

/-- info: 'RoutingTests.Kernel.handler' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms handler

end RoutingTests.Kernel
