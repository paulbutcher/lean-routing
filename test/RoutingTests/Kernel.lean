/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import RoutingStd

/-!
Tables proved by the kernel rather than `native_decide`, from a module, as a consumer that admits
only the standard axioms would prove them. `generic` and `genericRouter` are written over any
engine, as a library leaving the engine to its application writes them, which `decide +kernel`
alone cannot prove.
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

def ok : Result .std := fun _ => Response.ok.text "ok"

def index : RouteIndex (Result .std) :=
  RouteIndex.of
    [ .get App.patterns.list ok, .post App.patterns.create ok, .get App.patterns.new ok,
      .get App.patterns.item fun _ => ok, .get App.patterns.padded ok ]
    (by routes_unshadowed +kernel)

def router : Router .std :=
  { routers := [ { routes := [ .get App.patterns.item fun _ => ok ] },
      { routes := [ .mount (.mk ["todos"]) [ .get [] ok ] ] } ] }

def handler : StatelessHandler .std := router.toHandler (by routes_unshadowed +kernel)

-- The default proof of a router's table, which is evaluated while compiling, from a module that
-- imports `Routing.Router` only as code.
def handlerNative : StatelessHandler .std := router.toHandler

def genericOk {e : Engine} : Result e := fun _ => e.text Response.ok "ok"

def generic {e : Engine} : StatelessHandler e :=
  toHandler [ .get App.patterns.list genericOk, .get App.patterns.new genericOk ]
    (h := by routes_unshadowed +kernel)

def genericRouter {e : Engine} : StatelessHandler e :=
  Router.toHandler { routes := [ .mount (.mk ["todos"]) [ .get [] genericOk ] ] }
    (by routes_unshadowed +kernel)

/-- info: 'RoutingTests.Kernel.index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms index

/-- info: 'RoutingTests.Kernel.handler' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms handler

/-- info: 'RoutingTests.Kernel.generic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms generic

/--
info: 'RoutingTests.Kernel.genericRouter' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms genericRouter

-- The kernel check reports a shadowed route as the default does.
/--
error: GET /todos/new is unreachable behind GET /todos/:name:String
-/
#guard_msgs in
example : StatelessHandler .std :=
  toHandler [ .get [.lit "todos", .capture "name" .string] (fun _ => ok), .get App.patterns.new ok ]
    (h := by routes_unshadowed +kernel)

end RoutingTests.Kernel
