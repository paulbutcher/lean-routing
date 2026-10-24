/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Routing.Router

/-!
The core routes on an engine with no server behind it at all: handlers in `Id`, bodies as
`String`. The `404` and the slash redirect are the two responses the core builds itself, through
`Engine.text`, so they are what this checks.
-/

namespace RoutingTests.Engine

open Routing
open Std.Http

private def pureEngine : Engine where
  M := Id
  Hook := Id
  ReqBody := Unit
  RespBody := String
  text builder content := builder.body content

private def router : Router pureEngine :=
  { routes := [ .mount (.mk ["blog"]) [ .get [] fun _ => pure (Response.ok.body "blog") ] ] }

private def answer (target : String) : Option (Status × String × Option String) :=
  (RequestTarget.parse? target).map fun uri =>
    let response := (router.toHandler.onRequest { line := { method := .get, version := .v11, uri }, body := () } : Id _)
    (response.line.status, response.body, (response.line.headers.get? Header.Name.location).map toString)

#guard answer "/blog/" == some (.ok, "blog", none)
#guard answer "/blog?page=2" == some (.permanentRedirect, "", some "/blog/?page=2")
#guard answer "/nope" == some (.notFound, "Not Found", none)

end RoutingTests.Engine
