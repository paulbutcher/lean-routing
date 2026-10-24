/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Routing
public import Std.Http.Server

public section

@[expose] section

namespace Routing

open Std Async
open Std.Http

/-- `Std.Http.Server`: handlers in `ContextAsync` over a `Body.Stream`, answering with a
`Body.Any`, exactly as `Std.Http.Server.StatelessHandler`'s are. -/
@[reducible] def Engine.std : Engine where
  M := ContextAsync
  Hook := Async
  ReqBody := Body.Stream
  RespBody := Body.Any
  text builder content := builder.text content

def StatelessHandler.toStd (h : StatelessHandler .std) : Server.StatelessHandler :=
  { onRequest := h.onRequest, onFailure := h.onFailure, onContinue := h.onContinue }

/-- A handler, or middleware, written against `Std.Http.Server` directly. -/
def StatelessHandler.ofStd (h : Server.StatelessHandler) : StatelessHandler .std :=
  { onRequest := h.onRequest, onFailure := h.onFailure, onContinue := h.onContinue }

/-- So that `Std.Http.Server.serve` takes a router's handler as it is. -/
instance : Server.Handler (StatelessHandler .std) where
  onRequest h := h.onRequest
  onFailure h := h.onFailure
  onContinue h := h.onContinue

end Routing
