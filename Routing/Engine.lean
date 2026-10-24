/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Http.Data.Request
public import Std.Http.Data.Response

public section

@[expose] section

namespace Routing

open Std.Http

/-- What the router needs of the server it runs on. Requests and responses are `Std.Http`'s on
every engine; only the monads and the body types differ.

`Hook` is separate from `M` because `Std.Http.Server` runs `onRequest` in `ContextAsync` but its
hooks in `Async`, and a single monad would change one of them. `text` builds the two responses the
router answers itself, the `404` and the slash redirect, which no engine-neutral body type could. -/
structure Engine where
  M : Type → Type
  Hook : Type → Type
  ReqBody : Type
  RespBody : Type
  [monad : Monad M]
  [hookMonad : Monad Hook]
  text : Response.Builder → String → M (Response RespBody)

attribute [instance] Engine.monad Engine.hookMonad

/-- `text` from a function building a response from bytes, setting a plain-text content type, so
that engines whose `text` is this answer alike. -/
def Engine.textOf {M : Type → Type} {RespBody : Type}
    (bytes : Response.Builder → ByteArray → M (Response RespBody))
    (builder : Response.Builder) (content : String) : M (Response RespBody) :=
  bytes (builder.header Header.Name.contentType (.mk "text/plain; charset=utf-8")) content.toUTF8

/-- A route's handler once its captures are applied. -/
abbrev Result (e : Engine) := Request e.ReqBody → e.M (Response e.RespBody)

/-- A handler with `Std.Http.Server.StatelessHandler`'s three fields, on any engine. Middleware is
a function from one of these to another. -/
structure StatelessHandler (e : Engine) where
  onRequest : Result e
  /-- Told of a failure; the failure still takes its course. -/
  onFailure : IO.Error → e.Hook Unit := fun _ => pure ()
  /-- Whether to accept a request's body when it carries `Expect: 100-continue`. -/
  onContinue : Request.Head → e.Hook Bool := fun _ => pure true

def StatelessHandler.ofFn {e : Engine} (f : Result e) : StatelessHandler e :=
  { onRequest := f }

end Routing
