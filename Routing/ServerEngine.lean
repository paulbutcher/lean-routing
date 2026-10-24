/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Routing.Engine

public section

@[expose] section

namespace Routing

open Std.Http

/-- What a handler or middleware needs of its engine beyond what the router does. A library generic
over the server takes `{e : Engine} [ServerEngine e]`; `routing-std` and `routing-leanin` provide
the instances.

This is a class over `Engine` rather than more of its fields so that an engine the router alone
runs on, a pure one for tests or proofs among them, need provide none of it. -/
class ServerEngine (e : Engine) where
  [liftIO : MonadLiftT IO e.M]
  [hookLiftIO : MonadLiftT IO e.Hook]
  /-- So that a middleware catching a failure can run `onFailure` itself. -/
  [liftHook : MonadLiftT e.Hook e.M]
  [monadExcept : MonadExcept IO.Error e.M]
  [monadFinally : MonadFinally e.M]
  /-- The whole body, failing once more than `maximum` bytes have arrived, so that a client cannot
  make a handler hold more of its body than the handler chose to. -/
  readBody : e.ReqBody → (maximum : Nat) → e.M ByteArray
  /-- A body reading as `bytes`, keeping whatever else `body` carries, such as LeanIn's peer
  address. For a middleware that reads the body and still has to hand one on. -/
  replaceBody : (body : e.ReqBody) → (bytes : ByteArray) → e.M e.ReqBody
  /-- A response with `bytes` as its body and whatever content type `builder` already has. -/
  bytes : Response.Builder → ByteArray → e.M (Response e.RespBody)

attribute [instance_reducible, instance] ServerEngine.liftIO ServerEngine.hookLiftIO
  ServerEngine.liftHook ServerEngine.monadExcept ServerEngine.monadFinally

namespace ServerEngine

variable {e : Engine} [ServerEngine e]

/-- `readBody`, decoded as UTF-8, failing on bytes that are not. -/
def readText (body : e.ReqBody) (maximum : Nat) : e.M String := do
  match String.fromUTF8? (← readBody body maximum) with
  | some text => pure text
  | none => throw (.userError "the request body is not UTF-8")

def html (builder : Response.Builder) (content : String) : e.M (Response e.RespBody) :=
  bytes (builder.header Header.Name.contentType (.mk "text/html; charset=utf-8")) content.toUTF8

/-- A response with no body, for a redirect, a `204` or a `304`. Both engines leave the framing
headers off the statuses that forbid a body. -/
def empty (builder : Response.Builder) : e.M (Response e.RespBody) :=
  bytes builder .empty

end ServerEngine

end Routing
