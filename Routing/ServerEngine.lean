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

/-- A body read up to a limit: its bytes, or that it ran past the limit. A failed read is not one of
these; it raises, so that a handler answering `413` for one cannot mistake the other for it. -/
inductive BodyRead (α : Type) where
  | ok (value : α)
  | tooLarge

/-- `BodyRead` for a body read as text, which can also turn out not to be UTF-8. -/
inductive TextRead where
  | text (value : String)
  | tooLarge
  | notUtf8

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
  /-- `MonadExceptOf` rather than `MonadExcept`, which follows from it but not the other way round,
  and which transformers such as `ReaderT` lift only from `MonadExceptOf`. -/
  [monadExceptOf : MonadExceptOf IO.Error e.M]
  [monadFinally : MonadFinally e.M]
  /-- The whole body, or `tooLarge` once more than `maximum` bytes have arrived, so that a client
  cannot make a handler hold more of its body than the handler chose to. -/
  readBody : e.ReqBody → (maximum : Nat) → e.M (BodyRead ByteArray)
  /-- A body reading as `bytes`, keeping whatever else `body` carries, such as LeanIn's peer
  address. For a middleware that reads the body and still has to hand one on. -/
  replaceBody : (body : e.ReqBody) → (bytes : ByteArray) → e.M e.ReqBody
  /-- A response with `bytes` as its body and whatever content type `builder` already has. -/
  bytes : Response.Builder → ByteArray → e.M (Response e.RespBody)
  /-- A response whose body is what `write` sends, chunk by chunk, with `length?` its size when known
  and whatever content type `builder` already has. `write` runs only once the body is being sent,
  and not at all for a response that is never sent, so it should open whatever it reads from itself
  and close it in a `finally`. -/
  stream : Response.Builder → (length? : Option Nat) →
    (write : (ByteArray → e.M Unit) → e.M Unit) → e.M (Response e.RespBody)

attribute [instance_reducible, instance] ServerEngine.liftIO ServerEngine.hookLiftIO
  ServerEngine.liftHook ServerEngine.monadExceptOf ServerEngine.monadFinally

namespace ServerEngine

variable {e : Engine} [ServerEngine e]

/-- `readBody`, decoded as UTF-8. -/
def readText (body : e.ReqBody) (maximum : Nat) : e.M TextRead := do
  return match ← readBody body maximum with
    | .tooLarge => .tooLarge
    | .ok bytes => (String.fromUTF8? bytes).elim .notUtf8 .text

def html (builder : Response.Builder) (content : String) : e.M (Response e.RespBody) :=
  bytes (builder.header Header.Name.contentType (.mk "text/html; charset=utf-8")) content.toUTF8

/-- A response with no body, for a redirect, a `204` or a `304`. Both engines leave the framing
headers off the statuses that forbid a body. -/
def empty (builder : Response.Builder) : e.M (Response e.RespBody) :=
  bytes builder .empty

end ServerEngine

end Routing
