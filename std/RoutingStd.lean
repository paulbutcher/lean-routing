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

/-- Not `Builder.bytes`, which sets a content type of its own. -/
def Engine.stdBytes (builder : Response.Builder) (content : ByteArray) :
    ContextAsync (Response Body.Any) := do
  return builder.body (Body.Any.ofBody (← Body.Full.ofByteArray content))

/-- `Std.Http.Server`: handlers in `ContextAsync` over a `Body.Stream`, answering with a
`Body.Any`, exactly as `Std.Http.Server.StatelessHandler`'s are. -/
@[reducible] def Engine.std : Engine where
  M := ContextAsync
  Hook := Async
  ReqBody := Body.Stream
  RespBody := Body.Any
  text := Engine.textOf Engine.stdBytes

/-- `body`, or `tooLarge` once more than `maximum` bytes arrive. Not `Body.Stream.readAll`, which
says so only in an error's message, and which in `ContextAsync` takes a cancelled request's body as
ended, handing back however much had arrived. A read either ends the body or brings it a byte nearer
the limit, so `maximum + 2` reads reach one or the other. -/
def Engine.stdRead (body : Body.Stream) (maximum : Nat) : ContextAsync (BodyRead ByteArray) :=
  go (maximum + 2) .empty
where
  go : Nat → ByteArray → ContextAsync (BodyRead ByteArray)
    | 0, _ => throw (.userError "the request body yielded empty reads without ending")
    | fuel + 1, acc => do
      let next ← Selectable.one #[
        .case body.recvSelector pure,
        .case (← ContextAsync.doneSelector)
          (fun _ => throw (.userError "the request was cancelled while its body was being read"))]
      match next with
      | none => pure (.ok acc)
      | some chunk =>
        let acc := acc ++ chunk.data
        if acc.size > maximum then pure .tooLarge else go fuel acc

/-- A body sending what `write` sends. `Body.stream` would start `write` at once, but a response can
be built and then dropped, by a middleware answering `304` in its place say, and nothing then
closes its body: `write` would wait on its first chunk, and hold what it opened, for as long as the
process runs. So `write` waits for a reader, and does not run at all for a body closed unread. -/
def Engine.stdStream (builder : Response.Builder) (length? : Option Nat)
    (write : (ByteArray → ContextAsync Unit) → ContextAsync Unit) :
    ContextAsync (Response Body.Any) := do
  let context ← read
  let s ← Body.mkStream
  s.setKnownSize (some (length?.elim .chunked .fixed))
  -- In `Async`, as `Body.stream` runs its producer, rather than tied to the request, which may
  -- finish before its body is sent.
  (background (do
    try
      if ← Selectable.one #[.case s.interestSelector pure] then
        ReaderT.run (write fun chunk => s.send (Chunk.ofByteArray chunk)) context
      s.close
    catch err =>
      s.closeWithError err) : Async Unit)
  return builder.body (Body.Any.ofBody s)

instance : ServerEngine .std where
  readBody := Engine.stdRead
  -- A `Body.Stream` carries nothing but its bytes; the peer address is the request's extension.
  replaceBody _ bytes := Body.fromBytes bytes
  bytes := Engine.stdBytes
  stream := Engine.stdStream

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
