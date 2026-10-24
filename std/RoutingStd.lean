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

/-- Where a streamed body is: not yet read, with the size it will declare; closed before anything
read it; or reading from the stream its producer sends into. -/
inductive Engine.StreamState where
  | waiting (size : Option Body.Length)
  | closed
  | started (body : Body.Any)

/-- A body sending what `write` sends. `Body.stream` would start `write` at once, but a response can
be built and then dropped, by a middleware answering `304` in its place say, and nothing then
closes its body: `write` would wait on its first chunk, and hold what it opened, for as long as the
process runs.

So nothing is started until something reads. Until then the body is these closures and the
`waiting` state: no stream, no task and nothing registered anywhere, so a dropped body is freed as
any other value is. The first `recv`, `tryRecv` or use of `recvSelector` makes the stream and
starts `write` sending into it, once, under the mutex. Asking the size and closing start nothing,
which is what `Std.Http.Server` does with a `HEAD` response's body. -/
def Engine.stdStream (builder : Response.Builder) (length? : Option Nat)
    (write : (ByteArray → ContextAsync Unit) → ContextAsync Unit) :
    ContextAsync (Response Body.Any) := do
  let context ← read
  let state ← Std.Mutex.new (StreamState.waiting (some (length?.elim .chunked .fixed)))
  -- The stream to read from, made and its producer started on the first call; `none` once closed.
  let started : Async (Option Body.Any) := do
    let (body?, fresh?) ← state.atomically do
      match ← get with
      | .started body => return (some body, none)
      | .closed => return (none, none)
      | .waiting size =>
        let s ← Body.mkStream
        s.setKnownSize size
        let body := Body.Any.ofBody s
        set (StreamState.started body)
        return (some body, some s)
    if let some s := fresh? then
      -- In `Async`, as `Body.stream` runs its producer, rather than tied to the request, which may
      -- finish before its body is sent.
      background do
        try
          ReaderT.run (write fun chunk => s.send (Chunk.ofByteArray chunk)) context
          s.close
        catch err =>
          s.closeWithError err
    return body?
  let current : Async StreamState := state.atomically get
  let body : Body.Any :=
    { recv := do (← started).elim (pure none) (·.recv)
      tryRecv := do (← started).elim (pure (some none)) (·.tryRecv)
      recvSelector :=
        { tryFn := do (← started).elim (pure (some none)) (·.recvSelector.tryFn)
          registerFn := fun waiter => do
            match ← started with
            | some body => body.recvSelector.registerFn waiter
            | none => waiter.race (pure ()) fun promise => promise.resolve (.ok none)
          unregisterFn := do
            if let .started body ← current then body.recvSelector.unregisterFn }
      close := do
        let body? ← state.atomically do
          match ← get with
          | .started body => return some body
          | _ => set StreamState.closed; return none
        if let some body := body? then body.close
      isClosed := do
        match ← current with
        | .waiting _ => return false
        | .closed => return true
        | .started body => body.isClosed
      getKnownSize := do
        match ← current with
        | .waiting size => return size
        | .closed => return some (.fixed 0)
        | .started body => body.getKnownSize
      setKnownSize := fun size => do
        let body? ← state.atomically do
          match ← get with
          | .waiting _ => set (StreamState.waiting size); return none
          | .closed => return none
          | .started body => return some body
        if let some body := body? then body.setKnownSize size }
  return builder.body body

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
