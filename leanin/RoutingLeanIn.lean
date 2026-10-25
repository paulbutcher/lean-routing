/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Routing
public import LeanIn.Http.StdHandler

public section

@[expose] section

namespace Routing

open Std.Http
open LeanIn.Http

def Engine.leaninBytes (builder : Response.Builder) (content : ByteArray) :
    LeanIn.Runtime.VM (Response LeanIn.Http.ResponseBody) :=
  pure (builder.body (.bytes content))

/-- LeanIn: handlers and hooks in its `VM`, over its streaming `BodyReader`, answering with its
`ResponseBody`, buffered or streamed. -/
@[reducible] def Engine.leanin : Engine where
  M := LeanIn.Runtime.VM
  Hook := LeanIn.Runtime.VM
  ReqBody := Server.BodyReader
  RespBody := LeanIn.Http.ResponseBody
  text := Engine.textOf Engine.leaninBytes

/-- `body`, or `tooLarge` once more than `maximum` bytes arrive. A read either ends the body or
brings it a byte nearer the limit, so `maximum + 2` reads reach one or the other; running out means
a reader that keeps answering with nothing. -/
def Engine.leaninRead (body : Server.BodyReader) (maximum : Nat) :
    LeanIn.Runtime.VM (BodyRead ByteArray) :=
  go (maximum + 2) .empty
where
  go : Nat → ByteArray → LeanIn.Runtime.VM (BodyRead ByteArray)
    | 0, _ => throw (.userError "the request body yielded empty reads without ending")
    | fuel + 1, acc => do
      match ← body.recv 65536 with
      | none => pure (.ok acc)
      | some chunk =>
        let acc := acc ++ chunk
        if acc.size > maximum then pure .tooLarge else go fuel acc

/-- A reader handing out `bytes` in pieces no larger than each `recv` asks for. The rest is
`body`'s own: the peer address, and the bytes after the body that the driver resumes from. -/
def Engine.leaninReplace (body : Server.BodyReader) (bytes : ByteArray) :
    LeanIn.Runtime.VM Server.BodyReader := do
  let rest ← (IO.mkRef bytes : IO _)
  return { body with
    recv := fun n => (rest.modifyGet fun r =>
        if r.isEmpty then (none, r)
        else
          let k := min (max n 1) r.size
          (some (r.extract 0 k), r.extract k r.size) : IO _)
    drained := ((·.isEmpty) <$> rest.get : IO _) }

instance : ServerEngine .leanin where
  readBody := Engine.leaninRead
  replaceBody := Engine.leaninReplace
  bytes := Engine.leaninBytes
  stream builder length? write := pure (builder.body (.stream length? write))

/-- What `Server.serveConnStd` serves. Its `Config.continuePolicy` must be `.application`, so that
`onContinue` makes the decision. -/
def StatelessHandler.toLeanIn (h : StatelessHandler .leanin) : StdHandler :=
  { onRequest := h.onRequest, onFailure := h.onFailure, onContinue := h.onContinue }

end Routing
