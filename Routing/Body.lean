/-
The host-neutral body layer. Request bodies are read through a capability; response bodies are
bytes or a producer. The native and stock adapters keep their own concrete body types.
-/
module

public import Routing.Server
public import Std.Http.Data.Body

public section

namespace Routing.Body

open Std Async

/-- One chunk read from a request body. -/
class RequestBody (m : Type → Type) (β : Type) where
  recv : β → Nat → m (Option ByteArray)

instance : RequestBody LeanIn.Runtime.VM LeanIn.Http.Server.BodyReader where
  recv body n := body.recv n

instance : RequestBody ContextAsync Std.Http.Body.Stream where
  recv body n := do
    let chunk ← (Std.Http.Body.recv body : Async (Option Std.Http.Chunk))
    pure (chunk.map (·.data))

/-- Read a request body, optionally bounded, through the host capability. -/
partial def readAll {m : Type → Type} [Monad m] [MonadExcept IO.Error m] {β : Type}
    [RequestBody m β] (body : β) (maximum? : Option Nat := none) : m ByteArray :=
  let rec loop (acc : ByteArray) : m ByteArray := do
    match ← RequestBody.recv (m := m) body 65536 with
    | none => pure acc
    | some chunk =>
      let acc := acc ++ chunk
      if let some maximum := maximum? then
        if acc.size > maximum then
          throw (.userError s!"routing: request body exceeds {maximum} bytes")
      loop acc
  loop .empty

/-- A response body: buffered bytes, or a producer handed a chunk sink. -/
inductive ResponseBody (m : Type → Type) where
  | bytes (data : ByteArray)
  | stream (length? : Option Nat) (write : (ByteArray → m Unit) → m Unit)

namespace ResponseBody

def toLeanIn (body : ResponseBody LeanIn.Runtime.VM) : LeanIn.Http.ResponseBody :=
  match body with
  | .bytes data => .bytes data
  | .stream length? write => .stream length? write

/-- The stock adapter buffers a producer: its public response type has no streaming constructor
this layer can hand a LeanIn writer to. -/
def toStock (body : ResponseBody ContextAsync) : ContextAsync Std.Http.Body.Any := do
  match body with
  | .bytes data =>
    let full ← (Std.Http.Body.Full.ofByteArray data : Async Std.Http.Body.Full)
    pure (Std.Http.Body.Any.ofBody full)
  | .stream _ write =>
    let buffer ← (monadLift (IO.mkRef (ByteArray.empty : ByteArray)) : ContextAsync (IO.Ref ByteArray))
    write fun chunk => monadLift (buffer.modify (fun acc => acc ++ chunk) : IO Unit)
    let data ← (monadLift (buffer.get : IO ByteArray) : ContextAsync ByteArray)
    let full ← (Std.Http.Body.Full.ofByteArray data : Async Std.Http.Body.Full)
    pure (Std.Http.Body.Any.ofBody full)

end ResponseBody

end Routing.Body
end
