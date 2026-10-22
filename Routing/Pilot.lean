/-
A shared middleware pilot. The same definition runs over any host monad and request body; it reads
the matched-route extension `toHandlerM` publishes and exposes the template as a response header.
-/
module

public import Routing.Server

public section

namespace Routing

/-- Publish the matched route template as `x-route`, or leave the response unchanged on a miss. -/
def withRouteHeader {m : Type → Type} [Monad m] {ReqBody : Type}
    (next : StatelessHandlerM m ReqBody) : StatelessHandlerM m ReqBody :=
  { next with
    onRequest := fun request => do
      let response ← next.onRequest request
      match matchedPattern? response.extensions with
      | some pattern => pure { response with headers := response.headers.push ("x-route", pattern) }
      | none => pure response }

/-- A host-neutral session counter. The middleware lifts its `IO.Ref` operations into either host. -/
structure SessionStore where
  next : IO.Ref Nat

def SessionStore.new : IO SessionStore :=
  return { next := ← IO.mkRef 0 }

private def cookieSession (headers : Std.Http.Headers) : Option String :=
  match headers.get? (Std.Http.Header.Name.ofString! "cookie") with
  | none => none
  | some value =>
    (value.value.splitOn ";" |>.findSome? fun part =>
      let part := part.trimAscii.toString
      if part.startsWith "session=" then some (part.drop 8 |>.toString) else none)

/-- Read `session=` from the request cookie, or allocate one from `store`, and set it on the response. -/
def withSession {m : Type → Type} [Monad m] [MonadLift IO m] {ReqBody : Type}
    (store : SessionStore) (next : StatelessHandlerM m ReqBody) : StatelessHandlerM m ReqBody :=
  { next with
    onRequest := fun request => do
      let id ← match cookieSession request.line.headers with
        | some id => pure id
        | none => do
          let n ← monadLift (store.next.modifyGet fun n => (n, n + 1) : IO Nat)
          pure s!"s{n}"
      let response ← next.onRequest request
      pure { response with headers := response.headers.push ("set-cookie", s!"session={id}") } }

end Routing
end
