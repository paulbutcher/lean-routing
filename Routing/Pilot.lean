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

end Routing
end
