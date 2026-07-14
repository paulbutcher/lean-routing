import Routing.Application

/-!
Regression for `urlTree` + `application ... using ...` (`Routing/Application.lean`), split across
*this* file and that one -- deliberately, not incidentally: `urlTreeExt` (the persistent
environment extension backing the split) can't be used in the same module it's `initialize`d in
(confirmed directly: "cannot evaluate `[init]` declaration ... in the same module"), so exercising
it at all requires a second, importing file -- which also happens to be exactly the real
Todo/Main split's shape (`Todo/Urls.lean` upstream, `Main.lean` downstream, `Routing/Application.lean`
holding the extension both import).
-/

namespace Routing

open Std.Http.Internal.Test
open Std.Async
open Std Http Server

private def rootHandler {Urls : Type} (_ctx : Nat) (_urls : Urls) (_req : Request Body.Stream) :
    ContextAsync (Response Body.Any) :=
  Response.ok |>.text "root"

private def itemGetHandler {Urls : Type} (_ctx : Nat) (_urls : Urls) (id : Nat)
    (_req : Request Body.Stream) : ContextAsync (Response Body.Any) :=
  Response.ok |>.text s!"get-item-{id}"

private def itemPutHandler {Urls : Type} (_ctx : Nat) (_urls : Urls) (id : Nat)
    (_req : Request Body.Stream) : ContextAsync (Response Body.Any) :=
  Response.ok |>.text s!"put-item-{id}"

private def specialHandler {Urls : Type} (_ctx : Nat) (_urls : Urls)
    (_req : Request Body.Stream) : ContextAsync (Response Body.Any) :=
  Response.ok |>.text "special"

private def badArityHandler {Urls : Type} (_ctx : Nat) (_urls : Urls) (_id : Nat) (_extra : String)
    (_req : Request Body.Stream) : ContextAsync (Response Body.Any) :=
  Response.ok |>.text "oops"

private def mkPut (path : String) : String :=
  s!"PUT {path} HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 0\x0d\n\x0d\n"

-- The upstream/downstream split, mirroring `Todo.Urls`/`Main.lean`: patterns and names are written
-- *only* in the `urlTree` block; the `using` block below contributes nothing but method/handler
-- wiring, referencing names it never redeclares.
namespace UrlTreeUpstream

urlTree SplitUrls where
  "/" as root { }
  "/items" {
    "/:id:Nat" as item { }
    "/special" as special { }
  }

end UrlTreeUpstream

namespace UrlTreeDownstream

application splitApp : Nat using UrlTreeUpstream.SplitUrls where
  root { get => rootHandler }
  item {
    get => itemGetHandler
    put => itemPutHandler
  }
  special { get => specialHandler }

#guard splitApp.urls.root = "/"
#guard splitApp.urls.item 7 = "/items/7"
#guard splitApp.urls.special = "/items/special"

private def splitHandler : TestHandler := (splitApp.handler 0).onRequest

#eval runGroup "UrlTreeDownstream" do
  checkClose "root" (mkGet "/") splitHandler (assertContains · "root")
  checkClose "item get" (mkGet "/items/7") splitHandler (assertContains · "get-item-7")
  checkClose "item put" (mkPut "/items/7") splitHandler (assertContains · "put-item-7")
  checkClose "special" (mkGet "/items/special") splitHandler (assertContains · "special")

end UrlTreeDownstream

-- A name the `using` tree references but the `urlTree` block never declared is a macro-time error
-- pointing at the offending identifier, not a redeclaration or a silently-empty pattern.
namespace UrlTreeUnknownNameTest

/--
error: application: 'nope' is not a name declared in Routing.UrlTreeUpstream.SplitUrls's urlTree block
-/
#guard_msgs in
application unknownNameApp : Nat using UrlTreeUpstream.SplitUrls where
  root { get => rootHandler }
  nope { get => rootHandler }

end UrlTreeUnknownNameTest

-- A wrong-arity handler in a `using` tree is rejected with the same quality of error as the
-- self-contained mode's `BadArityTest` (`Routing/Application.lean`).
namespace UrlTreeBadArityTest

/--
error: Application type mismatch: The argument
  badArityHandler ctx UrlTreeUpstream.splitUrls
has type
  Nat → String → Request Body.Stream → ContextAsync (Response Body.Any)
but is expected to have type
  HandlerType (parsePattern! "/items/:id:Nat") Result
in the application
  Route.put "/items/:id:Nat" (badArityHandler ctx UrlTreeUpstream.splitUrls)
-/
#guard_msgs in
application usingBadArityApp : Nat using UrlTreeUpstream.SplitUrls where
  item { put => badArityHandler }

end UrlTreeBadArityTest

end Routing
