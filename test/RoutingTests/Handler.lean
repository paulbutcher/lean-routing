/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Routing.Handler
import Routing.RelativeLink

namespace Routing

private def userPattern : List PathSeg := [.lit "users", .capture "id" .nat]

private def userHandler : HandlerType userPattern String :=
  fun (id : Nat) => s!"user #{id}"

#guard dispatch userPattern userHandler ["users", "42"] = some "user #42"
#guard dispatch userPattern userHandler ["users", "notanumber"] = none
#guard dispatch userPattern userHandler ["posts", "42"] = none          -- literal mismatch
#guard dispatch userPattern userHandler ["users"] = none                -- too few path segments
#guard dispatch userPattern userHandler ["users", "42", "extra"] = none -- too many path segments
#guard dispatch userPattern userHandler ["users", "42", ""] = some "user #42" -- trailing slash

-- Negative-compile regression: a wrong-arity handler against a real
-- pattern is rejected at compile time.
/--
error: Type mismatch
  fun _id _extra => "oops"
has type
  Nat → String → String
but is expected to have type
  HandlerType userPattern String
-/
#guard_msgs in
def badArity : HandlerType userPattern String :=
  fun (_id : Nat) (_extra : String) => "oops"

-- These examples stand in for the theorem one really wants: that dispatching the path `linkFor`
-- renders recovers the very captures it was given. Both halves of that round trip bottom out in
-- string functions with no equational theory to work from: `pathSegments` is `String.splitOn`,
-- whose implementation walks byte positions with a hand-written termination argument, and a `.nat`
-- capture needs `String.toNat?` to invert `toString`. Neither round trip has lemmas in core, so
-- proving this means building both theories first. `Routing/Pattern.lean` sidesteps exactly this
-- by parsing over `List Char` structurally, which is why its round trip *is* proved
-- (`parsePattern_renderPattern`, `Pattern.lean`).
#guard linkFor ([] : List PathSeg) = "/"
#guard linkFor [.lit "active"] = "/active"
#guard linkFor [.lit "todos", .capture "id" .nat] 42 = "/todos/42"
#guard linkFor [.lit "todos", .capture "id" .nat, .lit "edit"] 42 = "/todos/42/edit"
#guard linkFor [.lit "users", .capture "name" .string] "ada" = "/users/ada"

#guard dispatch userPattern userHandler (pathSegments (linkFor userPattern 42)) = some "user #42"

end Routing
