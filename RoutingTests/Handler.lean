import Routing.Handler

namespace Routing

private def userPattern : List PathSeg := parsePattern! "/users/:id:Nat"

private def userHandler : HandlerType userPattern String :=
  fun (id : Nat) => s!"user #{id}"

-- #guard tests: dispatch success, mistyped capture, literal mismatch, arity mismatch.
#guard dispatch userPattern userHandler ["users", "42"] = some "user #42"
#guard dispatch userPattern userHandler ["users", "notanumber"] = none
#guard dispatch userPattern userHandler ["posts", "42"] = none          -- literal mismatch
#guard dispatch userPattern userHandler ["users"] = none                -- too few path segments
#guard dispatch userPattern userHandler ["users", "42", "extra"] = none -- too many path segments

-- Negative-compile regression (§2): a wrong-arity handler against a real
-- pattern is rejected at compile time, pointing at the actual value
-- mismatch -- this is the whole payoff of computing the handler's type
-- from pattern data instead of hand-writing/documenting the arity.
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

-- #guard tests: no captures, one capture, a capture followed by more literal segments, and a
-- `String` (not just `Nat`) capture.
#guard linkFor ([] : List PathSeg) = "/"
#guard linkFor [.lit "active"] = "/active"
#guard linkFor (parsePattern! "/todos/:id:Nat") 42 = "/todos/42"
#guard linkFor (parsePattern! "/todos/:id:Nat/edit") 42 = "/todos/42/edit"
#guard linkFor (parsePattern! "/users/:name:String") "ada" = "/users/ada"

end Routing
