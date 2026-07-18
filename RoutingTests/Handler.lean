import Routing.Handler

namespace Routing

private def userPattern : List PathSeg := [.lit "users", .capture "id" .nat]

private def userHandler : HandlerType userPattern String :=
  fun (id : Nat) => s!"user #{id}"

#guard dispatch userPattern userHandler ["users", "42"] = some "user #42"
#guard dispatch userPattern userHandler ["users", "notanumber"] = none
#guard dispatch userPattern userHandler ["posts", "42"] = none          -- literal mismatch
#guard dispatch userPattern userHandler ["users"] = none                -- too few path segments
#guard dispatch userPattern userHandler ["users", "42", "extra"] = none -- too many path segments

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

#guard linkFor ([] : List PathSeg) = "/"
#guard linkFor [.lit "active"] = "/active"
#guard linkFor [.lit "todos", .capture "id" .nat] 42 = "/todos/42"
#guard linkFor [.lit "todos", .capture "id" .nat, .lit "edit"] 42 = "/todos/42/edit"
#guard linkFor [.lit "users", .capture "name" .string] "ada" = "/users/ada"

end Routing
