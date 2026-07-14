import Routing

/-!
`Todo.Urls`: the todo app's reverse-routing struct, generated from patterns written *once* here --
never restated in `Main.lean`, which only wires handlers to these already-declared names
(`application app : SQLite using Todo.Urls where ...`, `Main.lean`) via `urlTree`/`application`'s
upstream/downstream split (`Routing/Application.lean`, `docs/application-macro-plan.md`'s Phase 3
notes). `Todo` (this file included) sits upstream of `Main` in the import graph, so it can't
reference the concrete struct `application` alone would generate downstream -- `urlTree` is what
lets the struct exist here instead, with `Main.lean` only contributing dispatch (which method,
which handler), never pattern text.
-/

namespace Todo

urlTree Urls where
  "/" as index { }
  "/active" as active { }
  "/completed" as completed { }
  "/todos" as todos {
    "/:id:Nat" as todo {
      "/edit" as todoEdit { }
      "/toggle" as todoToggle { }
    }
    "/toggle-all" as toggleAll { }
    "/completed" as clearCompleted { }
  }

end Todo
