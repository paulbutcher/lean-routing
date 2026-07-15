import Routing.Handler
import Routing.Pattern

/-!
Route pattern strings and their reverse-routing `Links`, both derived from the same
`Routing.parsePattern!`/`Routing.linkFor` pair the routing library already provides.
`Main.lean`'s route table and `Todo.links` below both read off the pattern constants here, so a
path only ever appears in source once, rather than as separately hand-maintained pattern strings
(for dispatch) and literal path strings (in `Todo/Views.lean`'s `hx-*` attributes).
-/

namespace Todo

open Routing

def indexPattern := "/"
def activePattern := "/active"
def completedPattern := "/completed"
def todosPattern := "/todos"
def todoPattern := "/todos/:id:Nat"
def editPattern := "/todos/:id:Nat/edit"
def togglePattern := "/todos/:id:Nat/toggle"
def toggleAllPattern := "/todos/toggle-all"
def clearCompletedPattern := "/todos/completed"

/-- One reverse-routing field per named route above; `todo`/`edit`/`toggle` take the todo's `id`
since their patterns capture `:id:Nat`. -/
structure Links where
  index : String
  active : String
  completed : String
  todos : String
  todo : Nat → String
  edit : Nat → String
  toggle : Nat → String
  toggleAll : String
  clearCompleted : String

def links : Links :=
  { index := linkFor (parsePattern! indexPattern)
    active := linkFor (parsePattern! activePattern)
    completed := linkFor (parsePattern! completedPattern)
    todos := linkFor (parsePattern! todosPattern)
    todo := linkFor (parsePattern! todoPattern)
    edit := linkFor (parsePattern! editPattern)
    toggle := linkFor (parsePattern! togglePattern)
    toggleAll := linkFor (parsePattern! toggleAllPattern)
    clearCompleted := linkFor (parsePattern! clearCompletedPattern) }

#guard links.index = "/"
#guard links.active = "/active"
#guard links.completed = "/completed"
#guard links.todos = "/todos"
#guard links.todo 7 = "/todos/7"
#guard links.edit 7 = "/todos/7/edit"
#guard links.toggle 7 = "/todos/7/toggle"
#guard links.toggleAll = "/todos/toggle-all"
#guard links.clearCompleted = "/todos/completed"

end Todo
