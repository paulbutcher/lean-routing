import Todo.Db
import Todo.Links
import Todo.Views
import Todo.App

/-!
# `Todo`: a server-rendered TodoMVC demo

Persists todos in SQLite (`leansqlite`, `Todo/Db.lean`) and renders every page/fragment through
the existing `Html`/`Htmx` libraries (`Todo/Views.lean`). Routes live in `Todo/App.lean`, alongside
the `Routing.Result` change (`Routing/Server.lean`) that threads the full request into every
handler -- see `docs/todo-app-plan.md` for the design rationale.
-/
