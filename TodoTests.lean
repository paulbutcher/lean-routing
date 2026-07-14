import TodoTests.Db
import TodoTests.Views

/-!
# `TodoTests`: tests for the `Todo` library

Build-time tests (`#eval`/`#guard`) for `Todo.Db` (`TodoTests/Db.lean`) and `Todo.Views`
(`TodoTests/Views.lean`). Not a default target -- run via `lake test`, which for a library target
simply builds it (see the package's `testDriver` in `lakefile.toml`), triggering every `#eval`
and `#guard` below as a build-breaking error on failure.
-/
