# Server-rendered TodoMVC demo (HTMX + leansqlite)

## Context

The repo already has three hand-built, from-scratch libraries: a typed HTML
library (`Html`), a typed htmx-attribute layer on top of it (`Htmx`), and a
typed path router (`Routing`), wired together in `Main.lean` as a tiny demo
server on `Std.Http.Server` (which ships as part of this `v4.31.0` toolchain
itself — there's no external HTTP package dependency today).

The goal is a classic TodoMVC (add / toggle / edit-in-place / delete /
toggle-all / clear-completed / All-Active-Completed filters with a live
count) as a *fully server-rendered* demo: every interaction is a plain HTMX
request that returns an HTML fragment, no client-side state, persisted in
SQLite via `leansqlite` (https://reservoir.lean-lang.org/@leanprover/leansqlite,
source at github.com/leanprover/leansqlite) instead of TodoMVC's usual
localStorage. This exercises all three existing libraries together plus one
new dependency, and is meant to read as "the payoff demo" for the stack
that's been built up so far.

leansqlite's actual source (`SQLite.lean`, `LowLevel.lean`,
`QueryParam.lean`, `QueryResult.lean`, `Interpolation.lean`, its
`lakefile.lean`, and its test suite) was fetched and confirmed directly, and
`lean_run_code`/`#check`/`#print` against this project's live toolchain
confirmed the exact `Std.Http` shapes referenced below
(`Body.Stream.readAll`, `Response.Builder`, `Request.Head`, IO-lifting into
`ContextAsync`, etc.) — these aren't guesses.

## The one real design problem: handlers can't currently see the request

`Routing/Server.lean`'s `toHandler` calls `dispatchTable routes
request.line.method path` — it only ever passes the **method and decoded
path segments** into dispatch. No route handler, today, ever receives the
`Request` itself. That's fine for the existing demo (`/`, `/ping`,
`/hello/:name:String` are all pure functions of their path captures), but a
todo app needs to read a POST body (the new todo's title, an edited title)
and, as described below, one request header — and there is currently no
mechanism to get either into a handler.

**Fix, additive and proof-preserving:** `HandlerType segs result` in
`Routing/Handler.lean` is already generic in `result` — it's a purely
structural fold (`[] ↦ result`, `.capture _ kind :: rest ↦ kind.type →
HandlerType rest result`) with no proofs that depend on what `result`
*is*. So instead of touching `Handler.lean`/`Route.lean` (and their existing
`#guard`/`#guard_msgs` regressions and the round-trip proof in
`Pattern.lean`) at all, redefine `Routing/Server.lean`'s
`Result` from
```
abbrev Result := ContextAsync (Response Body.Any)
```
to
```
abbrev Result := Request Body.Stream → ContextAsync (Response Body.Any)
```
Every handler — captures or not — becomes a function that takes its typed
path captures (unchanged) followed by the whole incoming `Request
Body.Stream` as a trailing argument. `toHandler` changes its one call site
from `some result => result` to `some handler => handler request`. That's
the entire change to the routing library: no edits to `Handler.lean` or
`Route.lean`, and the existing three routes in `Main.lean` need one
mechanical update each (accept and, where unused, ignore the request).
This was confirmed to typecheck against the live toolchain (`HandlerType`
substituting a function type for `result` composes exactly as expected, and
`IO` lifts into `ContextAsync` via plain `do`-notation, confirmed with
`lean_run_code`).

This also lets me solve **which filter (All/Active/Completed) a mutating
response should render** without needing query-string dispatch support
(explicitly out of scope per `Routing.lean`'s own "not yet supported" list,
and I'm not adding it): htmx automatically sends an `HX-Current-URL` request
header with the current page URL on every htmx-triggered request. A mutation
handler reads `request.line.headers.get? "HX-Current-URL"` (confirmed to
exist: `Headers.get? : Headers → Header.Name → Option Header.Value`), pulls
the path off it, and maps `/active`/`/completed`/anything else to the
matching filter — no client-side JS, no hidden form fields, no session
state.

## Data model & leansqlite integration

Add the dependency (pin to the toolchain-matching tag — leansqlite tags
`v4.31.0` exactly, confirmed against its GitHub tag list, so no toolchain
skew):
```toml
[[require]]
name = "leansqlite"
git = "https://github.com/leanprover/leansqlite"
rev = "v4.31.0"
```
Its lib target is `SQLite` (imported as `import SQLite`).

One connection, opened once in `main` (`SQLite.open "todo.db"`, or
`:memory:` for a from-scratch-every-run demo — leaning towards a real file so
restarting the server doesn't lose data, matching TodoMVC's persistence
spirit) and closed over by the route table, the same way `Main.lean` already
builds `routes` as a plain `List (Route Result)` value. Schema created with
`db.exec` at startup:
```sql
CREATE TABLE IF NOT EXISTS todos (
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  title TEXT NOT NULL,
  completed INTEGER NOT NULL DEFAULT 0
);
```
Row type, using leansqlite's deriving handler exactly like its own test
suite does (`tests/SQLiteTest/Deriving.lean`):
```lean
structure Todo where
  id : Int64
  title : String
  completed : Bool
deriving Repr, SQLite.Row
```
CRUD as thin wrappers using the `sql!`/`exec!`/`query!` interpolation macros
(`SQLite/Interpolation.lean`) — e.g.
`db query!"SELECT id, title, completed FROM todos ORDER BY id" as Todo`,
`db exec!"INSERT INTO todos (title) VALUES ({title})"`,
`db exec!"UPDATE todos SET completed = NOT completed WHERE id = {(id : Int64)}"` —
`toggle-all` and `clear-completed` wrapped in `db.transaction` since they're
multi-row writes that should be atomic.

## Parsing the POST body

htmx form submissions arrive as `application/x-www-form-urlencoded` bodies
(`title=Buy+milk`). Read the raw bytes via
`request.body.readAll (α := String)` (confirmed: `Body.Stream.readAll`
exists and `Body.FromByteArray String` has an instance), then decode with a
small hand-rolled parser (split on `&`, split each pair on the first `=`,
percent-decode `%XX` and `+`→space) rather than reaching for
`Std.Http.URI`'s query-string types — the `URI.EncodedQueryString`
constructor is `private` with a validity proof obligation, built for parsing
*URIs*, not for reinterpreting an arbitrary body string, so bending it to
this purpose would fight the API rather than use it. A small `List
Char`-recursive decoder with `#guard` tests matches this codebase's own
established pattern for exactly this situation (`Routing/Pattern.lean`'s
module doc explains why it hand-rolled its parser instead of fighting
`String.splitOn`/stdlib types on this toolchain).

New file `Routing/FormBody.lean` (small, generically useful beyond just this
app — natural home is alongside the router that now exposes bodies to
handlers, mirroring where `Pattern.lean` lives):
```lean
def parseFormBody (body : String) : List (String × String)
```
with `#guard` tests for the empty body, a single pair, multiple pairs,
`+`-as-space, and `%XX` decoding.

## Routes

All literal-vs-capture path segments are unambiguous by construction
(`dispatch`'s `.nat` case only matches segments that parse via `Nat.toNat?`,
so e.g. `/todos/completed` (DELETE) and `/todos/:id:Nat` (DELETE) never
collide regardless of table order — same reasoning already used for the
existing route table).

| Method | Path                  | Behaviour |
|--------|-----------------------|-----------|
| GET    | `/`                   | full page, filter = All |
| GET    | `/active`             | full page, filter = Active |
| GET    | `/completed`          | full page, filter = Completed |
| POST   | `/todos`              | create (ignored if title is empty after trim) |
| GET    | `/todos/:id:Nat/edit` | swap that `<li>` into edit mode (`hx-trigger="dblclick"` on the label) |
| PUT    | `/todos/:id:Nat`      | save edited title; empty title **deletes** the todo (standard TodoMVC rule) |
| POST   | `/todos/:id:Nat/toggle` | toggle one todo's completed state |
| DELETE | `/todos/:id:Nat`      | delete one todo |
| POST   | `/todos/toggle-all`   | if any active, complete all; else un-complete all |
| DELETE | `/todos/completed`    | delete all completed todos |

Every mutating handler (all rows except the `.../edit` GET) shares one
render helper that re-queries the filtered list and renders
`<ul id="todo-list">…</ul>` immediately followed by an out-of-band
`<footer id="todo-footer" hx-swap-oob="true">…</footer>` (item count,
pluralized; Clear-completed button only shown when there are completed
items; filter links) in the same response body. This uses
`HtmxAttrs.hxSwapOob`, which already exists in `Htmx/Attrs.lean` — no library
change needed there. Clients target `hx-target="#todo-list"
hx-swap="outerHTML"` for their primary swap and get the footer update "for
free" via the OOB swap, so every mutation only needs one shared renderer.

## New files

- `Todo/Db.lean` — schema init + the CRUD functions described above.
- `Todo/Views.lean` — `Html`/`Htmx`-built fragments: full page shell, the
  `<ul>` list (view-mode and edit-mode `<li>` rendering), the OOB footer
  fragment, and the three filter links. Built entirely from existing
  `Html.*`/`Htmx.*` tag functions (`Htmx/Tags.lean`) — no new HTML/HTMX
  library primitives are needed; `HtmxAttrs` already covers every attribute
  this app uses (`hxGet`/`hxPost`/`hxPut`/`hxDelete`/`hxTarget`/`hxSwap`/
  `hxSwapOob`/`hxTrigger`).
- `Routing/FormBody.lean` — the form-body decoder described above.
- `Todo.lean` — umbrella import + short module doc, matching
  `Html.lean`/`Htmx.lean`/`Routing.lean`'s existing convention.
- `lakefile.toml` — add the `leansqlite` `[[require]]`, and a `[[lean_lib]]`
  entry for `Todo` (alongside the existing `Html`/`Htmx`/`Routing` entries),
  added to `defaultTargets`.
- `Routing/Server.lean` — the `Result`/`toHandler` change above (only
  existing file that changes).
- `Main.lean` — open the DB, run schema init, update the 3 existing routes'
  handler signatures (trailing `Request Body.Stream` arg, unused), add the
  10 todo routes, append them to the route table passed to `toHandler`.

## Verification

- After each `.lean` edit: `mcp__lean-lsp__lean_diagnostic_messages` (per
  `CLAUDE.md`); use `mcp__lean-lsp__lean_build` after the `lakefile.toml`
  dependency/import changes specifically, since those add new imports.
- `lake build` from repo root as final ground truth (per `CLAUDE.md`).
- `#guard` tests for `parseFormBody` (edge cases above) and smoke-test
  `#guard`s for the new view-rendering functions, matching the existing
  per-function `#guard` convention in `Html/Tags.lean`/`Htmx/Tags.lean`.
- Manually exercise the running server (`lake exe webapp`, then drive it
  with `curl`/a browser) through the full golden path: load `/`, add two
  todos, toggle one, edit a title, delete one, toggle-all, clear-completed,
  and check each of the three filter views and the item count — since this
  is a UI-facing change, `lake build` passing is necessary but not
  sufficient to call it done.
