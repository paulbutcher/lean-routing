# Task list: `Urls` bundle + `routes!` macro (Option C)

Execution checklist for `docs/reverse-routing-macro-plan.md` §2-8 (Option C: nested `routes!`
grammar + the `Todo.Urls` bundle it requires). **Read that doc in full before starting** -- this
file is the ordered execution checklist, not a restatement of the design rationale. Don't re-derive
decisions it already made; if something here seems to contradict it, the plan doc wins and this
file should be corrected to match.

Follow this repo's `CLAUDE.md` for the Lean verification workflow throughout: after editing a
`.lean` file, check it with `mcp__lean-lsp__lean_diagnostic_messages`; after adding/removing an
`import`, use `mcp__lean-lsp__lean_build` instead of (or in addition to) plain `lake build`; ignore
editor `<ide_diagnostics>` hook output, it can be stale; treat `lake build` (and `lake test` for
anything touching `Todo`/`TodoTests`) as final ground truth before considering any task done.

**Note on repo state:** `git status` may show modified/untracked files you didn't touch (e.g. an
in-progress `TodoTests` extraction, `lakefile.toml` changes). That's pre-existing work in the
working tree, not yours to revert -- only touch the files these tasks name.

## Phase 0 -- fix `parsePattern!`'s docstring lie now; retire it for real later (prerequisite)

`Routing/Pattern.lean`'s `parsePattern!` docstring claims it "panics on a malformed pattern." It
doesn't: `(parsePattern s).getD []` silently returns the root pattern `[]` instead. This isn't a
`routes!`-specific problem -- `route`/`Route.get`/`Route.post`/`Route.put`/`Route.delete`/`routeUrl`
all call it directly today -- so fix the documentation regardless of whether Phases 1-2 proceed.

There are two genuinely separate fixes here, done at two different times:

1. **Now (this phase):** stop the docstring lying about what the function does. Cheap, safe,
   zero behavior change, no sequencing constraints.
2. **Later (§2.4, after Phase 2's 2.3):** actually eliminate the redundant function and make a
   malformed pattern a compile-time failure instead of a silent default. This is a real,
   non-trivial change with a sequencing dependency on retiring `Todo/Routes.lean`'s named pattern
   constants first -- see §2.4 for why it can't happen before that, and why `panic!`-based or
   autoParam-based attempts at "just make it fail" don't work (confirmed by direct experiment, not
   assumed).

Confirmed against this toolchain, not assumed: swapping `getD []` for a `panic!`-based fallback
does **not** fix this. `example : (panic! "oops" : List Nat) = [] := by rfl` succeeds -- `panic!` is
definitionally transparent to `Inhabited.default`, so it's still `[]` at the one place that
matters (`HandlerType (parsePattern! pattern) result`'s kernel-defeq resolution during
elaboration); `#eval`-ing a `panic!` confirms it doesn't even abort at runtime, just logs a
backtrace and returns the default anyway. There is no fix to `parsePattern!` as an ordinary `def`
that makes a malformed *string literal* a compile error without changing the signature of its
callers (`route` et al.) -- see §2.4 for the fix that actually works and why it has to wait.

What's in scope for *this* phase (the docstring, not the deeper fix):

- **Correct the docstring** to describe the actual behavior: silently returns `[]` (the root
  pattern) for malformed input, never panics. State plainly that callers passing a non-literal or
  otherwise unverified string get silent misrouting, not a compile error, and that source-literal
  callers should not rely on any panic-based safety net -- there isn't one.
- **Add a `#guard` demonstrating the actual behavior directly**, next to the existing malformed-
  pattern `#guard`s for `parsePattern` in the same file (e.g. `#guard parsePattern! "users/:id:Nat"
  = []` -- missing leading `/`, silently root), so the behavior is a pinned, tested fact rather than
  a comment someone can let drift out of sync with the implementation again.
- Verify with `mcp__lean-lsp__lean_diagnostic_messages` on `Routing/Pattern.lean`, then `lake build`.

Do **not** attempt to make `parsePattern!` itself throw/panic/abort as part of this fix -- it can't,
for the reason above. The actual mitigation for `routes!`'s own use of pattern text is Phase 2's use
of `parsePattern` + `Macro.throwErrorAt` inside macro elaboration (§2.1/§2.2 below), which works
because macro elaboration has real error-throwing that a plain `def` does not.

## Phase 1 -- `Todo.Urls` bundle (no macro, pure refactor)

Goal: every `Todo.Views` function takes a `urls : Todo.Urls` parameter instead of reaching for
global `Todo.*Url` constants, with `Todo.urls`'s concrete value still hand-built from today's
`Todo/Routes.lean` pattern constants (no macro yet). This is intentionally decoupled from Phase 2
so a build failure is unambiguous about which piece broke -- see plan doc §6.6.

### 1.1 Add the `Urls` structure and its value to `Todo/Routes.lean`

Add, after the existing `*Pattern` constants and in place of the existing `*Url` constants (delete
those -- once 1.2-1.4 land nothing calls them individually anymore, everything goes through
`urls.<field>`):

```lean
structure Urls where
  index          : String
  active         : String
  completed      : String
  todos          : String
  todoEdit       : Nat → String
  todo           : Nat → String
  todoToggle     : Nat → String
  toggleAll      : String
  clearCompleted : String

def urls : Urls :=
  { index := routeUrl indexPattern, active := routeUrl activePattern,
    completed := routeUrl completedPattern, todos := routeUrl todosPattern,
    todoEdit := routeUrl todoEditPattern, todo := routeUrl todoPattern,
    todoToggle := routeUrl todoTogglePattern, toggleAll := routeUrl toggleAllPattern,
    clearCompleted := routeUrl clearCompletedPattern }

#guard urls.index = "/"
#guard urls.active = "/active"
#guard urls.completed = "/completed"
#guard urls.todos = "/todos"
#guard urls.todoEdit 7 = "/todos/7/edit"
#guard urls.todo 7 = "/todos/7"
#guard urls.todoToggle 7 = "/todos/7/toggle"
#guard urls.toggleAll = "/todos/toggle-all"
#guard urls.clearCompleted = "/todos/completed"
```

Both go inside `namespace Todo`, so the resulting names are `Todo.Urls`/`Todo.urls`.

**Note on the `#guard`s above:** `Routing/Url.lean`'s own tests needed each `routeUrl`-produced
value bound to its own top-level `def : String := ...` before comparing, because `#guard`'s
`Decidable` instance search can't reduce a `UrlType segs`-computed type down to `String` (see that
file's comment, or `docs/routing-design-plan.md` §4). `urls.index` etc. should *not* need that
workaround here -- `Urls.index`'s declared type is the literal, concrete `String`, not something
computed from `segs`, so instance search never has to see `UrlType`/`parsePattern!` at all. Verify
this rather than assume it (`mcp__lean-lsp__lean_diagnostic_messages`); if it turns out to need the
same workaround, apply it the same way (`private def urlsIndex : String := urls.index`, etc.).

### 1.2 Parameterize every `Todo.Views` function on `urls : Urls`

In `Todo/Views.lean`, thread a `urls : Urls` parameter through (open `Routing`/whatever's already
open is unaffected; `Urls` is `Todo.Urls`, already in scope since this file is inside `namespace
Todo`):

- `Filter.path (f : Filter) (urls : Urls) : String` -- was `Filter.path : Filter → String`; body
  becomes `match f with | .all => urls.index | .active => urls.active | .completed =>
  urls.completed`. Reordered so `target.path urls` still reads as dot-notation-plus-one-arg at
  every call site (`filterLink`, below).
- `itemView (urls : Urls) (item : Item) : Node .flow` -- reads `urls.todoToggle
  item.id.toNatClampNeg` / `urls.todoEdit item.id.toNatClampNeg` / `urls.todo
  item.id.toNatClampNeg` in place of the current `todoToggleUrl`/`todoEditUrl`/`todoUrl` calls.
- `itemEditView (urls : Urls) (item : Item) : Node .flow` -- reads `urls.todo
  item.id.toNatClampNeg`.
- `listSection (urls : Urls) (items : Array Item) : Node .flow` -- reads `urls.toggleAll`; the
  `ul (items.toList.map itemView)` line becomes `ul (items.toList.map (itemView urls))`.
- `filterLink (urls : Urls) (current target : Filter) (label : String) : Node .flow` -- the `href`
  line becomes `a { href := target.path urls } [label] ...`.
- `footerFragment (urls : Urls) (allItems : Array Item) (filter : Filter) : Node .flow` -- reads
  `urls.clearCompleted`; the three `filterLink filter .all/.active/.completed "..."` calls become
  `filterLink urls filter .all/.active/.completed "..."`.
- `mutationFragment (urls : Urls) (items allItems : Array Item) (filter : Filter) : String` --
  passes `urls` through to `listSection urls items` and `footerFragment urls allItems filter`.
- `page (urls : Urls) (items allItems : Array Item) (filter : Filter) : String` -- reads
  `urls.todos` in the add-form's `hxPost`; passes `urls` through to `listSection`/`footerFragment`.

`filterFromPath` is unchanged (it never touched a URL constant, only compares strings).

Verify with `mcp__lean-lsp__lean_diagnostic_messages` on `Todo/Views.lean` after this step --
expect errors only in files that call these functions (handled next), not within this file itself.

### 1.3 Thread `urls` through `Main.lean`

Every handler needs `urls` added as a parameter, placed so partial application composes cleanly
(see the worked `routes` rewrite below -- **don't** try to preserve the existing
`∘`/`.map (· db)` composition trick with a second curried parameter; it gets fragile fast with two
non-uniform curried arguments, direct application is simpler and equally correct here):

```lean
def render (urls : Todo.Urls) (db : SQLite) (filter : Todo.Filter)
    (renderHtml : Todo.Urls → Array Todo.Item → Array Todo.Item → Todo.Filter → String) :
    ContextAsync (Response Body.Any) := do
  let items ← Todo.list db filter
  let allItems ← Todo.list db .all
  Response.ok.html (renderHtml urls items allItems filter)

def renderMutation (urls : Todo.Urls) (db : SQLite) (req : Request Body.Stream) :
    ContextAsync (Response Body.Any) :=
  let currentFilter := match req.line.headers.get? (.ofString! "hx-current-url") with
    | some v => Todo.filterFromPath v.value
    | none => .all
  render urls db currentFilter Todo.mutationFragment

def pageHandler (filter : Todo.Filter) (urls : Todo.Urls) (db : SQLite)
    (_req : Request Body.Stream) : ContextAsync (Response Body.Any) :=
  render urls db filter Todo.page

def addHandler (urls : Todo.Urls) (db : SQLite) (req : Request Body.Stream) :
    ContextAsync (Response Body.Any) := do
  let title ← formField req "title"
  Todo.add db title
  renderMutation urls db req

def editHandler (urls : Todo.Urls) (db : SQLite) (id : Nat) (_req : Request Body.Stream) :
    ContextAsync (Response Body.Any) := do
  let items ← Todo.list db .all
  match items.find? (fun item => item.id == Int64.ofNat id) with
  | some item => Response.ok.html (Node.render (Todo.itemEditView urls item))
  | none => Response.notFound.text "Not Found"

-- saveHandler / toggleHandler / deleteHandler / toggleAllHandler / clearCompletedHandler:
-- same shape as addHandler -- add `(urls : Todo.Urls)` as the first parameter, pass `urls` (not
-- just `db`) into their `renderMutation` call.

def routes (urls : Todo.Urls) (db : SQLite) : List (Route Result) :=
  [ .get Todo.indexPattern (pageHandler .all urls db),
    .get Todo.activePattern (pageHandler .active urls db),
    .get Todo.completedPattern (pageHandler .completed urls db),
    .post Todo.todosPattern (addHandler urls db),
    .get Todo.todoEditPattern (editHandler urls db),
    .put Todo.todoPattern (saveHandler urls db),
    .post Todo.todoTogglePattern (toggleHandler urls db),
    .delete Todo.todoPattern (deleteHandler urls db),
    .post Todo.toggleAllPattern (toggleAllHandler urls db),
    .delete Todo.clearCompletedPattern (clearCompletedHandler urls db) ]

def main : IO Unit := Async.block do
  let db ← SQLite.open ":memory:"
  Todo.initSchema db
  let addr := .v4 ⟨.ofParts 127 0 0 1, 2000⟩
  let handler := routes Todo.urls db |> toHandler
  serve addr handler >>= waitShutdown
```

Each list element in `routes` is now a direct, fully- or partially-applied `Route Result` (no `∘`,
no trailing `.map`) -- e.g. for a no-capture pattern like `Todo.indexPattern`, `HandlerType [] Result
= Result`, so `pageHandler .all urls db : Result` slots in directly; for a captured pattern like
`Todo.todoEditPattern`, `HandlerType [...] Result = Nat → Result`, so `editHandler urls db : Nat →
Result` slots in directly too. If this doesn't typecheck as written, re-derive from
`HandlerType`'s definition (`Routing/Handler.lean`) rather than reintroducing `∘`.

### 1.4 Update `TodoTests/Views.lean` call sites

`Todo.urls` is already in scope here (this file imports `Todo.Views`, which now imports
`Todo.Routes`, which defines it) -- no new import needed. With `open Todo Html` already present,
add `urls` (bare, after the `open`) as an argument to every call:

- `itemView sampleItem` → `itemView urls sampleItem` (and the `sampleItemDone`/`sampleItemUnsafe`
  variants)
- `itemEditView sampleItem` → `itemEditView urls sampleItem` (and `sampleItemUnsafe`)
- `listSection #[...]` → `listSection urls #[...]`
- `filterLink .all .all "All"` → `filterLink urls .all .all "All"` (and the other `filterLink`
  call)
- `footerFragment #[...] .filter` → `footerFragment urls #[...] .filter` (all three)
- `Filter.path .all` → `Filter.path .all urls` (all three, inside the `filterFromPath` round-trip
  guards)

**None of the expected string literals change** -- `Urls`-bundling only changes how a view
*receives* its URLs, not what URL each one resolves to. If a diff to this task ends up changing an
expected string, something upstream is wrong; don't "fix" the test by editing the string.

### 1.5 Verify Phase 1

- `mcp__lean-lsp__lean_build` (imports changed in 1.1) then `mcp__lean-lsp__lean_diagnostic_messages`
  on `Todo/Routes.lean`, `Todo/Views.lean`, `Main.lean`, `TodoTests/Views.lean`.
- `lake build` clean, including the `webapp` executable target.
- `lake test` clean (`TodoTests`).
- Don't proceed to Phase 2 until this phase is fully green -- that's the point of splitting them
  (plan doc §6.6).

## Phase 2 -- the `routes!` macro (Option C: nested grammar)

Goal: replace `Main.lean`'s hand-written `routes`/`Todo.urls`-construction with one `routes!` block
using the nested grammar from plan doc §2 ("Option C"), so every pattern is written exactly once,
at the dispatch site, regardless of how many methods or nested sub-paths share it. Phase 1 must be
green first -- this phase only changes *how* `def urls`/`def routes` get written, not what anything
downstream (`Todo.Views`, `TodoTests`) expects from them.

### 2.1 Spike first (throwaway, do not ship this file)

Per plan doc §5, confirm by actual compilation, not just reasoning, before investing in the full
grammar:

- A minimal `syntax`/`macro_rules` can parse a 2-level nested, brace-delimited grammar (a fragment
  containing a mix of `method => handler` entries and further named nested fragments) and expand it
  into Lean terms, with each nested level's `List PathSeg` prefix correctly threaded down and
  appended (`docs/routing-design-plan.md`-style: confirm by compiling a toy example with 2-3 levels
  of nesting, not by reasoning about the macro in the abstract).
- A deliberately wrong-arity handler inside a nested block still produces a legible
  `HandlerType`-mismatch error pointing at the actual handler, not an opaque macro-expansion dump
  (mirror `Handler.lean`'s `badArity` / `Url.lean`'s `badUrlArity` regressions, but inside a
  `routes!` block).
- **Malformed fragment text is a macro-time error, not a silent misroute.** `parsePattern!`
  (`Pattern.lean`, docstring corrected in Phase 0) silently returns the *root* pattern `[]` for a
  missing leading `/`, a doubled `/`, an unknown/missing capture kind, or an empty capture name --
  and that can't be fixed by making `parsePattern!` itself panic (Phase 0: `panic!` is
  defeq-transparent to `default`, confirmed against this toolchain, so it wouldn't change anything
  at the point `HandlerType (parsePattern! pattern) result` gets resolved). `routes!` must instead
  call `parsePattern` (not `parsePattern!`) on each fragment's local text and turn `none` into
  `Macro.throwErrorAt` pointing at that fragment's syntax -- this works because macro elaboration
  (`MacroM`/`TermElabM`) has real error-throwing that a plain `def` doesn't. Confirm this in the
  spike with a deliberately malformed fragment (e.g. a nested `"todos/:id:Nat"` missing its leading
  `/`) and check the error actually fires and names the right fragment (plan doc §5).
- Whether the macro should emit the `Urls` record as one literal (`def urls : Todo.Urls := { ... }`,
  requiring the macro to be told the target structure type somehow, e.g. `routes! (urlsType :=
  Todo.Urls) ...` or via the ambient expected type at its use site) or some other shape. This wasn't
  settled in the plan doc precisely because it's exactly the kind of thing that needs to be spiked,
  not decided on paper -- try the simplest thing (macro parameterized by the target `Urls` type
  name) first.

Delete the spike file(s) once done; keep only what you learn (adjust §2.2-2.3 below if reality
disagrees with them). §2.4 is a separate piece of work with its own spike -- not decided by this
one.

### 2.2 Implement `routes!`

Location: a new file under `Routing/` (e.g. `Routing/RoutesMacro.lean`), imported from
`Routing.lean` like every other submodule. The macro should stay app-framework-agnostic per plan
doc §7 -- it doesn't need to know about `SQLite`/`db` threading, only about `method`, a pattern
fragment, `handler`, optional `as name`, and nested fragments. Grammar and expansion target: plan
doc §2 ("Option C") and §3.

Acceptance criteria:

- Expands to a `List (Route Result)`-shaped table (or whatever the spike in 2.1 settled on for
  threading `db`/`urls` into handlers -- match Phase 1's `routes urls db` shape if possible, so
  `Main.lean`'s call site barely changes).
- Expands to a `Todo.Urls`-shaped value (or generically, whatever named-fragment → struct-field
  mapping 2.1 settled on) with one field per `as`-named node, regardless of nesting depth or how
  many methods that node has.
- Duplicate `as` names anywhere in the tree → macro-time error, not a redeclaration error with a
  worse message (plan doc §5), as a **permanent** `#guard_msgs` regression in this file, not just a
  spike-confirmed behavior -- same treatment as the wrong-arity case below.
- Two different `as` names resolving to the *same* full pattern → rejected (compare resolved
  `List PathSeg`, not local text -- plan doc §2's `List PathSeg`-append semantics), also as a
  permanent `#guard_msgs` regression.
- Malformed fragment text (missing leading `/`, doubled `/`, unknown/missing capture kind, empty
  capture name) → macro-time error via `Macro.throwErrorAt`, never a silent fall-through to
  `parsePattern!`'s root-pattern default (plan doc §5's `parsePattern!`-danger risk; confirmed in
  the 2.1 spike) -- also a permanent `#guard_msgs` regression, since this is the one place a bug
  would be silently wrong rather than loudly broken.
- A wrong-arity/wrong-type handler → the same quality of `HandlerType`-mismatch error as a
  hand-written `route`/`Route.get` call gets today (confirmed in the spike, now as a permanent
  `#guard_msgs` regression in this file, mirroring `Handler.lean`'s `badArity`).
- The flattened `List (Route Result)` preserves the same-arity literal/capture disambiguation the
  hand-written table relies on today (e.g. `/todos/:id:Nat`'s `PUT`/`DELETE` vs
  `/todos/toggle-all`/`/todos/completed`'s literal routes under the same methods) -- add a
  `dispatchTable`-level `#guard` against the macro's actual expansion exercising these specific
  collisions, not just a manual browser click-through (plan doc §5's order-sensitivity risk).

### 2.3 Migrate `Main.lean`, retire the old constants

Replace `Main.lean`'s hand-written `routes`/`Todo.urls`-construction with one `routes!` block using
the exact nested example from plan doc §2:

```lean
routes! (db : SQLite) where
  "/" { get => pageHandler .all }
  "/active" { get => pageHandler .active }
  "/completed" { get => pageHandler .completed }
  "/todos" as todos {
    post => addHandler
    "/:id:Nat" as todo {
      put => saveHandler
      delete => deleteHandler
      "/edit" as todoEdit { get => editHandler }
      "/toggle" as todoToggle { post => toggleHandler }
    }
    "/toggle-all" as toggleAll { post => toggleAllHandler }
    "/completed" as clearCompleted { delete => clearCompletedHandler }
  }
```

Keep the last field named `clearCompleted`, matching Phase 1 (§6.1/1.1) -- **don't** rename it to
avoid a clash with the top-level `"/completed"` node. Per plan doc §3, a node only gets a field via
an explicit `as name`; names are never derived from path text. The top-level `"/completed"` node
has no `as` and so contributes no field at all, meaning there is no actual collision to avoid here.
If the 2.1/2.2 spike reveals a real reason two nodes' names *do* collide, that's a bigger surprise
than a naming footnote -- stop and reconcile it with plan doc §3 rather than silently renaming a
field Phase 1 already shipped and tested.

Once this compiles and dispatches correctly:

- Delete `Todo/Routes.lean`'s hand-written `*Pattern` constants and `def urls`/`structure Urls` --
  **except**: re-read plan doc §6.7/§7 first. `TodoTests` cannot import `Main.lean`'s `routes!`
  block output any more than `Todo/Views.lean` could (same import-direction constraint, §4) --
  unless a spike confirms `TodoTests` importing `Main` directly is viable *and worth it* (try it:
  add `import Main` to a `TodoTests` file and run `lake build`/`lake test`). Note there's no actual
  import cycle to worry about (`lakefile.toml`: `Main` is only a `lean_exe` root, not a `lean_lib`,
  and `TodoTests → Main → Todo` doesn't loop back through `Todo`), so this will likely just compile
  -- the real cost isn't a cycle, it's that the `TodoTests` binary would now link `Std.Http.Server`
  (and whatever else `Main.lean` pulls in) transitively, solely to read one `def urls` value. Decide
  based on whether that coupling is worth it, not just on whether `lake build` succeeds. If that
  doesn't pan out, keep `Todo/Routes.lean`'s `structure Urls` (the type
  only, no `routeUrl` calls) as the shared leaf-side type, and keep a hand-built `Todo.urls` value
  there too specifically for `TodoTests` to use -- accepting that this one value is now a
  deliberately-duplicated, hand-synced fixture against `Main.lean`'s `routes!`-generated one, scoped
  *only* to what tests need (not the full pattern-visibility goal, which `Main.lean`'s dispatch
  table still gets). Document whichever way this goes directly in `Todo/Routes.lean`'s module
  docstring, since it's a real trade-off future readers need to understand, not an implementation
  detail to bury.

### 2.4 Consolidate `parsePattern!` into `parsePattern`; make a malformed pattern a compile error

Phase 0 only fixed the *docstring*. This task does the fix it deferred: one parsing function, and a
malformed pattern is a genuine compile-time failure, not a silently-defaulting `[]`. Do this **only
after 2.3 has landed and retired `Todo/Routes.lean`'s named `*Pattern` constants** -- see "why this
has to wait" below; doing it earlier actively regresses the problem this whole project exists to
fix.

**Two plausible-looking fixes were tried and empirically ruled out** (confirmed by direct
compilation against this toolchain, not reasoned about in the abstract -- don't redo this
investigation):

- **`panic!` as the fallback.** `example : (panic! "oops" : List Nat) = [] := by rfl` **succeeds**.
  `panic!` is definitionally transparent to `Inhabited.default`, so `HandlerType (parsePattern!
  pattern) result` -- resolved by kernel defeq during elaboration, not by running compiled code --
  would still see `[]` for a malformed pattern, panic or no panic. `#eval`-ing a `panic!` confirms
  it doesn't abort at runtime either; it logs a backtrace and returns the default anyway.
- **A `(hwf : (parsePattern pattern).isSome := by decide)` autoParam placed before `handler`** (so
  `handler`'s type can reference the proof-unwrapped segs). Confirmed broken: `def foo (n : Nat) (h
  : n > 0 := by decide) (m : Nat) : Nat := n + m; #eval foo 5 10` fails to elaborate -- Lean
  consumes positional arguments left-to-right and only inserts a defaulted explicit parameter's
  default when the argument list *runs out* (i.e. for a trailing parameter), not when a later
  required parameter would otherwise be available; it does not "skip ahead." Making the parameter
  implicit instead (`{h : ... := by tac}`) isn't valid binder syntax either (confirmed: parse
  error).

**What actually works: elaboration-time literal checking**, the same technique `routes!`'s own
fragment parsing (2.1/2.2) already needs. Turn `route`/`Route.get`/`Route.post`/`Route.put`/
`Route.delete` (`Routing/Route.lean`) and `routeUrl` (`Routing/Url.lean`) into `macro`s (or a
shared `elab`-based helper they all delegate to, ideally the *same* helper `routes!`'s fragment
parsing uses, rather than a second copy of "parse this literal, throw on `none`") that:

- Require their pattern argument to be a string **literal** syntax node (not an arbitrary `String`
  expression).
- Parse it via `parsePattern` (the sole remaining function -- delete `parsePattern!`) at
  macro-expansion time.
- `Macro.throwErrorAt` the literal's own syntax on `none`.
- On `some segs`, splice a term for the concrete, now-known-good `segs`.

This needs its own throwaway spike first (mirroring 2.1's discipline), since the exact mechanics
(whether `Route.get` etc. should become `macro_rules`-defined syntax vs. an `elab_rules`-based term
elaborator attached to the existing application form) aren't settled and shouldn't be decided on
paper.

**Why this has to wait for 2.3, not run earlier:** this is a real, deliberate API restriction --
`route`/`Route.get`/`routeUrl` can no longer accept a *named* `String` constant, only an inline
literal, because a macro can only inspect syntax that's literally present at its own call site.
Before 2.3, `Main.lean`'s route table and `Todo/Routes.lean`'s `urls` value both go through named
`*Pattern` constants (`Route.get Todo.indexPattern ...`, `routeUrl indexPattern`) specifically so
each pattern's text is written once and shared -- the exact single-source mechanism this whole
project exists to preserve. Hardening `route`/`routeUrl` to be literal-only *before* `routes!`
replaces that sharing mechanism would force every pattern to be retyped at each call site,
reintroducing the hand-duplication problem this project exists to eliminate (plan doc §1) -- a
regression, not a fix. It only becomes safe once 2.3 has made `routes!`'s tree the single place a
pattern's text is written, at which point every remaining caller of `route`/`Route.get`/`routeUrl`
in the whole codebase is already a literal: `Routing/Route.lean`'s own `testRoutes`, `Routing/
Url.lean`'s own tests, and whatever `routes!`'s expansion emits. Confirm that's actually true (grep
for remaining non-literal call sites) before assuming it.

Acceptance criteria:

- `parsePattern!` no longer exists anywhere in the codebase.
- A malformed literal passed directly to `route`/`Route.get`/`Route.post`/`Route.put`/
  `Route.delete`/`routeUrl` is a **new** permanent `#guard_msgs` regression in `Route.lean`/
  `Url.lean` -- there wasn't one before; `Pattern.lean` only ever tested `parsePattern` in
  isolation, never the caller-facing guarantee.
- Every existing literal-based call site in `Route.lean`/`Url.lean`/`Main.lean`'s `routes!` block
  still compiles unchanged (no behavior change for well-formed input).
- Verify with `mcp__lean-lsp__lean_build` (macro machinery changed) → `lean_diagnostic_messages` on
  `Routing/Route.lean`, `Routing/Url.lean`, `Routing/Pattern.lean`, `Main.lean` → `lake build` clean
  → `lake test` clean.

### 2.5 Verify Phase 2

Same as 1.5: `mcp__lean-lsp__lean_build` → `lean_diagnostic_messages` on every touched file → `lake
build` clean (including `webapp` executable) → `lake test` clean. Additionally, actually run the
server (`lake exe webapp` or however `Main`'s `main` gets invoked in this repo) and click through
the TodoMVC UI in a browser -- add/toggle/edit/delete a todo, switch filters -- to confirm the
`routes!`-generated dispatch table and `Urls` bundle produce a working app, not just a green build.
