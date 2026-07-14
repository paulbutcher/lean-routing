# `routes!`: a route-table macro that keeps patterns single-sourced *and* visible

Context for a fresh session: `Routing` (`Routing.lean`, `docs/routing-design-plan.md`) is a typed
path router -- `route method pattern handler` builds a `Route`, `HandlerType` rejects a
wrong-arity/wrong-type handler at compile time. Reverse routing (`Routing/Url.lean`) was added on
top: `routeUrl pattern` builds a typed URL-generator from the same pattern string, the mirror image
of `HandlerType`/`dispatch`. This doc is the plan for closing the readability gap that reverse
routing's *adoption* exposed -- read this before writing the macro.

## 1. The problem, precisely

`Main.lean`'s route table used to read like Rails' `routes.rb` -- the pattern is right there:

```lean
.get "/todos/:id:Nat/edit" ∘ editHandler,
```

Wiring up reverse routing (`Todo/Routes.lean`) moved every pattern into named `String` constants,
so `Todo/Views.lean` and `Main.lean` share one textual source instead of two hand-written copies
that drift:

```lean
.get Todo.todoEditPattern ∘ editHandler,
```

This is a real regression: `Todo.todoEditPattern` is opaque at the call site. Reading the table no
longer tells you what URL you're looking at -- you have to jump to `Todo/Routes.lean`. Rails
doesn't have this tradeoff because `routes.rb` generates its named `_path` helpers via
metaprogramming *from* the table you're reading, at boot time. Lean has no such runtime
metaprogramming; the equivalent is a macro that expands a route-table declaration into both the
dispatch list and the named URL-builders, at compile time.

**A naive first sketch of that macro reintroduces the exact problem it's meant to solve.** One path
can accept several methods with different handlers (`PUT`/`DELETE` both on `/todos/:id:Nat`, today
sharing `Todo.todoPattern` for free in the current split design). A macro whose syntax is "one line
per method+pattern+handler" forces that shared pattern to be *retyped* per method:

```lean
-- BAD: reintroduces hand-duplication of "/todos/:id:Nat", now with no compiler check they match
put    "/todos/:id:Nat" => saveHandler   as todo
delete "/todos/:id:Nat" => deleteHandler
```

Any macro design has to solve this or it isn't actually an improvement over
`Todo/Routes.lean`'s current split -- it just moves the duplication risk from "two files" to "two
lines," with no compile-time link between them either way.

## 2. Design fork: where does "one path, several methods" live?

**Option A -- decouple naming from wiring (two flat lists).** Declare each unique path once, name
it; separately, wire `method, name => handler` entries that reference names, not text:

```lean
routes! where
  path index        "/"
  path todo          "/todos/:id:Nat"
  ...

routeTable! (db : SQLite) where
  get  index => pageHandler .all
  put  todo  => saveHandler
  delete todo => deleteHandler
  ...
```

Simplest possible grammar (two independent flat lists, no nesting) -- but it puts the pattern text
in a *different* block than the dispatch entry that uses it. That's strictly better than today's
"different file," but it does not fully close the gap the user is asking about: reading `put todo
=> saveHandler` still doesn't show `/todos/:id:Nat`. Rejected as the target design for that reason,
though it's the fallback if Option C's nested grammar (below) turns out to be more macro work than
it's worth.

**Option B -- group methods under one pattern, comma/brace-delimited, not indentation-sensitive.**
A route-table entry is one of two shapes: a single-method line, or a pattern followed by a
brace-delimited list of `method => handler` pairs:

```lean
routes! (db : SQLite) where
  get    "/"                     => pageHandler .all
  get    "/active"                => pageHandler .active
  get    "/completed"             => pageHandler .completed
  post   "/todos"                 => addHandler                 as todos
  get    "/todos/:id:Nat/edit"    => editHandler                as todoEdit
  "/todos/:id:Nat" as todo { put => saveHandler, delete => deleteHandler }
  post   "/todos/:id:Nat/toggle"  => toggleHandler               as todoToggle
  post   "/todos/toggle-all"      => toggleAllHandler             as toggleAll
  delete "/todos/completed"       => clearCompletedHandler        as clearCompleted
```

Every pattern appears exactly once per *method group*, which is real progress over the naive
sketch -- but the full pattern text is still repeated across sibling entries that share a prefix:
`/todos/:id:Nat/edit` and `/todos/:id:Nat/toggle` both restate `/todos/:id:Nat` in full, and every
entry under `/todos` restates `/todos`. That's the same class of duplication as the `PUT`/`DELETE`
case, just at the *prefix* level instead of the *method* level -- Option B only solved one axis.

**Option C (adopted) -- nest, so a shared prefix is written once regardless of how many methods or
sub-paths hang off it.** Every entry becomes a local path *fragment*, optionally named, containing
either direct `method => handler` pairs, further nested fragments, or both:

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

`/todos` is written once and everything beneath it -- the create route, the per-item routes, the
two collection actions -- inherits it. This generalizes Option B rather than replacing its
machinery: a leaf like `"/active" { get => pageHandler .active }` is exactly a degenerate,
childless node, and the brace-delimited `method => handler` list inside any node is the same
comma/brace grammar Option B already specified (§2's indentation-avoidance reasoning still holds).
What's new is that a node's body can *also* contain further `"fragment" (as name)? { ... }` nodes,
recursively -- so the grammar has exactly one production shape (a named-or-anonymous fragment
containing a mixed list of method-entries and child-fragments) instead of two, which is simpler to
parse despite looking like a bigger feature.

**Resolving a node's full pattern is `List PathSeg` append, not string concatenation.** Each node's
local text (`"/todos"`, `"/:id:Nat"`, `"/edit"`, ...) parses independently via the existing
`parsePattern` (`Routing/Pattern.lean`); a node's *resolved* segments are its parent's resolved
segments `++` its own, e.g. `todoEdit`'s resolved segs are `parsePattern! "/todos" ++ parsePattern!
"/:id:Nat" ++ parsePattern! "/edit"`, which is exactly `parsePattern! "/todos/:id:Nat/edit"` --
`List PathSeg` append sidesteps the string-join edge cases `Pattern.lean`'s own parser had to be
careful about (doubled/trailing `/`) by working in `List PathSeg` instead of `String` until the
final `route`/`routeUrl` call: appending two segment lists has no separator character to double or
drop, unlike splicing two path strings together, regardless of how many segments either side
contributes. (Every fragment must still start with `/` -- that's what lets its local text parse
independently via `parsePattern` -- but it need not contribute a *nonempty* segment list: the root
fragment `"/"` in §3's example resolves to `[]`, and appending `[]` onto a parent's segments is
exactly as safe as appending any other list.)

## 3. What the macro expands to

The macro walks the tree once, threading each node's resolved `List PathSeg` down to its children,
and at each node contributes to two elaborated things -- both built from the *existing*, unchanged
`Routing`/`Routing.Url` primitives; the macro is sugar over `route`/`Route.get`/`routeUrl`, it does
not reimplement dispatch or reverse routing:

1. `def routes (db : SQLite) : List (Route Result) := [...]` -- one `.get`/`.post`/`.put`/`.delete`
   element per `method => handler` pair anywhere in the tree, built from that pair's node's
   *resolved* segments (not its local text). A node with N direct methods and M children
   contributes N list elements itself, plus whatever its M children contribute recursively.
2. For every node carrying `as name` -- one field `name := routeUrl <resolved pattern>` in the
   `Urls` record literal (§6.4 folds this in directly; a node's `as name` is independent of how many
   methods or children it has, so `/todos/:id:Nat`'s `PUT`/`DELETE` still produces exactly one
   `todo` field, and `/todos`'s own `post` plus its three children still produces exactly one
   `todos` field alongside `todo`/`todoEdit`/`todoToggle`/`toggleAll`/`clearCompleted`).

Nodes without `as name` (`"/"`, `"/active"`, `"/completed"` above) don't get a field -- only
patterns actually consumed by `Todo/Views.lean` need one, and the macro should treat `as name` as
optional throughout, not just at leaves.

## 4. Where does this live, given the import graph?

`Todo/Views.lean` needs the generated `*Url` defs; `Main.lean`'s handlers need `Todo.Views` (to
render responses) and `SQLite`/`Request`/`ContextAsync`. So handlers can't move into whatever file
defines the `routes!` block without creating `Views → routes-file → Views` (handlers need Views,
route file needs handlers) -- the same cycle that justified splitting `Todo/Routes.lean` out in the
first place. **This means the `routes!` tree -- the one with handlers wired in -- has to stay in
`Main.lean` (or wherever handlers live), and `Todo/Views.lean` still can't import it.**

So `routes!` alone does not let one block simultaneously (a) show patterns next to handlers *and*
(b) be importable by `Todo/Views.lean` for the `*Url` defs -- the cycle is structural, not a syntax
problem, and no macro changes that. Two real options to actually close the loop:

- **4a. Split the macro's output, not its input.** Write *one* `routes!` block in `Main.lean` (or a
  new file importing `Todo.Views`), patterns visible, handlers wired -- satisfies the readability
  ask. Have the macro additionally emit the `*Url` defs into a *separate* namespace/file the macro
  writes to, or accept that the `*Url` defs it generates live alongside the table (in `Main.lean`)
  and `Todo/Views.lean` keeps calling hand-maintained `Todo.Routes` constants as it does today, now
  generated by a *second*, smaller `routes!`-adjacent block that only declares patterns (Option A,
  restricted to just the naming half) -- i.e. accept **two macro invocations**, one per side of the
  import cut, both still deriving their patterns from... which brings back the duplication question
  one level up, unless one of the two is generated *from* the other (code generation across files
  isn't something a Lean macro can do -- it expands in place, once, at its own call site).
- **4b. Invert `Todo/Views.lean`'s dependency: pass URLs in instead of importing them.** Change
  `itemView`, `itemEditView`, `listSection`, `footerFragment`, `filterLink`, `page` to take the URLs
  they need as parameters instead of reaching for global `Todo.*Url` constants. Then nothing in
  `Todo/Views.lean` needs route information at all, the import-direction constraint disappears, and
  the *entire* route table -- patterns, handlers, and generated URL bindings -- can live in one
  `routes!` block in `Main.lean`, which then threads the URLs it built through to the view calls.
  This is a real, if mechanical, refactor of every view function's signature and every call site
  that renders one, not just a routing change.

**4b is the only option that actually delivers "patterns visible, single-sourced, no duplication"
in full** -- 4a still ends up with the pattern declared twice (table + a naming-only block), just
now both machine-checked against drift instead of hand-synced, which is an improvement on today but
not what's being asked for. 4b is a larger, separate piece of work from the macro itself (it touches
every view function's public signature) and should be scoped and agreed on its own merits before
being bundled with `routes!` -- see §6.

## 5. Complexity and risk, compared to what's been built so far

Everything in `Routing`/`Routing.Url` so far is *type computed from a value* -- no macro, ordinary
`def`s, checked by Lean's existing elaborator (`docs/routing-design-plan.md` §2, confirmed by
`Handler.lean`'s `badArity` regression and `Url.lean`'s `badUrlArity`). `routes!` is categorically
different: real `syntax`/`macro_rules` work, parsing a small custom grammar and emitting
declarations (`def routes := ...`, one `def *Url := ...` per named entry) from it. Concrete risks
worth spiking before committing to full implementation, same spirit as
`docs/routing-design-plan.md` §2-4:

- **Error quality.** A wrong-arity handler inside a `routes!` block needs to still produce a
  `HandlerType`-mismatch error that points at the actual line/handler, not a macro-expansion dump.
  Worth a throwaway spike confirming this before investing in the full grammar -- more important
  now than under Option B, since a handler mismatch several levels deep in a nested tree is exactly
  where a bad error would be most disorienting (which ancestor's prefix is this even resolved
  against?).
- **Duplicate/unused names, now tree-wide.** Two nodes `as todo` anywhere in the tree (not just
  siblings) should be a macro-time error, not a silent `def`/field redeclaration failure with a
  worse message -- checking this means the macro collects `as` names across the *whole* walk, not
  per-block. Two nodes with the same *resolved* pattern but different `as` names is worth rejecting
  too (defeats the point); catching that requires comparing resolved `List PathSeg`, not the local
  text, since two different local fragments under different parents could coincidentally resolve
  to the same full path.
- **`parsePattern!` must not be the macro's parsing primitive -- and "just make it panic" doesn't
  fix it either.** `Pattern.lean`'s `parsePattern!` docstring says it "panics on a malformed
  pattern" -- the implementation doesn't: `(parsePattern s).getD []` *silently returns the root
  pattern* `[]` for any malformed string (missing leading `/`, doubled `/`, unknown/missing capture
  kind, empty capture name), no panic, no error. Confirmed directly against this toolchain rather
  than assumed: `example : (panic! "oops" : List Nat) = [] := by rfl` **succeeds** -- `panic!` is
  definitionally transparent to `Inhabited.default` (`[]` for `List`), so swapping `getD []` for a
  `panic!`-based fallback would be defeq-identical to today's behavior at the one place it matters
  (`HandlerType (parsePattern! pattern) result` is resolved by kernel defeq during elaboration, not
  by running compiled code); `#eval`-ing a `panic!` confirms it doesn't even abort at runtime --
  it logs a backtrace to stderr and still returns the default. There is no version of
  `parsePattern!` built as an ordinary `def` that can turn a malformed *string* into a compile-time
  failure -- `panic!`/`sorry`-style escape hatches are all defeq-transparent, not "stuck" or
  erroring. That's exactly why `routes!` can't route around this by calling a fixed
  `parsePattern!`; it has to parse with `parsePattern` *inside macro elaboration* (`MacroM`/
  `TermElabM`, which has real `throwError`) and reject `none` there itself, at every fragment,
  turning `none` into a macro-time error (`Macro.throwErrorAt`) pointing at that fragment's syntax.
  Worth its own permanent negative-test regression (mirroring the malformed-pattern `#guard`s
  already in `Pattern.lean`), not just a spike confirmation.

  Independent of `routes!`: **`parsePattern!`'s docstring is simply wrong about the primitive's own
  behavior**, and should be corrected to describe what it actually does (silently defaults to the
  root pattern, does not panic) regardless of whether `routes!` ever ships, since it's already used
  directly by `route`/`Route.get`/`Route.post`/`Route.put`/`Route.delete`/`routeUrl` today (task
  list Phase 0).

  **Decision: also retire `parsePattern!` entirely and harden its callers, not just document the
  gap.** Two ways of making this a "real" compile-time failure without touching the callers'
  call-site ergonomics were tried and empirically ruled out: a `panic!`-based fallback (above --
  defeq-transparent to `default`, changes nothing) and a `(hwf : (parsePattern pattern).isSome := by
  decide)` autoParam placed before `handler` so `handler`'s type could reference the unwrapped segs
  (confirmed broken by direct compilation: Lean only inserts a defaulted explicit parameter's
  default when the argument list runs out, i.e. for a *trailing* parameter -- not when a required
  parameter follows it in the telescope; a caller's positional arguments get consumed left-to-right
  regardless). The mechanism that does work is the same one `routes!` itself needs: parse the
  pattern *at elaboration time*, against the literal syntax the caller wrote, and
  `throwErrorAt`/`Macro.throwErrorAt` on `none` -- which means `route`/`Route.get`/`Route.post`/
  `Route.put`/`Route.delete`/`routeUrl` become macros (or share an `elab`-based helper) that only
  accept a string *literal*, not an arbitrary `String` expression.

  That's a real, deliberate API restriction, and it has a genuine sequencing dependency on this very
  plan: before `routes!` exists, `Main.lean`'s route table and `Todo/Routes.lean`'s `urls` value both
  go through *named* `String` constants (`Route.get Todo.indexPattern ...`, `routeUrl
  indexPattern`) specifically so a pattern's text is written once and shared -- literal-only
  `route`/`routeUrl` can't accept that indirection (a macro can only see syntax present at its own
  call site), so hardening them *before* `routes!` replaces that sharing mechanism would force every
  pattern to be retyped at each call site, reintroducing exactly the hand-duplication problem this
  project exists to eliminate (§1). It only becomes safe once `routes!`'s tree is the single place a
  pattern's text is written -- i.e. after the old named constants are retired (§2.3's last bullet).
  Scoped as its own task, sequenced after that point: task list §2.4.
- **Flattening a tree into a list is order-sensitive, and today's ordering is implicit.**
  `dispatchTable` (`Route.lean`) is first-match-wins over a flat list. The current hand-written
  table only works because same-arity literal/capture collisions (`/todos/toggle-all` vs
  `/todos/:id:Nat`, `/todos/completed` vs `/todos/:id:Nat`) happen to be disambiguated by the
  capture failing to parse as its type (`"toggle-all".toNat? = none`), not by list order per se --
  but nothing states that as an invariant. A tree walk could plausibly emit same-method,
  same-arity routes in a different relative order than the current flat list does. Worth a test
  against the macro's *actual* flattened output for exactly these collision cases, not just a
  manual click-through.
- **Recursive parsing is a bigger lift than Option B's flat grammar.** A single production
  (fragment containing a mixed list of methods and child fragments, §2) is conceptually simpler than
  two shapes, but implementing it means `macro_rules` recursing into nested `{ }` groups and
  threading accumulated `List PathSeg` state down through that recursion during elaboration --
  genuinely more `syntax`/`macro_rules` surface than Option B's flat list, closer in kind to parsing
  nested `do`-blocks than a single-level DSL. Worth a throwaway spike (mirroring
  `docs/routing-design-plan.md`'s own spike-before-committing practice) confirming the recursive
  expansion and prefix-threading works before investing in the full grammar, error-message polish,
  and duplicate-checking above.
- **Scope of the grammar.** Resist adding features beyond §2's fragment shape until they're
  actually needed -- e.g. no query-string syntax, no `resources`-style CRUD-verb inference from a
  bare name (Rails' `resources :todos` implicitly generating `index`/`create`/`edit`/`update`/etc.)
  -- both explicitly out of scope per `Routing.lean`'s existing "Not yet supported" list. Nesting
  itself is the one addition justified by concrete, demonstrated duplication (this section); further
  sugar on top isn't justified by anything seen so far.

**Decision: 4b.** Scoped in full below (§6). 4a was rejected as not actually delivering what's being
asked for -- it still leaves the pattern written twice across the import cut, just now generated on
both sides instead of hand-synced, which is strictly better than today but not the goal.

## 6. Scoping 4b: a `Todo.Urls` bundle, not per-URL parameters

§2's move to a nested grammar changes how `routes!`'s *input* is written, not what it elaborates
to -- per §3, the output is still exactly one flat `List (Route Result)` and one set of named
URL-builders, now sourced from resolved-segment tree nodes instead of flat literals. Everything
below is unaffected by that change: `Urls`'s fields are still one per `as`-named node regardless of
nesting depth, and §6.4's record literal is still built the same way, just fed by tree-resolved
patterns instead of flat ones.

Taking "pass URLs in instead of importing them" literally -- one parameter per URL -- doesn't
survive contact with the actual call graph. `page` calls `listSection` and `footerFragment`;
`listSection` calls `itemView` per item; `footerFragment` calls `filterLink` three times. Threading
nine individual URL parameters through four call layers, most of which only pass most of them
through unused, is exactly the kind of parameter-explosion Lean (or any language) makes miserable.
The fix is the standard one: bundle every URL into one record, thread *that*.

### 6.1 The bundle

```lean
-- Todo/Routes.lean
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
```

Field *types* here are plain, concrete function types (`String`, `Nat → String`) -- there's no need
for this structure to mention `Routing.UrlType`/`PathSeg` at all, so `Todo/Routes.lean` stays
decoupled from routing internals; it just declares the shape every URL-producing consumer needs.

### 6.2 Why this struct still has to be hand-written (a `routes!` limitation, not a 4b one)

It's tempting to want `routes!` to generate this struct too, so nothing is hand-maintained. It
can't: a macro invocation elaborates declarations into the file it's texually written in, and
§4 already established the `routes!` invocation itself has to live in `Main.lean` (it needs
handlers, which need `Todo.Views`). `Todo/Views.lean` needs `Urls` as a *type* it can put in a
function signature, and can't import anything that (transitively) imports itself. So the struct
*type* -- field names and argument shapes, no pattern text -- has to be declared somewhere on the
leaf side of that cut, by hand. This is a small, low-churn piece of boilerplate (it only changes
when a route's capture arity changes, e.g. `Nat` → `String`, or a route gains/loses a consumer
elsewhere), and a mismatch between it and what `routes!` builds is a plain Lean structure-literal
type error at the `routes!` call site -- compiler-caught, not a silent drift. That's an acceptable,
bounded cost for what it buys.

### 6.3 Full inventory of what needs threading

Every `Todo.Views` function that touches a URL, and what changes:

| Function | Today | After |
|---|---|---|
| `Filter.path` | matches on `Filter`, returns `indexUrl`/`activeUrl`/`completedUrl` | takes `urls : Urls`, returns `urls.index`/`.active`/`.completed` |
| `itemView` | reads `todoToggleUrl`/`todoEditUrl`/`todoUrl` | takes `urls : Urls`, reads `urls.todoToggle`/`.todoEdit`/`.todo` |
| `itemEditView` | reads `todoUrl` | takes `urls : Urls`, reads `urls.todo` |
| `listSection` | reads `toggleAllUrl`; calls `itemView` per item | takes `urls : Urls`, reads `urls.toggleAll`; passes `urls` to `itemView` |
| `filterLink` | calls `target.path` | takes `urls : Urls`, calls `target.path urls` |
| `footerFragment` | reads `clearCompletedUrl`; calls `filterLink` × 3 | takes `urls : Urls`, reads `urls.clearCompleted`; passes `urls` to each `filterLink` |
| `mutationFragment` | calls `listSection`, `footerFragment` | takes `urls : Urls`, passes it through to both |
| `page` | reads `todosUrl`; calls `listSection`, `footerFragment` | takes `urls : Urls`, reads `urls.todos`; passes it through to both |

`itemEditView` is called from `Main.lean`'s `editHandler`, not from another `Views` function, so
that call site needs `urls` threaded from the handler, not from a parent view -- see §6.4.

### 6.4 `routes!`'s output, revised

`routes!` in `Main.lean` now emits three things instead of one-def-per-named-pattern:

```lean
def urls : Todo.Urls :=
  { index := routeUrl "/", active := routeUrl "/active", completed := routeUrl "/completed",
    todos := routeUrl "/todos", todoEdit := routeUrl "/todos/:id:Nat/edit",
    todo := routeUrl "/todos/:id:Nat", todoToggle := routeUrl "/todos/:id:Nat/toggle",
    toggleAll := routeUrl "/todos/toggle-all", clearCompleted := routeUrl "/todos/completed" }

def routes (db : SQLite) : List (Route Result) := [ ... ]  -- unchanged shape from §3
```

i.e. every `as name` entry now contributes one *field* to a single `Urls` record literal instead of
a standalone top-level `def`. This is what actually eliminates the duplication for grouped entries:
`"/todos/:id:Nat" as todo { put => saveHandler, delete => deleteHandler }` is still one pattern,
written once, contributing one `urls.todo` field and two `routes` list elements.

### 6.5 Threading `urls` through `Main.lean`'s handlers

`render`/`renderMutation`/`pageHandler`/`editHandler` all currently close over `db` only; they need
`urls` too. Since `urls` is static (computed once at startup, unlike `db` which is a real resource),
the cleanest shape is currying it in the same way `db` already is:

```lean
def render (urls : Todo.Urls) (db : SQLite) (filter : Todo.Filter)
    (renderHtml : Todo.Urls → Array Todo.Item → Array Todo.Item → Todo.Filter → String) :
    ContextAsync (Response Body.Any) := do
  let items ← Todo.list db filter
  let allItems ← Todo.list db .all
  Response.ok.html (renderHtml urls items allItems filter)

def editHandler (urls : Todo.Urls) (db : SQLite) (id : Nat) (_req : Request Body.Stream) :
    ContextAsync (Response Body.Any) := do
  let items ← Todo.list db .all
  match items.find? (fun item => item.id == Int64.ofNat id) with
  | some item => Response.ok.html (Node.render (Todo.itemEditView urls item))
  | none => Response.notFound.text "Not Found"
```

and `main` builds `urls` once (from the `routes!`-generated `def urls`) and threads it into every
handler the same place `db` is threaded today: each `routes` list element becomes a directly (or
partially) applied `Route Result` value -- `pageHandler .all urls db`, `editHandler urls db`, etc.
-- rather than the old `∘`/`.map (· db)` composition trick. With two non-uniform curried arguments
(`urls`, `db`) instead of one, direct application is simpler and equally correct; `main` calls
`routes Todo.urls db |> toHandler`. (The worked example just below, and the task list, spell this
out concretely -- that's the wiring to build against, not a `.map`-based variant.)

### 6.6 Migration plan, phased to de-risk the macro separately from the refactor

The `Urls`-bundle refactor (§6.1-6.5) and the `routes!` macro (§2-§3) are independently useful and
independently risky -- doing both at once makes it hard to tell which one broke if `lake build`
fails. Sequence them:

1. **Phase 1 -- introduce `Urls`, keep today's `Todo/Routes.lean` constants as its only producer.**
   Add the `structure Urls` (§6.1), build one `def urls : Urls := { index := indexUrl, ... }` by
   hand from the *existing* `Todo.Routes.*Url` defs (no macro yet), parameterize every `Todo.Views`
   function per §6.3, thread `urls` through `Main.lean` per §6.5, update every `TodoTests/Views.lean`
   call site to pass a `urls` fixture (§6.7). This phase is pure refactoring against
   already-working, already-tested primitives -- verify with `lake build`/`lake test` before moving
   on, so a break here is unambiguously the refactor's fault, not the macro's.
2. **Phase 2 -- build `routes!`, retire the old `Todo.Routes.*Pattern`/`*Url` defs.** Once Phase 1's
   plumbing is proven, `routes!` only has to change how `def urls`/`def routes` in `Main.lean` get
   *written* (§6.4), not how anything downstream consumes them -- `Todo.Urls`'s type, and every
   `Todo.Views` signature, are already correct and untouched. A `routes!` bug at this point is
   isolated to "does this macro expand to the right `def urls`/`def routes`," checkable by
   comparing its expansion against Phase 1's hand-written versions field-for-field.

### 6.7 Test impact

`TodoTests/Views.lean`'s `#guard`s call `itemView sampleItem`, `footerFragment #[] .all`, etc.
directly; every one of those call sites needs a `urls` argument once §6.3 lands. Use the *real*
`urls` value (`Todo.urls` from `Main.lean`, or a `TodoTests`-local copy built the same way) rather
than a synthetic fixture -- matches this file's existing "captured from an actual `#eval`... not
hand-derived" convention (`TodoTests/Views.lean`'s own docstring), and turns these tests into an
end-to-end check that views and routes agree, not just that view functions are individually
well-typed. Since `Main.lean` isn't importable from `TodoTests` any more than `Todo/Views.lean` is
(same cycle, §4), Phase 1's hand-built `urls` needs a copy either in `TodoTests` directly or in a
shared non-`Main` location `TodoTests` can reach -- worth deciding in Phase 1, since it's the same
"where does the concrete `urls` value live" question `Main.lean` already has to answer.

## 7. Not yet decided

- **Naming convention for grouped entries' generated `Url`** -- `todoUrl` (pattern's `as` name plus
  `Url`) matches `Todo/Routes.lean`'s existing convention; no reason to deviate.
- **Whether `routes!` needs to know about `SQLite`/`db` threading at all**, or whether (as today)
  handlers stay `db`-curried and `routes!`'s output list gets `.map (· db)` applied outside the
  macro. Keeping the macro ignorant of `db` (just emitting `Route (SQLite → Result)` shaped
  handlers, mapped afterward) keeps its scope smaller and app-framework-agnostic. Recommended --
  same treatment should extend to `urls` (§6.5): `routes!` emits `def urls` and a `db`-and-`urls`-
  curried `routes` list, wiring both happens in `main`, the macro stays app-framework-agnostic.
- **Where `TodoTests`' copy of `urls` lives** (§6.7) -- a real open question, not yet resolved.
- **Whether Phase 1 is worth landing on its own** even if `routes!` (Phase 2) never gets built --
  it's a strict readability/consistency improvement (one `Urls` bundle instead of nine loose
  top-level `def`s) independent of the macro, so it may be worth doing regardless of the Phase 2
  decision.
- ~~Whether to harden `route`/`Route.get`/`routeUrl` themselves against malformed pattern
  literals~~ -- **decided** (§5): yes, retire `parsePattern!` and make `route`/`Route.get`/
  `Route.post`/`Route.put`/`Route.delete`/`routeUrl` literal-only macros, sequenced *after* `routes!`
  retires the named `*Pattern` constants (task list §2.4), not before -- doing it earlier would
  reintroduce the hand-duplication problem this project exists to fix. Not left as a deferred
  design pass; it's scoped and sequenced.

## 8. Test strategy note

Same default as `Routing`: `#guard` for behavior (a `routes!` block expanding to a table that
dispatches correctly, and to a `urls` value producing the expected strings), plus the negative
"should fail to typecheck/elaborate" cases from §5 (wrong arity, duplicate `as` name, two names
resolving to the same pattern, and malformed fragment text) as their own **permanent** regressions,
not just spike-confirmed behavior -- matching this codebase's existing practice of a permanent
guard per negative case (`Handler.lean`'s `badArity`, `Url.lean`'s `badUrlArity`, `Pattern.lean`'s
seven malformed-pattern `#guard`s).

The "no new proof obligations beyond what `Handler.lean`/`Url.lean` already carry" claim holds
*only if* §5's `parsePattern!`-danger risk is actually closed -- i.e. `routes!` uses `parsePattern`
and rejects `none` at macro time, never falls through to `parsePattern!`'s silent root-pattern
default. That's the one place this feature could introduce a real correctness gap (silently wrong
routing with no compiler feedback) rather than just an ergonomics one; everything else `routes!`
does is genuinely sugar over already-proven-safe primitives, per §3.

Phase 1's refactor needs no new test *strategy*, only updated call sites (§6.7) -- the assertions
themselves (expected rendered strings) don't change, since `Urls`-bundling doesn't change what any
view renders, only how it receives the URLs it renders.
