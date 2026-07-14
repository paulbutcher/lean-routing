import Lean
import Routing.Route
import Routing.Url
import Routing.Server

/-!
`urlTree`/`application`: a pair of route-tree command macros letting a pattern be written exactly
once, even when the reverse-routing struct it produces (`urlTree`, upstream) and the dispatch table
that wires handlers to it (`application ... using ...`, downstream) live in different files with a
one-way import edge between them. `application` alone (no `using` clause) also supports the
self-contained case, generating both the struct and the dispatch table from one tree when no
upstream/downstream split is needed. See `docs/application-macro-plan.md` for the full design
rationale -- this is the implementation.

## The problem `urlTree`/`application ... using ...` solves

A library upstream of the file `application` is invoked in (e.g. `Todo`, whose `Views.lean` needs
to project fields off a `Urls` value to render links) can't reference the struct `application`
generates, because that struct doesn't exist until *after* every handler `application`'s tree
references by name -- which necessarily live downstream, since they're ordinary identifiers
resolved at the point the tree is elaborated. An earlier version of this file solved this with a
`deriving <ClassName>` clause (a hand-written typeclass upstream, an instance the macro emitted
downstream) -- correct, but it still required the *set of route names* to be independently
maintained twice: once as the class's methods, once as the tree's `as` names, agreeing only because
a mismatch is a compile error, not because there was one source of truth. `urlTree`/`using` removes
the second copy entirely: patterns and names are written *once*, in `urlTree`, and `application`'s
downstream tree only ever contributes genuinely new information (which method, which handler) for
an already-declared name -- see "Two commands, one source of truth" below.

## Grammar (self-contained)

```
application app : SQLite where
  "/" as index { get => pageHandler .all }
  "/todos" as todos {
    post => addHandler
    "/:id:Nat" as todo {
      put => saveHandler
      delete => deleteHandler
    }
  }
```

A `routeItem` is either a `method => handler` entry or a `"pattern" (as name)? { item* }` fragment,
recursing into itself -- one syntax category, two productions, ported unchanged from the reverted
`routes!` spike (`git show a8a3cdc^:Routing/RoutesMacro.lean`). A node's *resolved* pattern is its
parent's resolved segments `++` its own local segments (`List PathSeg` append, not string
concatenation). This expands to two declarations: `structure <Name>Urls where ...` (one field per
`as`-named node, field type computed directly from that node's resolved `List PathSeg`) and
`def <name> : Application <CtxType> <Name>Urls := let urls := { ... }; { urls, handler := fun ctx =>
toHandler [ ... ] }` (every route handler applied to `ctx urls`, that order, before its captures).
`<Name>Urls` is derived from the binder (`app` → `AppUrls`), not a fixed literal -- lets two
`application` blocks coexist in one namespace without colliding.

## Two commands, one source of truth (the upstream/downstream split)

```
-- Todo/Urls.lean (upstream)
urlTree Urls where
  "/" as index { }
  "/todos" as todos {
    "/:id:Nat" as todo {
      "/edit" as todoEdit { }
    }
  }

-- Main.lean (downstream)
application app : SQLite using Todo.Urls where
  index { get => pageHandler .all }
  todos {
    post => addHandler
    todo {
      put => saveHandler
      delete => deleteHandler
      todoEdit { get => editHandler }
    }
  }
```

`urlTree` reuses the *same* `routeItem` grammar as self-contained `application` (patterns, `as`
names, nesting -- method entries are rejected, since `urlTree` only ever declares reverse routing,
never dispatch), and expands to the same `structure <Name> where ...` plus a value
`def <lowerFirst name> : <Name> := { ... }` -- but *also* records each named node's resolved
`List PathSeg` in a persistent environment extension (`urlTreeExt` below), keyed by the struct's
fully-qualified name and the node's name, so a *different* file/command invocation can look
patterns back up by name without re-parsing or re-typing them.

`application <name> : <CtxType> using <UrlsType> where <items>` never mentions a pattern string --
its `handlerItem` grammar (`ident " => " term` for a method entry, `ident " { " item* " } "` for a
named grouping) only ever *references* an already-`urlTree`'d name, resolving its pattern via
`urlTreeExt` (a macro-time error, pointing at the offending identifier, if the name isn't found --
never a redeclaration or a silently-empty pattern). Nesting here is purely cosmetic (grouping,
mirroring the `urlTree`'s own shape for readability) since every name's pattern is already fully
resolved independent of where it's referenced -- unlike self-contained `application`'s
`routeItem`, a `handlerItem` fragment's parent doesn't contribute anything to its children's
patterns.

## Structure declarations aren't quotable with a dynamic field list

Ordinary term-level quotation antiquotation (`Term.structInst`, `{ f := v, ... }`) already splices
a dynamic list fine (confirmed directly, and by the reverted spike's `def urls := { ... }`). But
`structure ... where`'s field list (`structFields`/`structSimpleBinder`,
`Lean/Parser/Command.lean`) is *not* a registered syntax category -- `` `(command| structure Foo
where $[$names : $tys]*) `` fails to parse ("unexpected token '$'; expected ')'"), confirmed
directly rather than assumed. Sidestepped by building the whole `structure` command as source text
(field types as concrete arrow-type text, e.g. `"Nat → String"`) and parsing it with
`Lean.Parser.runParserCategory`, then `elabCommand`ing the result the same way a quotation-built
`Syntax` would be -- this is also what lets field types be emitted as concrete arrow types directly
rather than `UrlType (parsePattern! ...)` (`docs/routing-design-plan.md` §4's instance-search
transparency concern).

## Non-hygienic names, deliberately

`urls` (the local reverse-routing bundle), `ctx` (the handler-closure's context parameter), and
`<Name>Urls` (the generated structure) are all built with `mkIdent`, not literal text in a
quotation -- a literal identifier written directly in `` `(...) `` is hygienically mangled per
quotation call and invisible to a *different* quotation call/call site, but `mkIdent` produces a
plain, unscoped name that resolves consistently everywhere it's spliced, exactly like ordinary
hand-written source. This is load-bearing here specifically because `urls`/`ctx` are referenced
across several independently-built `TSyntax` fragments (one per route entry) that all get spliced
into one final `def`.
-/

namespace Routing

open Lean Elab Command Meta
open Std Http Server

/-- Bundles a route table's dispatch handler (still curried over the app's context type) with a
reverse-routing `Urls` struct, produced together (self-contained `application`) or separately
(`urlTree` + `application ... using ...`) by the macros below. -/
structure Application (Ctx Urls : Type) where
  urls    : Urls
  handler : Ctx → StatelessHandler

/-- One node in a self-contained `application` tree or a `urlTree`: either a `method => handler`
entry, or a further `"pattern" (as name)? { ... }` fragment. Ported unchanged from the reverted
`routes!` spike. -/
declare_syntax_cat routeItem

/-- `get => handler`, `post => handler`, `put => handler`, `delete => handler`. -/
syntax ident " => " term : routeItem

/-- `"pattern" (as name)? { item* }`. `manyIndent`, not a bare `routeItem*`: without it, a handler
`term` with nothing to stop it greedily continues parsing across a newline as a further
application argument, mis-parsing the next sibling fragment as an extra argument to the previous
handler (confirmed by the reverted spike). -/
syntax str (" as " ident)? " { " manyIndent(routeItem) " } " : routeItem

/-- `application <name> : <CtxType> where <items>` (self-contained: generates its own struct). -/
syntax "application " ident " : " term " where " manyIndent(routeItem) : command

/-- `urlTree <Name> where <items>` -- patterns and names only, no handlers (module docstring). -/
syntax "urlTree " ident " where " manyIndent(routeItem) : command

/-- One node in an `application ... using ...` tree: a `method => handler` entry (applying to the
*enclosing* named node), or `name { item* }`, referencing an already-`urlTree`'d name and
recursing into it for its own methods/children. Unlike `routeItem`'s fragment production, `name`
here is a bare reference, not a pattern string -- module docstring. -/
declare_syntax_cat handlerItem

syntax ident " => " term : handlerItem

syntax ident " { " manyIndent(handlerItem) " } " : handlerItem

/-- `application <name> : <CtxType> using <UrlsType> where <items>` (module docstring). -/
syntax "application " ident " : " term " using " ident " where " manyIndent(handlerItem) : command

/-- One flattened `method => handler` entry, together with the resolved `List PathSeg` its pattern
resolves to (looked up via `urlTreeExt` for `using`-mode trees, computed directly by `processItems`
for self-contained/`urlTree` trees). -/
private structure MethodEntry where
  method  : TSyntax `ident
  handler : TSyntax `term
  segs    : List PathSeg

/-- One `as name` node, together with its resolved `List PathSeg`. -/
private structure NamedNode where
  name : TSyntax `ident
  segs : List PathSeg

/-- Whether a `routeItem`/`handlerItem` method identifier names one of the four supported HTTP
methods. -/
private def isKnownMethod (m : String) : Bool :=
  m = "get" || m = "post" || m = "put" || m = "delete"

/-- Walks a `routeItem` list, threading the accumulated parent `List PathSeg` down through nested
fragments, and flattens the tree into every `method => handler` entry (with its resolved segments)
and every `as`-named node (ditto) found anywhere in it. Shared by self-contained `application` and
`urlTree` -- the latter simply requires the resulting `methodEntries` to be empty (checked by its
own caller). Each fragment's local pattern text is parsed with `parsePattern` (never
`parsePattern!`) -- a `none` result is a macro-time `throwErrorAt` pointing at that fragment's own
string literal, never `parsePattern!`'s silent root-pattern fallback. -/
private partial def processItems (parentSegs : List PathSeg) (items : Array (TSyntax `routeItem)) :
    CommandElabM (Array MethodEntry × Array NamedNode) := do
  let mut methodEntries : Array MethodEntry := #[]
  let mut namedNodes : Array NamedNode := #[]
  for item in items do
    match item with
    | `(routeItem| $m:ident => $h:term) =>
      if !isKnownMethod m.getId.toString then
        throwErrorAt m
          s!"application: unknown HTTP method '{m.getId}' -- expected one of get, post, put, delete"
      methodEntries := methodEntries.push { method := m, handler := h, segs := parentSegs }
    | `(routeItem| $s:str $[as $n:ident]? { $subItems* }) =>
      let localStr := s.getString
      let localSegs ←
        match parsePattern localStr with
        | some segs => pure segs
        | none =>
          throwErrorAt s
            s!"application: malformed route pattern fragment {localStr.quote} -- expected a \
              leading '/', no doubled/trailing '/', and every capture written as ':name:Nat' or \
              ':name:String'"
      let resolvedSegs := parentSegs ++ localSegs
      if let some name := n then
        namedNodes := namedNodes.push { name := name, segs := resolvedSegs }
      let (subMethods, subNamed) ← processItems resolvedSegs subItems
      methodEntries := methodEntries ++ subMethods
      namedNodes := namedNodes ++ subNamed
    | _ => throwErrorAt item "application: unrecognized item"
  return (methodEntries, namedNodes)

/-- Erases capture names from a resolved `List PathSeg`, leaving only the shape (`.lit`/`.capture
_ kind`) that `HandlerType`/`dispatch` and `UrlType`/`renderUrl` actually match on -- capture names
are documentation-only downstream (`docs/application-macro-plan.md` §5). Used so the
duplicate-pattern check treats `/items/:id:Nat` and `/items/:pk:Nat` as the same route, which raw
`List PathSeg` equality (the reverted spike's check) would miss. -/
private def eraseNames (segs : List PathSeg) : List PathSeg :=
  segs.map fun
    | .lit s => .lit s
    | .capture _ kind => .capture "" kind

/-- Rejects two structural problems across the *whole* tree (not just siblings): two nodes sharing
an `as` name, and two different `as` names resolving to the same full pattern -- compared as a
name-erased *shape* (`eraseNames`), not raw `List PathSeg`, so `/items/:id:Nat` as `item` and
`/items/:pk:Nat` as `itemAgain` are correctly flagged as the same route despite differing capture
variable names. Both are macro-time errors pointing at the second (later) offending node. -/
private def checkNamedNodes (namedNodes : Array NamedNode) : CommandElabM Unit := do
  let mut seenNames : Std.HashMap String (List PathSeg) := {}
  let mut seenShapes : Array (List PathSeg × TSyntax `ident) := #[]
  for n in namedNodes do
    let nm := n.name.getId.toString
    if let some earlierSegs := seenNames[nm]? then
      throwErrorAt n.name
        s!"application: duplicate route name '{nm}' (already used for {renderPattern earlierSegs}) \
          -- every 'as' name must be unique across the whole tree"
    seenNames := seenNames.insert nm n.segs
    let shape := eraseNames n.segs
    if let some (_, earlierName) := seenShapes.find? (fun (s, _) => s == shape) then
      throwErrorAt n.name
        s!"application: 'as {nm}' resolves to the same pattern ({renderPattern n.segs}) as \
          'as {earlierName.getId}' -- two names for one pattern defeats the point of naming it"
    seenShapes := seenShapes.push (shape, n.name)

/-- Field-type text (`docs/application-macro-plan.md` §5): folds a resolved `List PathSeg` into
its reverse-routing field's arrow-type *text* directly (`"Nat → String"`, not
`"UrlType (parsePattern! ...)"`) -- avoids the instance-search transparency risk
`docs/routing-design-plan.md` §4 found for computed types. -/
private def fieldTypeText : List PathSeg → String
  | [] => "String"
  | .lit _ :: rest => fieldTypeText rest
  | .capture _ .nat :: rest => s!"Nat → {fieldTypeText rest}"
  | .capture _ .string :: rest => s!"String → {fieldTypeText rest}"

/-- `app` → `` `AppUrls ``: capitalizes the binder's first character and appends `Urls`. Deriving
from the user's chosen name (rather than a fixed literal, as the reverted spike used) is what lets
two self-contained `application` blocks coexist in one namespace. Only used by self-contained
`application` -- `urlTree` takes its struct's name directly from the user. -/
private def deriveUrlsName (appName : Name) : Name :=
  let s := appName.toString
  Name.mkSimple <|
    match s.toList with
    | [] => "Urls"
    | c :: cs => String.ofList (c.toUpper :: cs) ++ "Urls"

/-- `Urls` → `` `urls ``: lowercases the first character, the inverse of `deriveUrlsName`. Used to
name `urlTree`'s generated *value* (`def urls : Urls := { ... }`) from its struct's name, and to
derive that value's fully-qualified name back from a `using <UrlsType>` clause's struct reference
(same namespace, lowercased last component). -/
private def lowerFirst (n : Name) : Name :=
  match n with
  | .str pre s =>
    .str pre <|
      match s.toList with
      | [] => s
      | c :: cs => String.ofList (c.toLower :: cs)
  | n => n

/-- Parses `source` against the `command` category and `elabCommand`s the result -- the escape
hatch for splicing a `structure` declaration's dynamic field list (module docstring). -/
private def elabCommandFromString (source : String) : CommandElabM Unit := do
  let env ← getEnv
  match Parser.runParserCategory env `command source with
  | .ok stx => elabCommand stx
  | .error err => throwError err

/-- Builds the `structure <Name> where ...` source text shared by self-contained `application` and
`urlTree` -- one field per named node, using `fieldTypeText`. -/
private def structureSourceFor (structName : Name) (namedNodes : Array NamedNode) : String :=
  if namedNodes.isEmpty then
    s!"structure {structName} where"
  else
    let fieldLines := namedNodes.toList.map fun n => s!"  {n.name.getId} : {fieldTypeText n.segs}"
    s!"structure {structName} where\n" ++ String.intercalate "\n" fieldLines

/-- One entry recorded per named node in a `urlTree` block: which struct it belongs to (its
fully-qualified name), the node's own name, and its resolved `List PathSeg` -- enough for a later,
different-file `application ... using ...` invocation to look the pattern back up by name alone.
-/
private structure UrlTreeEntry where
  structName : Name
  nodeName   : Name
  segs       : List PathSeg
deriving Inhabited

/-- Persistent environment extension backing `urlTree`/`using` (module docstring's "Two commands,
one source of truth"): the state is a lookup table from `(structName, nodeName)` to the node's
resolved `List PathSeg`, rebuilt from every entry recorded across the current file and every
imported one -- this is exactly the mechanism Lean's own `deriving`/`simp`-set machinery uses to
share data across files, applied here to share pattern data instead. -/
initialize urlTreeExt :
    SimplePersistentEnvExtension UrlTreeEntry (Std.HashMap (Name × Name) (List PathSeg)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m e => m.insert (e.structName, e.nodeName) e.segs
    addImportedFn := fun ass => Id.run do
      let mut m : Std.HashMap (Name × Name) (List PathSeg) := {}
      for es in ass do
        for e in es do
          m := m.insert (e.structName, e.nodeName) e.segs
      return m
  }

/-- Records one named node's resolved pattern against `structName` in `urlTreeExt`, for later
lookup by an `application ... using ...` block elsewhere. -/
private def registerUrlTreeEntry (structName : Name) (n : NamedNode) : CommandElabM Unit :=
  modifyEnv fun env =>
    urlTreeExt.addEntry env { structName, nodeName := n.name.getId, segs := n.segs }

/-- Looks up `nodeIdent`'s resolved pattern against `structName` in `urlTreeExt` -- a macro-time
error, pointing at `nodeIdent` itself, if the name was never declared in that struct's `urlTree`
block (never a redeclaration or a silently-empty pattern). -/
private def lookupUrlTreeSegs (structName : Name) (nodeIdent : TSyntax `ident) :
    CommandElabM (List PathSeg) := do
  let env ← getEnv
  match (urlTreeExt.getState env)[(structName, nodeIdent.getId)]? with
  | some segs => pure segs
  | none =>
    throwErrorAt nodeIdent
      s!"application: '{nodeIdent.getId}' is not a name declared in {structName}'s urlTree block"

/-- Builds the `Route.get`/`.post`/`.put`/`.delete` term for one flattened `MethodEntry`, applying
its handler to `$ctxIdent $urlsIdent` first (§5's ordering: `ctx` then `urls`, before captures).
Shared by self-contained `application` and `application ... using ...`. -/
private def buildRouteElem (ctxIdent urlsIdent : Ident) (e : MethodEntry) :
    CommandElabM (TSyntax `term) := do
  let patLit := Syntax.mkStrLit (renderPattern e.segs)
  let handlerApplied ← `($(e.handler) $ctxIdent $urlsIdent)
  -- `Route.get`/`.post`/`.put`/`.delete` are literal-only macros (`Routing/Route.lean`), not
  -- plain `def`s -- reached only via their own quotation form here. `isKnownMethod` was already
  -- checked true for every entry that reaches this function.
  match e.method.getId.toString with
  | "get" => `(Route.get $patLit $handlerApplied)
  | "post" => `(Route.post $patLit $handlerApplied)
  | "put" => `(Route.put $patLit $handlerApplied)
  | "delete" => `(Route.delete $patLit $handlerApplied)
  | m => throwErrorAt e.method s!"application: unknown HTTP method '{m}'"

/-- Walks an `application ... using ...` tree. `currentSegs` is `none` at the top level (a bare
`method => handler` there is rejected -- it has no enclosing name to resolve a pattern from) and
`some segs` once inside a `name { ... }` node. Unlike `processItems`, nesting here is purely
cosmetic: a child's pattern is looked up independently by its own name (`lookupUrlTreeSegs`), never
extended from its parent's, since every name's pattern is already fully resolved by the `urlTree`
block that declared it. -/
private partial def processHandlerItems (structName : Name) (currentSegs : Option (List PathSeg))
    (items : Array (TSyntax `handlerItem)) : CommandElabM (Array MethodEntry) := do
  let mut methodEntries : Array MethodEntry := #[]
  for item in items do
    match item with
    | `(handlerItem| $m:ident => $h:term) =>
      match currentSegs with
      | none =>
        throwErrorAt item "application: a method entry must be inside a named node's braces"
      | some segs =>
        if !isKnownMethod m.getId.toString then
          throwErrorAt m
            s!"application: unknown HTTP method '{m.getId}' -- expected one of get, post, put, delete"
        methodEntries := methodEntries.push { method := m, handler := h, segs := segs }
    | `(handlerItem| $n:ident { $subItems* }) =>
      let segs ← lookupUrlTreeSegs structName n
      let subEntries ← processHandlerItems structName (some segs) subItems
      methodEntries := methodEntries ++ subEntries
    | _ => throwErrorAt item "application: unrecognized item"
  return methodEntries

elab_rules : command
  -- Self-contained: `application <name> : <CtxType> where <routeItem>*`.
  | `(application $name:ident : $ctxTy where $items*) => do
    let (methodEntries, namedNodes) ← processItems [] items
    checkNamedNodes namedNodes
    let urlsTypeIdent := mkIdent (deriveUrlsName name.getId)
    elabCommandFromString (structureSourceFor urlsTypeIdent.getId namedNodes)
    let ctxIdent := mkIdent `ctx
    let urlsIdent := mkIdent `urls
    let urlsFields ← namedNodes.mapM fun n => do
      let patLit := Syntax.mkStrLit (renderPattern n.segs)
      `(routeUrl $patLit)
    let urlsNames := namedNodes.map (·.name)
    let routeElems ← methodEntries.mapM (buildRouteElem ctxIdent urlsIdent)
    let appDef ← `(command|
      def $name : Application $ctxTy $urlsTypeIdent :=
        let $urlsIdent:ident : $urlsTypeIdent := { $[$urlsNames:ident := $urlsFields],* }
        { urls := $urlsIdent, handler := fun ($ctxIdent : $ctxTy) => toHandler [ $routeElems,* ] })
    elabCommand appDef
  -- `urlTree <Name> where <routeItem>*` -- patterns and names only (module docstring).
  | `(urlTree $name:ident where $items*) => do
    let (methodEntries, namedNodes) ← processItems [] items
    if let some e := methodEntries[0]? then
      throwErrorAt e.method
        "urlTree: no methods here -- urlTree only declares patterns and names, never dispatch; \
          attach handlers via a separate 'application ... using ...' block"
    checkNamedNodes namedNodes
    elabCommandFromString (structureSourceFor name.getId namedNodes)
    let structName := (← getCurrNamespace) ++ name.getId
    for n in namedNodes do
      registerUrlTreeEntry structName n
    let valueIdent := mkIdent (lowerFirst name.getId)
    let urlsFields ← namedNodes.mapM fun n => do
      let patLit := Syntax.mkStrLit (renderPattern n.segs)
      `(routeUrl $patLit)
    let urlsNames := namedNodes.map (·.name)
    let valueDef ← `(command|
      def $valueIdent : $name := { $[$urlsNames:ident := $urlsFields],* })
    elabCommand valueDef
  -- `application <name> : <CtxType> using <UrlsType> where <handlerItem>*` (module docstring).
  | `(application $name:ident : $ctxTy using $urlsTypeIdent:ident where $items*) => do
    -- `urlsTypeIdent.getId` is the identifier *as written* (possibly relative to an open
    -- namespace) -- `urlTreeExt` is keyed by fully-qualified names (`getCurrNamespace ++ ...` at
    -- the point `urlTree` ran), so the reference must be resolved the same way, not trusted as
    -- already-qualified text.
    let structName ← resolveGlobalConstNoOverload urlsTypeIdent
    let valueIdent := mkIdent (lowerFirst structName)
    let methodEntries ← processHandlerItems structName none items
    let ctxIdent := mkIdent `ctx
    let routeElems ← methodEntries.mapM (buildRouteElem ctxIdent valueIdent)
    let appDef ← `(command|
      def $name : Application $ctxTy $urlsTypeIdent :=
        { urls := $valueIdent, handler := fun ($ctxIdent : $ctxTy) => toHandler [ $routeElems,* ] })
    elabCommand appDef

/-! ## Tests

`Routing` stays app-framework-agnostic (`Routing.lean`'s module docstring) -- it can't depend on
`Todo`/`SQLite`, so these use a toy `Nat` standing in for a context, mirroring the shape a real
consumer supplies without actually depending on one.

`Application.handler` is fixed at `Ctx → StatelessHandler`, not generic over a toy `result` type
the way the reverted spike's `Route result`/`dispatchTable` tests were -- so exercising the
macro's *actual* flattened output here means running real `Request`/`Response` values through it,
not just comparing a `String` return value. `Std.Http.Test.Helpers` (part of the toolchain, used by
`Std.Http`'s own server tests) gives exactly that: a mock connection, request-string builders
(`mkGet`/`mkPost`), and response assertions (`assertContains`) -- reused here rather than
hand-rolling `Body.Stream`/`ContextAsync` plumbing. -/

open Std.Http.Internal.Test
open Std.Async

private def rootHandler {Urls : Type} (_ctx : Nat) (_urls : Urls) (_req : Request Body.Stream) :
    ContextAsync (Response Body.Any) :=
  Response.ok |>.text "root"

private def itemGetHandler {Urls : Type} (_ctx : Nat) (_urls : Urls) (id : Nat)
    (_req : Request Body.Stream) : ContextAsync (Response Body.Any) :=
  Response.ok |>.text s!"get-item-{id}"

private def itemPutHandler {Urls : Type} (_ctx : Nat) (_urls : Urls) (id : Nat)
    (_req : Request Body.Stream) : ContextAsync (Response Body.Any) :=
  Response.ok |>.text s!"put-item-{id}"

private def specialHandler {Urls : Type} (_ctx : Nat) (_urls : Urls)
    (_req : Request Body.Stream) : ContextAsync (Response Body.Any) :=
  Response.ok |>.text "special"

private def badArityHandler {Urls : Type} (_ctx : Nat) (_urls : Urls) (_id : Nat) (_extra : String)
    (_req : Request Body.Stream) : ContextAsync (Response Body.Any) :=
  Response.ok |>.text "oops"

/-- `mkGet`/`mkPost` are provided by `Std.Http.Test.Helpers`; `PUT`/`DELETE` aren't, so build them
the same way. -/
private def mkPut (path : String) : String :=
  s!"PUT {path} HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 0\x0d\n\x0d\n"

private def mkDelete (path : String) : String :=
  s!"DELETE {path} HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 0\x0d\n\x0d\n"

-- Main positive regression: 2-3 levels of nesting, a captured node with two methods sharing one
-- written pattern (`PUT`/`GET` on `/items/:id:Nat`), a same-arity literal/capture collision
-- (`/items/special` vs `/items/:id:Nat`) exercised through the macro's *actual* flattened dispatch
-- output, and an `as`-named node with a method entry directly on it *and* nested child fragments
-- (`/todos` below).
namespace PositiveTest

application testApp : Nat where
  "/" as root { get => rootHandler }
  "/items" {
    "/:id:Nat" as item {
      get => itemGetHandler
      put => itemPutHandler
    }
    "/special" as special { get => specialHandler }
  }
  "/todos" as todos {
    post => rootHandler
    "/:id:Nat" as todo { get => itemGetHandler }
  }

#guard testApp.urls.root = "/"
#guard testApp.urls.item 7 = "/items/7"
#guard testApp.urls.special = "/items/special"
#guard testApp.urls.todos = "/todos"
#guard testApp.urls.todo 3 = "/todos/3"

private def testHandler : TestHandler := (testApp.handler 0).onRequest

#eval runGroup "PositiveTest" do
  checkClose "root" (mkGet "/") testHandler (assertContains · "root")
  checkClose "item get" (mkGet "/items/7") testHandler (assertContains · "get-item-7")
  checkClose "item put" (mkPut "/items/7") testHandler (assertContains · "put-item-7")
  -- The literal `/items/special` must win over the capture `/items/:id:Nat` for the same method.
  checkClose "special beats capture" (mkGet "/items/special") testHandler (assertContains · "special")
  checkClose "todos: method on a named node with children" (mkPost "/todos" "") testHandler
    (assertContains · "root")
  checkClose "todos: nested child nested under it" (mkGet "/todos/3") testHandler
    (assertContains · "get-item-3")
  checkClose "unmatched route falls through to 404" (mkGet "/nope") testHandler
    (fun r => assertStatus r "HTTP/1.1 404")

end PositiveTest

-- A wrong-arity handler is rejected with the same quality of `HandlerType`-mismatch error a
-- hand-written `Route.put "..." handler` call would give.
namespace BadArityTest

/--
error: Application type mismatch: The argument
  badArityHandler ctx urls
has type
  Nat → String → Request Body.Stream → ContextAsync (Response Body.Any)
but is expected to have type
  HandlerType (parsePattern! "/items/:id:Nat") Result
in the application
  Route.put "/items/:id:Nat" (badArityHandler ctx urls)
-/
#guard_msgs in
application badArityApp : Nat where
  "/" as root { get => rootHandler }
  "/items/:id:Nat" as item { put => badArityHandler }
  "/items/special" as special { get => specialHandler }

end BadArityTest

-- Malformed fragment text is a macro-time error, never `parsePattern!`'s silent root-pattern
-- fallback.
namespace MalformedPatternTest

/--
error: application: malformed route pattern fragment "items/:id:Nat" -- expected a leading '/', no doubled/trailing '/', and every capture written as ':name:Nat' or ':name:String'
-/
#guard_msgs in
application malformedApp : Nat where
  "/" as root { get => rootHandler }
  "items/:id:Nat" as item { get => itemGetHandler }
  "/items/special" as special { get => specialHandler }

end MalformedPatternTest

-- Two nodes with the same `as` name anywhere in the tree (not just siblings) is a macro-time
-- error, not a worse-quality redeclaration failure.
namespace DuplicateNameTest

/--
error: application: duplicate route name 'item' (already used for /items/:id:Nat) -- every 'as' name must be unique across the whole tree
-/
#guard_msgs in
application duplicateNameApp : Nat where
  "/" as root { get => rootHandler }
  "/items/:id:Nat" as item { get => itemGetHandler }
  "/items/other/:id:Nat" as item { get => itemGetHandler }

end DuplicateNameTest

-- Two different `as` names resolving to the same full pattern (same literal/capture-kind shape)
-- is rejected too.
namespace DuplicatePatternTest

/--
error: application: 'as itemAgain' resolves to the same pattern (/items/:id:Nat) as 'as item' -- two names for one pattern defeats the point of naming it
-/
#guard_msgs in
application duplicatePatternApp : Nat where
  "/" as root { get => rootHandler }
  "/items/:id:Nat" as item { get => itemGetHandler }
  "/items" { "/:id:Nat" as itemAgain { put => itemPutHandler } }

end DuplicatePatternTest

-- Two names resolving to the same shape via *different* capture variable names -- the
-- name-erasure fix, confirming what raw `List PathSeg` equality (the reverted spike's check)
-- would miss.
namespace DuplicatePatternCaptureNameTest

/--
error: application: 'as itemAgain' resolves to the same pattern (/items/:pk:Nat) as 'as item' -- two names for one pattern defeats the point of naming it
-/
#guard_msgs in
application duplicateCaptureApp : Nat where
  "/" as root { get => rootHandler }
  "/items/:id:Nat" as item { get => itemGetHandler }
  "/items/:pk:Nat" as itemAgain { get => itemGetHandler }

end DuplicatePatternCaptureNameTest

-- Edge case: zero `as`-named nodes anywhere -- the generated `structure` has no fields, and the
-- empty anonymous-constructor splice `{ }` must still elaborate.
namespace EmptyUrlsTest

application emptyUrlsApp : Nat where
  "/" { get => rootHandler }
  "/items/:id:Nat" { get => itemGetHandler }

#eval runGroup "EmptyUrlsTest" do
  checkClose "root" (mkGet "/") (emptyUrlsApp.handler 0).onRequest (assertContains · "root")

end EmptyUrlsTest

-- Edge case: zero method entries anywhere -- the generated `toHandler [...]` list is empty, and
-- every request falls through to `notFound`.
namespace EmptyMethodsTest

application emptyMethodsApp : Nat where
  "/" as root { }

#guard emptyMethodsApp.urls.root = "/"

#eval runGroup "EmptyMethodsTest" do
  checkClose "no routes, always 404" (mkGet "/") (emptyMethodsApp.handler 0).onRequest
    (fun r => assertStatus r "HTTP/1.1 404")

end EmptyMethodsTest

-- Two self-contained `application` blocks in the *same* namespace, each generating its own
-- `<Name>Urls` struct/def -- the direct check of deriving generated names from the binder (rather
-- than the reverted spike's fixed `urls`/`routes` idents) removing the multi-block collision the
-- old version needed per-test `namespace` isolation to avoid.
namespace TwoBlocksTest

application app1 : Nat where
  "/" as root { get => rootHandler }

application app2 : Nat where
  "/" as root { get => rootHandler }

#guard app1.urls.root = "/"
#guard app2.urls.root = "/"

end TwoBlocksTest

-- `urlTree` + `application ... using ...`'s cross-file regression lives in
-- `Routing/ApplicationUsingTest.lean`, not here: `urlTreeExt` (the persistent environment
-- extension backing the split) can't be *used* in the same module it's `initialize`d in --
-- confirmed directly ("cannot evaluate `[init]` declaration ... in the same module"), and this is
-- in fact exactly the real Todo/Main split's shape (the extension lives in this file, `urlTree`
-- runs in one importer, `application ... using ...` runs in another).

-- `urlTree` itself rejects a method entry -- it only ever declares patterns and names. This one
-- case *can* stay here, since the check runs (and throws) before anything touches `urlTreeExt`.
namespace UrlTreeNoMethodsTest

/--
error: urlTree: no methods here -- urlTree only declares patterns and names, never dispatch; attach handlers via a separate 'application ... using ...' block
-/
#guard_msgs in
urlTree BadUrlTree where
  "/" as root { get => rootHandler }

end UrlTreeNoMethodsTest

end Routing
