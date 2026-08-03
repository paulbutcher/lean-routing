import Lean
import Routing.Handler

/-!
`routeTable! App [ name := "pattern", ... ]`: generates, for each row, a field of a generated
`App.Patterns` structure (`List Routing.PathSeg`, the parsed pattern) and the corresponding field
of `App.patterns`, and a field of a generated `App.Links` structure (`Routing.LinkType` of the
parsed pattern -- `Handler.lean`) and the corresponding field of `App.links` (built with
`Routing.linkFor`).

Every pattern is parsed exactly once, right here, at the `routeTable!` row that declares it --
a malformed pattern is a compile error at that row. `App.patterns`, consumed directly by
`Route.get`/`.post`/etc. (`Route.lean`), is how a route built from this table avoids re-parsing
(and so re-validating) the same pattern string a second time.

A row can also *mount* another `routeTable!`-generated app under a literal path prefix
(`name := mount "prefix" SubApp`), nesting `SubApp`'s whole `Patterns`/`Links` shape --
recursively, to whatever depth `SubApp` itself mounts further apps -- under `App.patterns.name`/
`App.links.name`. Prefixes must be literal (no `:name:Kind` captures): `HandlerType`/`LinkType`
only add a function arrow for `.capture` segments, so a literal prefix leaves a mounted route's
required handler type unchanged from what it would be for the un-mounted pattern -- no glue code
needed at the call site that builds the actual `Route`.
-/

namespace Routing

open Lean Lean.Elab Lean.Elab.Command

declare_syntax_cat routeTableRow
syntax ident ":=" str : routeTableRow
syntax ident ":=" "mount" str ident : routeTableRow

/-- The bracketed, comma-separated row list, factored out into its own named parser (rather than
inlined into `routeTableCmd` below) because the `,*,?` sepBy-with-optional-trailing-comma sugar
only elaborates inside a `syntax name := ...` alias, matching the same shape core uses for e.g.
`rwRuleSeq` (`Init/Tactics.lean`). -/
syntax routeTableRows := "[" withoutPosition(routeTableRow,*,?) "]"

/-- See the module docstring. `App` names the generated `App.Patterns`/`App.patterns`/
`App.Links`/`App.links` declarations. -/
syntax (name := routeTableCmd) "routeTable!" ident routeTableRows : command

/-- A row is either a plain pattern (`.leaf`) or a mount of another app's whole table under a
literal prefix (`.mount`). -/
private inductive RowKind where
  | leaf (pat : TSyntax `str)
  | mount (prefixPat : TSyntax `str) (sub : Ident)

private def qualifyPlain (src : Syntax) (appName : Name) (suffix : Name) : Ident :=
  mkIdentFrom src (appName ++ suffix)

/-- Parses `src` as a `command` and elaborates it, blaming `ref` (the `routeTable!` invocation) on
a parse failure. See the "3/4" comment below for why generated commands go through source text
rather than `Syntax` quotation here. -/
private def elabCommandFromSource (ref : Syntax) (src : String) : CommandElabM Unit := do
  match Lean.Parser.runParserCategory (← getEnv) `command src with
  | .error msg => throwErrorAt ref msg
  | .ok stx => elabCommand stx

/-- Lean *source text* for one already-parsed `PathSeg`, e.g. `.lit "todos"` renders as
`Routing.PathSeg.lit "todos"`. Used (below) to splice an already-parsed, already-in-normal-form
`List PathSeg` *literal* into generated code, rather than a pattern-string call the elaborator
would still have to reduce. -/
private def segSrc : PathSeg → String
  | .lit s => s!"Routing.PathSeg.lit {s.quote}"
  | .capture name .nat => s!"Routing.PathSeg.capture {name.quote} .nat"
  | .capture name .string => s!"Routing.PathSeg.capture {name.quote} .string"

/-- Parses `pat`'s string value with the real `Routing.parsePattern` (so this can never drift from
what `Main.lean`'s dispatch table itself accepts). `throwErrorAt pat` on a malformed pattern
directly: this runs in `CommandElabM`, building source text for codegen rather than elaborating an
object-level term, so plain `parsePattern` plus an explicit match is the natural way to get
"malformed pattern is a macro-time elaboration error" here. -/
private def parseSegsOrThrow (pat : TSyntax `str) : CommandElabM (List PathSeg) :=
  match parsePattern pat.getString with
  | some segs => pure segs
  | none => throwErrorAt pat s!"invalid route pattern {pat.getString.quote}"

/-- Renders already-parsed segments back to Lean source text for a `List PathSeg` literal. -/
private def segsListSrc (segs : List PathSeg) : String :=
  "[" ++ String.intercalate ", " (segs.map segSrc) ++ "]"

private def segsSrcFor (pat : TSyntax `str) : CommandElabM String :=
  return segsListSrc (← parseSegsOrThrow pat)

/-- Like `segsSrcFor`, but for a `mount` row's prefix: additionally rejects any `.capture`
segment, since mount prefixes are literal-only (see module docstring). -/
private def prefixSegsSrcFor (pat : TSyntax `str) : CommandElabM String := do
  let segs ← parseSegsOrThrow pat
  if segs.any (fun | .capture .. => true | .lit _ => false) then
    throwErrorAt pat s!"mount prefix must not contain captures (got {pat.getString.quote}); captured mount prefixes are not yet supported"
  pure (segsListSrc segs)

/-- Resolves `sub` (a `mount` row's app identifier) to its generated `Patterns` structure,
accounting for the current namespace/opens the same way a plain identifier typed by the user
would resolve. Fails loudly if `sub` doesn't name a `routeTable!`-generated app, rather than
risking `getStructureFields` silently treating a non-structure as having no fields. -/
private def resolveSubPatterns (sub : Ident) : CommandElabM Name := do
  let patternsId := mkIdentFrom sub (sub.getId ++ `Patterns)
  let name ← resolveGlobalConstNoOverload patternsId
  unless isStructure (← getEnv) name do
    throwErrorAt sub s!"'{sub.getId}' is not a routeTable!-generated app (no structure '{name}')"
  pure name

/-- `some structName` if `field` of `structName` is itself a `routeTable!`-generated `Patterns`-
shaped structure (i.e. `field` came from a `mount` row when `structName`'s table was declared);
`none` if it's a leaf field (`List Routing.PathSeg`). Reads the field's type off its projection
function's declared type -- `∀ (self : structName), FieldType` -- rather than the field's *value*,
since this only needs to classify the shape, not evaluate anything. -/
private def mountedFieldStruct? (env : Environment) (structName field : Name) :
    CommandElabM (Option Name) := do
  let some info := getFieldInfo? env structName field
    | throwError "internal error: field '{field}' not found on '{structName}'"
  let some ci := env.find? info.projFn
    | throwError "internal error: projection '{info.projFn}' not found"
  let .forallE _ _ body _ := ci.type
    | throwError "internal error: projection '{info.projFn}' has unexpected type"
  let some head := body.getAppFn.constName?
    | throwError "internal error: field '{field}' has unexpected type shape"
  if head == `List then
    pure none
  else if isStructure env head then
    pure (some head)
  else
    throwError "internal error: field '{field}' has unrecognized type head '{head}'"

/-- Recursively walks `structName` (a `Patterns`-shaped structure, reachable via `accessSrc` --
Lean source text for a value of that type, e.g. `"BlogRoutes.patterns"`), building the
`field := ..., ...` source for both the prefixed `Patterns` value and the corresponding `Links`
value. Recurses into fields that are themselves mounted sub-tables (`mountedFieldStruct?`), so a
mount nests to whatever depth the sub-table itself nests -- `prefixSegsSrc` is the same at every
depth, since a mount's prefix applies to everything under it. Links values are computed from the
*Patterns* side (`Routing.linkFor` applied to the prefixed segs), same as a leaf row does; there's
no pre-built link function to unwrap. -/
private partial def mountFieldsSrc (env : Environment) (structName : Name) (accessSrc : String)
    (prefixSegsSrc : String) : CommandElabM (String × String) := do
  let mut patFields : Array String := #[]
  let mut linkFields : Array String := #[]
  for f in getStructureFields env structName do
    let childAccessSrc := s!"{accessSrc}.{f}"
    match ← mountedFieldStruct? env structName f with
    | none =>
        patFields := patFields.push s!"{f} := {prefixSegsSrc} ++ {childAccessSrc}"
        linkFields := linkFields.push s!"{f} := Routing.linkFor ({prefixSegsSrc} ++ {childAccessSrc})"
    | some nestedStructName =>
        let (nestedPat, nestedLink) ← mountFieldsSrc env nestedStructName childAccessSrc prefixSegsSrc
        patFields := patFields.push (s!"{f} := " ++ "{ " ++ nestedPat ++ " }")
        linkFields := linkFields.push (s!"{f} := " ++ "{ " ++ nestedLink ++ " }")
  pure (String.intercalate ", " patFields.toList, String.intercalate ", " linkFields.toList)

/-- One row's generated field: its `Patterns`/`Links` field type and value, as Lean source text.
Computed once per row (`rowGenFor`), reused below by both `Patterns` (3/4) and `Links` (5/6). -/
private structure RowGen where
  name : Ident
  patternsFieldTypeSrc : String
  patternsValueSrc : String
  linksFieldTypeSrc : String
  linksValueSrc : String

private def rowGenFor (env : Environment) (name : Ident) : RowKind → CommandElabM RowGen
  | .leaf pat => do
      let segsSrc ← segsSrcFor pat
      pure
        { name
          patternsFieldTypeSrc := "List Routing.PathSeg"
          patternsValueSrc := segsSrc
          linksFieldTypeSrc := s!"Routing.LinkType {segsSrc}"
          linksValueSrc := s!"Routing.linkFor {segsSrc}" }
  | .mount prefixPat sub => do
      let prefixSegsSrc ← prefixSegsSrcFor prefixPat
      let subPatterns ← resolveSubPatterns sub
      let subApp := subPatterns.getPrefix
      let (patFieldsSrc, linkFieldsSrc) ←
        mountFieldsSrc env subPatterns s!"{subApp}.patterns" prefixSegsSrc
      pure
        { name
          patternsFieldTypeSrc := toString subPatterns
          patternsValueSrc := "{ " ++ patFieldsSrc ++ " }"
          linksFieldTypeSrc := toString (subApp ++ `Links)
          linksValueSrc := "{ " ++ linkFieldsSrc ++ " }" }

elab_rules : command
  | `(routeTable! $appId:ident [ $rows,* ]) => do
    let appName := appId.getId
    -- 1. Destructure each row into (name, row kind) -- a plain pattern (`RowKind.leaf`) or a
    -- mount of another app under a literal prefix (`RowKind.mount`).
    let entries ← rows.getElems.mapM fun row => do
      match row with
      | `(routeTableRow| $name:ident := $pat:str) => pure (name, RowKind.leaf pat)
      | `(routeTableRow| $name:ident := mount $prefixPat:str $sub:ident) =>
          pure (name, RowKind.mount prefixPat sub)
      | _ => throwUnsupportedSyntax

    -- 2. Reject a name declared twice -- each name denotes exactly one pattern or mount,
    -- regardless of row kind.
    let mut seen : Std.HashMap Name Syntax := {}
    for (name, _) in entries do
      if let some prior := seen[name.getId]? then
        throwErrorAt name s!"route name '{name.getId}' already declared at {prior}"
      seen := seen.insert name.getId name

    -- Compute each row's field type/value source once here (`rowGenFor`), reused below by both
    -- `Patterns` (3/4) and `Links` (5/6) -- rather than each recomputing it separately.
    let env ← getEnv
    let rowGens ← entries.mapM fun (name, kind) => rowGenFor env name kind

    -- 3/4. `structure App.Patterns where name : List Routing.PathSeg ...` and
    -- `def App.patterns : App.Patterns := { name := [PathSeg literal], ... }`.
    --
    -- Built as source text and reparsed (`elabCommandFromSource` above) rather than spliced via
    -- `$[...]*` quotation antiquotations: `structure`'s field list (`structFields`, `Parser/
    -- Command.lean`) is a `manyIndent`, which -- unlike the plain `sepBy` behind `$xs,*`
    -- splicing -- depends on real column/indentation tracking that synthetic, macro-built
    -- `Syntax` doesn't carry, so the antiquotation form silently parses as a zero-field
    -- structure. (Same technique reused below for `App.Links`/`App.links`.)
    --
    -- A leaf row's field is typed by an already-parsed `List PathSeg` *literal* (`segsSrcFor`),
    -- not a pattern-string call for the elaborator to reduce, so a `Route` built from a field
    -- (`Route.get`/`.post`/etc., `Route.lean`) needs no further parsing. A mount row's field
    -- reuses the sub-app's own `Patterns` structure type (`rowGenFor`'s `.mount` case) -- a
    -- literal prefix never changes a `Patterns` field's type, only its value.
    let patternsTypeIdent := qualifyPlain appId appName `Patterns
    let patternsValIdent := qualifyPlain appId appName `patterns
    let patternFieldsSrc := String.intercalate "\n  " <|
      rowGens.toList.map fun g => s!"{g.name.getId} : {g.patternsFieldTypeSrc}"
    elabCommandFromSource appId
      s!"structure {patternsTypeIdent.getId} where\n  {patternFieldsSrc}"

    let patternValFieldsSrc := String.intercalate ", " <|
      rowGens.toList.map fun g => s!"{g.name.getId} := {g.patternsValueSrc}"
    elabCommandFromSource appId <|
      "def " ++ toString patternsValIdent.getId ++ " : " ++ toString patternsTypeIdent.getId ++
        " := { " ++ patternValFieldsSrc ++ " }"

    -- 5/6. `structure App.Links where name : LinkType [PathSeg literal] ...` and
    -- `def App.links : App.Links := { name := linkFor [PathSeg literal], ... }`.
    --
    -- Same source-text-and-reparse technique as 3/4 above (see that comment for why). A leaf
    -- row's field is typed by `LinkType [PathSeg literal]`, not `LinkType App.Patterns.name`: a
    -- zero-capture field has no argument application to force reduction through a *reference* to
    -- the `Patterns` field, so it must splice the literal (`rowGens`, computed once above)
    -- directly. A mount row's field reuses the sub-app's own `Links` structure type, for the same
    -- reason its `Patterns` field does.
    let linksTypeIdent := qualifyPlain appId appName `Links
    let linksValIdent := qualifyPlain appId appName `links
    let structFieldsSrc := String.intercalate "\n  " <|
      rowGens.toList.map fun g => s!"{g.name.getId} : {g.linksFieldTypeSrc}"
    elabCommandFromSource appId
      s!"structure {linksTypeIdent.getId} where\n  {structFieldsSrc}"

    let valFieldsSrc := String.intercalate ", " <|
      rowGens.toList.map fun g => s!"{g.name.getId} := {g.linksValueSrc}"
    elabCommandFromSource appId <|
      "def " ++ toString linksValIdent.getId ++ " : " ++ toString linksTypeIdent.getId ++
        " := { " ++ valFieldsSrc ++ " }"

end Routing
