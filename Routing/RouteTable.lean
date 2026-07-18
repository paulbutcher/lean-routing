import Lean
import Routing.Handler

/-!
`routeTable! App [ name := "pattern", ... ]`: generates, for each row, a field of a generated
`App.Patterns` structure (`List Routing.PathSeg`, the parsed pattern) and the corresponding field
of `App.patterns`, and a field of a generated `App.Links` structure (`Routing.LinkType` of the
parsed pattern -- `Handler.lean`) and the corresponding field of `App.links` (built with
`Routing.linkFor`). This is exactly `Todo/Links.lean`'s hand-written shape from the routing
design plan's reverse-routing spike, automated.

Every pattern is parsed exactly once, right here, at the `routeTable!` row that declares it --
a malformed pattern is a compile error at that row. `App.patterns`, consumed directly by
`Route.get`/`.post`/etc. (`Route.lean`), is how a route built from this table avoids re-parsing
(and so re-validating) the same pattern string a second time.
-/

namespace Routing

open Lean Lean.Elab Lean.Elab.Command

declare_syntax_cat routeTableRow
syntax ident ":=" str : routeTableRow

/-- The bracketed, comma-separated row list, factored out into its own named parser (rather than
inlined into `routeTableCmd` below) because the `,*,?` sepBy-with-optional-trailing-comma sugar
only elaborates inside a `syntax name := ...` alias, matching the same shape core uses for e.g.
`rwRuleSeq` (`Init/Tactics.lean`). -/
syntax routeTableRows := "[" withoutPosition(routeTableRow,*,?) "]"

/-- See the module docstring. `App` names the generated `App.Patterns`/`App.patterns`/
`App.Links`/`App.links` declarations. -/
syntax (name := routeTableCmd) "routeTable!" ident routeTableRows : command

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
what `Main.lean`'s dispatch table itself accepts), then renders the result back to Lean source
text for a `List PathSeg` literal. `throwErrorAt pat` on a malformed pattern directly: this runs in
`CommandElabM`, building source text for codegen rather than elaborating an object-level term, so
plain `parsePattern` plus an explicit match is the natural way to get "malformed pattern is a
macro-time elaboration error" here. -/
private def segsSrcFor (pat : TSyntax `str) : CommandElabM String := do
  match parsePattern pat.getString with
  | some segs => pure <| "[" ++ String.intercalate ", " (segs.map segSrc) ++ "]"
  | none => throwErrorAt pat s!"invalid route pattern {pat.getString.quote}"

elab_rules : command
  | `(routeTable! $appId:ident [ $rows,* ]) => do
    let appName := appId.getId
    -- 1. Destructure each row into (pattern string literal, name).
    let entries ← rows.getElems.mapM fun row => do
      match row with
      | `(routeTableRow| $name:ident := $pat:str) => pure (pat, name)
      | _ => throwUnsupportedSyntax

    -- 2. Reject a name declared twice -- each name denotes exactly one pattern.
    let mut seen : Std.HashMap Name Syntax := {}
    for (_, name) in entries do
      if let some prior := seen[name.getId]? then
        throwErrorAt name s!"route name '{name.getId}' already declared at {prior}"
      seen := seen.insert name.getId name

    -- Parse each pattern once here, reused below by both `Patterns` (3/4) and `Links` (5/6) --
    -- rather than each calling `segsSrcFor` (and so re-running `parsePattern`) separately.
    let segsSrcs ← entries.toList.mapM fun (pat, name) => do
      pure (name, ← segsSrcFor pat)

    -- 3/4. `structure App.Patterns where name : List Routing.PathSeg ...` and
    -- `def App.patterns : App.Patterns := { name := [PathSeg literal], ... }`.
    --
    -- Three things worth flagging:
    --
    -- * Built as source text and reparsed (`elabCommandFromSource` above) rather than spliced via
    --   `$[...]*` quotation antiquotations: `structure`'s field list (`structFields`, `Parser/
    --   Command.lean`) is a `manyIndent`, which -- unlike the plain `sepBy` behind `$xs,*`
    --   splicing -- depends on real column/indentation tracking that synthetic, macro-built
    --   `Syntax` doesn't carry, so the antiquotation form silently parses as a zero-field
    --   structure. Confirmed by a throwaway spike (`lean_diagnostic_messages` against exactly
    --   this quotation) before falling back to this approach, matching `docs/routing-design-
    --   plan.md`'s own spike-first methodology.
    -- * The same technique is reused below (5/6) for `App.Links`/`App.links`.
    -- * Fields are typed by an already-parsed `List PathSeg` *literal* (`segsSrcFor`), not a
    --   pattern-string call for the elaborator to reduce -- this is the field
    --   `Route.get`/`.post`/`.put`/`.delete` (`Route.lean`) are meant to consume: a `List PathSeg`
    --   already known well-formed, so building a `Route` from it needs no further parsing (and so
    --   has no failure mode of its own).
    let patternsTypeIdent := qualifyPlain appId appName `Patterns
    let patternsValIdent := qualifyPlain appId appName `patterns
    let patternFieldsSrc := String.intercalate "\n  " <|
      segsSrcs.map fun (name, _) => s!"{name.getId} : List Routing.PathSeg"
    elabCommandFromSource appId
      s!"structure {patternsTypeIdent.getId} where\n  {patternFieldsSrc}"

    let patternValFieldsSrc := String.intercalate ", " <|
      segsSrcs.map fun (name, segsSrc) => s!"{name.getId} := {segsSrc}"
    elabCommandFromSource appId <|
      "def " ++ toString patternsValIdent.getId ++ " : " ++ toString patternsTypeIdent.getId ++
        " := { " ++ patternValFieldsSrc ++ " }"

    -- 5/6. `structure App.Links where name : LinkType [PathSeg literal] ...` and
    -- `def App.links : App.Links := { name := linkFor [PathSeg literal], ... }`.
    --
    -- Same source-text-and-reparse technique as 3/4 above (see that comment for why), plus one
    -- more wrinkle here:
    --
    -- * `LinkType [PathSeg literal]`, not `LinkType App.Patterns.name`: a zero-capture field
    --   (`toggleAll`, `clearCompleted`, ...) has no argument application to force reduction
    --   through a *reference* to the `Patterns` field, so real usage (`Todo/Views.lean`'s
    --   `hxPost := links.toggleAll` against an `Option String` field, via the `Coe String
    --   (Option String)` instance) failed to typecheck against that form -- caught by building
    --   `Todo/Links.lean` against this macro for real (`docs/todo-app-plan.md`'s own "verify
    --   end-to-end, not just typechecked" standard), not by this file's own `#guard`s in
    --   isolation. Splicing the literal again here (`segsSrcs`, computed once above) sidesteps it.
    let linksTypeIdent := qualifyPlain appId appName `Links
    let linksValIdent := qualifyPlain appId appName `links
    let structFieldsSrc := String.intercalate "\n  " <|
      segsSrcs.map fun (name, segsSrc) => s!"{name.getId} : Routing.LinkType {segsSrc}"
    elabCommandFromSource appId
      s!"structure {linksTypeIdent.getId} where\n  {structFieldsSrc}"

    let valFieldsSrc := String.intercalate ", " <|
      segsSrcs.map fun (name, segsSrc) => s!"{name.getId} := Routing.linkFor {segsSrc}"
    elabCommandFromSource appId <|
      "def " ++ toString linksValIdent.getId ++ " : " ++ toString linksTypeIdent.getId ++
        " := { " ++ valFieldsSrc ++ " }"

end Routing
