import Lean.Environment
import Lean.Util.FoldConsts
import Lean.Data.Json
import Lean.Elab.Import

/-!
Read-only documentation exporter. It reads the declaration bodies in fresh
compiler artifacts and records their named dependencies. It neither elaborates
new mathematical declarations nor treats this report as a proof certificate.
The source build and axiom audit are separate requirements.

The graph records syntactic constant references, not a minimal semantic
dependency graph. Structural references can contain legitimate cycles between
an inductive type and its constructors. Compiler-only `extraConstNames` are not
kernel declarations and are excluded. Each process must read a bounded batch:
compacted regions are intentionally left alive until process exit.
-/

open Lean

def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def structuralDependencies : ConstantInfo → Array Name
  | .inductInfo value => (value.all ++ value.ctors).toArray
  | .ctorInfo value => #[value.induct]
  | .recInfo value => value.rules.foldl
      (fun names rule => names ++ #[rule.ctor] ++ rule.rhs.getUsedConstants)
      value.all.toArray
  | _ => #[]

def namesJson (names : Array Name) : Json :=
  toJson ((names.toList.eraseDups.map Name.toString).mergeSort (· ≤ ·))

def declarationJson (moduleName : String) (info : ConstantInfo) : Json :=
  Json.mkObj [
    ("record", toJson "declaration"),
    ("module", toJson moduleName),
    ("name", toJson info.name.toString),
    ("kind", toJson (declarationKind info)),
    ("unsafe", toJson info.isUnsafe),
    ("partial", toJson info.isPartial),
    ("has_body", toJson (info.value? true).isSome),
    ("type_dependencies", namesJson info.type.getUsedConstants),
    ("body_dependencies", namesJson
      ((info.value? true).map Expr.getUsedConstants |>.getD #[])),
    ("structural_dependencies", namesJson (structuralDependencies info))]

def readCompleteModule (path : String) : IO (Bool × Array Name × NameMap ConstantInfo) := do
  let base : System.FilePath := path
  let server : System.FilePath := path ++ ".server"
  let privatePart : System.FilePath := path ++ ".private"
  let hasServer ← server.pathExists
  let hasPrivate ← privatePart.pathExists
  unless hasServer == hasPrivate do
    throw <| IO.userError s!"Incomplete ordered module facets: {path}"
  let mut files := #[base]
  if hasServer then files := files ++ #[server, privatePart]
  let parts ← Lean.readModuleDataParts files
  let some (first, _) := parts[0]? |
    throw <| IO.userError s!"No module data: {path}"
  if first.isModule && !hasPrivate then
    throw <| IO.userError s!"Module-system artifact lacks its full private facet: {path}"
  if !first.isModule && hasPrivate then
    throw <| IO.userError s!"Unexpected split facets for a legacy artifact: {path}"
  let mut declarations : NameMap ConstantInfo := {}
  let mut imports : Array Name := #[]
  -- Later private parts retain proof bodies omitted from public interfaces.
  for (data, _) in parts do
    unless data.constNames == data.constants.map (·.name) do
      throw <| IO.userError s!"Inconsistent constant index: {path}"
    imports := imports ++ data.imports.map (·.module)
    for info in data.constants do
      declarations := declarations.insert info.name info
  return (first.isModule, imports, declarations)

def exportModule (mode moduleName path : String) (stream : IO.FS.Handle) : IO Nat := do
  let (isModule, imports, declarations) ← readCompleteModule path
  let entries := declarations.toList.mergeSort (fun a b => Name.lt a.1 b.1)
  stream.putStrLn <| (Json.mkObj [
    ("record", toJson "module"), ("module", toJson moduleName),
    ("mode", toJson mode), ("is_module", toJson isModule),
    ("facet_count", toJson (if isModule then 3 else 1 : Nat)), ("imports", namesJson imports),
    ("declarations", toJson entries.length)]).compress
  for (_, info) in entries do
    let row := if mode == "project" then declarationJson moduleName info else
      Json.mkObj [
        ("record", toJson "boundary_declaration"),
        ("module", toJson moduleName), ("name", toJson info.name.toString),
        ("kind", toJson (declarationKind info)),
        ("unsafe", toJson info.isUnsafe), ("partial", toJson info.isPartial)]
    stream.putStrLn row.compress
  return entries.length

/-- Lean may generate the same equational theorem on demand in several modules.
For these occurrences, compare the complete types directly in Lean;
this is precisely the theorem/theorem branch of the pinned importer's
`subsumesInfo`, and does not rely on a type hash or pretty-printed comparison. -/
def compareTheorems (left right names : String) (stream : IO.FS.Handle) : IO Nat := do
  let (_, _, leftDecls) ← readCompleteModule left
  let (_, _, rightDecls) ← readCompleteModule right
  -- Resolve display names against actual declaration names rather than parsing
  -- quoted Lean identifiers with String.toName.
  let mut count := 0
  for displayName in names.splitOn "\t" do
    let leftMatches := leftDecls.toList.filter (fun entry => entry.1.toString == displayName)
    let rightMatches := rightDecls.toList.filter (fun entry => entry.1.toString == displayName)
    let [(_, .thmInfo a)] := leftMatches |
      throw <| IO.userError s!"Left duplicate is not a unique theorem: {displayName}"
    let [(_, .thmInfo b)] := rightMatches |
      throw <| IO.userError s!"Right duplicate is not a unique theorem: {displayName}"
    unless a.name == b.name && a.type == b.type && a.levelParams == b.levelParams && a.all == b.all do
      throw <| IO.userError s!"Incompatible repeated theorem: {displayName}"
    stream.putStrLn <| (Json.mkObj [
      ("record", toJson "compatible_theorem"), ("name", toJson displayName),
      ("left", toJson left), ("right", toJson right)]).compress
    count := count + 1
  return count

def exportArtifacts (args : List String) : IO UInt32 := do
  let [input, output] := args | throw <| IO.userError "expected input.tsv output.jsonl"
  let stream ← IO.FS.Handle.mk output .write
  let mut count := 0
  for line in (← IO.FS.lines input) do
    if line.isEmpty then continue
    match line.splitOn "\t" with
    | "compare" :: left :: right :: names =>
      if names.isEmpty then throw <| IO.userError "No duplicate names to compare"
      count := count + (← compareTheorems left right (String.intercalate "\t" names) stream)
    | [mode, name, path] =>
      unless mode == "project" || mode == "boundary" do
        throw <| IO.userError s!"Unknown extraction mode: {mode}"
      count := count + (← exportModule mode name path stream)
    | _ => throw <| IO.userError "expected mode<TAB>module<TAB>absolute artifact path"
  stream.flush
  IO.println s!"Exported {count} declarations."
  return 0

/-- Read both written and effective imports with Lean's own header parser.
The latter includes the implicit `Init` import unless `prelude` suppresses it.
No source body is elaborated or evaluated. -/
def exportSourceImports (input output : String) : IO UInt32 := do
  let stream ← IO.FS.Handle.mk output .write
  for line in (← IO.FS.lines input) do
    if line.isEmpty then continue
    let [moduleName, path] := line.splitOn "\t" |
      throw <| IO.userError "expected module<TAB>source path"
    let source ← IO.FS.readFile path
    let (header, _, messages) ← Parser.parseHeader (Parser.mkInputContext source path)
    if messages.hasErrors then
      throw <| IO.userError s!"Cannot parse source imports: {path}"
    stream.putStrLn <| (Json.mkObj [
      ("module", toJson moduleName), ("path", toJson path),
      ("is_module", toJson (Elab.HeaderSyntax.isModule header)),
      ("explicit_imports", namesJson ((Elab.HeaderSyntax.imports header false).map (·.module))),
      ("effective_imports", namesJson ((Elab.HeaderSyntax.imports header true).map (·.module)))]).compress
  stream.flush
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["source-imports", input, output] => exportSourceImports input output
  | _ => exportArtifacts args
