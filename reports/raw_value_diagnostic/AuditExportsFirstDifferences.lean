module
public import LeanExport.Parse
public import Lean.Data.Json
public import Lean.Util.FoldConsts
public import Std.Data.HashSet
@[expose] public section
open Lean
/-! Read-only diagnostic: enumerate every reachable raw dependency mismatch in
existing trusted exports. This is not a substitute for Comparator/NanoDa.
Run with the exact pinned toolchain:
lean --run AuditExports.lean Challenge.export Solution.export comparator.json
No project import or project rebuild is performed. -/

def namesField (j : Json) (field : String) : Except String (Array Name) := do
  let .ok a := j.getObjValAs? (Array String) field | return #[]
  pure (a.map String.toName)

def statementEqual (a b : ConstantInfo) : Bool :=
  a.name == b.name && a.levelParams == b.levelParams && a.type == b.type

def hintsText : ReducibilityHints → String
  | .abbrev => "abbrev"
  | .opaque => "opaque"
  | .regular n => s!"regular({n})"

def differenceFields (a b : ConstantInfo) : String :=
  let common := s!"type_eq={a.type == b.type} levels_eq={a.levelParams == b.levelParams}"
  match a,b with
  | .defnInfo x,.defnInfo y =>
      common ++ s!" value_eq={x.value == y.value} hints_challenge={hintsText x.hints} hints_solution={hintsText y.hints} safety_eq={x.safety == y.safety} mutual_names_eq={x.all == y.all}"
  | .thmInfo x,.thmInfo y =>
      common ++ s!" value_eq={x.value == y.value} mutual_names_eq={x.all == y.all}"
  | _,_ => common

/-- Bounded raw syntax comparison; no normalization or mathematical inference. -/
partial def firstExprDifferences (a b : Expr) (path : String := "value")
    (fuel : Nat := 96) : Array (String × Expr × Expr) := Id.run do
  if a == b then return #[]
  if fuel == 0 then return #[(path ++ ".depth-limit", a, b)]
  let next := fuel - 1
  let recur := fun x y suffix => firstExprDifferences x y (path ++ suffix) next
  match a, b with
  | .app af aa, .app bf ba =>
      return ((recur af bf ".fn") ++ (recur aa ba ".arg")).extract 0 6
  | .lam _ aty ab _, .lam _ bty bb _ =>
      return ((recur aty bty ".domain") ++ (recur ab bb ".body")).extract 0 6
  | .forallE _ aty ab _, .forallE _ bty bb _ =>
      return ((recur aty bty ".domain") ++ (recur ab bb ".body")).extract 0 6
  | .letE _ aty av ab _, .letE _ bty bv bb _ =>
      return ((recur aty bty ".type") ++ (recur av bv ".value") ++
        (recur ab bb ".body")).extract 0 6
  | .mdata _ ab, .mdata _ bb =>
      let ds := recur ab bb ".body"
      return if ds.isEmpty then #[(path ++ ".metadata", a, b)] else ds
  | .proj an ai ab, .proj bn bi bb =>
      if an != bn || ai != bi then return #[(path ++ ".projection", a, b)]
      return recur ab bb ".body"
  | _, _ => return #[(path, a, b)]

def boundedExprText (e : Expr) : String :=
  String.ofList ((reprStr e).toList.take 500)

def terminalTypeHead : Expr → String × Nat
  | .forallE _ _ b _ => let (head, count) := terminalTypeHead b; (head, count+1)
  | e => ((match e.getAppFn with | .const n _ => n.toString | _ => "nonconstant"), 0)

def rawTypeContext (a b : ConstantInfo) : Json :=
  let (ah, ac) := terminalTypeHead a.type
  let (bh, bc) := terminalTypeHead b.type
  Json.mkObj [("kind", toJson "RAW_TYPE_CONTEXT"), ("name", toJson a.name.toString),
    ("types_equal", toJson (a.type == b.type)),
    ("challenge_levels", toJson (a.levelParams.map Name.toString)),
    ("solution_levels", toJson (b.levelParams.map Name.toString)),
    ("challenge_conclusion_head", toJson ah), ("solution_conclusion_head", toJson bh),
    ("challenge_binders", toJson ac), ("solution_binders", toJson bc),
    ("challenge_type_characters", toJson (reprStr a.type).length),
    ("solution_type_characters", toJson (reprStr b.type).length),
    ("type_ast_not_printed", toJson true)]

def deps (ci : ConstantInfo) : Array Name := Id.run do
  let mut ds := ci.type.getUsedConstants
  if let some value := ci.value? (allowOpaque := true) then
    ds := ds ++ value.getUsedConstants
  match ci with
  | .inductInfo i => ds := ds ++ i.ctors.toArray ++ i.all.toArray
  | .ctorInfo i => ds := ds.push i.induct
  | .recInfo i =>
      for rule in i.rules do
        ds := (ds.push rule.ctor) ++ rule.rhs.getUsedConstants
  | _ => pure ()
  return ds

def main (args : List String) : IO UInt32 := do
  let [challengePath,solutionPath,configPath] := args
    | IO.eprintln "usage: AuditExports.lean Challenge.export Solution.export comparator.json"; return 2
  let challenge ← IO.FS.withFile challengePath .read fun h =>
    LeanExport.parseStream (IO.FS.Stream.ofHandle h)
  let solution ← IO.FS.withFile solutionPath .read fun h =>
    LeanExport.parseStream (IO.FS.Stream.ofHandle h)
  for n in #[`FourPapers.Universal.ScalarFamilies.Family._proof_1,
      `FourPapers.Universal.integralStalkComparison._proof_2] do
    for (label, env) in #[("challenge", challenge), ("solution", solution)] do
      match env.constMap[n]? with
      | none => IO.println s!"MEASURED_HELPER_MISSING {label} {n}"
      | some d =>
        let raw := reprStr d.type
        IO.println (Json.mkObj [("kind", toJson "MEASURED_HELPER_TYPE"),
          ("environment", toJson label), ("name", toJson n.toString),
          ("levels", toJson (reprStr d.levelParams)),
          ("characters", toJson raw.length),
          ("truncated", toJson (decide (10000 < raw.length))),
          ("type", toJson (String.ofList (raw.toList.take 10000)))]).compress
  return 0
