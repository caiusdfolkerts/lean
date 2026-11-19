module
public import Mathlib
public meta import Lean
@[expose] public section
open Lean
partial def firstExprDifferences (a b : Expr) (path : String := "value")
    (fuel : Nat := 96) (limit : Nat := 6) : Array (String × Expr × Expr) := Id.run do
  if limit == 0 || a == b then return #[]
  if fuel == 0 then return #[(path ++ ".depth-limit", a, b)]
  let recur := fun x y suffix cap => firstExprDifferences x y (path ++ suffix) (fuel-1) cap
  match a,b with
  | .app af aa, .app bf ba =>
      let first := recur af bf ".fn" limit
      if first.size >= limit then return first
      return first ++ recur aa ba ".arg" (limit-first.size)
  | .lam an aty ab ai, .lam bn bty bb bi
  | .forallE an aty ab ai, .forallE bn bty bb bi =>
      let first := recur aty bty ".domain" limit
      if first.size >= limit then return first
      return first ++ recur ab bb ".body" (limit-first.size)
  | .letE an aty av ab ai, .letE bn bty bv bb bi =>
      if ai != bi then return #[(path ++ ".let-nondep",a,b)]
      let first := recur aty bty ".type" limit
      if first.size >= limit then return first
      let second := first ++ recur av bv ".value" (limit-first.size)
      if second.size >= limit then return second
      return second ++ recur ab bb ".body" (limit-second.size)
  | .mdata _ ab, .mdata _ bb =>
      let ds := recur ab bb ".body" limit
      return if ds.isEmpty then #[(path ++ ".metadata",a,b)] else ds
  | .proj an ai ab, .proj bn bi bb =>
      if an != bn || ai != bi then return #[(path ++ ".projection",a,b)]
      return recur ab bb ".body" limit
  | _,_ => return #[(path,a,b)]

/-- A shallow exact constructor/head description, never `reprStr` of an Expr.
Full shared-DAG AST size is deliberately not computed or rendered. -/
def shallowExprText (e : Expr) : String :=
  match e with
  | .const n levels => s!"const {reprStr n} levels={reprStr levels}"
  | .bvar i => s!"bvar {i}"
  | .fvar i => s!"fvar {reprStr i}"
  | .mvar i => s!"mvar {reprStr i}"
  | .sort level => s!"sort {reprStr level}"
  | .lit value => s!"lit {reprStr value}"
  | .app _ _ => s!"app head={(match e.getAppFn with | .const n _ => n.toString | _ => "nonconstant")} full_ast_not_rendered=true"
  | .lam n _ _ bi => s!"lam binder={reprStr n} binder_info={reprStr bi} full_ast_not_rendered=true"
  | .forallE n _ _ bi => s!"forallE binder={reprStr n} binder_info={reprStr bi} full_ast_not_rendered=true"
  | .letE n _ _ _ nd => s!"letE binder={reprStr n} nondep={nd} full_ast_not_rendered=true"
  | .mdata _ _ => "mdata full_ast_not_rendered=true"
  | .proj n i _ => s!"proj {reprStr n} {i} full_ast_not_rendered=true"

def boundedExprText (e : Expr) : String :=
  String.ofList ((shallowExprText e).toList.take 500)


noncomputable section
set_option autoImplicit false
attribute [-instance] MvPolynomial.instModuleSelf MvPolynomial.instModule
open scoped TensorProduct
namespace Wrapped
set_option backward.inferInstanceAs.wrap.instances true
variable (K : Type*) [CommRing K] (n : ℕ)
abbrev PolynomialRing := MvPolynomial (Fin n) K
abbrev OddModule := (Fin n ⊕ Fin n) → K
theorem polynomialSelfCommute : SMulCommClass K (PolynomialRing K n) (PolynomialRing K n) := by infer_instance
theorem polynomialSelfTower : IsScalarTower K (PolynomialRing K n) (PolynomialRing K n) := by infer_instance
theorem exteriorSelfCommute : SMulCommClass K (ExteriorAlgebra K (OddModule K n)) (ExteriorAlgebra K (OddModule K n)) := by infer_instance
theorem exteriorSelfTower : IsScalarTower K (ExteriorAlgebra K (OddModule K n)) (ExteriorAlgebra K (OddModule K n)) := by infer_instance
attribute [instance 2100] polynomialSelfCommute polynomialSelfTower exteriorSelfCommute exteriorSelfTower
abbrev SuperRing := PolynomialRing K n ⊗[K] ExteriorAlgebra K (OddModule K n)
@[reducible] noncomputable instance superQuotientModule (I : TwoSidedIdeal (SuperRing K n)) : Module K I.ringCon.Quotient := by
  let q : SuperRing K n →+ I.ringCon.Quotient := { toFun := fun x ↦ (x : I.ringCon.Quotient), map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  exact Function.Surjective.module K q (fun x ↦ I.ringCon.mk'_surjective x) (fun _ _ ↦ rfl)
end Wrapped
namespace Unwrapped
set_option backward.inferInstanceAs.wrap.instances false
variable (K : Type*) [CommRing K] (n : ℕ)
abbrev PolynomialRing := MvPolynomial (Fin n) K
abbrev OddModule := (Fin n ⊕ Fin n) → K
theorem polynomialSelfCommute : SMulCommClass K (PolynomialRing K n) (PolynomialRing K n) := by infer_instance
theorem polynomialSelfTower : IsScalarTower K (PolynomialRing K n) (PolynomialRing K n) := by infer_instance
theorem exteriorSelfCommute : SMulCommClass K (ExteriorAlgebra K (OddModule K n)) (ExteriorAlgebra K (OddModule K n)) := by infer_instance
theorem exteriorSelfTower : IsScalarTower K (ExteriorAlgebra K (OddModule K n)) (ExteriorAlgebra K (OddModule K n)) := by infer_instance
attribute [instance 2100] polynomialSelfCommute polynomialSelfTower exteriorSelfCommute exteriorSelfTower
abbrev SuperRing := PolynomialRing K n ⊗[K] ExteriorAlgebra K (OddModule K n)
@[reducible] noncomputable instance superQuotientModule (I : TwoSidedIdeal (SuperRing K n)) : Module K I.ringCon.Quotient := by
  let q : SuperRing K n →+ I.ringCon.Quotient := { toFun := fun x ↦ (x : I.ringCon.Quotient), map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  exact Function.Surjective.module K q (fun x ↦ I.ringCon.mk'_surjective x) (fun _ _ ↦ rfl)
end Unwrapped
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let rec peel : Expr → Expr
    | .forallE _ _ b _ => peel b
    | .lam _ _ b _ => peel b
    | .mdata _ b => peel b
    | e => e
  let shape := fun e : Expr => String.ofList ((match e with
    | .const n _ => "const " ++ n.toString
    | .bvar i => "bvar " ++ toString i
    | .app _ _ => "app " ++ (e.getAppFn.constName?.map Name.toString).getD "nonconstant"
    | .proj n i _ => "proj " ++ n.toString ++ " " ++ toString i
    | .sort _ => "sort"
    | _ => "other").toList.take 240)
  for ns in ["Wrapped", "Unwrapped"] do
    logInfo (Json.mkObj [("kind",toJson "INSTANCE_LOOKUP_CONTROL"),("namespace",toJson ns),
      ("instance_found",toJson ((env.find? ((ns ++ ".superQuotientModule").toName)).isSome)),
      ("law_found",toJson ((env.find? ((ns ++ ".polynomialSelfCommute").toName)).isSome))]).compress
    let names := env.constants.toList.filterMap fun (n, _) =>
      if n.toString.startsWith (ns ++ ".") && (n.toString.splitOn "_proof_").length > 1 then some n.toString else none
    logInfo (Json.mkObj [("kind",toJson "AUXILIARY_NAME_COVERAGE"),("namespace",toJson ns),
      ("total",toJson names.length),("emitted",toJson (names.take 24)),("cap",toJson (24 : Nat)),
      ("omitted",toJson (names.length - min names.length 24))]).compress
    for (i, law) in [(1,"polynomialSelfCommute"),(2,"polynomialSelfTower"),(3,"exteriorSelfCommute"),(4,"exteriorSelfTower")] do
      let name := (ns ++ ".superQuotientModule._proof_" ++ toString i).toName
      let some c := env.find? name | logInfo (Json.mkObj [("kind",toJson "INSTANCE_REPRO"),("namespace",toJson ns),("name",toJson name.toString),("found",toJson false)]).compress; continue
      let some d := env.find? ((ns ++ "." ++ law).toName) | throwError "Missing named law"
      let ct := c.type.instantiateLevelParams c.levelParams (c.levelParams.map fun _ => Level.zero)
      let dt := d.type.instantiateLevelParams d.levelParams (d.levelParams.map fun _ => Level.zero)
      let value := (c.value? (allowOpaque := true)).map peel
      let diffs := firstExprDifferences ct dt "class-type"
      logInfo (Json.mkObj [("kind",toJson "EXACT_CLASS_TYPE_LEAVES"),("name",toJson name.toString),("returned",toJson diffs.size),("candidate_cap",toJson (6 : Nat)),("candidate_cap_reached",toJson (diffs.size == 6)),("leaves",toJson (diffs.toList.map fun (path,a,b) => Json.mkObj [("path",toJson path),("actual",toJson (boundedExprText a)),("named",toJson (boundedExprText b))]))]).compress
      logInfo (Json.mkObj [("kind",toJson "INSTANCE_REPRO"),("namespace",toJson ns),("name",toJson name.toString),("found",toJson true),
        ("normalized_level_zero_type_equal_named_law",toJson (ct == dt)),
        ("aux_class_arg_heads",toJson ((peel ct).getAppArgs.toList.map shape)),
        ("named_class_arg_heads",toJson ((peel dt).getAppArgs.toList.map shape)),
        ("value_head",toJson (value.map shape)),("value_arg_heads",toJson (value.map fun x => x.getAppArgs.toList.map shape)),
        ("no_full_expr_rendering",toJson true)]).compress

#check @Algebra.TensorProduct.instRing
#check @Function.Surjective.module

#check @SMulCommClass
#check @IsScalarTower
#check @Algebra.toSMul
#check @Algebra.TensorProduct.instNonAssocRing
