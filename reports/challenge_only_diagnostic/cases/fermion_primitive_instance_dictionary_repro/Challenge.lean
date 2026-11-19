module
public import Mathlib
public meta import Lean
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
    for (i, law) in [(1,"polynomialSelfCommute"),(2,"polynomialSelfTower"),(3,"exteriorSelfCommute"),(4,"exteriorSelfTower")] do
      let name := (ns ++ ".superQuotientModule._proof_" ++ toString i).toName
      let some c := env.find? name | logInfo (Json.mkObj [("kind",toJson "INSTANCE_REPRO"),("namespace",toJson ns),("name",toJson name.toString),("found",toJson false)]).compress; continue
      let some d := env.find? ((ns ++ "." ++ law).toName) | throwError "Missing named law"
      let ct := c.type.instantiateLevelParams c.levelParams (c.levelParams.map fun _ => Level.zero)
      let dt := d.type.instantiateLevelParams d.levelParams (d.levelParams.map fun _ => Level.zero)
      let value := c.value?.map peel
      logInfo (Json.mkObj [("kind",toJson "INSTANCE_REPRO"),("namespace",toJson ns),("name",toJson name.toString),("found",toJson true),
        ("normalized_level_zero_type_equal_named_law",toJson (ct == dt)),
        ("aux_class_arg_heads",toJson ((peel ct).getAppArgs.toList.map shape)),
        ("named_class_arg_heads",toJson ((peel dt).getAppArgs.toList.map shape)),
        ("value_head",toJson (value.map shape)),("value_arg_heads",toJson (value.map fun x => x.getAppArgs.toList.map shape)),
        ("no_full_expr_rendering",toJson true)]).compress
