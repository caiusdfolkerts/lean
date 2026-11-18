module
public import Mathlib
public meta import Lean
@[expose] public section
namespace Papers.Rigidity
abbrev Vec3 := Fin 3 → ℝ
end Papers.Rigidity
namespace Papers.Rigidity
open Matrix
open scoped Matrix
abbrev Twist := Vec3 × Vec3
def evaluateTwist (p : Vec3) : Twist →ₗ[ℝ] Vec3 :=
  LinearMap.snd ℝ Vec3 Vec3 +
    ((crossProduct (R := ℝ)).flip p).comp (LinearMap.fst ℝ Vec3 Vec3)
end Papers.Rigidity
namespace Papers.Rigidity
open scoped BigOperators Classical
structure PairPinGraph (B E : Type) where
  left : E → B
  right : E → B
  loopless : ∀ e, left e ≠ right e
namespace PairPinGraph
variable {B E : Type}
def compatibilityOperator (J : PairPinGraph B E) (p : E → Vec3) :
    (B → Twist) →ₗ[ℝ] (E → Vec3) :=
  LinearMap.pi fun e =>
    (evaluateTwist (p e)).comp
      (LinearMap.proj (R := ℝ) (φ := fun _ : B => Twist) (J.left e) -
        LinearMap.proj (R := ℝ) (φ := fun _ : B => Twist) (J.right e))
end PairPinGraph
end Papers.Rigidity
namespace Papers.Rigidity.PairPinGraph
variable {B E : Type}
def pinRow (J : PairPinGraph B E) (p : E → Vec3) (a : E × Fin 3) :
    (B → Twist) →ₗ[ℝ] ℝ :=
  (LinearMap.proj a.2).comp ((LinearMap.proj a.1).comp (compatibilityOperator J p))
end Papers.Rigidity.PairPinGraph
/- Diagnostic fragment only. Add Lean.Meta.Basic / Lean.PrettyPrinter meta imports
in the module header, then append this fragment to each temporary export module.
Do not change any mathematical declaration. Put pinRow last so a bounded build
log retains it. This prints full explicit values and regular reducibility heights.
-/
open Lean Meta Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  for n in #[`Papers.Rigidity.Vec3, `Papers.Rigidity.Twist,
      `Papers.Rigidity.evaluateTwist,
      `Papers.Rigidity.PairPinGraph,
      `Papers.Rigidity.PairPinGraph.compatibilityOperator,
      `Papers.Rigidity.PairPinGraph.pinRow] do
    let some info := env.checked.get.find? n | throwError "No checked constant {n}"
    let typeText ← liftTermElabM do
      withOptions (fun o => o.setBool `pp.all true) do
        return (← ppExpr info.type).pretty
    let origin := match env.getModuleIdxFor? n with
      | some i => env.header.moduleNames[i.toNat]!.toString
      | none => env.mainModule.toString
    let mut fields := [("name", toJson n.toString), ("origin", toJson origin),
      ("type", toJson typeText), ("type_raw", toJson info.type.dbgToString), ("type_hash", toJson (hash info.type).toNat), ("levels", toJson (info.levelParams.map Name.toString)),
      ("value_available", toJson (info.value? (allowOpaque := true)).isSome)]
    match info with
    | .defnInfo d =>
      let hints := match d.hints with
        | .opaque => "opaque"
        | .abbrev => "abbrev"
        | .regular h => "regular " ++ toString h.toNat
      let valueText ← liftTermElabM do
        withOptions (fun o => o.setBool `pp.all true) do
          return (← ppExpr d.value).pretty
      fields := fields ++ [("kind", toJson "definition"), ("hints", toJson hints),
        ("safety", toJson (reprStr d.safety)),
        ("mutual_all", toJson (d.all.map Name.toString)), ("value", toJson valueText), ("value_raw", toJson d.value.dbgToString), ("value_constants", toJson (d.value.getUsedConstants.map Name.toString)), ("value_hash", toJson (hash d.value).toNat)]
    | .inductInfo d => fields := fields ++ [("kind", toJson "inductive"),
        ("num_params", toJson d.numParams), ("num_indices", toJson d.numIndices),
        ("mutual_all", toJson (d.all.map Name.toString)), ("constructors", toJson (d.ctors.map Name.toString)),
        ("num_nested", toJson d.numNested), ("recursive", toJson d.isRec),
        ("unsafe", toJson d.isUnsafe), ("reflexive", toJson d.isReflexive)]
    | .axiomInfo _ => fields := fields ++ [("kind", toJson "axiom/interface")]
    | .thmInfo _ => fields := fields ++ [("kind", toJson "theorem")]
    | .opaqueInfo _ => fields := fields ++ [("kind", toJson "opaque")]
    | _ => fields := fields ++ [("kind", toJson "other")]
    logInfo m!"PALOMAR_CONSTINFO {(Json.mkObj fields).compress}"
