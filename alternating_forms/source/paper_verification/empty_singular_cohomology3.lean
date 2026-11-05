module

public import paper_verification.oai_thom000_run1
import all paper_verification.oai_thom000_run1
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

@[expose] public section ComponentSource_0
/- Original module: PaperVerification.EmptySingularCohomology -/

/-!
# Singular cohomology of the empty space

The argument uses actual singular simplices. A simplex has a vertex, so an
empty space has no singular simplices in any degree. Its whole cochain complex
is therefore zero. The cochain proof is the generic argument in the pinned
OpenAI Math `Duality/Poincare/CompactSupportCohomology.lean`; no compact-support
theory is required here. See the accompanying third-party attribution.
-/

namespace PaperVerification.EmptySingularCohomology

noncomputable section

open CategoryTheory CategoryTheory.Limits
open OAI.AlgebraicTopology.Cohomology.Singular

variable {R : Type} [Ring R] (M : ModuleCat.{0} R) (X : TopCat.{0}) [IsEmpty X]

theorem cochains_isZero : IsZero (Basic.singularCochains M X) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply HomologicalComplex.hom_ext
  intro n
  have : IsEmpty (Basic.singularSimplices X n) := ⟨fun s =>
    isEmptyElim (Coefficients.singularSimplicesEquivContinuousMap X n s
      (Convexity.StdSimplex.single (R := ℝ) (0 : Fin (n + 1))))⟩
  exact ((ModuleCat.isZero_of_subsingleton
    (ModuleCat.of R (Basic.singularSimplices X n → M))).of_iso
      (Coefficients.singularDegreewiseFunctionIso M X n)).eq_of_tgt _ _

/-- The statement includes degree zero. -/
theorem cohomology_isZero (n : ℕ) : IsZero (Basic.singularCohomology M X n) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.up ℕ) n).map_isZero (cochains_isZero M X)

end
end PaperVerification.EmptySingularCohomology
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.EmptySingularCohomology"


set_option pp.explicit false
set_option pp.proofs false
set_option pp.deepTerms false
set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let opts ← getOptions
  if true && env.header.trustLevel != 0 then
    throwError "The final environment has nonzero kernel trust level"
  if Lean.debug.skipKernelTC.get opts then
    throwError "The final environment disabled kernel type checking"
  if Lean.Elab.inServer.get opts then
    throwError "The final environment unexpectedly uses server mode"
  let required : Array (Name × String) := #[
    (`PaperVerification.EmptySingularCohomology.cochains_isZero, "theorem"),
    (`PaperVerification.EmptySingularCohomology.cohomology_isZero, "theorem")
  ]
  let localNames := env.checked.get.constants.foldStage2 (fun acc name _ => acc.push name) (#[] : Array Name)
  if localNames.isEmpty then throwError "Empty authored declaration audit"
  let mut names := localNames
  for (name, _) in required do
    unless names.contains name do names := names.push name
  let mut rows : Array Json := #[]
  for name in names do
    let some info := env.checked.get.find? name | throwError "Missing checked declaration {name}"
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient primitive"
    if kind == "axiom" then throwError "Authored axiom {name}"
    let value := info.value? (allowOpaque := true)
    if kind == "theorem" || kind == "definition" || kind == "opaque" then
      unless value.isSome do throwError "No actual body {name}"
    for (requiredName, expectedKind) in required do
      if name == requiredName && kind != expectedKind then
        throwError "Endpoint kind mismatch {name}: expected {expectedKind}, got {kind}"
    let axioms ← collectAxioms name
    for ax in axioms do
      if ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound then
        throwError "Unapproved transitive axiom {name}: {ax}"
    let mut fields := [("name", toJson name.toString), ("kind", toJson kind),
      ("actual_body_available", toJson value.isSome),
      ("universe_parameters", toJson (info.levelParams.map Name.toString)),
      ("type_dependencies", toJson (info.type.getUsedConstants.map Name.toString)),
      ("body_dependencies", toJson ((value.map Expr.getUsedConstants).getD #[] |>.map Name.toString)),
      ("transitive_axioms", toJson (axioms.map Name.toString))]
    if required.any (fun e => e.1 == name) then
      let typeText ← liftTermElabM <| return (← Meta.ppExpr info.type).pretty
      fields := fields ++ [("readable_type", toJson typeText)]
    rows := rows.push (Json.mkObj fields)
  IO.FS.createDirAll ".lake/reports"
  let path := ".lake/reports/" ++ (← getEnv).mainModule.toString ++ ".json"
  IO.FS.writeFile path (Json.mkObj [("accepted", toJson true),
    ("nonce", toJson "ec84a7c455f10f18d10fae36f24b7d53"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:ec84a7c455f10f18d10fae36f24b7d53"
