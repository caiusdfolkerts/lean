module

public import paper_verification.graded_degenerations3
import all paper_verification.graded_degenerations3
public import paper_verification.literal011
import all paper_verification.literal011
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

section ComponentSource_0
/- Original module: PaperVerification.AlternatingFormsGradedCharacteristic -/


/-!
# The graded flat family in the range of Theorem 7.1

The generic coefficient grading requires no characteristic assumption. The
only arithmetic input is the already proved initial-ideal equality. This
file applies it under the exact degree-dependent factorial condition and,
as a consequence, in the printed range `s < 2*p`, including characteristic
two. The one-plane boundary works over every field.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open MvPolynomial PaperVerification.WeightedInitialFiber

namespace PaperVerification.AlternatingForms

variable {K : Type*} [Field K]

/-- The original odd Rees family is graded and flat whenever the exact
local factorial denominators are invertible. No additional geometric
hypothesis is needed. -/
def oddRichardsonGradedFlatDegeneration_of_degree_factorials
    (k t : ℕ) (hs : t + 2 ≤ k + 1) (hfac : DegreeFactorials K (t + 2)) :
    CoordinateGradedReesDegeneration
      (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms k))
      (isotropicPluckerIdeal_isHomogeneous _)
      (pluckerVertexWeight (oddNatVertexWeight k))
      (isotropicPluckerIdeal (t := t) (oddPluckerForms k))
      (intervalPluckerIdeal (oddIntervalLower k (t + 2) hs)
        (oddIntervalUpper k (t + 2) hs)) where
  flat := inferInstance
  specialFiberEquiv := specialFiberEquivOfInitial _ _ _
    (odd_isotropic_initial_eq_interval_of_degree_factorials (K := K) k t hs hfac)
  specialFiber_piece := specialFiberEquivOfInitial_coordinate_piece _ _ _ _ _
  nonzeroFiberEquiv := nonzeroFiberEquiv _ _
  nonzeroFiber_piece := nonzeroFiberEquiv_coordinate_piece _ _ _

/-- The precise positive-characteristic range of Theorem 7.1, strengthened
to include the actual ordinary grading and every fiber isomorphism. -/
def paper_theorem_7_1_graded_flat_family (p k t : ℕ) [Fact p.Prime] [CharP K p]
    (hs : t + 2 ≤ k + 1) (hp : t + 2 < 2 * p) :=
  oddRichardsonGradedFlatDegeneration_of_degree_factorials (K := K) k t hs
    (degreeFactorials_of_lt_twice_characteristic p (t + 2) hp)

/-- Every line, over every field, including ambient dimension one. -/
def oddOnePlaneGradedFlatDegeneration_all_fields (k : ℕ) :
    CoordinateGradedReesDegeneration
      (matrixPluckerIdeal (K := K) (s := 1) (n := 2 * k + 1))
      (matrixPluckerIdeal_isHomogeneous (by decide : 0 < 1))
      (pluckerVertexWeight (oddNatVertexWeight k))
      (matrixPluckerIdeal (s := 1) (n := 2 * k + 1))
      (intervalPluckerIdeal (oddIntervalLower k 1 (by omega))
        (oddIntervalUpper k 1 (by omega))) where
  flat := inferInstance
  specialFiberEquiv := specialFiberEquivOfInitial _ _ _
    (paper_theorem_7_1_initial_ideal_one_plane (K := K) k)
  specialFiber_piece := specialFiberEquivOfInitial_coordinate_piece _ _ _ _ _
  nonzeroFiberEquiv := nonzeroFiberEquiv _ _
  nonzeroFiber_piece := nonzeroFiberEquiv_coordinate_piece _ _ _

end PaperVerification.AlternatingForms
end
end
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsGradedCharacteristic"


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
    (`PaperVerification.AlternatingForms.oddRichardsonGradedFlatDegeneration_of_degree_factorials, "definition"),
    (`PaperVerification.AlternatingForms.paper_theorem_7_1_graded_flat_family, "definition"),
    (`PaperVerification.AlternatingForms.oddOnePlaneGradedFlatDegeneration_all_fields, "definition")
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
    ("nonce", toJson "d652b629dbd1e3b9d85ed0732bbdfed2"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:d652b629dbd1e3b9d85ed0732bbdfed2"
