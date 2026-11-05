module

public import verification.internal.ellipsoid_remaining_statements
public import ellipsoid.coefficient_corners
public import ellipsoid.sharpness_neighborhood
import Lean.Util.CollectAxioms

/- Read-only full principal inspection. Ordinary imported interfaces can hide
   theorem bodies as axiom-shaped placeholders. The records below therefore
   read each root owner's complete public/server/private ModuleData parts and
   require an actual ordinary theorem with a proof value. Axiom reports from
   collectAxioms are separately labeled cached imported metadata; they do not
   replace a complete actual-body dependency walk or kernel replay. -/

#print axioms EllipsoidVerification.intrinsic_reconstruction
#print axioms EllipsoidVerification.exists_fullEllipsoid_of_affineBall
#print axioms EllipsoidVerification.FullEllipsoid.exists_affineBallParameterization
#print axioms EllipsoidVerification.symmetricPart_balancedJacobian_posDef
#print axioms EllipsoidVerification.uniform_holder_recovery
#print axioms EllipsoidVerification.sharp_holder_recovery
#print axioms EllipsoidVerification.sharp_holder_recovery_at_fixed_volume
#print axioms EllipsoidVerification.coefficient_transform_theorem
#print axioms EllipsoidVerification.measured_coefficient_box
#print axioms EllipsoidVerification.coefficientTransform_gt_sqrt
#print axioms EllipsoidAudit.uniformOneOverN_statement
#print axioms EllipsoidAudit.noLargerExponent_statement
#print axioms EllipsoidAudit.noLargerExponentEqualVolume_statement
#print axioms EllipsoidAudit.coefficientTransformFull_statement
#print axioms EllipsoidAudit.coefficient_strict_bound_statement
#print axioms EllipsoidAudit.measuredCoefficientBox_statement
#print axioms EllipsoidVerification.orderedMomentKernel_posDef
#print axioms EllipsoidVerification.coefficient_transform_manifold_with_corners
#print axioms EllipsoidVerification.sharp_holder_recovery_near_sphere
#print axioms EllipsoidVerification.sharp_holder_recovery_at_fixed_volume_near_sphere
#print axioms EllipsoidVerification.FullEllipsoid.hasSteinerFormula

open Lean Elab Command

private def inspectedKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

run_cmd do
  let env ← getEnv
  let groups : Array (Name × Array Name) := #[
    (`ellipsoid.verified.reconstruction01, #[`EllipsoidVerification.intrinsic_reconstruction]),
    (`ellipsoid.verified.affine01, #[`EllipsoidVerification.exists_fullEllipsoid_of_affineBall, `EllipsoidVerification.FullEllipsoid.exists_affineBallParameterization]),
    (`ellipsoid.verified.main04, #[`EllipsoidVerification.symmetricPart_balancedJacobian_posDef]),
    (`ellipsoid.verified.main_remainder01, #[`EllipsoidVerification.uniform_holder_recovery]),
    (`ellipsoid.verified.main_remainder02, #[`EllipsoidVerification.sharp_holder_recovery, `EllipsoidVerification.sharp_holder_recovery_at_fixed_volume]),
    (`ellipsoid.verified.main_remainder03, #[`EllipsoidVerification.coefficient_transform_theorem, `EllipsoidVerification.measured_coefficient_box, `EllipsoidVerification.coefficientTransform_gt_sqrt]),
    (`verification.internal.ellipsoid_remaining_statements, #[`EllipsoidAudit.uniformOneOverN_statement, `EllipsoidAudit.noLargerExponent_statement, `EllipsoidAudit.noLargerExponentEqualVolume_statement, `EllipsoidAudit.coefficientTransformFull_statement, `EllipsoidAudit.coefficient_strict_bound_statement, `EllipsoidAudit.measuredCoefficientBox_statement]),
    (`ellipsoid.verified.main03, #[`EllipsoidVerification.orderedMomentKernel_posDef]),
    (`ellipsoid.coefficient_corners, #[`EllipsoidVerification.coefficient_transform_manifold_with_corners]),
    (`ellipsoid.sharpness_neighborhood, #[`EllipsoidVerification.sharp_holder_recovery_near_sphere, `EllipsoidVerification.sharp_holder_recovery_at_fixed_volume_near_sphere]),
    (`ellipsoid.verified.main02, #[`EllipsoidVerification.FullEllipsoid.hasSteinerFormula])
  ]
  let mut total : Nat := 0
  for (ownerName, rootNames) in groups do
    let basePath ← liftIO (findOLean ownerName)
    let paths := #[basePath, basePath.addExtension "server", basePath.addExtension "private"]
    let parts ← liftIO (readModuleDataParts paths)
    let some (data, _) := parts.back? |
      throwError "No complete private module data for {ownerName}"
    unless data.constNames.size == data.constants.size do
      throwError "Mismatched private module arrays for {ownerName}"
    let mut found : NameSet := {}
    for index in [:data.constants.size] do
      let ci := data.constants[index]!
      let cname := data.constNames[index]!
      if rootNames.contains cname then
        unless ci.name == cname do
          throwError "Private ConstantInfo name does not match its module entry: {cname}"
        if found.contains cname then
          throwError "Repeated principal record: {cname}"
        found := found.insert cname
        unless inspectedKind ci == "theorem" && ci.hasValue (allowOpaque := true) do
          throwError "Principal root lacks an actual ordinary theorem body: {cname}"
        if ci.isUnsafe || ci.isPartial then
          throwError "Unsafe or partial principal root: {cname}"
        let some visible := env.find? cname |
          throwError "Principal root missing from the imported interface: {cname}"
        unless visible.type == ci.type && visible.levelParams == ci.levelParams do
          throwError "Public and private principal signatures differ: {cname}"
        let axioms ← collectAxioms cname
        let row := Json.mkObj [
          ("schema", toJson (1 : Nat)),
          ("record", toJson "principal_root"),
          ("name", toJson cname.toString),
          ("kind", toJson (inspectedKind ci)),
          ("publicKind", toJson (inspectedKind visible)),
          ("owner", toJson ownerName.toString),
          ("rawType", toJson (reprStr ci.type)),
          ("levelParameters", toJson (ci.levelParams.map reprStr)),
          ("hasValue", toJson (ci.hasValue (allowOpaque := true))),
          ("isUnsafe", toJson ci.isUnsafe),
          ("isPartial", toJson ci.isPartial),
          ("axioms", toJson ((axioms.qsort Name.lt).map Name.toString)),
          ("axiomSource", toJson "Lean.collectAxioms imported metadata; full actual-body closure must be checked separately"),
          ("bodySource", toJson "Original ConstantInfo from explicitly read public/server/private ModuleData parts"),
          ("artifactParts", toJson (paths.map System.FilePath.toString)),
          ("leanVersion", toJson Lean.versionString)]
        logInfo m!"ELLIPSOID_FULL21_ROOT {row.compress}"
        total := total + 1
    for cname in rootNames do
      unless found.contains cname do
        throwError "Principal root absent from complete private owner data: {cname}"
    -- Keep all part regions alive until every selected CI has been inspected.
    unless parts.size == 3 do
      throwError "Expected exactly three original module parts for {ownerName}"
  unless total == 21 do
    throwError "Full21 inspection emitted {total} records instead of 21"
  logInfo "ELLIPSOID_FULL21_INSPECTION_COMPLETE roots=21; actual private root bodies present; complete dependency replay remains separate"
