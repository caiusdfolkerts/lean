module
import all release_all
import all paper_verification.lattice001
import all paper_verification.lattice002
import all paper_verification.lattice003
import all paper_verification.lattice004
import all paper_verification.lattice005
import all paper_verification.lattice006
import all paper_verification.lattice007
import all paper_verification.lattice008
import all e7_orbits
import all coordinate_orbits
import all e8_orbits
public meta import Lean.Util.CollectAxioms
public meta import Lean.Elab.Command
public meta import Lean.Meta.Basic
open Lean Elab Command
run_cmd do
  let env := (← getEnv).setExporting false
  let localModules := #[`paper_verification, `paper_verification.lattice001,
    `paper_verification.lattice002, `paper_verification.lattice003,
    `paper_verification.lattice004, `paper_verification.lattice005,
    `paper_verification.lattice006, `paper_verification.lattice007,
    `paper_verification.lattice008, `e7_orbits, `coordinate_orbits, `e8_orbits, `release_all]
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, info) in env.checked.get.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some owner := env.header.moduleNames[idx.toNat]? | continue
    unless localModules.contains owner do continue
    if info.isUnsafe || info.isPartial then
      throwError "Unsafe or partial project declaration: {name}"
    match info with
    | .axiomInfo _ => throwError "Project axiom declaration: {name}"
    | _ => pure ()
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected transitive axiom {ax} in {name}"
    if info.type.hasMVar || info.type.hasFVar then
      throwError "Open project declaration type: {name}"
    count := count + 1
    if !modules.contains owner then modules := modules.push owner
  if count == 0 then throwError "No local declarations were checked"
  for required in #[`paper_verification.lattice001, `paper_verification.lattice002,
      `paper_verification.lattice003, `paper_verification.lattice004,
      `paper_verification.lattice005, `paper_verification.lattice006,
      `paper_verification.lattice007, `paper_verification.lattice008,
      `e7_orbits, `coordinate_orbits, `e8_orbits] do
    unless modules.contains required do throwError "Missing audited module: {required}"
  logInfo m!"Checked all {count} local declarations, including private definitions, across {modules.size} mathematical modules. No project axioms, unsafe/partial declarations, open types, or nonstandard transitive axioms."

set_option pp.universes false in
#check PaperVerification.ColdSpots.e7_deep_holes_single_affine_orbit
#check PaperVerification.ColdSpots.dn_deep_holes_single_affine_orbit
#check PaperVerification.ColdSpots.e8_deep_holes_single_affine_weyl_orbit
#check PaperVerification.ColdSpots.IsE7AffineSymmetry.euclidean_distance
#check PaperVerification.ColdSpots.CoordinateLatticeSymmetry.euclidean_distance
#check PaperVerification.ColdSpots.E8AffineWeyl.euclidean_distance
#print PaperVerification.ColdSpots.E8AffineWeyl
#print axioms PaperVerification.ColdSpots.e7_deep_holes_single_affine_orbit
#print axioms PaperVerification.ColdSpots.dn_deep_holes_single_affine_orbit
#print axioms PaperVerification.ColdSpots.e8_deep_holes_single_affine_weyl_orbit
