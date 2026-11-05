module

public import normal_projective.complete
public import normal_projective.polar_correction
public import cor2_complete

import all normal_projective.admissible_projectivity
import all normal_projective.geometry
import all normal_projective.uniform_bound
import all normal_projective.halfspace_faces
import all normal_projective.simple_vertices
import all normal_projective.simple_stability
import all normal_projective.face_correspondence
import all normal_projective.stable_incidence
import all normal_projective.canonical_model
import all normal_projective.unit_normalization
import all normal_projective.normalization_topology
import all normal_projective.elementary_projectivity
import all normal_projective.local_control
import all normal_projective.control
import all normal_projective.connected_classes
import all normal_projective.rank_obstruction
import all normal_projective.complete
import all normal_projective.polar_correction
import all dirichlet
import all closed_cover
import all triangulation
import all subfaces
import all dirichlet_strong
import all region_barrier
import all tau_ceti.data.fin.basic
import all tau_ceti.geometry.polygon.basic
import all tau_ceti.analysis.complex.circle
import all tau_ceti.topology.locally_connected
import all tau_ceti.topology.jordan_curve.basic
import all tau_ceti.analysis.convex.between
import all tau_ceti.geometry.polygon.simple
import all tau_ceti.analysis.normed.module.convex
import all tau_ceti.topology.unit_interval
import all tau_ceti.topology.homotopy.path
import all tau_ceti.topology.path_component
import all tau_ceti.topology.connected_components
import all tau_ceti.topology.frontier
import all tau_ceti.topology.filled_hull
import all tau_ceti.analysis.normed.module.ball.exterior
import all tau_ceti.analysis.normed.module.ball
import all tau_ceti.analysis.normed.module.filled_hull
import all tau_ceti.analysis.complex.continuous_log.basic
import all tau_ceti.analysis.complex.plane_separation.basic
import all tau_ceti.topology.circle.arc
import all tau_ceti.analysis.special_functions.trigonometric.arccos
import all tau_ceti.topology.circle.metric
import all tau_ceti.topology.jordan_curve.separation
import all tau_ceti.topology.jordan_curve.small_arc
import all tau_ceti.topology.jordan_curve.subcontinuum
import all tau_ceti.analysis.complex.continuous_log.path
import all tau_ceti.analysis.complex.plane_separation.jordan_curve
import all tau_ceti.analysis.contour.cauchy.principal_value.basic
import all tau_ceti.analysis.contour.winding.number.basic
import all tau_ceti.analysis.contour.null_homologous
import all tau_ceti.analysis.contour.winding.number.scale
import all tau_ceti.analysis.contour.winding.number.translate
import all tau_ceti.analysis.contour.winding.number.affine
import all tau_ceti.analysis.complex.upper_log_continuity
import all tau_ceti.analysis.contour.piecewise_c1_on
import all tau_ceti.analysis.contour.curve.integrability
import all tau_ceti.analysis.contour.log_deriv_ftc
import all tau_ceti.analysis.contour.winding.number.segment.formula
import all tau_ceti.analysis.contour.curve.distance
import all tau_ceti.analysis.contour.winding.number.reverse
import all tau_ceti.analysis.contour.winding.continuity
import all tau_ceti.analysis.contour.argument.lift
import all tau_ceti.analysis.contour.winding.segment_sum
import all tau_ceti.analysis.contour.winding.endpoint_ratio
import all tau_ceti.analysis.contour.winding.integer
import all tau_ceti.analysis.contour.winding.locally_constant
import all tau_ceti.analysis.contour.winding.number.concat
import all tau_ceti.analysis.contour.winding.number.segment.jump
import all tau_ceti.analysis.contour.curve.approximation
import all tau_ceti.analysis.contour.winding.separation
import all tau_ceti.analysis.complex.plane_separation.local_separation
import all graph_polygon
import all triangle_sides
import all polygon_local
import all face_separation
import all triangular_disk
import all cycle_barrier
import all boundary_corners
import all falling_paths
import all exterior_path
import all walk_cycle
import all harmonic_adjacent
import all planar_geometry
import all planar_tools
import all cap_polarity_geometry
import all cap_extraction_geometry
import all punctured_convex
import all face_graph
import all interval_chain
import all harmonic_embedding
import all maxwell_core
import all maxwell_development
import all cor2_complete
import Lean.Elab.Command
import Lean.Meta.Basic
import Lean.Util.CollectAxioms
import Lean.Data.Json.Basic
import Lean.Data.Json.FromToJson.Basic
import Lean.Data.Json.Printer

-- Generated verification output directories.
run_cmd Lean.Elab.Command.liftIO do
  IO.FS.createDirAll ".lake/reports/audit/final"


/-!
# Normal–projective verification: complete project entry point

This entry point includes every principal mathematical claim. The current
verification status is recorded separately in `audit/current/checkpoint_status.json`.
`Complete` proves the full component characterization (Theorem 1)
and the local `2d`-move statement (Lemma 4), in every dimension, for actual labelled
full-dimensional polytopes and their actual affine quotient. It also proves
Theorem 3 in all dimensions `d ≥ 2`: exactly `d-1` projective and `d-2` normal
moves suffice for every cube, every cyclic member with `0 < ε < 1` requires
at least both counts, and the largest actual minimum distance to `[-1,1]^d`
is `2d-3`, allowing every induced endpoint facet labelling.
`PolarCorrection` verifies the
counterexample to the auxiliary polarity identity with a boundary origin.

`cor2_complete` contains the proof of Corollary 2 through geometric harmonic
embeddings, the planar Euler count, Maxwell lifting, and paths of actual
convex caps. Importing the root therefore requires checking this entire chain.
-/


/-!
# Actual declaration-body and transitive axiom audit

Every definition and theorem belonging to the local mathematical import
closure is inspected with its private body available. The only accepted
axioms are Lean's ordinary classical foundations: propext, Classical.choice,
and Quot.sound. This audit command adds no theorem or axiom.
-/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let localModules : Array Name := #[`normal_projective.admissible_projectivity, `normal_projective.geometry, `normal_projective.uniform_bound, `normal_projective.halfspace_faces, `normal_projective.simple_vertices, `normal_projective.simple_stability, `normal_projective.face_correspondence, `normal_projective.stable_incidence, `normal_projective.canonical_model, `normal_projective.unit_normalization, `normal_projective.normalization_topology, `normal_projective.elementary_projectivity, `normal_projective.local_control, `normal_projective.control, `normal_projective.connected_classes, `normal_projective.rank_obstruction, `normal_projective.complete, `normal_projective.polar_correction, `dirichlet, `closed_cover, `triangulation, `subfaces, `dirichlet_strong, `region_barrier, `tau_ceti.data.fin.basic, `tau_ceti.geometry.polygon.basic, `tau_ceti.analysis.complex.circle, `tau_ceti.topology.locally_connected, `tau_ceti.topology.jordan_curve.basic, `tau_ceti.analysis.convex.between, `tau_ceti.geometry.polygon.simple, `tau_ceti.analysis.normed.module.convex, `tau_ceti.topology.unit_interval, `tau_ceti.topology.homotopy.path, `tau_ceti.topology.path_component, `tau_ceti.topology.connected_components, `tau_ceti.topology.frontier, `tau_ceti.topology.filled_hull, `tau_ceti.analysis.normed.module.ball.exterior, `tau_ceti.analysis.normed.module.ball, `tau_ceti.analysis.normed.module.filled_hull, `tau_ceti.analysis.complex.continuous_log.basic, `tau_ceti.analysis.complex.plane_separation.basic, `tau_ceti.topology.circle.arc, `tau_ceti.analysis.special_functions.trigonometric.arccos, `tau_ceti.topology.circle.metric, `tau_ceti.topology.jordan_curve.separation, `tau_ceti.topology.jordan_curve.small_arc, `tau_ceti.topology.jordan_curve.subcontinuum, `tau_ceti.analysis.complex.continuous_log.path, `tau_ceti.analysis.complex.plane_separation.jordan_curve, `tau_ceti.analysis.contour.cauchy.principal_value.basic, `tau_ceti.analysis.contour.winding.number.basic, `tau_ceti.analysis.contour.null_homologous, `tau_ceti.analysis.contour.winding.number.scale, `tau_ceti.analysis.contour.winding.number.translate, `tau_ceti.analysis.contour.winding.number.affine, `tau_ceti.analysis.complex.upper_log_continuity, `tau_ceti.analysis.contour.piecewise_c1_on, `tau_ceti.analysis.contour.curve.integrability, `tau_ceti.analysis.contour.log_deriv_ftc, `tau_ceti.analysis.contour.winding.number.segment.formula, `tau_ceti.analysis.contour.curve.distance, `tau_ceti.analysis.contour.winding.number.reverse, `tau_ceti.analysis.contour.winding.continuity, `tau_ceti.analysis.contour.argument.lift, `tau_ceti.analysis.contour.winding.segment_sum, `tau_ceti.analysis.contour.winding.endpoint_ratio, `tau_ceti.analysis.contour.winding.integer, `tau_ceti.analysis.contour.winding.locally_constant, `tau_ceti.analysis.contour.winding.number.concat, `tau_ceti.analysis.contour.winding.number.segment.jump, `tau_ceti.analysis.contour.curve.approximation, `tau_ceti.analysis.contour.winding.separation, `tau_ceti.analysis.complex.plane_separation.local_separation, `graph_polygon, `triangle_sides, `polygon_local, `face_separation, `triangular_disk, `cycle_barrier, `boundary_corners, `falling_paths, `exterior_path, `walk_cycle, `harmonic_adjacent, `planar_geometry, `planar_tools, `cap_polarity_geometry, `cap_extraction_geometry, `punctured_convex, `face_graph, `interval_chain, `harmonic_embedding, `maxwell_core, `maxwell_development, `cor2_complete]
  let moduleOf (n : Name) : Name :=
    match env.getModuleIdxFor? n with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => env.mainModule
  let isLocal (n : Name) : Bool := localModules.contains (moduleOf n)
  let names := env.constants.fold (init := (#[] : Array Name)) fun ns n _ =>
    if isLocal n then ns.push n else ns
  let names := names.qsort Name.lt
  let mut records : Array Json := #[]
  let mut boundaries : NameSet := {}
  for n in names do
    let some ci := env.find? n | throwError "Missing imported declaration {n}"
    match ci with
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
        unless (ci.value? true).isSome do
          throwError "Local proof or definition body unavailable: {n}"
    | .axiomInfo _ => throwError "Local axiom declaration is forbidden: {n}"
    | _ => pure ()
    let axs ← collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved transitive axiom {ax} in {n}"
    let typeDeps := ci.type.getUsedConstants
    let valueDeps := (ci.value? true).map Expr.getUsedConstants |>.getD #[]
    let ctorDeps := match ci with
      | .inductInfo v => v.ctors.toArray
      | _ => #[]
    let deps := (typeDeps ++ valueDeps ++ ctorDeps).foldl (fun s x => s.insert x) ({} : NameSet)
    for d in deps.toArray do
      unless isLocal d do boundaries := boundaries.insert d
    let typeString ← liftTermElabM <| return (← Meta.ppExpr ci.type).pretty
    records := records.push <| Json.mkObj [
      ("name", toJson n.toString), ("module", toJson (moduleOf n).toString),
      ("type", toJson typeString),
      ("proof_or_definition_body_available", toJson (ci.value? true).isSome),
      ("direct_dependencies", toJson (deps.toArray.qsort Name.lt |>.map Name.toString)),
      ("transitive_axioms", toJson (axs.map Name.toString))]
  let mut boundaryRecords : Array Json := #[]
  for n in boundaries.toArray.qsort Name.lt do
    let axs ← collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved library-boundary axiom {ax} in {n}"
    boundaryRecords := boundaryRecords.push <| Json.mkObj [
      ("name", toJson n.toString), ("module", toJson (moduleOf n).toString),
      ("transitive_axioms", toJson (axs.map Name.toString))]
  let result := Json.mkObj [
    ("lean_version", toJson "4.35.0"),
    ("mathlib_commit", toJson "56a005855ea17e0b0958f73ec801ae140b0a1679"),
    ("local_modules", toJson (localModules.map Name.toString)),
    ("local_declarations", Json.arr records),
    ("pinned_library_boundary", Json.arr boundaryRecords),
    ("unapproved_axioms", Json.arr #[])]
  IO.FS.createDirAll ".lake/reports/audit/final"
  IO.FS.writeFile ".lake/reports/audit/final/actual_dependencies.json" result.pretty
  logInfo m!"Audited {records.size} local declarations and {boundaryRecords.size} pinned-library boundaries."

set_option pp.proofs false in
#check @NormalProjective.CanonicalModel.Realization.pnRelated_iff_same_component
#print axioms NormalProjective.CanonicalModel.Realization.pnRelated_iff_same_component
set_option pp.proofs false in
#check @NormalProjective.simple_three_pn_unique
#print axioms NormalProjective.simple_three_pn_unique
set_option pp.proofs false in
#check @NormalProjective.simple_three_presentations_pn
#print axioms NormalProjective.simple_three_presentations_pn
set_option pp.proofs false in
#check @NormalProjective.simple_three_faceOrderIso_pn
#print axioms NormalProjective.simple_three_faceOrderIso_pn
set_option pp.proofs false in
#check @NormalProjective.CubeTargetLabels.geometric_largest_PN_distance
#print axioms NormalProjective.CubeTargetLabels.geometric_largest_PN_distance
#print axioms NormalProjective.normalized_matrix_local_word
set_option pp.proofs false in
#check @NormalProjective.CanonicalModel.Realization.local_word_neighbourhood
#print axioms NormalProjective.CanonicalModel.Realization.local_word_neighbourhood
set_option pp.proofs false in
#check @NormalProjective.CubeUpper.every_cube_exact_word
#print axioms NormalProjective.CubeUpper.every_cube_exact_word
set_option pp.proofs false in
#check @NormalProjective.CubeUpper.every_cube_exact_word_of_faceOrderIso
#print axioms NormalProjective.CubeUpper.every_cube_exact_word_of_faceOrderIso
set_option pp.proofs false in
#check @NormalProjective.CubeTargetLabels.cyclic_to_geometric_cube_lower_bound
#print axioms NormalProjective.CubeTargetLabels.cyclic_to_geometric_cube_lower_bound
set_option pp.proofs false in
#check @NormalProjective.Planar.TriangularDisk.elementary_face_count
#print axioms NormalProjective.Planar.TriangularDisk.elementary_face_count
set_option pp.proofs false in
#check @NormalProjective.Planar.StrictConvexCap.exists_path_sameCombinatorics
#print axioms NormalProjective.Planar.StrictConvexCap.exists_path_sameCombinatorics
set_option pp.proofs false in
#check @NormalProjective.FiniteHullModel.finite_hull_has_facet_model_all_dimensions
#print axioms NormalProjective.FiniteHullModel.finite_hull_has_facet_model_all_dimensions
#print axioms NormalProjective.PolarCorrection.boundary_origin_counterexample
