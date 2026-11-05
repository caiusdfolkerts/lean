module

public import Lean.Elab.Command
public import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
import all volume_polynomials.mixed_volume_basis_part01
import all volume_polynomials.mixed_volume_basis_part02
import all rank_three_algebra
import all volume_polynomials.projection_area_foundation
import all projection_core
import all projection_boundary
import all projection_escape
import all main
import all additional_results

-- Generated verification output directories.
run_cmd Lean.Elab.Command.liftIO do
  IO.FS.createDirAll ".lake/reports/audit"


set_option Elab.async false
set_option debug.skipKernelTC false

/-!
# Complete local proof dependency audit

This module performs no mathematical construction. It reads the already
checked kernel declarations, expands every local proof dependency (including
both mixed-volume bases), checks their transitive axioms, and writes the
combined statement report and graph in `audit/`.

The module imports private proof bodies solely for inspection. An audit
report does not replace successful source compilation of its dependencies.
-/

set_option maxHeartbeats 0 in
run_cmd do
  let env := (← Lean.getEnv).setExporting false
  if Lean.debug.skipKernelTC.get (← Lean.getOptions) then
    throwError "The ordinary Lean kernel checker must be enabled"
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  let compiledProjectModules : Array Lean.Name := #[
    `volume_polynomials.mixed_volume_basis_part01,
    `volume_polynomials.mixed_volume_basis_part02,
    `rank_three_algebra,
    `volume_polynomials.projection_area_foundation,
    `projection_core,
    `projection_boundary,
    `projection_escape,
    `main,
    `additional_results]
  let moduleOf (name : Lean.Name) : Lean.Name :=
    match env.getModuleIdxFor? name with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => env.mainModule
  let expandedProjectModules := compiledProjectModules.push env.mainModule
  let required : Array Lean.Name := #[
    `ProjectionAreaPaper.positive_rank_three_obstruction,
    `ProjectionAreaPaper.positive_rank_le_three_not_realizable,
    `ProjectionAreaPaper.positive_rank_le_three_not_in_closure,
    `ProjectionAreaPaper.escapeCone_eq_divergingDiameterLimits,
    `ProjectionAreaPaper.mem_escapeCone_iff_exists_diverging_sequence,
    `ProjectionAreaPaper.closure_realizationLocus_eq_union_escapeCone,
    `ProjectionAreaPaper.mem_escapeCone_iff_exists_full_dimensional_symmetric_sequence,
    `ProjectionAreaPaper.escapeCone_isClosed,
    `ProjectionAreaStrict.strict_weighted_realization,
    `ProjectionAreaStrict.strict_weighted_realization_with_vertex_bound,
    `ProjectionAreaStrict.strict_nonnegative_weighted_realization_with_vertex_bound,
    `ProjectionAreaPaper.NonnegativeHollowMatrix.rank_at_most_three_classification,
    `ProjectionAreaPaper.exists_open_nonrealizable_strict_quartets,
    `ProjectionAreaPaper.boundary_compatibility,
    `ProjectionAreaMixedGeometry.actual_boundary_choices_compatible,
    `ProjectionAreaSharpness.sharp_three_boundary_quartets,
    `ProjectionAreaMixedGeometry.boundary_quartets_bound_sharp,
    `ProjectionAreaMixedGeometry.boundary_quartets_unique_extension,
    `ProjectionAreaPaper.selected_boundary_quartets_card_le_three,
    `ProjectionAreaPaper.selected_boundary_quartets_unique_extension,
    `ProjectionAreaSpectralZero.local_spectral_zero_reduction,
    `ProjectionAreaEscape.ExactPrism.coordinate_area_prism,
    `ProjectionAreaEscape.exists_polytope_prescribed_widths,
    `ProjectionAreaEscape.exists_prescribed_width_polytope_exact_prisms,
    `ProjectionAreaRankThree.PositiveHollowMatrix.weighted_triangles_obstruction,
    `ProjectionAreaPaper.all_zero_realized_by_point,
    `ProjectionAreaMixedGeometry.five_positive_rank_not_le_three,
    `ProjectionAreaMixedGeometry.triple_projection_interior,
    `ProjectionAreaMixedGeometry.deletion_fiberHull_of_kernel,
    `ProjectionAreaMixedGeometry.mixedVolume_two_coordinateSegments,
    `ProjectionAreaFourDimensional.exists_realizer_of_nonpositive_determinant,
    `VolumePolynomials.mixedVolume_alexandrovFenchel,
    `ProjectionAreaExamples.hexagonPoint_norm,
    `ProjectionAreaExamples.hexagonMatrix_eq_sq_dist,
    `ProjectionAreaExamples.hexagonPoint_injective,
    `ProjectionAreaExamples.hexagon_rank,
    `ProjectionAreaExamples.hexagon_obstruction,
    `ProjectionAreaExamples.hexagon_has_no_escape_weights,
    `ProjectionAreaPaper.closure_strictWeightedLocus,
    `ProjectionAreaPaper.strictWeightedLocus_subset_realizationLocus,
    `ProjectionAreaPaper.closure_realizable_strictWeightedLocus,
    `ProjectionAreaPaper.unit_seminorm_of_escapeCone,
    `ProjectionAreaPaper.escaping_limit_seminorm,
    `ProjectionAreaCircleMetric.rank_three_circle_realization,
    `ProjectionAreaExamples.hexagon_quadratic_form,
    `ProjectionAreaExamples.hexagon_signature,
    `ProjectionAreaBrightness.brightness_hlawka,
    `ProjectionAreaBrightness.brightness_pos,
    `ProjectionAreaFullInterior.positive_boundary_interior,
    `ProjectionAreaFullInterior.positive_boundary_interior_of_det_zero,
    `ProjectionAreaFullInterior.positive_boundary_interior_of_equality,
    `ProjectionAreaZeroDimension.coordinateBody_zero_diameter,
    `ProjectionAreaZeroDimension.strict_empty_data_counterexample,
    `ProjectionAreaPaper.boundary_compatibility_of_local_positivity,
    `ProjectionAreaMixedGeometry.positiveOnQuartet_coordinateAreaMatrix_iff]
  let defining : Array Lean.Name := #[
    `ProjectionAreaTopology.coordinateAreas,
    `ProjectionAreaTopology.realizationLocus,
    `ProjectionAreaTopology.divergingDiameterLimits,
    `ProjectionAreaTopology.escapingLimits,
    `ProjectionAreaEscape.IsSymmetricPolytope,
    `ConvexBody.mk,
    `ProjectionAreaEscape.EscapeCone,
    `ProjectionAreaEscape.WeightedTriangleWitness,
    `ProjectionAreaEscape.pairWidth,
    `ProjectionAreaEscape.pairFunctional,
    `ProjectionAreaEscape.ExactPrism.prism,
    `ProjectionAreaRankThree.PositiveHollowMatrix,
    `ProjectionAreaRankThree.PositiveHollowMatrix.mk,
    `ProjectionAreaRankThree.NonnegativeHollowMatrix,
    `ProjectionAreaRankThree.NonnegativeHollowMatrix.mk,
    `ProjectionAreaRankThree.NonnegativeHollowMatrix.Classes,
    `ProjectionAreaRankThree.NonnegativeHollowMatrix.zeroSetoid,
    `ProjectionAreaRankThree.NonnegativeHollowMatrix.quotientPositive,
    `ProjectionAreaRankThree.NonnegativeHollowMatrix.replicationMatrix,
    `ProjectionAreaStrict.metricPolytope,
    `ProjectionAreaStrict.euclideanDiameter,
    `ProjectionAreaMixedGeometry.coordinateAreaMatrix,
    `ProjectionAreaMixedGeometry.BoundaryAt,
    `ProjectionAreaMixedGeometry.BoundaryPartitionExtension,
    `ProjectionAreaSharpness.IsBoundaryQuartet,
    `ProjectionAreaSharpness.sharpBody,
    `ProjectionAreaSpectralZero.LocalFourSpectral,
    `ProjectionAreaSpectralZero.zeroSetoid,
    `ProjectionAreaSpectralZero.Classes,
    `ProjectionAreaSpectralZero.Representatives,
    `ProjectionAreaSpectralZero.quotientPositive,
    `VolumePolynomials.mixedVolume,
    `VolumePolynomials.volumePolynomial,
    `ProjectionAreaExamples.hexagonMatrix,
    `ProjectionAreaExamples.hexagonPoint,
    `ProjectionAreaPaper.strictWeightedLocus,
    `ProjectionAreaEscape.widthEvaluation,
    `ProjectionAreaEscape.widthSeminorm,
    `ProjectionAreaPaper.coordinateBasisVector,
    `ProjectionAreaCircleMetric.Plane,
    `ProjectionAreaRankThree.PositiveMetricMatrix,
    `ProjectionAreaRankThree.PositiveMetricMatrix.mk,
    `ProjectionAreaCircleMetric.point,
    `ProjectionAreaCircleMetric.rectanglePoints,
    `ProjectionAreaCircleMetric.IsRectangleSet,
    `ProjectionAreaBrightness.brightness,
    `ProjectionAreaBoundaryKernel.BoundaryEquality,
    `ProjectionAreaMixedGeometry.PositiveOnQuartet]
  let mut statements : Array Lean.Json := #[]
  for name in required do
    let some ci := env.find? name
      | throwError "Required theorem is missing: {name}"
    unless ci.isTheorem do
      throwError "Required entry is not a kernel theorem: {name}"
    unless (ci.value? (allowOpaque := true)).isSome do
      throwError "Actual proof body is unavailable for required theorem: {name}"
    unless (← Lean.Elab.Command.liftTermElabM <| Lean.Meta.isProp ci.type) do
      throwError "Required entry is not a proposition: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unapproved transitive axiom in {name}: {ax}"
    let prettyType ← Lean.Elab.Command.liftTermElabM <| Lean.Meta.ppExpr ci.type
    statements := statements.push <| Lean.Json.mkObj [
      ("name", Lean.toJson name.toString),
      ("module", Lean.toJson (moduleOf name).toString),
      ("compiled_project_stage", Lean.toJson (compiledProjectModules.contains (moduleOf name))),
      ("proof_body_available", Lean.toJson true),
      ("type", Lean.toJson prettyType.pretty),
      ("complete_type_expression", Lean.toJson (reprStr ci.type)),
      ("axioms", Lean.toJson (axioms.map Lean.Name.toString))]
  let mut definitions : Array Lean.Json := #[]
  for name in defining do
    let some ci := env.find? name
      | throwError "Defining mathematical constant is missing: {name}"
    let prettyType ← Lean.Elab.Command.liftTermElabM <| Lean.Meta.ppExpr ci.type
    let mut row := [
      ("name", Lean.toJson name.toString),
      ("module", Lean.toJson (moduleOf name).toString),
      ("compiled_project_stage", Lean.toJson (compiledProjectModules.contains (moduleOf name))),
      ("type", Lean.toJson prettyType.pretty),
      ("complete_type_expression", Lean.toJson (reprStr ci.type))]
    if let some value := ci.value? (allowOpaque := true) then
      let prettyValue ← Lean.Elab.Command.liftTermElabM <| Lean.Meta.ppExpr value
      row := row ++ [("value", Lean.toJson prettyValue.pretty),
        ("complete_value_expression", Lean.toJson (reprStr value))]
    definitions := definitions.push (Lean.Json.mkObj row)
  let mut pending : List Lean.Name := (required ++ defining).toList
  let mut seen : Lean.NameSet := {}
  let mut nodes : Array Lean.Json := #[]
  let mut foundAxioms : Lean.NameSet := {}
  while !pending.isEmpty do
    match pending with
    | [] => pure ()
    | name :: rest =>
      pending := rest
      unless seen.contains name do
        seen := seen.insert name
        let some ci := env.find? name
          | throwError "A logical dependency cannot be inspected: {name}"
        let imported := (env.getModuleIdxFor? name).isSome
        let moduleName := moduleOf name
        let compiledStage := imported && compiledProjectModules.contains moduleName
        let importedBoundary := imported && !compiledStage
        let mut boundaryAxioms : Array Lean.Name := #[]
        let dependencies ← if importedBoundary then do
          -- Only pinned external libraries and Lean itself form this boundary.
          -- Every local stage, including both mixed-volume basis modules,
          -- is expanded through its actual private proof bodies.
          boundaryAxioms ← Lean.collectAxioms name
          for ax in boundaryAxioms do
            unless allowed.contains ax do
              throwError "Unapproved imported transitive axiom in {name}: {ax}"
            foundAxioms := foundAxioms.insert ax
          pure []
        else do
          -- Explicit `import all` loads each compiled project stage's full
          -- ConstantInfo records. In private scope this traverses actual proof
          -- bodies, including private helpers, across the stage boundaries.
          if ci.isUnsafe || ci.isPartial then
            throwError "An unsafe or partial declaration occurs in the logical graph: {name}"
          if ci.isAxiom then
            foundAxioms := foundAxioms.insert name
            unless allowed.contains name do
              throwError "Unapproved axiom in the transitive graph: {name}"
          pure ci.getUsedConstantsAsSet.toList
        pending := dependencies ++ pending
        nodes := nodes.push <| Lean.Json.mkObj [
          ("name", Lean.toJson name.toString),
          ("module", Lean.toJson moduleName.toString),
          ("is_theorem", Lean.toJson ci.isTheorem),
          ("compiled_project_stage", Lean.toJson compiledStage),
          ("proof_body_available", Lean.toJson ((ci.value? (allowOpaque := true)).isSome)),
          ("imported_checked_boundary", Lean.toJson importedBoundary),
          ("imported_transitive_axioms", Lean.toJson (boundaryAxioms.map Lean.Name.toString)),
          ("is_local_axiom", Lean.toJson (!importedBoundary && ci.isAxiom)),
          ("dependencies", Lean.toJson (dependencies.map Lean.Name.toString))]
  let graph := Lean.Json.mkObj [
    ("roots", Lean.toJson ((required ++ defining).map Lean.Name.toString)),
    ("expanded_project_modules", Lean.toJson (expandedProjectModules.map Lean.Name.toString)),
    ("allowed_axioms", Lean.toJson (allowed.map Lean.Name.toString)),
    ("encountered_axioms", Lean.toJson (foundAxioms.toList.map Lean.Name.toString)),
    ("node_count", Lean.toJson nodes.size),
    ("nodes", Lean.Json.arr nodes)]
  let report := Lean.Json.mkObj [
    ("scope", Lean.toJson "Combined theorem and definition audit. Every local mathematical module, including both mixed-volume bases and the additional results, is expanded through actual private proof bodies. The graph stops only at Lean and pinned external library declarations, using stock Lean's exported transitive axiom metadata. Separate successful compiler checks bind every local module to its actual source and artifacts."),
    ("required_separate_gate", Lean.toJson "Require complete successful ordinary compiler runs for every compiled project stage and the final module, bound to the current source and artifact hashes. This audit output alone is not a successful verification."),
    ("expanded_project_modules", Lean.toJson (expandedProjectModules.map Lean.Name.toString)),
    ("required_statements", Lean.Json.arr statements),
    ("defining_constants", Lean.Json.arr definitions),
    ("allowed_axioms", Lean.toJson (allowed.map Lean.Name.toString)),
    ("dependency_node_count", Lean.toJson nodes.size)]
  Lean.Elab.Command.liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/full-dependency-graph.json" graph.pretty
  Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/full-statements-and-axioms.json" report.pretty
  Lean.logInfo m!"FULL LOCAL DEPENDENCY AUDIT PASSED: {required.size} kernel theorems, {nodes.size} transitive logical declarations; only the standard axioms."
