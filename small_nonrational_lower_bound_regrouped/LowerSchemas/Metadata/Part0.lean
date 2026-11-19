module
public meta import NumericProofSchema
public meta section
open Lean Elab Command

elab "cert_graph_aligned " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_aligned : ∀ c, Aligned record⟪0⟫ SharedSix0CellPool.entry c :=
  aligned_of_interval record⟪0⟫ SharedSix0CellPool.entry record⟪0⟫_alignment_checked"### args

elab "cert_graph_aligned_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_aligned : ∀ c, Aligned record⟪0⟫ SharedSmallCellPool.entry c :=
  aligned_of_interval record⟪0⟫ SharedSmallCellPool.entry record⟪0⟫_alignment_checked"### args

elab "cert_graph_alignment_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_alignment_⟪1⟫ : Interval (alignedCheck record⟪0⟫ SharedSmallCellPool.entry) ⟪2⟫ ⟪3⟫ := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow⟪4⟫Part⟪5⟫.record⟪6⟫_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))"### args

elab "cert_graph_alignment_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_alignment_⟪1⟫ : Interval (alignedCheck record⟪0⟫ SharedSmallCellPool.entry) ⟪2⟫ ⟪3⟫ :=
  interval_of_check _ ⟪2⟫ ⟪4⟫ (by decide +kernel)"### args

elab "cert_graph_alignment_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_alignment_⟪1⟫ : Interval (alignedCheck record⟪0⟫ SharedSix0CellPool.entry) ⟪2⟫ ⟪3⟫ :=
  interval_of_check _ ⟪2⟫ ⟪4⟫ (by decide +kernel)"### args

elab "cert_graph_alignment_checked " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_alignment_checked : Interval (alignedCheck record⟪0⟫ SharedSmallCellPool.entry) 0 ⟪1⟫ :=
  (interval_append _ 0 64 ⟪1⟫ record⟪0⟫_alignment_0 (interval_append _ 64 128 ⟪1⟫ record⟪0⟫_alignment_1 record⟪0⟫_alignment_2))"### args

elab "cert_graph_alignment_checked_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_alignment_checked : Interval (alignedCheck record⟪0⟫ SharedSix0CellPool.entry) 0 ⟪1⟫ :=
  (interval_append _ 0 64 ⟪1⟫ record⟪0⟫_alignment_0 record⟪0⟫_alignment_1)"### args

elab "cert_graph_alignment_checked_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_alignment_checked : Interval (alignedCheck record⟪0⟫ SharedSix0CellPool.entry) 0 ⟪1⟫ :=
  (interval_append _ 0 64 ⟪1⟫ record⟪0⟫_alignment_0 (interval_append _ 64 128 ⟪1⟫ record⟪0⟫_alignment_1 record⟪0⟫_alignment_2))"### args

elab "cert_graph_alignment_checked_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_alignment_checked : Interval (alignedCheck record⟪0⟫ SharedSmallCellPool.entry) 0 ⟪1⟫ :=
  record⟪0⟫_alignment_0"### args

elab "cert_graph_alignment_checked_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_alignment_checked : Interval (alignedCheck record⟪0⟫ SharedSmallCellPool.entry) 0 ⟪1⟫ :=
  (interval_append _ 0 64 ⟪1⟫ record⟪0⟫_alignment_0 record⟪0⟫_alignment_1)"### args

elab "cert_graph_alignment_checked_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_alignment_checked : Interval (alignedCheck record⟪0⟫ SharedSix0CellPool.entry) 0 ⟪1⟫ :=
  record⟪0⟫_alignment_0"### args

elab "cert_graph_cells_exact " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_cells_exact : ∀ c, record⟪0⟫.data.cells c = FacetUniverses.FullSix0.cells (embedding record⟪0⟫ c) :=
  literal_cells record⟪0⟫ SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record⟪0⟫_aligned"### args

elab "cert_graph_cells_exact_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_cells_exact : ∀ c, record⟪0⟫.data.cells c = FacetUniverses.FullSmall.cells (embedding record⟪0⟫ c) :=
  literal_cells record⟪0⟫ SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record⟪0⟫_aligned"### args

elab "cert_graph_edge_matrix " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_edge_matrix :
    record⟪0⟫.data.edgeMatrix = PackedIncidenceMatrix.code record⟪0⟫.data.edgeLists := by
  decide +kernel"### args

elab "cert_graph_edge_matrix_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_edge_matrix :
    record⟪0⟫.data.edgeMatrix = PackedIncidenceMatrix.code record⟪0⟫.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow⟪1⟫Part⟪2⟫.record⟪3⟫_edge_matrix"### args

elab "cert_graph_kind_checked " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_kind_checked : Interval record⟪0⟫.data.kindTest 0 record⟪0⟫.k :=
  interval_of_check _ 0 5 (by decide +kernel)"### args

elab "cert_graph_kind_checked_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_kind_checked : Interval record⟪0⟫.data.kindTest 0 record⟪0⟫.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow⟪1⟫Part⟪2⟫.record⟪3⟫_kind_checked"### args

elab "cert_graph_literal " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_literal : RawGraphSemanticCertificate.LiteralFacts record⟪0⟫.data :=
  literal_facts record⟪0⟫ SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record⟪0⟫_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record⟪0⟫ SharedSmallCellPool.entry record⟪0⟫_vertex_width record⟪0⟫_vertex_code)"### args

elab "cert_graph_literal_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_literal : RawGraphSemanticCertificate.LiteralFacts record⟪0⟫.data :=
  literal_facts record⟪0⟫ SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record⟪0⟫_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record⟪0⟫ SharedSix0CellPool.entry record⟪0⟫_vertex_width record⟪0⟫_vertex_code)"### args

elab "cert_graph_local_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_local_⟪1⟫ : Interval (localCheck record⟪0⟫) ⟪2⟫ ⟪3⟫ :=
  interval_of_check _ ⟪2⟫ ⟪4⟫ (by decide +kernel)"### args

elab "cert_graph_local_checked " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_local_checked : Interval (localCheck record⟪0⟫) 0 ⟪1⟫ :=
  (interval_append _ 0 64 ⟪1⟫ record⟪0⟫_local_0 record⟪0⟫_local_1)"### args

elab "cert_graph_local_checked_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_local_checked : Interval (localCheck record⟪0⟫) 0 ⟪1⟫ :=
  interval_of_check _ 0 ⟪1⟫ (by decide +kernel)"### args

elab "cert_graph_local_checked_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_local_checked : Interval (localCheck record⟪0⟫) 0 ⟪1⟫ :=
  record⟪0⟫_local_0"### args

elab "cert_graph_local_checked_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_local_checked : Interval (localCheck record⟪0⟫) 0 ⟪1⟫ :=
  (interval_append _ 0 64 ⟪1⟫ record⟪0⟫_local_0 (interval_append _ 64 128 ⟪1⟫ record⟪0⟫_local_1 record⟪0⟫_local_2))"### args

elab "cert_graph_matrix_checked " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_matrix_checked : MatrixGraphProblem.Checked record⟪0⟫.data :=
  matrix_checked record⟪0⟫ SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record⟪0⟫_aligned (by decide +kernel) record⟪0⟫_local_checked
    record⟪0⟫_kind_checked record⟪0⟫_ridge_matrix record⟪0⟫_edge_matrix record⟪0⟫_missing_matrix"### args

elab "cert_graph_matrix_checked_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_matrix_checked : MatrixGraphProblem.Checked record⟪0⟫.data :=
  matrix_checked record⟪0⟫ SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record⟪0⟫_aligned (by decide +kernel) record⟪0⟫_local_checked
    record⟪0⟫_kind_checked record⟪0⟫_ridge_matrix record⟪0⟫_edge_matrix record⟪0⟫_missing_matrix"### args

elab "cert_graph_missing_matrix " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_missing_matrix :
    record⟪0⟫.data.missingMatrix = PackedIncidenceMatrix.code record⟪0⟫.data.missingLists := by
  decide +kernel"### args

elab "cert_graph_missing_matrix_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_missing_matrix :
    record⟪0⟫.data.missingMatrix = PackedIncidenceMatrix.code record⟪0⟫.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow⟪1⟫Part⟪2⟫.record⟪3⟫_missing_matrix"### args

elab "cert_graph_ridge_matrix " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_ridge_matrix :
    record⟪0⟫.data.candidateMatrix = PackedIncidenceMatrix.code record⟪0⟫.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow⟪1⟫Part⟪2⟫.record⟪3⟫_ridge_matrix"### args

elab "cert_graph_ridge_matrix_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_ridge_matrix :
    record⟪0⟫.data.candidateMatrix = PackedIncidenceMatrix.code record⟪0⟫.data.ridgeList := by
  decide +kernel"### args

elab "cert_graph_validity " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_validity : GraphGrowthInputs.Valid record⟪0⟫.inputs :=
  valid_of_matrix record⟪0⟫ record⟪0⟫_matrix_checked"### args

elab "cert_graph_vertex_code " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_vertex_code : record⟪0⟫.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record⟪0⟫ SharedSmallCellPool.entry c).vertices) := by decide +kernel"### args

elab "cert_graph_vertex_code_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_vertex_code : record⟪0⟫.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record⟪0⟫ SharedSix0CellPool.entry c).vertices) := by decide +kernel"### args

elab "cert_graph_vertex_code_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_vertex_code : record⟪0⟫.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record⟪0⟫ SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow⟪1⟫Part⟪2⟫.record⟪3⟫_vertex_code"### args

elab "cert_graph_vertex_width " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_vertex_width : record⟪0⟫.vertexRows.width = record⟪0⟫.n := by decide +kernel"### args

elab "cert_graph_vertex_width_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_vertex_width : record⟪0⟫.vertexRows.width = record⟪0⟫.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow⟪1⟫Part⟪2⟫.record⟪3⟫_vertex_width"### args

