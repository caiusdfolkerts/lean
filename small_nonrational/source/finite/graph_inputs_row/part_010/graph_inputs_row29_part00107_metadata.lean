module
prelude
public import GraphInputsRow29Part00107Data
public import SharedGraphCellPool
public import SharedSmallCellPoolChecked
public import GraphInputsRow25Part00013Metadata

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00107
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool FiniteChecks

theorem record000_alignment_0 : Interval (alignedCheck record000 SharedSmallCellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record000_alignment_1 : Interval (alignedCheck record000 SharedSmallCellPool.entry) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)

theorem record000_alignment_checked : Interval (alignedCheck record000 SharedSmallCellPool.entry) 0 111 :=
  (interval_append _ 0 64 111 record000_alignment_0 record000_alignment_1)
theorem record000_aligned : ∀ c, Aligned record000 SharedSmallCellPool.entry c :=
  aligned_of_interval record000 SharedSmallCellPool.entry record000_alignment_checked

theorem record000_local_0 : Interval (localCheck record000) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record000_local_1 : Interval (localCheck record000) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)

theorem record000_local_checked : Interval (localCheck record000) 0 111 :=
  (interval_append _ 0 64 111 record000_local_0 record000_local_1)
theorem record000_kind_checked : Interval record000.data.kindTest 0 record000.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record000_ridge_matrix :
    record000.data.candidateMatrix = PackedIncidenceMatrix.code record000.data.ridgeList := by
  decide +kernel

theorem record000_edge_matrix :
    record000.data.edgeMatrix = PackedIncidenceMatrix.code record000.data.edgeLists := by
  decide +kernel

theorem record000_missing_matrix :
    record000.data.missingMatrix = PackedIncidenceMatrix.code record000.data.missingLists := by
  decide +kernel

theorem record000_matrix_checked : MatrixGraphProblem.Checked record000.data :=
  matrix_checked record000 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record000_aligned (by decide +kernel) record000_local_checked
    record000_kind_checked record000_ridge_matrix record000_edge_matrix record000_missing_matrix

theorem record000_validity : GraphGrowthInputs.Valid record000.inputs :=
  valid_of_matrix record000 record000_matrix_checked

theorem record000_vertex_width : record000.vertexRows.width = record000.n := by decide +kernel

theorem record000_vertex_code : record000.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record000 SharedSmallCellPool.entry c).vertices) := by decide +kernel

theorem record000_literal : RawGraphSemanticCertificate.LiteralFacts record000.data :=
  literal_facts record000 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record000_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record000 SharedSmallCellPool.entry record000_vertex_width record000_vertex_code)

theorem record000_cells_exact : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c) :=
  literal_cells record000 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record000_aligned

#print axioms record000_validity
#print axioms record000_literal

theorem record001_alignment_0 : Interval (alignedCheck record001 SharedSmallCellPool.entry) 0 64 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record029_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record001_alignment_1 : Interval (alignedCheck record001 SharedSmallCellPool.entry) 64 107 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record029_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record001_alignment_checked : Interval (alignedCheck record001 SharedSmallCellPool.entry) 0 107 :=
  (interval_append _ 0 64 107 record001_alignment_0 record001_alignment_1)
theorem record001_aligned : ∀ c, Aligned record001 SharedSmallCellPool.entry c :=
  aligned_of_interval record001 SharedSmallCellPool.entry record001_alignment_checked

theorem record001_local_0 : Interval (localCheck record001) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record001_local_1 : Interval (localCheck record001) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)

theorem record001_local_checked : Interval (localCheck record001) 0 107 :=
  (interval_append _ 0 64 107 record001_local_0 record001_local_1)
theorem record001_kind_checked : Interval record001.data.kindTest 0 record001.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record029_kind_checked

theorem record001_ridge_matrix :
    record001.data.candidateMatrix = PackedIncidenceMatrix.code record001.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record029_ridge_matrix

theorem record001_edge_matrix :
    record001.data.edgeMatrix = PackedIncidenceMatrix.code record001.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record029_edge_matrix

theorem record001_missing_matrix :
    record001.data.missingMatrix = PackedIncidenceMatrix.code record001.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record029_missing_matrix

theorem record001_matrix_checked : MatrixGraphProblem.Checked record001.data :=
  matrix_checked record001 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record001_aligned (by decide +kernel) record001_local_checked
    record001_kind_checked record001_ridge_matrix record001_edge_matrix record001_missing_matrix

theorem record001_validity : GraphGrowthInputs.Valid record001.inputs :=
  valid_of_matrix record001 record001_matrix_checked

theorem record001_vertex_width : record001.vertexRows.width = record001.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record029_vertex_width

theorem record001_vertex_code : record001.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record001 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record029_vertex_code

theorem record001_literal : RawGraphSemanticCertificate.LiteralFacts record001.data :=
  literal_facts record001 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record001_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record001 SharedSmallCellPool.entry record001_vertex_width record001_vertex_code)

theorem record001_cells_exact : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c) :=
  literal_cells record001 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record001_aligned

#print axioms record001_validity
#print axioms record001_literal

theorem record002_alignment_0 : Interval (alignedCheck record002 SharedSmallCellPool.entry) 0 64 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record030_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record002_alignment_1 : Interval (alignedCheck record002 SharedSmallCellPool.entry) 64 128 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record030_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record002_alignment_2 : Interval (alignedCheck record002 SharedSmallCellPool.entry) 128 131 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record030_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record002_alignment_checked : Interval (alignedCheck record002 SharedSmallCellPool.entry) 0 131 :=
  (interval_append _ 0 64 131 record002_alignment_0 (interval_append _ 64 128 131 record002_alignment_1 record002_alignment_2))
theorem record002_aligned : ∀ c, Aligned record002 SharedSmallCellPool.entry c :=
  aligned_of_interval record002 SharedSmallCellPool.entry record002_alignment_checked

theorem record002_local_0 : Interval (localCheck record002) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record002_local_1 : Interval (localCheck record002) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)

theorem record002_local_2 : Interval (localCheck record002) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)

theorem record002_local_checked : Interval (localCheck record002) 0 131 :=
  (interval_append _ 0 64 131 record002_local_0 (interval_append _ 64 128 131 record002_local_1 record002_local_2))
theorem record002_kind_checked : Interval record002.data.kindTest 0 record002.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record030_kind_checked

theorem record002_ridge_matrix :
    record002.data.candidateMatrix = PackedIncidenceMatrix.code record002.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record030_ridge_matrix

theorem record002_edge_matrix :
    record002.data.edgeMatrix = PackedIncidenceMatrix.code record002.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record030_edge_matrix

theorem record002_missing_matrix :
    record002.data.missingMatrix = PackedIncidenceMatrix.code record002.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record030_missing_matrix

theorem record002_matrix_checked : MatrixGraphProblem.Checked record002.data :=
  matrix_checked record002 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record002_aligned (by decide +kernel) record002_local_checked
    record002_kind_checked record002_ridge_matrix record002_edge_matrix record002_missing_matrix

theorem record002_validity : GraphGrowthInputs.Valid record002.inputs :=
  valid_of_matrix record002 record002_matrix_checked

theorem record002_vertex_width : record002.vertexRows.width = record002.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record030_vertex_width

theorem record002_vertex_code : record002.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record002 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record030_vertex_code

theorem record002_literal : RawGraphSemanticCertificate.LiteralFacts record002.data :=
  literal_facts record002 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record002_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record002 SharedSmallCellPool.entry record002_vertex_width record002_vertex_code)

theorem record002_cells_exact : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c) :=
  literal_cells record002 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record002_aligned

#print axioms record002_validity
#print axioms record002_literal

theorem record003_alignment_0 : Interval (alignedCheck record003 SharedSmallCellPool.entry) 0 64 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record031_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record003_alignment_1 : Interval (alignedCheck record003 SharedSmallCellPool.entry) 64 114 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record031_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record003_alignment_checked : Interval (alignedCheck record003 SharedSmallCellPool.entry) 0 114 :=
  (interval_append _ 0 64 114 record003_alignment_0 record003_alignment_1)
theorem record003_aligned : ∀ c, Aligned record003 SharedSmallCellPool.entry c :=
  aligned_of_interval record003 SharedSmallCellPool.entry record003_alignment_checked

theorem record003_local_0 : Interval (localCheck record003) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record003_local_1 : Interval (localCheck record003) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)

theorem record003_local_checked : Interval (localCheck record003) 0 114 :=
  (interval_append _ 0 64 114 record003_local_0 record003_local_1)
theorem record003_kind_checked : Interval record003.data.kindTest 0 record003.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record031_kind_checked

theorem record003_ridge_matrix :
    record003.data.candidateMatrix = PackedIncidenceMatrix.code record003.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record031_ridge_matrix

theorem record003_edge_matrix :
    record003.data.edgeMatrix = PackedIncidenceMatrix.code record003.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record031_edge_matrix

theorem record003_missing_matrix :
    record003.data.missingMatrix = PackedIncidenceMatrix.code record003.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record031_missing_matrix

theorem record003_matrix_checked : MatrixGraphProblem.Checked record003.data :=
  matrix_checked record003 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record003_aligned (by decide +kernel) record003_local_checked
    record003_kind_checked record003_ridge_matrix record003_edge_matrix record003_missing_matrix

theorem record003_validity : GraphGrowthInputs.Valid record003.inputs :=
  valid_of_matrix record003 record003_matrix_checked

theorem record003_vertex_width : record003.vertexRows.width = record003.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record031_vertex_width

theorem record003_vertex_code : record003.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record003 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record031_vertex_code

theorem record003_literal : RawGraphSemanticCertificate.LiteralFacts record003.data :=
  literal_facts record003 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record003_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record003 SharedSmallCellPool.entry record003_vertex_width record003_vertex_code)

theorem record003_cells_exact : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c) :=
  literal_cells record003 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record003_aligned

#print axioms record003_validity
#print axioms record003_literal

theorem record004_alignment_0 : Interval (alignedCheck record004 SharedSmallCellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record004_alignment_1 : Interval (alignedCheck record004 SharedSmallCellPool.entry) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)

theorem record004_alignment_checked : Interval (alignedCheck record004 SharedSmallCellPool.entry) 0 114 :=
  (interval_append _ 0 64 114 record004_alignment_0 record004_alignment_1)
theorem record004_aligned : ∀ c, Aligned record004 SharedSmallCellPool.entry c :=
  aligned_of_interval record004 SharedSmallCellPool.entry record004_alignment_checked

theorem record004_local_0 : Interval (localCheck record004) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record004_local_1 : Interval (localCheck record004) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)

theorem record004_local_checked : Interval (localCheck record004) 0 114 :=
  (interval_append _ 0 64 114 record004_local_0 record004_local_1)
theorem record004_kind_checked : Interval record004.data.kindTest 0 record004.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record004_ridge_matrix :
    record004.data.candidateMatrix = PackedIncidenceMatrix.code record004.data.ridgeList := by
  decide +kernel

theorem record004_edge_matrix :
    record004.data.edgeMatrix = PackedIncidenceMatrix.code record004.data.edgeLists := by
  decide +kernel

theorem record004_missing_matrix :
    record004.data.missingMatrix = PackedIncidenceMatrix.code record004.data.missingLists := by
  decide +kernel

theorem record004_matrix_checked : MatrixGraphProblem.Checked record004.data :=
  matrix_checked record004 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record004_aligned (by decide +kernel) record004_local_checked
    record004_kind_checked record004_ridge_matrix record004_edge_matrix record004_missing_matrix

theorem record004_validity : GraphGrowthInputs.Valid record004.inputs :=
  valid_of_matrix record004 record004_matrix_checked

theorem record004_vertex_width : record004.vertexRows.width = record004.n := by decide +kernel

theorem record004_vertex_code : record004.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record004 SharedSmallCellPool.entry c).vertices) := by decide +kernel

theorem record004_literal : RawGraphSemanticCertificate.LiteralFacts record004.data :=
  literal_facts record004 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record004_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record004 SharedSmallCellPool.entry record004_vertex_width record004_vertex_code)

theorem record004_cells_exact : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c) :=
  literal_cells record004 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record004_aligned

#print axioms record004_validity
#print axioms record004_literal

theorem record005_alignment_0 : Interval (alignedCheck record005 SharedSmallCellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record005_alignment_1 : Interval (alignedCheck record005 SharedSmallCellPool.entry) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)

theorem record005_alignment_checked : Interval (alignedCheck record005 SharedSmallCellPool.entry) 0 96 :=
  (interval_append _ 0 64 96 record005_alignment_0 record005_alignment_1)
theorem record005_aligned : ∀ c, Aligned record005 SharedSmallCellPool.entry c :=
  aligned_of_interval record005 SharedSmallCellPool.entry record005_alignment_checked

theorem record005_local_0 : Interval (localCheck record005) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record005_local_1 : Interval (localCheck record005) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)

theorem record005_local_checked : Interval (localCheck record005) 0 96 :=
  (interval_append _ 0 64 96 record005_local_0 record005_local_1)
theorem record005_kind_checked : Interval record005.data.kindTest 0 record005.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record005_ridge_matrix :
    record005.data.candidateMatrix = PackedIncidenceMatrix.code record005.data.ridgeList := by
  decide +kernel

theorem record005_edge_matrix :
    record005.data.edgeMatrix = PackedIncidenceMatrix.code record005.data.edgeLists := by
  decide +kernel

theorem record005_missing_matrix :
    record005.data.missingMatrix = PackedIncidenceMatrix.code record005.data.missingLists := by
  decide +kernel

theorem record005_matrix_checked : MatrixGraphProblem.Checked record005.data :=
  matrix_checked record005 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record005_aligned (by decide +kernel) record005_local_checked
    record005_kind_checked record005_ridge_matrix record005_edge_matrix record005_missing_matrix

theorem record005_validity : GraphGrowthInputs.Valid record005.inputs :=
  valid_of_matrix record005 record005_matrix_checked

theorem record005_vertex_width : record005.vertexRows.width = record005.n := by decide +kernel

theorem record005_vertex_code : record005.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record005 SharedSmallCellPool.entry c).vertices) := by decide +kernel

theorem record005_literal : RawGraphSemanticCertificate.LiteralFacts record005.data :=
  literal_facts record005 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record005_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record005 SharedSmallCellPool.entry record005_vertex_width record005_vertex_code)

theorem record005_cells_exact : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c) :=
  literal_cells record005 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record005_aligned

#print axioms record005_validity
#print axioms record005_literal

theorem record006_alignment_0 : Interval (alignedCheck record006 SharedSmallCellPool.entry) 0 64 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record032_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record006_alignment_1 : Interval (alignedCheck record006 SharedSmallCellPool.entry) 64 104 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record032_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record006_alignment_checked : Interval (alignedCheck record006 SharedSmallCellPool.entry) 0 104 :=
  (interval_append _ 0 64 104 record006_alignment_0 record006_alignment_1)
theorem record006_aligned : ∀ c, Aligned record006 SharedSmallCellPool.entry c :=
  aligned_of_interval record006 SharedSmallCellPool.entry record006_alignment_checked

theorem record006_local_0 : Interval (localCheck record006) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record006_local_1 : Interval (localCheck record006) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)

theorem record006_local_checked : Interval (localCheck record006) 0 104 :=
  (interval_append _ 0 64 104 record006_local_0 record006_local_1)
theorem record006_kind_checked : Interval record006.data.kindTest 0 record006.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record032_kind_checked

theorem record006_ridge_matrix :
    record006.data.candidateMatrix = PackedIncidenceMatrix.code record006.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record032_ridge_matrix

theorem record006_edge_matrix :
    record006.data.edgeMatrix = PackedIncidenceMatrix.code record006.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record032_edge_matrix

theorem record006_missing_matrix :
    record006.data.missingMatrix = PackedIncidenceMatrix.code record006.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record032_missing_matrix

theorem record006_matrix_checked : MatrixGraphProblem.Checked record006.data :=
  matrix_checked record006 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record006_aligned (by decide +kernel) record006_local_checked
    record006_kind_checked record006_ridge_matrix record006_edge_matrix record006_missing_matrix

theorem record006_validity : GraphGrowthInputs.Valid record006.inputs :=
  valid_of_matrix record006 record006_matrix_checked

theorem record006_vertex_width : record006.vertexRows.width = record006.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record032_vertex_width

theorem record006_vertex_code : record006.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record006 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record032_vertex_code

theorem record006_literal : RawGraphSemanticCertificate.LiteralFacts record006.data :=
  literal_facts record006 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record006_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record006 SharedSmallCellPool.entry record006_vertex_width record006_vertex_code)

theorem record006_cells_exact : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c) :=
  literal_cells record006 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record006_aligned

#print axioms record006_validity
#print axioms record006_literal

end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00107
