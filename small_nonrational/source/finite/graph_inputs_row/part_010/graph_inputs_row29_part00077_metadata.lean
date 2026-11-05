module
prelude
public import GraphInputsRow29Part00077Data
public import SharedGraphCellPool
public import SharedSmallCellPoolChecked
public import GraphInputsRow25Part00010Metadata

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool FiniteChecks

theorem record000_alignment_0 : Interval (alignedCheck record000 SharedSmallCellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record000_alignment_1 : Interval (alignedCheck record000 SharedSmallCellPool.entry) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)

theorem record000_alignment_checked : Interval (alignedCheck record000 SharedSmallCellPool.entry) 0 96 :=
  (interval_append _ 0 64 96 record000_alignment_0 record000_alignment_1)
theorem record000_aligned : ∀ c, Aligned record000 SharedSmallCellPool.entry c :=
  aligned_of_interval record000 SharedSmallCellPool.entry record000_alignment_checked

theorem record000_local_0 : Interval (localCheck record000) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record000_local_1 : Interval (localCheck record000) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)

theorem record000_local_checked : Interval (localCheck record000) 0 96 :=
  (interval_append _ 0 64 96 record000_local_0 record000_local_1)
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
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record000_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record001_alignment_1 : Interval (alignedCheck record001 SharedSmallCellPool.entry) 64 97 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record000_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record001_alignment_checked : Interval (alignedCheck record001 SharedSmallCellPool.entry) 0 97 :=
  (interval_append _ 0 64 97 record001_alignment_0 record001_alignment_1)
theorem record001_aligned : ∀ c, Aligned record001 SharedSmallCellPool.entry c :=
  aligned_of_interval record001 SharedSmallCellPool.entry record001_alignment_checked

theorem record001_local_0 : Interval (localCheck record001) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record001_local_1 : Interval (localCheck record001) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)

theorem record001_local_checked : Interval (localCheck record001) 0 97 :=
  (interval_append _ 0 64 97 record001_local_0 record001_local_1)
theorem record001_kind_checked : Interval record001.data.kindTest 0 record001.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record000_kind_checked

theorem record001_ridge_matrix :
    record001.data.candidateMatrix = PackedIncidenceMatrix.code record001.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record000_ridge_matrix

theorem record001_edge_matrix :
    record001.data.edgeMatrix = PackedIncidenceMatrix.code record001.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record000_edge_matrix

theorem record001_missing_matrix :
    record001.data.missingMatrix = PackedIncidenceMatrix.code record001.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record000_missing_matrix

theorem record001_matrix_checked : MatrixGraphProblem.Checked record001.data :=
  matrix_checked record001 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record001_aligned (by decide +kernel) record001_local_checked
    record001_kind_checked record001_ridge_matrix record001_edge_matrix record001_missing_matrix

theorem record001_validity : GraphGrowthInputs.Valid record001.inputs :=
  valid_of_matrix record001 record001_matrix_checked

theorem record001_vertex_width : record001.vertexRows.width = record001.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record000_vertex_width

theorem record001_vertex_code : record001.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record001 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record000_vertex_code

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
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record001_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record002_alignment_1 : Interval (alignedCheck record002 SharedSmallCellPool.entry) 64 99 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record001_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record002_alignment_checked : Interval (alignedCheck record002 SharedSmallCellPool.entry) 0 99 :=
  (interval_append _ 0 64 99 record002_alignment_0 record002_alignment_1)
theorem record002_aligned : ∀ c, Aligned record002 SharedSmallCellPool.entry c :=
  aligned_of_interval record002 SharedSmallCellPool.entry record002_alignment_checked

theorem record002_local_0 : Interval (localCheck record002) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record002_local_1 : Interval (localCheck record002) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)

theorem record002_local_checked : Interval (localCheck record002) 0 99 :=
  (interval_append _ 0 64 99 record002_local_0 record002_local_1)
theorem record002_kind_checked : Interval record002.data.kindTest 0 record002.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record001_kind_checked

theorem record002_ridge_matrix :
    record002.data.candidateMatrix = PackedIncidenceMatrix.code record002.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record001_ridge_matrix

theorem record002_edge_matrix :
    record002.data.edgeMatrix = PackedIncidenceMatrix.code record002.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record001_edge_matrix

theorem record002_missing_matrix :
    record002.data.missingMatrix = PackedIncidenceMatrix.code record002.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record001_missing_matrix

theorem record002_matrix_checked : MatrixGraphProblem.Checked record002.data :=
  matrix_checked record002 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record002_aligned (by decide +kernel) record002_local_checked
    record002_kind_checked record002_ridge_matrix record002_edge_matrix record002_missing_matrix

theorem record002_validity : GraphGrowthInputs.Valid record002.inputs :=
  valid_of_matrix record002 record002_matrix_checked

theorem record002_vertex_width : record002.vertexRows.width = record002.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record001_vertex_width

theorem record002_vertex_code : record002.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record002 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record001_vertex_code

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
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record002_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record003_alignment_1 : Interval (alignedCheck record003 SharedSmallCellPool.entry) 64 100 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record002_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record003_alignment_checked : Interval (alignedCheck record003 SharedSmallCellPool.entry) 0 100 :=
  (interval_append _ 0 64 100 record003_alignment_0 record003_alignment_1)
theorem record003_aligned : ∀ c, Aligned record003 SharedSmallCellPool.entry c :=
  aligned_of_interval record003 SharedSmallCellPool.entry record003_alignment_checked

theorem record003_local_0 : Interval (localCheck record003) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record003_local_1 : Interval (localCheck record003) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)

theorem record003_local_checked : Interval (localCheck record003) 0 100 :=
  (interval_append _ 0 64 100 record003_local_0 record003_local_1)
theorem record003_kind_checked : Interval record003.data.kindTest 0 record003.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record002_kind_checked

theorem record003_ridge_matrix :
    record003.data.candidateMatrix = PackedIncidenceMatrix.code record003.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record002_ridge_matrix

theorem record003_edge_matrix :
    record003.data.edgeMatrix = PackedIncidenceMatrix.code record003.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record002_edge_matrix

theorem record003_missing_matrix :
    record003.data.missingMatrix = PackedIncidenceMatrix.code record003.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record002_missing_matrix

theorem record003_matrix_checked : MatrixGraphProblem.Checked record003.data :=
  matrix_checked record003 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record003_aligned (by decide +kernel) record003_local_checked
    record003_kind_checked record003_ridge_matrix record003_edge_matrix record003_missing_matrix

theorem record003_validity : GraphGrowthInputs.Valid record003.inputs :=
  valid_of_matrix record003 record003_matrix_checked

theorem record003_vertex_width : record003.vertexRows.width = record003.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record002_vertex_width

theorem record003_vertex_code : record003.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record003 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record002_vertex_code

theorem record003_literal : RawGraphSemanticCertificate.LiteralFacts record003.data :=
  literal_facts record003 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record003_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record003 SharedSmallCellPool.entry record003_vertex_width record003_vertex_code)

theorem record003_cells_exact : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c) :=
  literal_cells record003 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record003_aligned

#print axioms record003_validity
#print axioms record003_literal

theorem record004_alignment_0 : Interval (alignedCheck record004 SharedSmallCellPool.entry) 0 64 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record003_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record004_alignment_1 : Interval (alignedCheck record004 SharedSmallCellPool.entry) 64 99 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record003_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record004_alignment_checked : Interval (alignedCheck record004 SharedSmallCellPool.entry) 0 99 :=
  (interval_append _ 0 64 99 record004_alignment_0 record004_alignment_1)
theorem record004_aligned : ∀ c, Aligned record004 SharedSmallCellPool.entry c :=
  aligned_of_interval record004 SharedSmallCellPool.entry record004_alignment_checked

theorem record004_local_0 : Interval (localCheck record004) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record004_local_1 : Interval (localCheck record004) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)

theorem record004_local_checked : Interval (localCheck record004) 0 99 :=
  (interval_append _ 0 64 99 record004_local_0 record004_local_1)
theorem record004_kind_checked : Interval record004.data.kindTest 0 record004.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record003_kind_checked

theorem record004_ridge_matrix :
    record004.data.candidateMatrix = PackedIncidenceMatrix.code record004.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record003_ridge_matrix

theorem record004_edge_matrix :
    record004.data.edgeMatrix = PackedIncidenceMatrix.code record004.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record003_edge_matrix

theorem record004_missing_matrix :
    record004.data.missingMatrix = PackedIncidenceMatrix.code record004.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record003_missing_matrix

theorem record004_matrix_checked : MatrixGraphProblem.Checked record004.data :=
  matrix_checked record004 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record004_aligned (by decide +kernel) record004_local_checked
    record004_kind_checked record004_ridge_matrix record004_edge_matrix record004_missing_matrix

theorem record004_validity : GraphGrowthInputs.Valid record004.inputs :=
  valid_of_matrix record004 record004_matrix_checked

theorem record004_vertex_width : record004.vertexRows.width = record004.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record003_vertex_width

theorem record004_vertex_code : record004.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record004 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record003_vertex_code

theorem record004_literal : RawGraphSemanticCertificate.LiteralFacts record004.data :=
  literal_facts record004 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record004_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record004 SharedSmallCellPool.entry record004_vertex_width record004_vertex_code)

theorem record004_cells_exact : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c) :=
  literal_cells record004 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record004_aligned

#print axioms record004_validity
#print axioms record004_literal

theorem record005_alignment_0 : Interval (alignedCheck record005 SharedSmallCellPool.entry) 0 64 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record004_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record005_alignment_1 : Interval (alignedCheck record005 SharedSmallCellPool.entry) 64 95 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record004_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record005_alignment_checked : Interval (alignedCheck record005 SharedSmallCellPool.entry) 0 95 :=
  (interval_append _ 0 64 95 record005_alignment_0 record005_alignment_1)
theorem record005_aligned : ∀ c, Aligned record005 SharedSmallCellPool.entry c :=
  aligned_of_interval record005 SharedSmallCellPool.entry record005_alignment_checked

theorem record005_local_0 : Interval (localCheck record005) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record005_local_1 : Interval (localCheck record005) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)

theorem record005_local_checked : Interval (localCheck record005) 0 95 :=
  (interval_append _ 0 64 95 record005_local_0 record005_local_1)
theorem record005_kind_checked : Interval record005.data.kindTest 0 record005.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record004_kind_checked

theorem record005_ridge_matrix :
    record005.data.candidateMatrix = PackedIncidenceMatrix.code record005.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record004_ridge_matrix

theorem record005_edge_matrix :
    record005.data.edgeMatrix = PackedIncidenceMatrix.code record005.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record004_edge_matrix

theorem record005_missing_matrix :
    record005.data.missingMatrix = PackedIncidenceMatrix.code record005.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record004_missing_matrix

theorem record005_matrix_checked : MatrixGraphProblem.Checked record005.data :=
  matrix_checked record005 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record005_aligned (by decide +kernel) record005_local_checked
    record005_kind_checked record005_ridge_matrix record005_edge_matrix record005_missing_matrix

theorem record005_validity : GraphGrowthInputs.Valid record005.inputs :=
  valid_of_matrix record005 record005_matrix_checked

theorem record005_vertex_width : record005.vertexRows.width = record005.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record004_vertex_width

theorem record005_vertex_code : record005.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record005 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record004_vertex_code

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
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record005_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record006_alignment_1 : Interval (alignedCheck record006 SharedSmallCellPool.entry) 64 119 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record005_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record006_alignment_checked : Interval (alignedCheck record006 SharedSmallCellPool.entry) 0 119 :=
  (interval_append _ 0 64 119 record006_alignment_0 record006_alignment_1)
theorem record006_aligned : ∀ c, Aligned record006 SharedSmallCellPool.entry c :=
  aligned_of_interval record006 SharedSmallCellPool.entry record006_alignment_checked

theorem record006_local_0 : Interval (localCheck record006) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record006_local_1 : Interval (localCheck record006) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)

theorem record006_local_checked : Interval (localCheck record006) 0 119 :=
  (interval_append _ 0 64 119 record006_local_0 record006_local_1)
theorem record006_kind_checked : Interval record006.data.kindTest 0 record006.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record005_kind_checked

theorem record006_ridge_matrix :
    record006.data.candidateMatrix = PackedIncidenceMatrix.code record006.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record005_ridge_matrix

theorem record006_edge_matrix :
    record006.data.edgeMatrix = PackedIncidenceMatrix.code record006.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record005_edge_matrix

theorem record006_missing_matrix :
    record006.data.missingMatrix = PackedIncidenceMatrix.code record006.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record005_missing_matrix

theorem record006_matrix_checked : MatrixGraphProblem.Checked record006.data :=
  matrix_checked record006 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record006_aligned (by decide +kernel) record006_local_checked
    record006_kind_checked record006_ridge_matrix record006_edge_matrix record006_missing_matrix

theorem record006_validity : GraphGrowthInputs.Valid record006.inputs :=
  valid_of_matrix record006 record006_matrix_checked

theorem record006_vertex_width : record006.vertexRows.width = record006.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record005_vertex_width

theorem record006_vertex_code : record006.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record006 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record005_vertex_code

theorem record006_literal : RawGraphSemanticCertificate.LiteralFacts record006.data :=
  literal_facts record006 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record006_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record006 SharedSmallCellPool.entry record006_vertex_width record006_vertex_code)

theorem record006_cells_exact : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c) :=
  literal_cells record006 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record006_aligned

#print axioms record006_validity
#print axioms record006_literal

theorem record007_alignment_0 : Interval (alignedCheck record007 SharedSmallCellPool.entry) 0 64 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record006_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record007_alignment_1 : Interval (alignedCheck record007 SharedSmallCellPool.entry) 64 97 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record006_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record007_alignment_checked : Interval (alignedCheck record007 SharedSmallCellPool.entry) 0 97 :=
  (interval_append _ 0 64 97 record007_alignment_0 record007_alignment_1)
theorem record007_aligned : ∀ c, Aligned record007 SharedSmallCellPool.entry c :=
  aligned_of_interval record007 SharedSmallCellPool.entry record007_alignment_checked

theorem record007_local_0 : Interval (localCheck record007) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record007_local_1 : Interval (localCheck record007) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)

theorem record007_local_checked : Interval (localCheck record007) 0 97 :=
  (interval_append _ 0 64 97 record007_local_0 record007_local_1)
theorem record007_kind_checked : Interval record007.data.kindTest 0 record007.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record006_kind_checked

theorem record007_ridge_matrix :
    record007.data.candidateMatrix = PackedIncidenceMatrix.code record007.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record006_ridge_matrix

theorem record007_edge_matrix :
    record007.data.edgeMatrix = PackedIncidenceMatrix.code record007.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record006_edge_matrix

theorem record007_missing_matrix :
    record007.data.missingMatrix = PackedIncidenceMatrix.code record007.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record006_missing_matrix

theorem record007_matrix_checked : MatrixGraphProblem.Checked record007.data :=
  matrix_checked record007 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record007_aligned (by decide +kernel) record007_local_checked
    record007_kind_checked record007_ridge_matrix record007_edge_matrix record007_missing_matrix

theorem record007_validity : GraphGrowthInputs.Valid record007.inputs :=
  valid_of_matrix record007 record007_matrix_checked

theorem record007_vertex_width : record007.vertexRows.width = record007.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record006_vertex_width

theorem record007_vertex_code : record007.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record007 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record006_vertex_code

theorem record007_literal : RawGraphSemanticCertificate.LiteralFacts record007.data :=
  literal_facts record007 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record007_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record007 SharedSmallCellPool.entry record007_vertex_width record007_vertex_code)

theorem record007_cells_exact : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c) :=
  literal_cells record007 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record007_aligned

#print axioms record007_validity
#print axioms record007_literal

theorem record008_alignment_0 : Interval (alignedCheck record008 SharedSmallCellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record008_alignment_1 : Interval (alignedCheck record008 SharedSmallCellPool.entry) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)

theorem record008_alignment_checked : Interval (alignedCheck record008 SharedSmallCellPool.entry) 0 95 :=
  (interval_append _ 0 64 95 record008_alignment_0 record008_alignment_1)
theorem record008_aligned : ∀ c, Aligned record008 SharedSmallCellPool.entry c :=
  aligned_of_interval record008 SharedSmallCellPool.entry record008_alignment_checked

theorem record008_local_0 : Interval (localCheck record008) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record008_local_1 : Interval (localCheck record008) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)

theorem record008_local_checked : Interval (localCheck record008) 0 95 :=
  (interval_append _ 0 64 95 record008_local_0 record008_local_1)
theorem record008_kind_checked : Interval record008.data.kindTest 0 record008.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record008_ridge_matrix :
    record008.data.candidateMatrix = PackedIncidenceMatrix.code record008.data.ridgeList := by
  decide +kernel

theorem record008_edge_matrix :
    record008.data.edgeMatrix = PackedIncidenceMatrix.code record008.data.edgeLists := by
  decide +kernel

theorem record008_missing_matrix :
    record008.data.missingMatrix = PackedIncidenceMatrix.code record008.data.missingLists := by
  decide +kernel

theorem record008_matrix_checked : MatrixGraphProblem.Checked record008.data :=
  matrix_checked record008 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record008_aligned (by decide +kernel) record008_local_checked
    record008_kind_checked record008_ridge_matrix record008_edge_matrix record008_missing_matrix

theorem record008_validity : GraphGrowthInputs.Valid record008.inputs :=
  valid_of_matrix record008 record008_matrix_checked

theorem record008_vertex_width : record008.vertexRows.width = record008.n := by decide +kernel

theorem record008_vertex_code : record008.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record008 SharedSmallCellPool.entry c).vertices) := by decide +kernel

theorem record008_literal : RawGraphSemanticCertificate.LiteralFacts record008.data :=
  literal_facts record008 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record008_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record008 SharedSmallCellPool.entry record008_vertex_width record008_vertex_code)

theorem record008_cells_exact : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c) :=
  literal_cells record008 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record008_aligned

#print axioms record008_validity
#print axioms record008_literal

theorem record009_alignment_0 : Interval (alignedCheck record009 SharedSmallCellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record009_alignment_1 : Interval (alignedCheck record009 SharedSmallCellPool.entry) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)

theorem record009_alignment_checked : Interval (alignedCheck record009 SharedSmallCellPool.entry) 0 101 :=
  (interval_append _ 0 64 101 record009_alignment_0 record009_alignment_1)
theorem record009_aligned : ∀ c, Aligned record009 SharedSmallCellPool.entry c :=
  aligned_of_interval record009 SharedSmallCellPool.entry record009_alignment_checked

theorem record009_local_0 : Interval (localCheck record009) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record009_local_1 : Interval (localCheck record009) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)

theorem record009_local_checked : Interval (localCheck record009) 0 101 :=
  (interval_append _ 0 64 101 record009_local_0 record009_local_1)
theorem record009_kind_checked : Interval record009.data.kindTest 0 record009.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record009_ridge_matrix :
    record009.data.candidateMatrix = PackedIncidenceMatrix.code record009.data.ridgeList := by
  decide +kernel

theorem record009_edge_matrix :
    record009.data.edgeMatrix = PackedIncidenceMatrix.code record009.data.edgeLists := by
  decide +kernel

theorem record009_missing_matrix :
    record009.data.missingMatrix = PackedIncidenceMatrix.code record009.data.missingLists := by
  decide +kernel

theorem record009_matrix_checked : MatrixGraphProblem.Checked record009.data :=
  matrix_checked record009 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record009_aligned (by decide +kernel) record009_local_checked
    record009_kind_checked record009_ridge_matrix record009_edge_matrix record009_missing_matrix

theorem record009_validity : GraphGrowthInputs.Valid record009.inputs :=
  valid_of_matrix record009 record009_matrix_checked

theorem record009_vertex_width : record009.vertexRows.width = record009.n := by decide +kernel

theorem record009_vertex_code : record009.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record009 SharedSmallCellPool.entry c).vertices) := by decide +kernel

theorem record009_literal : RawGraphSemanticCertificate.LiteralFacts record009.data :=
  literal_facts record009 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record009_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record009 SharedSmallCellPool.entry record009_vertex_width record009_vertex_code)

theorem record009_cells_exact : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c) :=
  literal_cells record009 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record009_aligned

#print axioms record009_validity
#print axioms record009_literal

theorem record010_alignment_0 : Interval (alignedCheck record010 SharedSmallCellPool.entry) 0 64 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record007_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record010_alignment_1 : Interval (alignedCheck record010 SharedSmallCellPool.entry) 64 97 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record007_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record010_alignment_checked : Interval (alignedCheck record010 SharedSmallCellPool.entry) 0 97 :=
  (interval_append _ 0 64 97 record010_alignment_0 record010_alignment_1)
theorem record010_aligned : ∀ c, Aligned record010 SharedSmallCellPool.entry c :=
  aligned_of_interval record010 SharedSmallCellPool.entry record010_alignment_checked

theorem record010_local_0 : Interval (localCheck record010) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record010_local_1 : Interval (localCheck record010) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)

theorem record010_local_checked : Interval (localCheck record010) 0 97 :=
  (interval_append _ 0 64 97 record010_local_0 record010_local_1)
theorem record010_kind_checked : Interval record010.data.kindTest 0 record010.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record007_kind_checked

theorem record010_ridge_matrix :
    record010.data.candidateMatrix = PackedIncidenceMatrix.code record010.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record007_ridge_matrix

theorem record010_edge_matrix :
    record010.data.edgeMatrix = PackedIncidenceMatrix.code record010.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record007_edge_matrix

theorem record010_missing_matrix :
    record010.data.missingMatrix = PackedIncidenceMatrix.code record010.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record007_missing_matrix

theorem record010_matrix_checked : MatrixGraphProblem.Checked record010.data :=
  matrix_checked record010 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record010_aligned (by decide +kernel) record010_local_checked
    record010_kind_checked record010_ridge_matrix record010_edge_matrix record010_missing_matrix

theorem record010_validity : GraphGrowthInputs.Valid record010.inputs :=
  valid_of_matrix record010 record010_matrix_checked

theorem record010_vertex_width : record010.vertexRows.width = record010.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record007_vertex_width

theorem record010_vertex_code : record010.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record010 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record007_vertex_code

theorem record010_literal : RawGraphSemanticCertificate.LiteralFacts record010.data :=
  literal_facts record010 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record010_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record010 SharedSmallCellPool.entry record010_vertex_width record010_vertex_code)

theorem record010_cells_exact : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c) :=
  literal_cells record010 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record010_aligned

#print axioms record010_validity
#print axioms record010_literal

theorem record011_alignment_0 : Interval (alignedCheck record011 SharedSmallCellPool.entry) 0 64 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record008_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record011_alignment_1 : Interval (alignedCheck record011 SharedSmallCellPool.entry) 64 107 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record008_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record011_alignment_checked : Interval (alignedCheck record011 SharedSmallCellPool.entry) 0 107 :=
  (interval_append _ 0 64 107 record011_alignment_0 record011_alignment_1)
theorem record011_aligned : ∀ c, Aligned record011 SharedSmallCellPool.entry c :=
  aligned_of_interval record011 SharedSmallCellPool.entry record011_alignment_checked

theorem record011_local_0 : Interval (localCheck record011) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record011_local_1 : Interval (localCheck record011) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)

theorem record011_local_checked : Interval (localCheck record011) 0 107 :=
  (interval_append _ 0 64 107 record011_local_0 record011_local_1)
theorem record011_kind_checked : Interval record011.data.kindTest 0 record011.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record008_kind_checked

theorem record011_ridge_matrix :
    record011.data.candidateMatrix = PackedIncidenceMatrix.code record011.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record008_ridge_matrix

theorem record011_edge_matrix :
    record011.data.edgeMatrix = PackedIncidenceMatrix.code record011.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record008_edge_matrix

theorem record011_missing_matrix :
    record011.data.missingMatrix = PackedIncidenceMatrix.code record011.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record008_missing_matrix

theorem record011_matrix_checked : MatrixGraphProblem.Checked record011.data :=
  matrix_checked record011 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record011_aligned (by decide +kernel) record011_local_checked
    record011_kind_checked record011_ridge_matrix record011_edge_matrix record011_missing_matrix

theorem record011_validity : GraphGrowthInputs.Valid record011.inputs :=
  valid_of_matrix record011 record011_matrix_checked

theorem record011_vertex_width : record011.vertexRows.width = record011.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record008_vertex_width

theorem record011_vertex_code : record011.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record011 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record008_vertex_code

theorem record011_literal : RawGraphSemanticCertificate.LiteralFacts record011.data :=
  literal_facts record011 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record011_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record011 SharedSmallCellPool.entry record011_vertex_width record011_vertex_code)

theorem record011_cells_exact : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c) :=
  literal_cells record011 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record011_aligned

#print axioms record011_validity
#print axioms record011_literal

theorem record012_alignment_0 : Interval (alignedCheck record012 SharedSmallCellPool.entry) 0 64 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record009_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record012_alignment_1 : Interval (alignedCheck record012 SharedSmallCellPool.entry) 64 105 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record009_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record012_alignment_checked : Interval (alignedCheck record012 SharedSmallCellPool.entry) 0 105 :=
  (interval_append _ 0 64 105 record012_alignment_0 record012_alignment_1)
theorem record012_aligned : ∀ c, Aligned record012 SharedSmallCellPool.entry c :=
  aligned_of_interval record012 SharedSmallCellPool.entry record012_alignment_checked

theorem record012_local_0 : Interval (localCheck record012) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record012_local_1 : Interval (localCheck record012) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)

theorem record012_local_checked : Interval (localCheck record012) 0 105 :=
  (interval_append _ 0 64 105 record012_local_0 record012_local_1)
theorem record012_kind_checked : Interval record012.data.kindTest 0 record012.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record009_kind_checked

theorem record012_ridge_matrix :
    record012.data.candidateMatrix = PackedIncidenceMatrix.code record012.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record009_ridge_matrix

theorem record012_edge_matrix :
    record012.data.edgeMatrix = PackedIncidenceMatrix.code record012.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record009_edge_matrix

theorem record012_missing_matrix :
    record012.data.missingMatrix = PackedIncidenceMatrix.code record012.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record009_missing_matrix

theorem record012_matrix_checked : MatrixGraphProblem.Checked record012.data :=
  matrix_checked record012 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record012_aligned (by decide +kernel) record012_local_checked
    record012_kind_checked record012_ridge_matrix record012_edge_matrix record012_missing_matrix

theorem record012_validity : GraphGrowthInputs.Valid record012.inputs :=
  valid_of_matrix record012 record012_matrix_checked

theorem record012_vertex_width : record012.vertexRows.width = record012.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record009_vertex_width

theorem record012_vertex_code : record012.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record012 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record009_vertex_code

theorem record012_literal : RawGraphSemanticCertificate.LiteralFacts record012.data :=
  literal_facts record012 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record012_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record012 SharedSmallCellPool.entry record012_vertex_width record012_vertex_code)

theorem record012_cells_exact : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c) :=
  literal_cells record012 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record012_aligned

#print axioms record012_validity
#print axioms record012_literal

theorem record013_alignment_0 : Interval (alignedCheck record013 SharedSmallCellPool.entry) 0 64 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record010_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record013_alignment_1 : Interval (alignedCheck record013 SharedSmallCellPool.entry) 64 106 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record010_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record013_alignment_checked : Interval (alignedCheck record013 SharedSmallCellPool.entry) 0 106 :=
  (interval_append _ 0 64 106 record013_alignment_0 record013_alignment_1)
theorem record013_aligned : ∀ c, Aligned record013 SharedSmallCellPool.entry c :=
  aligned_of_interval record013 SharedSmallCellPool.entry record013_alignment_checked

theorem record013_local_0 : Interval (localCheck record013) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record013_local_1 : Interval (localCheck record013) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)

theorem record013_local_checked : Interval (localCheck record013) 0 106 :=
  (interval_append _ 0 64 106 record013_local_0 record013_local_1)
theorem record013_kind_checked : Interval record013.data.kindTest 0 record013.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record010_kind_checked

theorem record013_ridge_matrix :
    record013.data.candidateMatrix = PackedIncidenceMatrix.code record013.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record010_ridge_matrix

theorem record013_edge_matrix :
    record013.data.edgeMatrix = PackedIncidenceMatrix.code record013.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record010_edge_matrix

theorem record013_missing_matrix :
    record013.data.missingMatrix = PackedIncidenceMatrix.code record013.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record010_missing_matrix

theorem record013_matrix_checked : MatrixGraphProblem.Checked record013.data :=
  matrix_checked record013 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record013_aligned (by decide +kernel) record013_local_checked
    record013_kind_checked record013_ridge_matrix record013_edge_matrix record013_missing_matrix

theorem record013_validity : GraphGrowthInputs.Valid record013.inputs :=
  valid_of_matrix record013 record013_matrix_checked

theorem record013_vertex_width : record013.vertexRows.width = record013.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record010_vertex_width

theorem record013_vertex_code : record013.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record013 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record010_vertex_code

theorem record013_literal : RawGraphSemanticCertificate.LiteralFacts record013.data :=
  literal_facts record013 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record013_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record013 SharedSmallCellPool.entry record013_vertex_width record013_vertex_code)

theorem record013_cells_exact : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c) :=
  literal_cells record013 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record013_aligned

#print axioms record013_validity
#print axioms record013_literal

theorem record014_alignment_0 : Interval (alignedCheck record014 SharedSmallCellPool.entry) 0 64 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record011_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record014_alignment_1 : Interval (alignedCheck record014 SharedSmallCellPool.entry) 64 97 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record011_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record014_alignment_checked : Interval (alignedCheck record014 SharedSmallCellPool.entry) 0 97 :=
  (interval_append _ 0 64 97 record014_alignment_0 record014_alignment_1)
theorem record014_aligned : ∀ c, Aligned record014 SharedSmallCellPool.entry c :=
  aligned_of_interval record014 SharedSmallCellPool.entry record014_alignment_checked

theorem record014_local_0 : Interval (localCheck record014) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record014_local_1 : Interval (localCheck record014) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)

theorem record014_local_checked : Interval (localCheck record014) 0 97 :=
  (interval_append _ 0 64 97 record014_local_0 record014_local_1)
theorem record014_kind_checked : Interval record014.data.kindTest 0 record014.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record011_kind_checked

theorem record014_ridge_matrix :
    record014.data.candidateMatrix = PackedIncidenceMatrix.code record014.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record011_ridge_matrix

theorem record014_edge_matrix :
    record014.data.edgeMatrix = PackedIncidenceMatrix.code record014.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record011_edge_matrix

theorem record014_missing_matrix :
    record014.data.missingMatrix = PackedIncidenceMatrix.code record014.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record011_missing_matrix

theorem record014_matrix_checked : MatrixGraphProblem.Checked record014.data :=
  matrix_checked record014 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record014_aligned (by decide +kernel) record014_local_checked
    record014_kind_checked record014_ridge_matrix record014_edge_matrix record014_missing_matrix

theorem record014_validity : GraphGrowthInputs.Valid record014.inputs :=
  valid_of_matrix record014 record014_matrix_checked

theorem record014_vertex_width : record014.vertexRows.width = record014.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record011_vertex_width

theorem record014_vertex_code : record014.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record014 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record011_vertex_code

theorem record014_literal : RawGraphSemanticCertificate.LiteralFacts record014.data :=
  literal_facts record014 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record014_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record014 SharedSmallCellPool.entry record014_vertex_width record014_vertex_code)

theorem record014_cells_exact : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c) :=
  literal_cells record014 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record014_aligned

#print axioms record014_validity
#print axioms record014_literal

theorem record015_alignment_0 : Interval (alignedCheck record015 SharedSmallCellPool.entry) 0 64 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record012_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record015_alignment_1 : Interval (alignedCheck record015 SharedSmallCellPool.entry) 64 99 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record012_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record015_alignment_checked : Interval (alignedCheck record015 SharedSmallCellPool.entry) 0 99 :=
  (interval_append _ 0 64 99 record015_alignment_0 record015_alignment_1)
theorem record015_aligned : ∀ c, Aligned record015 SharedSmallCellPool.entry c :=
  aligned_of_interval record015 SharedSmallCellPool.entry record015_alignment_checked

theorem record015_local_0 : Interval (localCheck record015) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record015_local_1 : Interval (localCheck record015) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)

theorem record015_local_checked : Interval (localCheck record015) 0 99 :=
  (interval_append _ 0 64 99 record015_local_0 record015_local_1)
theorem record015_kind_checked : Interval record015.data.kindTest 0 record015.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record012_kind_checked

theorem record015_ridge_matrix :
    record015.data.candidateMatrix = PackedIncidenceMatrix.code record015.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record012_ridge_matrix

theorem record015_edge_matrix :
    record015.data.edgeMatrix = PackedIncidenceMatrix.code record015.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record012_edge_matrix

theorem record015_missing_matrix :
    record015.data.missingMatrix = PackedIncidenceMatrix.code record015.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record012_missing_matrix

theorem record015_matrix_checked : MatrixGraphProblem.Checked record015.data :=
  matrix_checked record015 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record015_aligned (by decide +kernel) record015_local_checked
    record015_kind_checked record015_ridge_matrix record015_edge_matrix record015_missing_matrix

theorem record015_validity : GraphGrowthInputs.Valid record015.inputs :=
  valid_of_matrix record015 record015_matrix_checked

theorem record015_vertex_width : record015.vertexRows.width = record015.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record012_vertex_width

theorem record015_vertex_code : record015.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record015 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record012_vertex_code

theorem record015_literal : RawGraphSemanticCertificate.LiteralFacts record015.data :=
  literal_facts record015 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record015_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record015 SharedSmallCellPool.entry record015_vertex_width record015_vertex_code)

theorem record015_cells_exact : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c) :=
  literal_cells record015 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record015_aligned

#print axioms record015_validity
#print axioms record015_literal

theorem record016_alignment_0 : Interval (alignedCheck record016 SharedSmallCellPool.entry) 0 64 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record013_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record016_alignment_1 : Interval (alignedCheck record016 SharedSmallCellPool.entry) 64 99 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record013_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record016_alignment_checked : Interval (alignedCheck record016 SharedSmallCellPool.entry) 0 99 :=
  (interval_append _ 0 64 99 record016_alignment_0 record016_alignment_1)
theorem record016_aligned : ∀ c, Aligned record016 SharedSmallCellPool.entry c :=
  aligned_of_interval record016 SharedSmallCellPool.entry record016_alignment_checked

theorem record016_local_0 : Interval (localCheck record016) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record016_local_1 : Interval (localCheck record016) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)

theorem record016_local_checked : Interval (localCheck record016) 0 99 :=
  (interval_append _ 0 64 99 record016_local_0 record016_local_1)
theorem record016_kind_checked : Interval record016.data.kindTest 0 record016.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record013_kind_checked

theorem record016_ridge_matrix :
    record016.data.candidateMatrix = PackedIncidenceMatrix.code record016.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record013_ridge_matrix

theorem record016_edge_matrix :
    record016.data.edgeMatrix = PackedIncidenceMatrix.code record016.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record013_edge_matrix

theorem record016_missing_matrix :
    record016.data.missingMatrix = PackedIncidenceMatrix.code record016.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record013_missing_matrix

theorem record016_matrix_checked : MatrixGraphProblem.Checked record016.data :=
  matrix_checked record016 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record016_aligned (by decide +kernel) record016_local_checked
    record016_kind_checked record016_ridge_matrix record016_edge_matrix record016_missing_matrix

theorem record016_validity : GraphGrowthInputs.Valid record016.inputs :=
  valid_of_matrix record016 record016_matrix_checked

theorem record016_vertex_width : record016.vertexRows.width = record016.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record013_vertex_width

theorem record016_vertex_code : record016.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record016 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record013_vertex_code

theorem record016_literal : RawGraphSemanticCertificate.LiteralFacts record016.data :=
  literal_facts record016 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record016_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record016 SharedSmallCellPool.entry record016_vertex_width record016_vertex_code)

theorem record016_cells_exact : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c) :=
  literal_cells record016 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record016_aligned

#print axioms record016_validity
#print axioms record016_literal

theorem record017_alignment_0 : Interval (alignedCheck record017 SharedSmallCellPool.entry) 0 64 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record014_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record017_alignment_1 : Interval (alignedCheck record017 SharedSmallCellPool.entry) 64 98 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record014_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record017_alignment_checked : Interval (alignedCheck record017 SharedSmallCellPool.entry) 0 98 :=
  (interval_append _ 0 64 98 record017_alignment_0 record017_alignment_1)
theorem record017_aligned : ∀ c, Aligned record017 SharedSmallCellPool.entry c :=
  aligned_of_interval record017 SharedSmallCellPool.entry record017_alignment_checked

theorem record017_local_0 : Interval (localCheck record017) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record017_local_1 : Interval (localCheck record017) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)

theorem record017_local_checked : Interval (localCheck record017) 0 98 :=
  (interval_append _ 0 64 98 record017_local_0 record017_local_1)
theorem record017_kind_checked : Interval record017.data.kindTest 0 record017.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record014_kind_checked

theorem record017_ridge_matrix :
    record017.data.candidateMatrix = PackedIncidenceMatrix.code record017.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record014_ridge_matrix

theorem record017_edge_matrix :
    record017.data.edgeMatrix = PackedIncidenceMatrix.code record017.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record014_edge_matrix

theorem record017_missing_matrix :
    record017.data.missingMatrix = PackedIncidenceMatrix.code record017.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record014_missing_matrix

theorem record017_matrix_checked : MatrixGraphProblem.Checked record017.data :=
  matrix_checked record017 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record017_aligned (by decide +kernel) record017_local_checked
    record017_kind_checked record017_ridge_matrix record017_edge_matrix record017_missing_matrix

theorem record017_validity : GraphGrowthInputs.Valid record017.inputs :=
  valid_of_matrix record017 record017_matrix_checked

theorem record017_vertex_width : record017.vertexRows.width = record017.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record014_vertex_width

theorem record017_vertex_code : record017.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record017 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record014_vertex_code

theorem record017_literal : RawGraphSemanticCertificate.LiteralFacts record017.data :=
  literal_facts record017 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record017_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record017 SharedSmallCellPool.entry record017_vertex_width record017_vertex_code)

theorem record017_cells_exact : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c) :=
  literal_cells record017 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record017_aligned

#print axioms record017_validity
#print axioms record017_literal

theorem record018_alignment_0 : Interval (alignedCheck record018 SharedSmallCellPool.entry) 0 64 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record015_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record018_alignment_1 : Interval (alignedCheck record018 SharedSmallCellPool.entry) 64 95 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record015_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record018_alignment_checked : Interval (alignedCheck record018 SharedSmallCellPool.entry) 0 95 :=
  (interval_append _ 0 64 95 record018_alignment_0 record018_alignment_1)
theorem record018_aligned : ∀ c, Aligned record018 SharedSmallCellPool.entry c :=
  aligned_of_interval record018 SharedSmallCellPool.entry record018_alignment_checked

theorem record018_local_0 : Interval (localCheck record018) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record018_local_1 : Interval (localCheck record018) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)

theorem record018_local_checked : Interval (localCheck record018) 0 95 :=
  (interval_append _ 0 64 95 record018_local_0 record018_local_1)
theorem record018_kind_checked : Interval record018.data.kindTest 0 record018.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record015_kind_checked

theorem record018_ridge_matrix :
    record018.data.candidateMatrix = PackedIncidenceMatrix.code record018.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record015_ridge_matrix

theorem record018_edge_matrix :
    record018.data.edgeMatrix = PackedIncidenceMatrix.code record018.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record015_edge_matrix

theorem record018_missing_matrix :
    record018.data.missingMatrix = PackedIncidenceMatrix.code record018.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record015_missing_matrix

theorem record018_matrix_checked : MatrixGraphProblem.Checked record018.data :=
  matrix_checked record018 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record018_aligned (by decide +kernel) record018_local_checked
    record018_kind_checked record018_ridge_matrix record018_edge_matrix record018_missing_matrix

theorem record018_validity : GraphGrowthInputs.Valid record018.inputs :=
  valid_of_matrix record018 record018_matrix_checked

theorem record018_vertex_width : record018.vertexRows.width = record018.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record015_vertex_width

theorem record018_vertex_code : record018.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record018 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record015_vertex_code

theorem record018_literal : RawGraphSemanticCertificate.LiteralFacts record018.data :=
  literal_facts record018 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record018_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record018 SharedSmallCellPool.entry record018_vertex_width record018_vertex_code)

theorem record018_cells_exact : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c) :=
  literal_cells record018 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record018_aligned

#print axioms record018_validity
#print axioms record018_literal

theorem record019_alignment_0 : Interval (alignedCheck record019 SharedSmallCellPool.entry) 0 64 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record016_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record019_alignment_1 : Interval (alignedCheck record019 SharedSmallCellPool.entry) 64 108 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record016_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record019_alignment_checked : Interval (alignedCheck record019 SharedSmallCellPool.entry) 0 108 :=
  (interval_append _ 0 64 108 record019_alignment_0 record019_alignment_1)
theorem record019_aligned : ∀ c, Aligned record019 SharedSmallCellPool.entry c :=
  aligned_of_interval record019 SharedSmallCellPool.entry record019_alignment_checked

theorem record019_local_0 : Interval (localCheck record019) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record019_local_1 : Interval (localCheck record019) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)

theorem record019_local_checked : Interval (localCheck record019) 0 108 :=
  (interval_append _ 0 64 108 record019_local_0 record019_local_1)
theorem record019_kind_checked : Interval record019.data.kindTest 0 record019.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record016_kind_checked

theorem record019_ridge_matrix :
    record019.data.candidateMatrix = PackedIncidenceMatrix.code record019.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record016_ridge_matrix

theorem record019_edge_matrix :
    record019.data.edgeMatrix = PackedIncidenceMatrix.code record019.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record016_edge_matrix

theorem record019_missing_matrix :
    record019.data.missingMatrix = PackedIncidenceMatrix.code record019.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record016_missing_matrix

theorem record019_matrix_checked : MatrixGraphProblem.Checked record019.data :=
  matrix_checked record019 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record019_aligned (by decide +kernel) record019_local_checked
    record019_kind_checked record019_ridge_matrix record019_edge_matrix record019_missing_matrix

theorem record019_validity : GraphGrowthInputs.Valid record019.inputs :=
  valid_of_matrix record019 record019_matrix_checked

theorem record019_vertex_width : record019.vertexRows.width = record019.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record016_vertex_width

theorem record019_vertex_code : record019.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record019 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record016_vertex_code

theorem record019_literal : RawGraphSemanticCertificate.LiteralFacts record019.data :=
  literal_facts record019 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record019_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record019 SharedSmallCellPool.entry record019_vertex_width record019_vertex_code)

theorem record019_cells_exact : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c) :=
  literal_cells record019 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record019_aligned

#print axioms record019_validity
#print axioms record019_literal

theorem record020_alignment_0 : Interval (alignedCheck record020 SharedSmallCellPool.entry) 0 64 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record017_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record020_alignment_1 : Interval (alignedCheck record020 SharedSmallCellPool.entry) 64 103 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record017_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record020_alignment_checked : Interval (alignedCheck record020 SharedSmallCellPool.entry) 0 103 :=
  (interval_append _ 0 64 103 record020_alignment_0 record020_alignment_1)
theorem record020_aligned : ∀ c, Aligned record020 SharedSmallCellPool.entry c :=
  aligned_of_interval record020 SharedSmallCellPool.entry record020_alignment_checked

theorem record020_local_0 : Interval (localCheck record020) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record020_local_1 : Interval (localCheck record020) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)

theorem record020_local_checked : Interval (localCheck record020) 0 103 :=
  (interval_append _ 0 64 103 record020_local_0 record020_local_1)
theorem record020_kind_checked : Interval record020.data.kindTest 0 record020.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record017_kind_checked

theorem record020_ridge_matrix :
    record020.data.candidateMatrix = PackedIncidenceMatrix.code record020.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record017_ridge_matrix

theorem record020_edge_matrix :
    record020.data.edgeMatrix = PackedIncidenceMatrix.code record020.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record017_edge_matrix

theorem record020_missing_matrix :
    record020.data.missingMatrix = PackedIncidenceMatrix.code record020.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record017_missing_matrix

theorem record020_matrix_checked : MatrixGraphProblem.Checked record020.data :=
  matrix_checked record020 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record020_aligned (by decide +kernel) record020_local_checked
    record020_kind_checked record020_ridge_matrix record020_edge_matrix record020_missing_matrix

theorem record020_validity : GraphGrowthInputs.Valid record020.inputs :=
  valid_of_matrix record020 record020_matrix_checked

theorem record020_vertex_width : record020.vertexRows.width = record020.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record017_vertex_width

theorem record020_vertex_code : record020.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record020 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record017_vertex_code

theorem record020_literal : RawGraphSemanticCertificate.LiteralFacts record020.data :=
  literal_facts record020 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record020_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record020 SharedSmallCellPool.entry record020_vertex_width record020_vertex_code)

theorem record020_cells_exact : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c) :=
  literal_cells record020 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record020_aligned

#print axioms record020_validity
#print axioms record020_literal

theorem record021_alignment_0 : Interval (alignedCheck record021 SharedSmallCellPool.entry) 0 64 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record018_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record021_alignment_1 : Interval (alignedCheck record021 SharedSmallCellPool.entry) 64 107 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record018_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record021_alignment_checked : Interval (alignedCheck record021 SharedSmallCellPool.entry) 0 107 :=
  (interval_append _ 0 64 107 record021_alignment_0 record021_alignment_1)
theorem record021_aligned : ∀ c, Aligned record021 SharedSmallCellPool.entry c :=
  aligned_of_interval record021 SharedSmallCellPool.entry record021_alignment_checked

theorem record021_local_0 : Interval (localCheck record021) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record021_local_1 : Interval (localCheck record021) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)

theorem record021_local_checked : Interval (localCheck record021) 0 107 :=
  (interval_append _ 0 64 107 record021_local_0 record021_local_1)
theorem record021_kind_checked : Interval record021.data.kindTest 0 record021.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record018_kind_checked

theorem record021_ridge_matrix :
    record021.data.candidateMatrix = PackedIncidenceMatrix.code record021.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record018_ridge_matrix

theorem record021_edge_matrix :
    record021.data.edgeMatrix = PackedIncidenceMatrix.code record021.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record018_edge_matrix

theorem record021_missing_matrix :
    record021.data.missingMatrix = PackedIncidenceMatrix.code record021.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record018_missing_matrix

theorem record021_matrix_checked : MatrixGraphProblem.Checked record021.data :=
  matrix_checked record021 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record021_aligned (by decide +kernel) record021_local_checked
    record021_kind_checked record021_ridge_matrix record021_edge_matrix record021_missing_matrix

theorem record021_validity : GraphGrowthInputs.Valid record021.inputs :=
  valid_of_matrix record021 record021_matrix_checked

theorem record021_vertex_width : record021.vertexRows.width = record021.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record018_vertex_width

theorem record021_vertex_code : record021.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record021 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record018_vertex_code

theorem record021_literal : RawGraphSemanticCertificate.LiteralFacts record021.data :=
  literal_facts record021 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record021_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record021 SharedSmallCellPool.entry record021_vertex_width record021_vertex_code)

theorem record021_cells_exact : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c) :=
  literal_cells record021 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record021_aligned

#print axioms record021_validity
#print axioms record021_literal

theorem record022_alignment_0 : Interval (alignedCheck record022 SharedSmallCellPool.entry) 0 64 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record019_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record022_alignment_1 : Interval (alignedCheck record022 SharedSmallCellPool.entry) 64 101 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record019_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record022_alignment_checked : Interval (alignedCheck record022 SharedSmallCellPool.entry) 0 101 :=
  (interval_append _ 0 64 101 record022_alignment_0 record022_alignment_1)
theorem record022_aligned : ∀ c, Aligned record022 SharedSmallCellPool.entry c :=
  aligned_of_interval record022 SharedSmallCellPool.entry record022_alignment_checked

theorem record022_local_0 : Interval (localCheck record022) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record022_local_1 : Interval (localCheck record022) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)

theorem record022_local_checked : Interval (localCheck record022) 0 101 :=
  (interval_append _ 0 64 101 record022_local_0 record022_local_1)
theorem record022_kind_checked : Interval record022.data.kindTest 0 record022.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record019_kind_checked

theorem record022_ridge_matrix :
    record022.data.candidateMatrix = PackedIncidenceMatrix.code record022.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record019_ridge_matrix

theorem record022_edge_matrix :
    record022.data.edgeMatrix = PackedIncidenceMatrix.code record022.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record019_edge_matrix

theorem record022_missing_matrix :
    record022.data.missingMatrix = PackedIncidenceMatrix.code record022.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record019_missing_matrix

theorem record022_matrix_checked : MatrixGraphProblem.Checked record022.data :=
  matrix_checked record022 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record022_aligned (by decide +kernel) record022_local_checked
    record022_kind_checked record022_ridge_matrix record022_edge_matrix record022_missing_matrix

theorem record022_validity : GraphGrowthInputs.Valid record022.inputs :=
  valid_of_matrix record022 record022_matrix_checked

theorem record022_vertex_width : record022.vertexRows.width = record022.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record019_vertex_width

theorem record022_vertex_code : record022.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record022 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record019_vertex_code

theorem record022_literal : RawGraphSemanticCertificate.LiteralFacts record022.data :=
  literal_facts record022 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record022_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record022 SharedSmallCellPool.entry record022_vertex_width record022_vertex_code)

theorem record022_cells_exact : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c) :=
  literal_cells record022 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record022_aligned

#print axioms record022_validity
#print axioms record022_literal

theorem record023_alignment_0 : Interval (alignedCheck record023 SharedSmallCellPool.entry) 0 64 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record020_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record023_alignment_1 : Interval (alignedCheck record023 SharedSmallCellPool.entry) 64 105 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record020_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record023_alignment_checked : Interval (alignedCheck record023 SharedSmallCellPool.entry) 0 105 :=
  (interval_append _ 0 64 105 record023_alignment_0 record023_alignment_1)
theorem record023_aligned : ∀ c, Aligned record023 SharedSmallCellPool.entry c :=
  aligned_of_interval record023 SharedSmallCellPool.entry record023_alignment_checked

theorem record023_local_0 : Interval (localCheck record023) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record023_local_1 : Interval (localCheck record023) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)

theorem record023_local_checked : Interval (localCheck record023) 0 105 :=
  (interval_append _ 0 64 105 record023_local_0 record023_local_1)
theorem record023_kind_checked : Interval record023.data.kindTest 0 record023.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record020_kind_checked

theorem record023_ridge_matrix :
    record023.data.candidateMatrix = PackedIncidenceMatrix.code record023.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record020_ridge_matrix

theorem record023_edge_matrix :
    record023.data.edgeMatrix = PackedIncidenceMatrix.code record023.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record020_edge_matrix

theorem record023_missing_matrix :
    record023.data.missingMatrix = PackedIncidenceMatrix.code record023.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record020_missing_matrix

theorem record023_matrix_checked : MatrixGraphProblem.Checked record023.data :=
  matrix_checked record023 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record023_aligned (by decide +kernel) record023_local_checked
    record023_kind_checked record023_ridge_matrix record023_edge_matrix record023_missing_matrix

theorem record023_validity : GraphGrowthInputs.Valid record023.inputs :=
  valid_of_matrix record023 record023_matrix_checked

theorem record023_vertex_width : record023.vertexRows.width = record023.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record020_vertex_width

theorem record023_vertex_code : record023.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record023 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record020_vertex_code

theorem record023_literal : RawGraphSemanticCertificate.LiteralFacts record023.data :=
  literal_facts record023 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record023_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record023 SharedSmallCellPool.entry record023_vertex_width record023_vertex_code)

theorem record023_cells_exact : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c) :=
  literal_cells record023 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record023_aligned

#print axioms record023_validity
#print axioms record023_literal

theorem record024_alignment_0 : Interval (alignedCheck record024 SharedSmallCellPool.entry) 0 64 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record021_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record024_alignment_1 : Interval (alignedCheck record024 SharedSmallCellPool.entry) 64 101 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record021_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record024_alignment_checked : Interval (alignedCheck record024 SharedSmallCellPool.entry) 0 101 :=
  (interval_append _ 0 64 101 record024_alignment_0 record024_alignment_1)
theorem record024_aligned : ∀ c, Aligned record024 SharedSmallCellPool.entry c :=
  aligned_of_interval record024 SharedSmallCellPool.entry record024_alignment_checked

theorem record024_local_0 : Interval (localCheck record024) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record024_local_1 : Interval (localCheck record024) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)

theorem record024_local_checked : Interval (localCheck record024) 0 101 :=
  (interval_append _ 0 64 101 record024_local_0 record024_local_1)
theorem record024_kind_checked : Interval record024.data.kindTest 0 record024.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record021_kind_checked

theorem record024_ridge_matrix :
    record024.data.candidateMatrix = PackedIncidenceMatrix.code record024.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record021_ridge_matrix

theorem record024_edge_matrix :
    record024.data.edgeMatrix = PackedIncidenceMatrix.code record024.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record021_edge_matrix

theorem record024_missing_matrix :
    record024.data.missingMatrix = PackedIncidenceMatrix.code record024.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record021_missing_matrix

theorem record024_matrix_checked : MatrixGraphProblem.Checked record024.data :=
  matrix_checked record024 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record024_aligned (by decide +kernel) record024_local_checked
    record024_kind_checked record024_ridge_matrix record024_edge_matrix record024_missing_matrix

theorem record024_validity : GraphGrowthInputs.Valid record024.inputs :=
  valid_of_matrix record024 record024_matrix_checked

theorem record024_vertex_width : record024.vertexRows.width = record024.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record021_vertex_width

theorem record024_vertex_code : record024.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record024 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record021_vertex_code

theorem record024_literal : RawGraphSemanticCertificate.LiteralFacts record024.data :=
  literal_facts record024 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record024_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record024 SharedSmallCellPool.entry record024_vertex_width record024_vertex_code)

theorem record024_cells_exact : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c) :=
  literal_cells record024 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record024_aligned

#print axioms record024_validity
#print axioms record024_literal

theorem record025_alignment_0 : Interval (alignedCheck record025 SharedSmallCellPool.entry) 0 64 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record022_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record025_alignment_1 : Interval (alignedCheck record025 SharedSmallCellPool.entry) 64 105 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record022_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record025_alignment_checked : Interval (alignedCheck record025 SharedSmallCellPool.entry) 0 105 :=
  (interval_append _ 0 64 105 record025_alignment_0 record025_alignment_1)
theorem record025_aligned : ∀ c, Aligned record025 SharedSmallCellPool.entry c :=
  aligned_of_interval record025 SharedSmallCellPool.entry record025_alignment_checked

theorem record025_local_0 : Interval (localCheck record025) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record025_local_1 : Interval (localCheck record025) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)

theorem record025_local_checked : Interval (localCheck record025) 0 105 :=
  (interval_append _ 0 64 105 record025_local_0 record025_local_1)
theorem record025_kind_checked : Interval record025.data.kindTest 0 record025.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record022_kind_checked

theorem record025_ridge_matrix :
    record025.data.candidateMatrix = PackedIncidenceMatrix.code record025.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record022_ridge_matrix

theorem record025_edge_matrix :
    record025.data.edgeMatrix = PackedIncidenceMatrix.code record025.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record022_edge_matrix

theorem record025_missing_matrix :
    record025.data.missingMatrix = PackedIncidenceMatrix.code record025.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record022_missing_matrix

theorem record025_matrix_checked : MatrixGraphProblem.Checked record025.data :=
  matrix_checked record025 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record025_aligned (by decide +kernel) record025_local_checked
    record025_kind_checked record025_ridge_matrix record025_edge_matrix record025_missing_matrix

theorem record025_validity : GraphGrowthInputs.Valid record025.inputs :=
  valid_of_matrix record025 record025_matrix_checked

theorem record025_vertex_width : record025.vertexRows.width = record025.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record022_vertex_width

theorem record025_vertex_code : record025.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record025 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record022_vertex_code

theorem record025_literal : RawGraphSemanticCertificate.LiteralFacts record025.data :=
  literal_facts record025 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record025_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record025 SharedSmallCellPool.entry record025_vertex_width record025_vertex_code)

theorem record025_cells_exact : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c) :=
  literal_cells record025 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record025_aligned

#print axioms record025_validity
#print axioms record025_literal

theorem record026_alignment_0 : Interval (alignedCheck record026 SharedSmallCellPool.entry) 0 64 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record023_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record026_alignment_1 : Interval (alignedCheck record026 SharedSmallCellPool.entry) 64 105 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record023_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record026_alignment_checked : Interval (alignedCheck record026 SharedSmallCellPool.entry) 0 105 :=
  (interval_append _ 0 64 105 record026_alignment_0 record026_alignment_1)
theorem record026_aligned : ∀ c, Aligned record026 SharedSmallCellPool.entry c :=
  aligned_of_interval record026 SharedSmallCellPool.entry record026_alignment_checked

theorem record026_local_0 : Interval (localCheck record026) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record026_local_1 : Interval (localCheck record026) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)

theorem record026_local_checked : Interval (localCheck record026) 0 105 :=
  (interval_append _ 0 64 105 record026_local_0 record026_local_1)
theorem record026_kind_checked : Interval record026.data.kindTest 0 record026.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record023_kind_checked

theorem record026_ridge_matrix :
    record026.data.candidateMatrix = PackedIncidenceMatrix.code record026.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record023_ridge_matrix

theorem record026_edge_matrix :
    record026.data.edgeMatrix = PackedIncidenceMatrix.code record026.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record023_edge_matrix

theorem record026_missing_matrix :
    record026.data.missingMatrix = PackedIncidenceMatrix.code record026.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record023_missing_matrix

theorem record026_matrix_checked : MatrixGraphProblem.Checked record026.data :=
  matrix_checked record026 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record026_aligned (by decide +kernel) record026_local_checked
    record026_kind_checked record026_ridge_matrix record026_edge_matrix record026_missing_matrix

theorem record026_validity : GraphGrowthInputs.Valid record026.inputs :=
  valid_of_matrix record026 record026_matrix_checked

theorem record026_vertex_width : record026.vertexRows.width = record026.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record023_vertex_width

theorem record026_vertex_code : record026.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record026 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record023_vertex_code

theorem record026_literal : RawGraphSemanticCertificate.LiteralFacts record026.data :=
  literal_facts record026 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record026_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record026 SharedSmallCellPool.entry record026_vertex_width record026_vertex_code)

theorem record026_cells_exact : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c) :=
  literal_cells record026 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record026_aligned

#print axioms record026_validity
#print axioms record026_literal

theorem record027_alignment_0 : Interval (alignedCheck record027 SharedSmallCellPool.entry) 0 64 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record024_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record027_alignment_1 : Interval (alignedCheck record027 SharedSmallCellPool.entry) 64 112 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record024_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record027_alignment_checked : Interval (alignedCheck record027 SharedSmallCellPool.entry) 0 112 :=
  (interval_append _ 0 64 112 record027_alignment_0 record027_alignment_1)
theorem record027_aligned : ∀ c, Aligned record027 SharedSmallCellPool.entry c :=
  aligned_of_interval record027 SharedSmallCellPool.entry record027_alignment_checked

theorem record027_local_0 : Interval (localCheck record027) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record027_local_1 : Interval (localCheck record027) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)

theorem record027_local_checked : Interval (localCheck record027) 0 112 :=
  (interval_append _ 0 64 112 record027_local_0 record027_local_1)
theorem record027_kind_checked : Interval record027.data.kindTest 0 record027.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record024_kind_checked

theorem record027_ridge_matrix :
    record027.data.candidateMatrix = PackedIncidenceMatrix.code record027.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record024_ridge_matrix

theorem record027_edge_matrix :
    record027.data.edgeMatrix = PackedIncidenceMatrix.code record027.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record024_edge_matrix

theorem record027_missing_matrix :
    record027.data.missingMatrix = PackedIncidenceMatrix.code record027.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record024_missing_matrix

theorem record027_matrix_checked : MatrixGraphProblem.Checked record027.data :=
  matrix_checked record027 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record027_aligned (by decide +kernel) record027_local_checked
    record027_kind_checked record027_ridge_matrix record027_edge_matrix record027_missing_matrix

theorem record027_validity : GraphGrowthInputs.Valid record027.inputs :=
  valid_of_matrix record027 record027_matrix_checked

theorem record027_vertex_width : record027.vertexRows.width = record027.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record024_vertex_width

theorem record027_vertex_code : record027.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record027 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record024_vertex_code

theorem record027_literal : RawGraphSemanticCertificate.LiteralFacts record027.data :=
  literal_facts record027 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record027_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record027 SharedSmallCellPool.entry record027_vertex_width record027_vertex_code)

theorem record027_cells_exact : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c) :=
  literal_cells record027 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record027_aligned

#print axioms record027_validity
#print axioms record027_literal

theorem record028_alignment_0 : Interval (alignedCheck record028 SharedSmallCellPool.entry) 0 64 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record025_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record028_alignment_1 : Interval (alignedCheck record028 SharedSmallCellPool.entry) 64 110 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record025_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record028_alignment_checked : Interval (alignedCheck record028 SharedSmallCellPool.entry) 0 110 :=
  (interval_append _ 0 64 110 record028_alignment_0 record028_alignment_1)
theorem record028_aligned : ∀ c, Aligned record028 SharedSmallCellPool.entry c :=
  aligned_of_interval record028 SharedSmallCellPool.entry record028_alignment_checked

theorem record028_local_0 : Interval (localCheck record028) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record028_local_1 : Interval (localCheck record028) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)

theorem record028_local_checked : Interval (localCheck record028) 0 110 :=
  (interval_append _ 0 64 110 record028_local_0 record028_local_1)
theorem record028_kind_checked : Interval record028.data.kindTest 0 record028.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record025_kind_checked

theorem record028_ridge_matrix :
    record028.data.candidateMatrix = PackedIncidenceMatrix.code record028.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record025_ridge_matrix

theorem record028_edge_matrix :
    record028.data.edgeMatrix = PackedIncidenceMatrix.code record028.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record025_edge_matrix

theorem record028_missing_matrix :
    record028.data.missingMatrix = PackedIncidenceMatrix.code record028.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record025_missing_matrix

theorem record028_matrix_checked : MatrixGraphProblem.Checked record028.data :=
  matrix_checked record028 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record028_aligned (by decide +kernel) record028_local_checked
    record028_kind_checked record028_ridge_matrix record028_edge_matrix record028_missing_matrix

theorem record028_validity : GraphGrowthInputs.Valid record028.inputs :=
  valid_of_matrix record028 record028_matrix_checked

theorem record028_vertex_width : record028.vertexRows.width = record028.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record025_vertex_width

theorem record028_vertex_code : record028.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record028 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record025_vertex_code

theorem record028_literal : RawGraphSemanticCertificate.LiteralFacts record028.data :=
  literal_facts record028 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record028_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record028 SharedSmallCellPool.entry record028_vertex_width record028_vertex_code)

theorem record028_cells_exact : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c) :=
  literal_cells record028 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record028_aligned

#print axioms record028_validity
#print axioms record028_literal

theorem record029_alignment_0 : Interval (alignedCheck record029 SharedSmallCellPool.entry) 0 64 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record026_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record029_alignment_1 : Interval (alignedCheck record029 SharedSmallCellPool.entry) 64 114 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record026_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record029_alignment_checked : Interval (alignedCheck record029 SharedSmallCellPool.entry) 0 114 :=
  (interval_append _ 0 64 114 record029_alignment_0 record029_alignment_1)
theorem record029_aligned : ∀ c, Aligned record029 SharedSmallCellPool.entry c :=
  aligned_of_interval record029 SharedSmallCellPool.entry record029_alignment_checked

theorem record029_local_0 : Interval (localCheck record029) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record029_local_1 : Interval (localCheck record029) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)

theorem record029_local_checked : Interval (localCheck record029) 0 114 :=
  (interval_append _ 0 64 114 record029_local_0 record029_local_1)
theorem record029_kind_checked : Interval record029.data.kindTest 0 record029.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record026_kind_checked

theorem record029_ridge_matrix :
    record029.data.candidateMatrix = PackedIncidenceMatrix.code record029.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record026_ridge_matrix

theorem record029_edge_matrix :
    record029.data.edgeMatrix = PackedIncidenceMatrix.code record029.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record026_edge_matrix

theorem record029_missing_matrix :
    record029.data.missingMatrix = PackedIncidenceMatrix.code record029.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record026_missing_matrix

theorem record029_matrix_checked : MatrixGraphProblem.Checked record029.data :=
  matrix_checked record029 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record029_aligned (by decide +kernel) record029_local_checked
    record029_kind_checked record029_ridge_matrix record029_edge_matrix record029_missing_matrix

theorem record029_validity : GraphGrowthInputs.Valid record029.inputs :=
  valid_of_matrix record029 record029_matrix_checked

theorem record029_vertex_width : record029.vertexRows.width = record029.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record026_vertex_width

theorem record029_vertex_code : record029.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record029 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record026_vertex_code

theorem record029_literal : RawGraphSemanticCertificate.LiteralFacts record029.data :=
  literal_facts record029 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record029_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record029 SharedSmallCellPool.entry record029_vertex_width record029_vertex_code)

theorem record029_cells_exact : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c) :=
  literal_cells record029 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record029_aligned

#print axioms record029_validity
#print axioms record029_literal

theorem record030_alignment_0 : Interval (alignedCheck record030 SharedSmallCellPool.entry) 0 64 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record027_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record030_alignment_1 : Interval (alignedCheck record030 SharedSmallCellPool.entry) 64 109 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record027_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record030_alignment_checked : Interval (alignedCheck record030 SharedSmallCellPool.entry) 0 109 :=
  (interval_append _ 0 64 109 record030_alignment_0 record030_alignment_1)
theorem record030_aligned : ∀ c, Aligned record030 SharedSmallCellPool.entry c :=
  aligned_of_interval record030 SharedSmallCellPool.entry record030_alignment_checked

theorem record030_local_0 : Interval (localCheck record030) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record030_local_1 : Interval (localCheck record030) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)

theorem record030_local_checked : Interval (localCheck record030) 0 109 :=
  (interval_append _ 0 64 109 record030_local_0 record030_local_1)
theorem record030_kind_checked : Interval record030.data.kindTest 0 record030.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record027_kind_checked

theorem record030_ridge_matrix :
    record030.data.candidateMatrix = PackedIncidenceMatrix.code record030.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record027_ridge_matrix

theorem record030_edge_matrix :
    record030.data.edgeMatrix = PackedIncidenceMatrix.code record030.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record027_edge_matrix

theorem record030_missing_matrix :
    record030.data.missingMatrix = PackedIncidenceMatrix.code record030.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record027_missing_matrix

theorem record030_matrix_checked : MatrixGraphProblem.Checked record030.data :=
  matrix_checked record030 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record030_aligned (by decide +kernel) record030_local_checked
    record030_kind_checked record030_ridge_matrix record030_edge_matrix record030_missing_matrix

theorem record030_validity : GraphGrowthInputs.Valid record030.inputs :=
  valid_of_matrix record030 record030_matrix_checked

theorem record030_vertex_width : record030.vertexRows.width = record030.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record027_vertex_width

theorem record030_vertex_code : record030.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record030 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record027_vertex_code

theorem record030_literal : RawGraphSemanticCertificate.LiteralFacts record030.data :=
  literal_facts record030 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record030_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record030 SharedSmallCellPool.entry record030_vertex_width record030_vertex_code)

theorem record030_cells_exact : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c) :=
  literal_cells record030 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record030_aligned

#print axioms record030_validity
#print axioms record030_literal

theorem record031_alignment_0 : Interval (alignedCheck record031 SharedSmallCellPool.entry) 0 64 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record028_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record031_alignment_1 : Interval (alignedCheck record031 SharedSmallCellPool.entry) 64 109 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record028_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record031_alignment_checked : Interval (alignedCheck record031 SharedSmallCellPool.entry) 0 109 :=
  (interval_append _ 0 64 109 record031_alignment_0 record031_alignment_1)
theorem record031_aligned : ∀ c, Aligned record031 SharedSmallCellPool.entry c :=
  aligned_of_interval record031 SharedSmallCellPool.entry record031_alignment_checked

theorem record031_local_0 : Interval (localCheck record031) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record031_local_1 : Interval (localCheck record031) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)

theorem record031_local_checked : Interval (localCheck record031) 0 109 :=
  (interval_append _ 0 64 109 record031_local_0 record031_local_1)
theorem record031_kind_checked : Interval record031.data.kindTest 0 record031.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record028_kind_checked

theorem record031_ridge_matrix :
    record031.data.candidateMatrix = PackedIncidenceMatrix.code record031.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record028_ridge_matrix

theorem record031_edge_matrix :
    record031.data.edgeMatrix = PackedIncidenceMatrix.code record031.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record028_edge_matrix

theorem record031_missing_matrix :
    record031.data.missingMatrix = PackedIncidenceMatrix.code record031.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record028_missing_matrix

theorem record031_matrix_checked : MatrixGraphProblem.Checked record031.data :=
  matrix_checked record031 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record031_aligned (by decide +kernel) record031_local_checked
    record031_kind_checked record031_ridge_matrix record031_edge_matrix record031_missing_matrix

theorem record031_validity : GraphGrowthInputs.Valid record031.inputs :=
  valid_of_matrix record031 record031_matrix_checked

theorem record031_vertex_width : record031.vertexRows.width = record031.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record028_vertex_width

theorem record031_vertex_code : record031.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record031 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record028_vertex_code

theorem record031_literal : RawGraphSemanticCertificate.LiteralFacts record031.data :=
  literal_facts record031 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record031_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record031 SharedSmallCellPool.entry record031_vertex_width record031_vertex_code)

theorem record031_cells_exact : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c) :=
  literal_cells record031 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record031_aligned

#print axioms record031_validity
#print axioms record031_literal

theorem record032_alignment_0 : Interval (alignedCheck record032 SharedSmallCellPool.entry) 0 64 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record029_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record032_alignment_1 : Interval (alignedCheck record032 SharedSmallCellPool.entry) 64 109 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record029_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record032_alignment_checked : Interval (alignedCheck record032 SharedSmallCellPool.entry) 0 109 :=
  (interval_append _ 0 64 109 record032_alignment_0 record032_alignment_1)
theorem record032_aligned : ∀ c, Aligned record032 SharedSmallCellPool.entry c :=
  aligned_of_interval record032 SharedSmallCellPool.entry record032_alignment_checked

theorem record032_local_0 : Interval (localCheck record032) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record032_local_1 : Interval (localCheck record032) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)

theorem record032_local_checked : Interval (localCheck record032) 0 109 :=
  (interval_append _ 0 64 109 record032_local_0 record032_local_1)
theorem record032_kind_checked : Interval record032.data.kindTest 0 record032.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record029_kind_checked

theorem record032_ridge_matrix :
    record032.data.candidateMatrix = PackedIncidenceMatrix.code record032.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record029_ridge_matrix

theorem record032_edge_matrix :
    record032.data.edgeMatrix = PackedIncidenceMatrix.code record032.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record029_edge_matrix

theorem record032_missing_matrix :
    record032.data.missingMatrix = PackedIncidenceMatrix.code record032.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record029_missing_matrix

theorem record032_matrix_checked : MatrixGraphProblem.Checked record032.data :=
  matrix_checked record032 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record032_aligned (by decide +kernel) record032_local_checked
    record032_kind_checked record032_ridge_matrix record032_edge_matrix record032_missing_matrix

theorem record032_validity : GraphGrowthInputs.Valid record032.inputs :=
  valid_of_matrix record032 record032_matrix_checked

theorem record032_vertex_width : record032.vertexRows.width = record032.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record029_vertex_width

theorem record032_vertex_code : record032.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record032 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record029_vertex_code

theorem record032_literal : RawGraphSemanticCertificate.LiteralFacts record032.data :=
  literal_facts record032 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record032_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record032 SharedSmallCellPool.entry record032_vertex_width record032_vertex_code)

theorem record032_cells_exact : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c) :=
  literal_cells record032 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record032_aligned

#print axioms record032_validity
#print axioms record032_literal

theorem record033_alignment_0 : Interval (alignedCheck record033 SharedSmallCellPool.entry) 0 64 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record030_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record033_alignment_1 : Interval (alignedCheck record033 SharedSmallCellPool.entry) 64 107 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record030_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record033_alignment_checked : Interval (alignedCheck record033 SharedSmallCellPool.entry) 0 107 :=
  (interval_append _ 0 64 107 record033_alignment_0 record033_alignment_1)
theorem record033_aligned : ∀ c, Aligned record033 SharedSmallCellPool.entry c :=
  aligned_of_interval record033 SharedSmallCellPool.entry record033_alignment_checked

theorem record033_local_0 : Interval (localCheck record033) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record033_local_1 : Interval (localCheck record033) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)

theorem record033_local_checked : Interval (localCheck record033) 0 107 :=
  (interval_append _ 0 64 107 record033_local_0 record033_local_1)
theorem record033_kind_checked : Interval record033.data.kindTest 0 record033.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record030_kind_checked

theorem record033_ridge_matrix :
    record033.data.candidateMatrix = PackedIncidenceMatrix.code record033.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record030_ridge_matrix

theorem record033_edge_matrix :
    record033.data.edgeMatrix = PackedIncidenceMatrix.code record033.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record030_edge_matrix

theorem record033_missing_matrix :
    record033.data.missingMatrix = PackedIncidenceMatrix.code record033.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record030_missing_matrix

theorem record033_matrix_checked : MatrixGraphProblem.Checked record033.data :=
  matrix_checked record033 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record033_aligned (by decide +kernel) record033_local_checked
    record033_kind_checked record033_ridge_matrix record033_edge_matrix record033_missing_matrix

theorem record033_validity : GraphGrowthInputs.Valid record033.inputs :=
  valid_of_matrix record033 record033_matrix_checked

theorem record033_vertex_width : record033.vertexRows.width = record033.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record030_vertex_width

theorem record033_vertex_code : record033.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record033 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record030_vertex_code

theorem record033_literal : RawGraphSemanticCertificate.LiteralFacts record033.data :=
  literal_facts record033 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record033_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record033 SharedSmallCellPool.entry record033_vertex_width record033_vertex_code)

theorem record033_cells_exact : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c) :=
  literal_cells record033 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record033_aligned

#print axioms record033_validity
#print axioms record033_literal

end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077
