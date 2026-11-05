module
prelude
public import GraphInputsRow29Part00026Data
public import SharedGraphCellPool
public import SharedSmallCellPoolChecked
public import GraphInputsRow25Part00004Metadata

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool FiniteChecks

theorem record000_alignment_0 : Interval (alignedCheck record000 SharedSmallCellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record000_alignment_1 : Interval (alignedCheck record000 SharedSmallCellPool.entry) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)

theorem record000_alignment_checked : Interval (alignedCheck record000 SharedSmallCellPool.entry) 0 114 :=
  (interval_append _ 0 64 114 record000_alignment_0 record000_alignment_1)
theorem record000_aligned : ∀ c, Aligned record000 SharedSmallCellPool.entry c :=
  aligned_of_interval record000 SharedSmallCellPool.entry record000_alignment_checked

theorem record000_local_0 : Interval (localCheck record000) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record000_local_1 : Interval (localCheck record000) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)

theorem record000_local_checked : Interval (localCheck record000) 0 114 :=
  (interval_append _ 0 64 114 record000_local_0 record000_local_1)
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
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record007_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record001_alignment_1 : Interval (alignedCheck record001 SharedSmallCellPool.entry) 64 103 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record007_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record001_alignment_checked : Interval (alignedCheck record001 SharedSmallCellPool.entry) 0 103 :=
  (interval_append _ 0 64 103 record001_alignment_0 record001_alignment_1)
theorem record001_aligned : ∀ c, Aligned record001 SharedSmallCellPool.entry c :=
  aligned_of_interval record001 SharedSmallCellPool.entry record001_alignment_checked

theorem record001_local_0 : Interval (localCheck record001) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record001_local_1 : Interval (localCheck record001) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)

theorem record001_local_checked : Interval (localCheck record001) 0 103 :=
  (interval_append _ 0 64 103 record001_local_0 record001_local_1)
theorem record001_kind_checked : Interval record001.data.kindTest 0 record001.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record007_kind_checked

theorem record001_ridge_matrix :
    record001.data.candidateMatrix = PackedIncidenceMatrix.code record001.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record007_ridge_matrix

theorem record001_edge_matrix :
    record001.data.edgeMatrix = PackedIncidenceMatrix.code record001.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record007_edge_matrix

theorem record001_missing_matrix :
    record001.data.missingMatrix = PackedIncidenceMatrix.code record001.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record007_missing_matrix

theorem record001_matrix_checked : MatrixGraphProblem.Checked record001.data :=
  matrix_checked record001 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record001_aligned (by decide +kernel) record001_local_checked
    record001_kind_checked record001_ridge_matrix record001_edge_matrix record001_missing_matrix

theorem record001_validity : GraphGrowthInputs.Valid record001.inputs :=
  valid_of_matrix record001 record001_matrix_checked

theorem record001_vertex_width : record001.vertexRows.width = record001.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record007_vertex_width

theorem record001_vertex_code : record001.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record001 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record007_vertex_code

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
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record008_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record002_alignment_1 : Interval (alignedCheck record002 SharedSmallCellPool.entry) 64 100 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record008_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record002_alignment_checked : Interval (alignedCheck record002 SharedSmallCellPool.entry) 0 100 :=
  (interval_append _ 0 64 100 record002_alignment_0 record002_alignment_1)
theorem record002_aligned : ∀ c, Aligned record002 SharedSmallCellPool.entry c :=
  aligned_of_interval record002 SharedSmallCellPool.entry record002_alignment_checked

theorem record002_local_0 : Interval (localCheck record002) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record002_local_1 : Interval (localCheck record002) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)

theorem record002_local_checked : Interval (localCheck record002) 0 100 :=
  (interval_append _ 0 64 100 record002_local_0 record002_local_1)
theorem record002_kind_checked : Interval record002.data.kindTest 0 record002.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record008_kind_checked

theorem record002_ridge_matrix :
    record002.data.candidateMatrix = PackedIncidenceMatrix.code record002.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record008_ridge_matrix

theorem record002_edge_matrix :
    record002.data.edgeMatrix = PackedIncidenceMatrix.code record002.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record008_edge_matrix

theorem record002_missing_matrix :
    record002.data.missingMatrix = PackedIncidenceMatrix.code record002.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record008_missing_matrix

theorem record002_matrix_checked : MatrixGraphProblem.Checked record002.data :=
  matrix_checked record002 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record002_aligned (by decide +kernel) record002_local_checked
    record002_kind_checked record002_ridge_matrix record002_edge_matrix record002_missing_matrix

theorem record002_validity : GraphGrowthInputs.Valid record002.inputs :=
  valid_of_matrix record002 record002_matrix_checked

theorem record002_vertex_width : record002.vertexRows.width = record002.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record008_vertex_width

theorem record002_vertex_code : record002.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record002 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record008_vertex_code

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
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record009_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record003_alignment_1 : Interval (alignedCheck record003 SharedSmallCellPool.entry) 64 105 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record009_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record003_alignment_checked : Interval (alignedCheck record003 SharedSmallCellPool.entry) 0 105 :=
  (interval_append _ 0 64 105 record003_alignment_0 record003_alignment_1)
theorem record003_aligned : ∀ c, Aligned record003 SharedSmallCellPool.entry c :=
  aligned_of_interval record003 SharedSmallCellPool.entry record003_alignment_checked

theorem record003_local_0 : Interval (localCheck record003) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record003_local_1 : Interval (localCheck record003) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)

theorem record003_local_checked : Interval (localCheck record003) 0 105 :=
  (interval_append _ 0 64 105 record003_local_0 record003_local_1)
theorem record003_kind_checked : Interval record003.data.kindTest 0 record003.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record009_kind_checked

theorem record003_ridge_matrix :
    record003.data.candidateMatrix = PackedIncidenceMatrix.code record003.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record009_ridge_matrix

theorem record003_edge_matrix :
    record003.data.edgeMatrix = PackedIncidenceMatrix.code record003.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record009_edge_matrix

theorem record003_missing_matrix :
    record003.data.missingMatrix = PackedIncidenceMatrix.code record003.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record009_missing_matrix

theorem record003_matrix_checked : MatrixGraphProblem.Checked record003.data :=
  matrix_checked record003 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record003_aligned (by decide +kernel) record003_local_checked
    record003_kind_checked record003_ridge_matrix record003_edge_matrix record003_missing_matrix

theorem record003_validity : GraphGrowthInputs.Valid record003.inputs :=
  valid_of_matrix record003 record003_matrix_checked

theorem record003_vertex_width : record003.vertexRows.width = record003.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record009_vertex_width

theorem record003_vertex_code : record003.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record003 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record009_vertex_code

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
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record010_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record004_alignment_1 : Interval (alignedCheck record004 SharedSmallCellPool.entry) 64 91 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record010_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record004_alignment_checked : Interval (alignedCheck record004 SharedSmallCellPool.entry) 0 91 :=
  (interval_append _ 0 64 91 record004_alignment_0 record004_alignment_1)
theorem record004_aligned : ∀ c, Aligned record004 SharedSmallCellPool.entry c :=
  aligned_of_interval record004 SharedSmallCellPool.entry record004_alignment_checked

theorem record004_local_0 : Interval (localCheck record004) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record004_local_1 : Interval (localCheck record004) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)

theorem record004_local_checked : Interval (localCheck record004) 0 91 :=
  (interval_append _ 0 64 91 record004_local_0 record004_local_1)
theorem record004_kind_checked : Interval record004.data.kindTest 0 record004.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record010_kind_checked

theorem record004_ridge_matrix :
    record004.data.candidateMatrix = PackedIncidenceMatrix.code record004.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record010_ridge_matrix

theorem record004_edge_matrix :
    record004.data.edgeMatrix = PackedIncidenceMatrix.code record004.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record010_edge_matrix

theorem record004_missing_matrix :
    record004.data.missingMatrix = PackedIncidenceMatrix.code record004.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record010_missing_matrix

theorem record004_matrix_checked : MatrixGraphProblem.Checked record004.data :=
  matrix_checked record004 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record004_aligned (by decide +kernel) record004_local_checked
    record004_kind_checked record004_ridge_matrix record004_edge_matrix record004_missing_matrix

theorem record004_validity : GraphGrowthInputs.Valid record004.inputs :=
  valid_of_matrix record004 record004_matrix_checked

theorem record004_vertex_width : record004.vertexRows.width = record004.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record010_vertex_width

theorem record004_vertex_code : record004.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record004 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record010_vertex_code

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

theorem record005_alignment_1 : Interval (alignedCheck record005 SharedSmallCellPool.entry) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)

theorem record005_alignment_checked : Interval (alignedCheck record005 SharedSmallCellPool.entry) 0 102 :=
  (interval_append _ 0 64 102 record005_alignment_0 record005_alignment_1)
theorem record005_aligned : ∀ c, Aligned record005 SharedSmallCellPool.entry c :=
  aligned_of_interval record005 SharedSmallCellPool.entry record005_alignment_checked

theorem record005_local_0 : Interval (localCheck record005) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record005_local_1 : Interval (localCheck record005) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)

theorem record005_local_checked : Interval (localCheck record005) 0 102 :=
  (interval_append _ 0 64 102 record005_local_0 record005_local_1)
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
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record011_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record006_alignment_1 : Interval (alignedCheck record006 SharedSmallCellPool.entry) 64 107 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record011_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record006_alignment_checked : Interval (alignedCheck record006 SharedSmallCellPool.entry) 0 107 :=
  (interval_append _ 0 64 107 record006_alignment_0 record006_alignment_1)
theorem record006_aligned : ∀ c, Aligned record006 SharedSmallCellPool.entry c :=
  aligned_of_interval record006 SharedSmallCellPool.entry record006_alignment_checked

theorem record006_local_0 : Interval (localCheck record006) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record006_local_1 : Interval (localCheck record006) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)

theorem record006_local_checked : Interval (localCheck record006) 0 107 :=
  (interval_append _ 0 64 107 record006_local_0 record006_local_1)
theorem record006_kind_checked : Interval record006.data.kindTest 0 record006.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record011_kind_checked

theorem record006_ridge_matrix :
    record006.data.candidateMatrix = PackedIncidenceMatrix.code record006.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record011_ridge_matrix

theorem record006_edge_matrix :
    record006.data.edgeMatrix = PackedIncidenceMatrix.code record006.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record011_edge_matrix

theorem record006_missing_matrix :
    record006.data.missingMatrix = PackedIncidenceMatrix.code record006.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record011_missing_matrix

theorem record006_matrix_checked : MatrixGraphProblem.Checked record006.data :=
  matrix_checked record006 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record006_aligned (by decide +kernel) record006_local_checked
    record006_kind_checked record006_ridge_matrix record006_edge_matrix record006_missing_matrix

theorem record006_validity : GraphGrowthInputs.Valid record006.inputs :=
  valid_of_matrix record006 record006_matrix_checked

theorem record006_vertex_width : record006.vertexRows.width = record006.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record011_vertex_width

theorem record006_vertex_code : record006.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record006 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record011_vertex_code

theorem record006_literal : RawGraphSemanticCertificate.LiteralFacts record006.data :=
  literal_facts record006 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record006_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record006 SharedSmallCellPool.entry record006_vertex_width record006_vertex_code)

theorem record006_cells_exact : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c) :=
  literal_cells record006 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record006_aligned

#print axioms record006_validity
#print axioms record006_literal

theorem record007_alignment_0 : Interval (alignedCheck record007 SharedSmallCellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record007_alignment_1 : Interval (alignedCheck record007 SharedSmallCellPool.entry) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)

theorem record007_alignment_checked : Interval (alignedCheck record007 SharedSmallCellPool.entry) 0 115 :=
  (interval_append _ 0 64 115 record007_alignment_0 record007_alignment_1)
theorem record007_aligned : ∀ c, Aligned record007 SharedSmallCellPool.entry c :=
  aligned_of_interval record007 SharedSmallCellPool.entry record007_alignment_checked

theorem record007_local_0 : Interval (localCheck record007) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record007_local_1 : Interval (localCheck record007) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)

theorem record007_local_checked : Interval (localCheck record007) 0 115 :=
  (interval_append _ 0 64 115 record007_local_0 record007_local_1)
theorem record007_kind_checked : Interval record007.data.kindTest 0 record007.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record007_ridge_matrix :
    record007.data.candidateMatrix = PackedIncidenceMatrix.code record007.data.ridgeList := by
  decide +kernel

theorem record007_edge_matrix :
    record007.data.edgeMatrix = PackedIncidenceMatrix.code record007.data.edgeLists := by
  decide +kernel

theorem record007_missing_matrix :
    record007.data.missingMatrix = PackedIncidenceMatrix.code record007.data.missingLists := by
  decide +kernel

theorem record007_matrix_checked : MatrixGraphProblem.Checked record007.data :=
  matrix_checked record007 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record007_aligned (by decide +kernel) record007_local_checked
    record007_kind_checked record007_ridge_matrix record007_edge_matrix record007_missing_matrix

theorem record007_validity : GraphGrowthInputs.Valid record007.inputs :=
  valid_of_matrix record007 record007_matrix_checked

theorem record007_vertex_width : record007.vertexRows.width = record007.n := by decide +kernel

theorem record007_vertex_code : record007.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record007 SharedSmallCellPool.entry c).vertices) := by decide +kernel

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

theorem record008_alignment_1 : Interval (alignedCheck record008 SharedSmallCellPool.entry) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)

theorem record008_alignment_checked : Interval (alignedCheck record008 SharedSmallCellPool.entry) 0 117 :=
  (interval_append _ 0 64 117 record008_alignment_0 record008_alignment_1)
theorem record008_aligned : ∀ c, Aligned record008 SharedSmallCellPool.entry c :=
  aligned_of_interval record008 SharedSmallCellPool.entry record008_alignment_checked

theorem record008_local_0 : Interval (localCheck record008) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record008_local_1 : Interval (localCheck record008) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)

theorem record008_local_checked : Interval (localCheck record008) 0 117 :=
  (interval_append _ 0 64 117 record008_local_0 record008_local_1)
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

theorem record009_alignment_0 : Interval (alignedCheck record009 SharedSmallCellPool.entry) 0 64 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record012_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record009_alignment_1 : Interval (alignedCheck record009 SharedSmallCellPool.entry) 64 94 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record012_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record009_alignment_checked : Interval (alignedCheck record009 SharedSmallCellPool.entry) 0 94 :=
  (interval_append _ 0 64 94 record009_alignment_0 record009_alignment_1)
theorem record009_aligned : ∀ c, Aligned record009 SharedSmallCellPool.entry c :=
  aligned_of_interval record009 SharedSmallCellPool.entry record009_alignment_checked

theorem record009_local_0 : Interval (localCheck record009) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record009_local_1 : Interval (localCheck record009) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)

theorem record009_local_checked : Interval (localCheck record009) 0 94 :=
  (interval_append _ 0 64 94 record009_local_0 record009_local_1)
theorem record009_kind_checked : Interval record009.data.kindTest 0 record009.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record012_kind_checked

theorem record009_ridge_matrix :
    record009.data.candidateMatrix = PackedIncidenceMatrix.code record009.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record012_ridge_matrix

theorem record009_edge_matrix :
    record009.data.edgeMatrix = PackedIncidenceMatrix.code record009.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record012_edge_matrix

theorem record009_missing_matrix :
    record009.data.missingMatrix = PackedIncidenceMatrix.code record009.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record012_missing_matrix

theorem record009_matrix_checked : MatrixGraphProblem.Checked record009.data :=
  matrix_checked record009 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record009_aligned (by decide +kernel) record009_local_checked
    record009_kind_checked record009_ridge_matrix record009_edge_matrix record009_missing_matrix

theorem record009_validity : GraphGrowthInputs.Valid record009.inputs :=
  valid_of_matrix record009 record009_matrix_checked

theorem record009_vertex_width : record009.vertexRows.width = record009.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record012_vertex_width

theorem record009_vertex_code : record009.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record009 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record012_vertex_code

theorem record009_literal : RawGraphSemanticCertificate.LiteralFacts record009.data :=
  literal_facts record009 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record009_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record009 SharedSmallCellPool.entry record009_vertex_width record009_vertex_code)

theorem record009_cells_exact : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c) :=
  literal_cells record009 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record009_aligned

#print axioms record009_validity
#print axioms record009_literal

theorem record010_alignment_0 : Interval (alignedCheck record010 SharedSmallCellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record010_alignment_1 : Interval (alignedCheck record010 SharedSmallCellPool.entry) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)

theorem record010_alignment_checked : Interval (alignedCheck record010 SharedSmallCellPool.entry) 0 102 :=
  (interval_append _ 0 64 102 record010_alignment_0 record010_alignment_1)
theorem record010_aligned : ∀ c, Aligned record010 SharedSmallCellPool.entry c :=
  aligned_of_interval record010 SharedSmallCellPool.entry record010_alignment_checked

theorem record010_local_0 : Interval (localCheck record010) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record010_local_1 : Interval (localCheck record010) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)

theorem record010_local_checked : Interval (localCheck record010) 0 102 :=
  (interval_append _ 0 64 102 record010_local_0 record010_local_1)
theorem record010_kind_checked : Interval record010.data.kindTest 0 record010.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record010_ridge_matrix :
    record010.data.candidateMatrix = PackedIncidenceMatrix.code record010.data.ridgeList := by
  decide +kernel

theorem record010_edge_matrix :
    record010.data.edgeMatrix = PackedIncidenceMatrix.code record010.data.edgeLists := by
  decide +kernel

theorem record010_missing_matrix :
    record010.data.missingMatrix = PackedIncidenceMatrix.code record010.data.missingLists := by
  decide +kernel

theorem record010_matrix_checked : MatrixGraphProblem.Checked record010.data :=
  matrix_checked record010 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record010_aligned (by decide +kernel) record010_local_checked
    record010_kind_checked record010_ridge_matrix record010_edge_matrix record010_missing_matrix

theorem record010_validity : GraphGrowthInputs.Valid record010.inputs :=
  valid_of_matrix record010 record010_matrix_checked

theorem record010_vertex_width : record010.vertexRows.width = record010.n := by decide +kernel

theorem record010_vertex_code : record010.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record010 SharedSmallCellPool.entry c).vertices) := by decide +kernel

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
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record011_alignment_1 : Interval (alignedCheck record011 SharedSmallCellPool.entry) 64 99 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record011_alignment_checked : Interval (alignedCheck record011 SharedSmallCellPool.entry) 0 99 :=
  (interval_append _ 0 64 99 record011_alignment_0 record011_alignment_1)
theorem record011_aligned : ∀ c, Aligned record011 SharedSmallCellPool.entry c :=
  aligned_of_interval record011 SharedSmallCellPool.entry record011_alignment_checked

theorem record011_local_0 : Interval (localCheck record011) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record011_local_1 : Interval (localCheck record011) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)

theorem record011_local_checked : Interval (localCheck record011) 0 99 :=
  (interval_append _ 0 64 99 record011_local_0 record011_local_1)
theorem record011_kind_checked : Interval record011.data.kindTest 0 record011.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013_kind_checked

theorem record011_ridge_matrix :
    record011.data.candidateMatrix = PackedIncidenceMatrix.code record011.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013_ridge_matrix

theorem record011_edge_matrix :
    record011.data.edgeMatrix = PackedIncidenceMatrix.code record011.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013_edge_matrix

theorem record011_missing_matrix :
    record011.data.missingMatrix = PackedIncidenceMatrix.code record011.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013_missing_matrix

theorem record011_matrix_checked : MatrixGraphProblem.Checked record011.data :=
  matrix_checked record011 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record011_aligned (by decide +kernel) record011_local_checked
    record011_kind_checked record011_ridge_matrix record011_edge_matrix record011_missing_matrix

theorem record011_validity : GraphGrowthInputs.Valid record011.inputs :=
  valid_of_matrix record011 record011_matrix_checked

theorem record011_vertex_width : record011.vertexRows.width = record011.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013_vertex_width

theorem record011_vertex_code : record011.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record011 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013_vertex_code

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
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record014_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record012_alignment_1 : Interval (alignedCheck record012 SharedSmallCellPool.entry) 64 106 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record014_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record012_alignment_checked : Interval (alignedCheck record012 SharedSmallCellPool.entry) 0 106 :=
  (interval_append _ 0 64 106 record012_alignment_0 record012_alignment_1)
theorem record012_aligned : ∀ c, Aligned record012 SharedSmallCellPool.entry c :=
  aligned_of_interval record012 SharedSmallCellPool.entry record012_alignment_checked

theorem record012_local_0 : Interval (localCheck record012) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record012_local_1 : Interval (localCheck record012) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)

theorem record012_local_checked : Interval (localCheck record012) 0 106 :=
  (interval_append _ 0 64 106 record012_local_0 record012_local_1)
theorem record012_kind_checked : Interval record012.data.kindTest 0 record012.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record014_kind_checked

theorem record012_ridge_matrix :
    record012.data.candidateMatrix = PackedIncidenceMatrix.code record012.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record014_ridge_matrix

theorem record012_edge_matrix :
    record012.data.edgeMatrix = PackedIncidenceMatrix.code record012.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record014_edge_matrix

theorem record012_missing_matrix :
    record012.data.missingMatrix = PackedIncidenceMatrix.code record012.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record014_missing_matrix

theorem record012_matrix_checked : MatrixGraphProblem.Checked record012.data :=
  matrix_checked record012 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record012_aligned (by decide +kernel) record012_local_checked
    record012_kind_checked record012_ridge_matrix record012_edge_matrix record012_missing_matrix

theorem record012_validity : GraphGrowthInputs.Valid record012.inputs :=
  valid_of_matrix record012 record012_matrix_checked

theorem record012_vertex_width : record012.vertexRows.width = record012.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record014_vertex_width

theorem record012_vertex_code : record012.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record012 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record014_vertex_code

theorem record012_literal : RawGraphSemanticCertificate.LiteralFacts record012.data :=
  literal_facts record012 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record012_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record012 SharedSmallCellPool.entry record012_vertex_width record012_vertex_code)

theorem record012_cells_exact : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c) :=
  literal_cells record012 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record012_aligned

#print axioms record012_validity
#print axioms record012_literal

theorem record013_alignment_0 : Interval (alignedCheck record013 SharedSmallCellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record013_alignment_1 : Interval (alignedCheck record013 SharedSmallCellPool.entry) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)

theorem record013_alignment_checked : Interval (alignedCheck record013 SharedSmallCellPool.entry) 0 107 :=
  (interval_append _ 0 64 107 record013_alignment_0 record013_alignment_1)
theorem record013_aligned : ∀ c, Aligned record013 SharedSmallCellPool.entry c :=
  aligned_of_interval record013 SharedSmallCellPool.entry record013_alignment_checked

theorem record013_local_0 : Interval (localCheck record013) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record013_local_1 : Interval (localCheck record013) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)

theorem record013_local_checked : Interval (localCheck record013) 0 107 :=
  (interval_append _ 0 64 107 record013_local_0 record013_local_1)
theorem record013_kind_checked : Interval record013.data.kindTest 0 record013.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record013_ridge_matrix :
    record013.data.candidateMatrix = PackedIncidenceMatrix.code record013.data.ridgeList := by
  decide +kernel

theorem record013_edge_matrix :
    record013.data.edgeMatrix = PackedIncidenceMatrix.code record013.data.edgeLists := by
  decide +kernel

theorem record013_missing_matrix :
    record013.data.missingMatrix = PackedIncidenceMatrix.code record013.data.missingLists := by
  decide +kernel

theorem record013_matrix_checked : MatrixGraphProblem.Checked record013.data :=
  matrix_checked record013 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record013_aligned (by decide +kernel) record013_local_checked
    record013_kind_checked record013_ridge_matrix record013_edge_matrix record013_missing_matrix

theorem record013_validity : GraphGrowthInputs.Valid record013.inputs :=
  valid_of_matrix record013 record013_matrix_checked

theorem record013_vertex_width : record013.vertexRows.width = record013.n := by decide +kernel

theorem record013_vertex_code : record013.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record013 SharedSmallCellPool.entry c).vertices) := by decide +kernel

theorem record013_literal : RawGraphSemanticCertificate.LiteralFacts record013.data :=
  literal_facts record013 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record013_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record013 SharedSmallCellPool.entry record013_vertex_width record013_vertex_code)

theorem record013_cells_exact : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c) :=
  literal_cells record013 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record013_aligned

#print axioms record013_validity
#print axioms record013_literal

theorem record014_alignment_0 : Interval (alignedCheck record014 SharedSmallCellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record014_alignment_1 : Interval (alignedCheck record014 SharedSmallCellPool.entry) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)

theorem record014_alignment_checked : Interval (alignedCheck record014 SharedSmallCellPool.entry) 0 98 :=
  (interval_append _ 0 64 98 record014_alignment_0 record014_alignment_1)
theorem record014_aligned : ∀ c, Aligned record014 SharedSmallCellPool.entry c :=
  aligned_of_interval record014 SharedSmallCellPool.entry record014_alignment_checked

theorem record014_local_0 : Interval (localCheck record014) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record014_local_1 : Interval (localCheck record014) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)

theorem record014_local_checked : Interval (localCheck record014) 0 98 :=
  (interval_append _ 0 64 98 record014_local_0 record014_local_1)
theorem record014_kind_checked : Interval record014.data.kindTest 0 record014.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record014_ridge_matrix :
    record014.data.candidateMatrix = PackedIncidenceMatrix.code record014.data.ridgeList := by
  decide +kernel

theorem record014_edge_matrix :
    record014.data.edgeMatrix = PackedIncidenceMatrix.code record014.data.edgeLists := by
  decide +kernel

theorem record014_missing_matrix :
    record014.data.missingMatrix = PackedIncidenceMatrix.code record014.data.missingLists := by
  decide +kernel

theorem record014_matrix_checked : MatrixGraphProblem.Checked record014.data :=
  matrix_checked record014 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record014_aligned (by decide +kernel) record014_local_checked
    record014_kind_checked record014_ridge_matrix record014_edge_matrix record014_missing_matrix

theorem record014_validity : GraphGrowthInputs.Valid record014.inputs :=
  valid_of_matrix record014 record014_matrix_checked

theorem record014_vertex_width : record014.vertexRows.width = record014.n := by decide +kernel

theorem record014_vertex_code : record014.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record014 SharedSmallCellPool.entry c).vertices) := by decide +kernel

theorem record014_literal : RawGraphSemanticCertificate.LiteralFacts record014.data :=
  literal_facts record014 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record014_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record014 SharedSmallCellPool.entry record014_vertex_width record014_vertex_code)

theorem record014_cells_exact : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c) :=
  literal_cells record014 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record014_aligned

#print axioms record014_validity
#print axioms record014_literal

theorem record015_alignment_0 : Interval (alignedCheck record015 SharedSmallCellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record015_alignment_1 : Interval (alignedCheck record015 SharedSmallCellPool.entry) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)

theorem record015_alignment_checked : Interval (alignedCheck record015 SharedSmallCellPool.entry) 0 98 :=
  (interval_append _ 0 64 98 record015_alignment_0 record015_alignment_1)
theorem record015_aligned : ∀ c, Aligned record015 SharedSmallCellPool.entry c :=
  aligned_of_interval record015 SharedSmallCellPool.entry record015_alignment_checked

theorem record015_local_0 : Interval (localCheck record015) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record015_local_1 : Interval (localCheck record015) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)

theorem record015_local_checked : Interval (localCheck record015) 0 98 :=
  (interval_append _ 0 64 98 record015_local_0 record015_local_1)
theorem record015_kind_checked : Interval record015.data.kindTest 0 record015.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record015_ridge_matrix :
    record015.data.candidateMatrix = PackedIncidenceMatrix.code record015.data.ridgeList := by
  decide +kernel

theorem record015_edge_matrix :
    record015.data.edgeMatrix = PackedIncidenceMatrix.code record015.data.edgeLists := by
  decide +kernel

theorem record015_missing_matrix :
    record015.data.missingMatrix = PackedIncidenceMatrix.code record015.data.missingLists := by
  decide +kernel

theorem record015_matrix_checked : MatrixGraphProblem.Checked record015.data :=
  matrix_checked record015 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record015_aligned (by decide +kernel) record015_local_checked
    record015_kind_checked record015_ridge_matrix record015_edge_matrix record015_missing_matrix

theorem record015_validity : GraphGrowthInputs.Valid record015.inputs :=
  valid_of_matrix record015 record015_matrix_checked

theorem record015_vertex_width : record015.vertexRows.width = record015.n := by decide +kernel

theorem record015_vertex_code : record015.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record015 SharedSmallCellPool.entry c).vertices) := by decide +kernel

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
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record015_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record016_alignment_1 : Interval (alignedCheck record016 SharedSmallCellPool.entry) 64 108 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record015_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record016_alignment_checked : Interval (alignedCheck record016 SharedSmallCellPool.entry) 0 108 :=
  (interval_append _ 0 64 108 record016_alignment_0 record016_alignment_1)
theorem record016_aligned : ∀ c, Aligned record016 SharedSmallCellPool.entry c :=
  aligned_of_interval record016 SharedSmallCellPool.entry record016_alignment_checked

theorem record016_local_0 : Interval (localCheck record016) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record016_local_1 : Interval (localCheck record016) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)

theorem record016_local_checked : Interval (localCheck record016) 0 108 :=
  (interval_append _ 0 64 108 record016_local_0 record016_local_1)
theorem record016_kind_checked : Interval record016.data.kindTest 0 record016.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record015_kind_checked

theorem record016_ridge_matrix :
    record016.data.candidateMatrix = PackedIncidenceMatrix.code record016.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record015_ridge_matrix

theorem record016_edge_matrix :
    record016.data.edgeMatrix = PackedIncidenceMatrix.code record016.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record015_edge_matrix

theorem record016_missing_matrix :
    record016.data.missingMatrix = PackedIncidenceMatrix.code record016.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record015_missing_matrix

theorem record016_matrix_checked : MatrixGraphProblem.Checked record016.data :=
  matrix_checked record016 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record016_aligned (by decide +kernel) record016_local_checked
    record016_kind_checked record016_ridge_matrix record016_edge_matrix record016_missing_matrix

theorem record016_validity : GraphGrowthInputs.Valid record016.inputs :=
  valid_of_matrix record016 record016_matrix_checked

theorem record016_vertex_width : record016.vertexRows.width = record016.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record015_vertex_width

theorem record016_vertex_code : record016.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record016 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record015_vertex_code

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
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record016_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record017_alignment_1 : Interval (alignedCheck record017 SharedSmallCellPool.entry) 64 101 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record016_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record017_alignment_checked : Interval (alignedCheck record017 SharedSmallCellPool.entry) 0 101 :=
  (interval_append _ 0 64 101 record017_alignment_0 record017_alignment_1)
theorem record017_aligned : ∀ c, Aligned record017 SharedSmallCellPool.entry c :=
  aligned_of_interval record017 SharedSmallCellPool.entry record017_alignment_checked

theorem record017_local_0 : Interval (localCheck record017) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record017_local_1 : Interval (localCheck record017) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)

theorem record017_local_checked : Interval (localCheck record017) 0 101 :=
  (interval_append _ 0 64 101 record017_local_0 record017_local_1)
theorem record017_kind_checked : Interval record017.data.kindTest 0 record017.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record016_kind_checked

theorem record017_ridge_matrix :
    record017.data.candidateMatrix = PackedIncidenceMatrix.code record017.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record016_ridge_matrix

theorem record017_edge_matrix :
    record017.data.edgeMatrix = PackedIncidenceMatrix.code record017.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record016_edge_matrix

theorem record017_missing_matrix :
    record017.data.missingMatrix = PackedIncidenceMatrix.code record017.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record016_missing_matrix

theorem record017_matrix_checked : MatrixGraphProblem.Checked record017.data :=
  matrix_checked record017 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record017_aligned (by decide +kernel) record017_local_checked
    record017_kind_checked record017_ridge_matrix record017_edge_matrix record017_missing_matrix

theorem record017_validity : GraphGrowthInputs.Valid record017.inputs :=
  valid_of_matrix record017 record017_matrix_checked

theorem record017_vertex_width : record017.vertexRows.width = record017.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record016_vertex_width

theorem record017_vertex_code : record017.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record017 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record016_vertex_code

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
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record017_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record018_alignment_1 : Interval (alignedCheck record018 SharedSmallCellPool.entry) 64 111 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record017_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record018_alignment_checked : Interval (alignedCheck record018 SharedSmallCellPool.entry) 0 111 :=
  (interval_append _ 0 64 111 record018_alignment_0 record018_alignment_1)
theorem record018_aligned : ∀ c, Aligned record018 SharedSmallCellPool.entry c :=
  aligned_of_interval record018 SharedSmallCellPool.entry record018_alignment_checked

theorem record018_local_0 : Interval (localCheck record018) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record018_local_1 : Interval (localCheck record018) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)

theorem record018_local_checked : Interval (localCheck record018) 0 111 :=
  (interval_append _ 0 64 111 record018_local_0 record018_local_1)
theorem record018_kind_checked : Interval record018.data.kindTest 0 record018.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record017_kind_checked

theorem record018_ridge_matrix :
    record018.data.candidateMatrix = PackedIncidenceMatrix.code record018.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record017_ridge_matrix

theorem record018_edge_matrix :
    record018.data.edgeMatrix = PackedIncidenceMatrix.code record018.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record017_edge_matrix

theorem record018_missing_matrix :
    record018.data.missingMatrix = PackedIncidenceMatrix.code record018.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record017_missing_matrix

theorem record018_matrix_checked : MatrixGraphProblem.Checked record018.data :=
  matrix_checked record018 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record018_aligned (by decide +kernel) record018_local_checked
    record018_kind_checked record018_ridge_matrix record018_edge_matrix record018_missing_matrix

theorem record018_validity : GraphGrowthInputs.Valid record018.inputs :=
  valid_of_matrix record018 record018_matrix_checked

theorem record018_vertex_width : record018.vertexRows.width = record018.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record017_vertex_width

theorem record018_vertex_code : record018.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record018 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record017_vertex_code

theorem record018_literal : RawGraphSemanticCertificate.LiteralFacts record018.data :=
  literal_facts record018 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record018_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record018 SharedSmallCellPool.entry record018_vertex_width record018_vertex_code)

theorem record018_cells_exact : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c) :=
  literal_cells record018 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record018_aligned

#print axioms record018_validity
#print axioms record018_literal

end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026
