module
prelude
public import GraphInputsSix0Part00000Data
public import SharedGraphCellPool
public import SharedSix0CellPoolChecked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool FiniteChecks

theorem record000_alignment_0 : Interval (alignedCheck record000 SharedSix0CellPool.entry) 0 38 :=
  interval_of_check _ 0 38 (by decide +kernel)

theorem record000_alignment_checked : Interval (alignedCheck record000 SharedSix0CellPool.entry) 0 38 :=
  record000_alignment_0
theorem record000_aligned : ∀ c, Aligned record000 SharedSix0CellPool.entry c :=
  aligned_of_interval record000 SharedSix0CellPool.entry record000_alignment_checked

theorem record000_local_0 : Interval (localCheck record000) 0 38 :=
  interval_of_check _ 0 38 (by decide +kernel)

theorem record000_local_checked : Interval (localCheck record000) 0 38 :=
  record000_local_0
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
  matrix_checked record000 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record000_aligned (by decide +kernel) record000_local_checked
    record000_kind_checked record000_ridge_matrix record000_edge_matrix record000_missing_matrix

theorem record000_validity : GraphGrowthInputs.Valid record000.inputs :=
  valid_of_matrix record000 record000_matrix_checked

theorem record000_vertex_width : record000.vertexRows.width = record000.n := by decide +kernel

theorem record000_vertex_code : record000.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record000 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record000_literal : RawGraphSemanticCertificate.LiteralFacts record000.data :=
  literal_facts record000 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record000_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record000 SharedSix0CellPool.entry record000_vertex_width record000_vertex_code)

theorem record000_cells_exact : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c) :=
  literal_cells record000 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record000_aligned

#print axioms record000_validity
#print axioms record000_literal

theorem record001_alignment_0 : Interval (alignedCheck record001 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record001_alignment_1 : Interval (alignedCheck record001 SharedSix0CellPool.entry) 64 66 :=
  interval_of_check _ 64 2 (by decide +kernel)

theorem record001_alignment_checked : Interval (alignedCheck record001 SharedSix0CellPool.entry) 0 66 :=
  (interval_append _ 0 64 66 record001_alignment_0 record001_alignment_1)
theorem record001_aligned : ∀ c, Aligned record001 SharedSix0CellPool.entry c :=
  aligned_of_interval record001 SharedSix0CellPool.entry record001_alignment_checked

theorem record001_local_0 : Interval (localCheck record001) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record001_local_1 : Interval (localCheck record001) 64 66 :=
  interval_of_check _ 64 2 (by decide +kernel)

theorem record001_local_checked : Interval (localCheck record001) 0 66 :=
  (interval_append _ 0 64 66 record001_local_0 record001_local_1)
theorem record001_kind_checked : Interval record001.data.kindTest 0 record001.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record001_ridge_matrix :
    record001.data.candidateMatrix = PackedIncidenceMatrix.code record001.data.ridgeList := by
  decide +kernel

theorem record001_edge_matrix :
    record001.data.edgeMatrix = PackedIncidenceMatrix.code record001.data.edgeLists := by
  decide +kernel

theorem record001_missing_matrix :
    record001.data.missingMatrix = PackedIncidenceMatrix.code record001.data.missingLists := by
  decide +kernel

theorem record001_matrix_checked : MatrixGraphProblem.Checked record001.data :=
  matrix_checked record001 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record001_aligned (by decide +kernel) record001_local_checked
    record001_kind_checked record001_ridge_matrix record001_edge_matrix record001_missing_matrix

theorem record001_validity : GraphGrowthInputs.Valid record001.inputs :=
  valid_of_matrix record001 record001_matrix_checked

theorem record001_vertex_width : record001.vertexRows.width = record001.n := by decide +kernel

theorem record001_vertex_code : record001.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record001 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record001_literal : RawGraphSemanticCertificate.LiteralFacts record001.data :=
  literal_facts record001 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record001_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record001 SharedSix0CellPool.entry record001_vertex_width record001_vertex_code)

theorem record001_cells_exact : ∀ c, record001.data.cells c = FacetUniverses.FullSix0.cells (embedding record001 c) :=
  literal_cells record001 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record001_aligned

#print axioms record001_validity
#print axioms record001_literal

theorem record002_alignment_0 : Interval (alignedCheck record002 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record002_alignment_checked : Interval (alignedCheck record002 SharedSix0CellPool.entry) 0 64 :=
  record002_alignment_0
theorem record002_aligned : ∀ c, Aligned record002 SharedSix0CellPool.entry c :=
  aligned_of_interval record002 SharedSix0CellPool.entry record002_alignment_checked

theorem record002_local_0 : Interval (localCheck record002) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record002_local_checked : Interval (localCheck record002) 0 64 :=
  record002_local_0
theorem record002_kind_checked : Interval record002.data.kindTest 0 record002.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record002_ridge_matrix :
    record002.data.candidateMatrix = PackedIncidenceMatrix.code record002.data.ridgeList := by
  decide +kernel

theorem record002_edge_matrix :
    record002.data.edgeMatrix = PackedIncidenceMatrix.code record002.data.edgeLists := by
  decide +kernel

theorem record002_missing_matrix :
    record002.data.missingMatrix = PackedIncidenceMatrix.code record002.data.missingLists := by
  decide +kernel

theorem record002_matrix_checked : MatrixGraphProblem.Checked record002.data :=
  matrix_checked record002 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record002_aligned (by decide +kernel) record002_local_checked
    record002_kind_checked record002_ridge_matrix record002_edge_matrix record002_missing_matrix

theorem record002_validity : GraphGrowthInputs.Valid record002.inputs :=
  valid_of_matrix record002 record002_matrix_checked

theorem record002_vertex_width : record002.vertexRows.width = record002.n := by decide +kernel

theorem record002_vertex_code : record002.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record002 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record002_literal : RawGraphSemanticCertificate.LiteralFacts record002.data :=
  literal_facts record002 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record002_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record002 SharedSix0CellPool.entry record002_vertex_width record002_vertex_code)

theorem record002_cells_exact : ∀ c, record002.data.cells c = FacetUniverses.FullSix0.cells (embedding record002 c) :=
  literal_cells record002 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record002_aligned

#print axioms record002_validity
#print axioms record002_literal

theorem record003_alignment_0 : Interval (alignedCheck record003 SharedSix0CellPool.entry) 0 47 :=
  interval_of_check _ 0 47 (by decide +kernel)

theorem record003_alignment_checked : Interval (alignedCheck record003 SharedSix0CellPool.entry) 0 47 :=
  record003_alignment_0
theorem record003_aligned : ∀ c, Aligned record003 SharedSix0CellPool.entry c :=
  aligned_of_interval record003 SharedSix0CellPool.entry record003_alignment_checked

theorem record003_local_0 : Interval (localCheck record003) 0 47 :=
  interval_of_check _ 0 47 (by decide +kernel)

theorem record003_local_checked : Interval (localCheck record003) 0 47 :=
  record003_local_0
theorem record003_kind_checked : Interval record003.data.kindTest 0 record003.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record003_ridge_matrix :
    record003.data.candidateMatrix = PackedIncidenceMatrix.code record003.data.ridgeList := by
  decide +kernel

theorem record003_edge_matrix :
    record003.data.edgeMatrix = PackedIncidenceMatrix.code record003.data.edgeLists := by
  decide +kernel

theorem record003_missing_matrix :
    record003.data.missingMatrix = PackedIncidenceMatrix.code record003.data.missingLists := by
  decide +kernel

theorem record003_matrix_checked : MatrixGraphProblem.Checked record003.data :=
  matrix_checked record003 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record003_aligned (by decide +kernel) record003_local_checked
    record003_kind_checked record003_ridge_matrix record003_edge_matrix record003_missing_matrix

theorem record003_validity : GraphGrowthInputs.Valid record003.inputs :=
  valid_of_matrix record003 record003_matrix_checked

theorem record003_vertex_width : record003.vertexRows.width = record003.n := by decide +kernel

theorem record003_vertex_code : record003.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record003 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record003_literal : RawGraphSemanticCertificate.LiteralFacts record003.data :=
  literal_facts record003 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record003_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record003 SharedSix0CellPool.entry record003_vertex_width record003_vertex_code)

theorem record003_cells_exact : ∀ c, record003.data.cells c = FacetUniverses.FullSix0.cells (embedding record003 c) :=
  literal_cells record003 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record003_aligned

#print axioms record003_validity
#print axioms record003_literal

theorem record004_alignment_0 : Interval (alignedCheck record004 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record004_alignment_1 : Interval (alignedCheck record004 SharedSix0CellPool.entry) 64 68 :=
  interval_of_check _ 64 4 (by decide +kernel)

theorem record004_alignment_checked : Interval (alignedCheck record004 SharedSix0CellPool.entry) 0 68 :=
  (interval_append _ 0 64 68 record004_alignment_0 record004_alignment_1)
theorem record004_aligned : ∀ c, Aligned record004 SharedSix0CellPool.entry c :=
  aligned_of_interval record004 SharedSix0CellPool.entry record004_alignment_checked

theorem record004_local_0 : Interval (localCheck record004) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record004_local_1 : Interval (localCheck record004) 64 68 :=
  interval_of_check _ 64 4 (by decide +kernel)

theorem record004_local_checked : Interval (localCheck record004) 0 68 :=
  (interval_append _ 0 64 68 record004_local_0 record004_local_1)
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
  matrix_checked record004 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record004_aligned (by decide +kernel) record004_local_checked
    record004_kind_checked record004_ridge_matrix record004_edge_matrix record004_missing_matrix

theorem record004_validity : GraphGrowthInputs.Valid record004.inputs :=
  valid_of_matrix record004 record004_matrix_checked

theorem record004_vertex_width : record004.vertexRows.width = record004.n := by decide +kernel

theorem record004_vertex_code : record004.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record004 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record004_literal : RawGraphSemanticCertificate.LiteralFacts record004.data :=
  literal_facts record004 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record004_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record004 SharedSix0CellPool.entry record004_vertex_width record004_vertex_code)

theorem record004_cells_exact : ∀ c, record004.data.cells c = FacetUniverses.FullSix0.cells (embedding record004 c) :=
  literal_cells record004 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record004_aligned

#print axioms record004_validity
#print axioms record004_literal

theorem record005_alignment_0 : Interval (alignedCheck record005 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record005_alignment_1 : Interval (alignedCheck record005 SharedSix0CellPool.entry) 64 71 :=
  interval_of_check _ 64 7 (by decide +kernel)

theorem record005_alignment_checked : Interval (alignedCheck record005 SharedSix0CellPool.entry) 0 71 :=
  (interval_append _ 0 64 71 record005_alignment_0 record005_alignment_1)
theorem record005_aligned : ∀ c, Aligned record005 SharedSix0CellPool.entry c :=
  aligned_of_interval record005 SharedSix0CellPool.entry record005_alignment_checked

theorem record005_local_0 : Interval (localCheck record005) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record005_local_1 : Interval (localCheck record005) 64 71 :=
  interval_of_check _ 64 7 (by decide +kernel)

theorem record005_local_checked : Interval (localCheck record005) 0 71 :=
  (interval_append _ 0 64 71 record005_local_0 record005_local_1)
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
  matrix_checked record005 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record005_aligned (by decide +kernel) record005_local_checked
    record005_kind_checked record005_ridge_matrix record005_edge_matrix record005_missing_matrix

theorem record005_validity : GraphGrowthInputs.Valid record005.inputs :=
  valid_of_matrix record005 record005_matrix_checked

theorem record005_vertex_width : record005.vertexRows.width = record005.n := by decide +kernel

theorem record005_vertex_code : record005.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record005 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record005_literal : RawGraphSemanticCertificate.LiteralFacts record005.data :=
  literal_facts record005 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record005_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record005 SharedSix0CellPool.entry record005_vertex_width record005_vertex_code)

theorem record005_cells_exact : ∀ c, record005.data.cells c = FacetUniverses.FullSix0.cells (embedding record005 c) :=
  literal_cells record005 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record005_aligned

#print axioms record005_validity
#print axioms record005_literal

theorem record006_alignment_0 : Interval (alignedCheck record006 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record006_alignment_1 : Interval (alignedCheck record006 SharedSix0CellPool.entry) 64 73 :=
  interval_of_check _ 64 9 (by decide +kernel)

theorem record006_alignment_checked : Interval (alignedCheck record006 SharedSix0CellPool.entry) 0 73 :=
  (interval_append _ 0 64 73 record006_alignment_0 record006_alignment_1)
theorem record006_aligned : ∀ c, Aligned record006 SharedSix0CellPool.entry c :=
  aligned_of_interval record006 SharedSix0CellPool.entry record006_alignment_checked

theorem record006_local_0 : Interval (localCheck record006) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record006_local_1 : Interval (localCheck record006) 64 73 :=
  interval_of_check _ 64 9 (by decide +kernel)

theorem record006_local_checked : Interval (localCheck record006) 0 73 :=
  (interval_append _ 0 64 73 record006_local_0 record006_local_1)
theorem record006_kind_checked : Interval record006.data.kindTest 0 record006.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record006_ridge_matrix :
    record006.data.candidateMatrix = PackedIncidenceMatrix.code record006.data.ridgeList := by
  decide +kernel

theorem record006_edge_matrix :
    record006.data.edgeMatrix = PackedIncidenceMatrix.code record006.data.edgeLists := by
  decide +kernel

theorem record006_missing_matrix :
    record006.data.missingMatrix = PackedIncidenceMatrix.code record006.data.missingLists := by
  decide +kernel

theorem record006_matrix_checked : MatrixGraphProblem.Checked record006.data :=
  matrix_checked record006 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record006_aligned (by decide +kernel) record006_local_checked
    record006_kind_checked record006_ridge_matrix record006_edge_matrix record006_missing_matrix

theorem record006_validity : GraphGrowthInputs.Valid record006.inputs :=
  valid_of_matrix record006 record006_matrix_checked

theorem record006_vertex_width : record006.vertexRows.width = record006.n := by decide +kernel

theorem record006_vertex_code : record006.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record006 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record006_literal : RawGraphSemanticCertificate.LiteralFacts record006.data :=
  literal_facts record006 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record006_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record006 SharedSix0CellPool.entry record006_vertex_width record006_vertex_code)

theorem record006_cells_exact : ∀ c, record006.data.cells c = FacetUniverses.FullSix0.cells (embedding record006 c) :=
  literal_cells record006 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record006_aligned

#print axioms record006_validity
#print axioms record006_literal

theorem record007_alignment_0 : Interval (alignedCheck record007 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record007_alignment_1 : Interval (alignedCheck record007 SharedSix0CellPool.entry) 64 73 :=
  interval_of_check _ 64 9 (by decide +kernel)

theorem record007_alignment_checked : Interval (alignedCheck record007 SharedSix0CellPool.entry) 0 73 :=
  (interval_append _ 0 64 73 record007_alignment_0 record007_alignment_1)
theorem record007_aligned : ∀ c, Aligned record007 SharedSix0CellPool.entry c :=
  aligned_of_interval record007 SharedSix0CellPool.entry record007_alignment_checked

theorem record007_local_0 : Interval (localCheck record007) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record007_local_1 : Interval (localCheck record007) 64 73 :=
  interval_of_check _ 64 9 (by decide +kernel)

theorem record007_local_checked : Interval (localCheck record007) 0 73 :=
  (interval_append _ 0 64 73 record007_local_0 record007_local_1)
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
  matrix_checked record007 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record007_aligned (by decide +kernel) record007_local_checked
    record007_kind_checked record007_ridge_matrix record007_edge_matrix record007_missing_matrix

theorem record007_validity : GraphGrowthInputs.Valid record007.inputs :=
  valid_of_matrix record007 record007_matrix_checked

theorem record007_vertex_width : record007.vertexRows.width = record007.n := by decide +kernel

theorem record007_vertex_code : record007.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record007 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record007_literal : RawGraphSemanticCertificate.LiteralFacts record007.data :=
  literal_facts record007 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record007_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record007 SharedSix0CellPool.entry record007_vertex_width record007_vertex_code)

theorem record007_cells_exact : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c) :=
  literal_cells record007 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record007_aligned

#print axioms record007_validity
#print axioms record007_literal

theorem record008_alignment_0 : Interval (alignedCheck record008 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record008_alignment_1 : Interval (alignedCheck record008 SharedSix0CellPool.entry) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)

theorem record008_alignment_checked : Interval (alignedCheck record008 SharedSix0CellPool.entry) 0 75 :=
  (interval_append _ 0 64 75 record008_alignment_0 record008_alignment_1)
theorem record008_aligned : ∀ c, Aligned record008 SharedSix0CellPool.entry c :=
  aligned_of_interval record008 SharedSix0CellPool.entry record008_alignment_checked

theorem record008_local_0 : Interval (localCheck record008) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record008_local_1 : Interval (localCheck record008) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)

theorem record008_local_checked : Interval (localCheck record008) 0 75 :=
  (interval_append _ 0 64 75 record008_local_0 record008_local_1)
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
  matrix_checked record008 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record008_aligned (by decide +kernel) record008_local_checked
    record008_kind_checked record008_ridge_matrix record008_edge_matrix record008_missing_matrix

theorem record008_validity : GraphGrowthInputs.Valid record008.inputs :=
  valid_of_matrix record008 record008_matrix_checked

theorem record008_vertex_width : record008.vertexRows.width = record008.n := by decide +kernel

theorem record008_vertex_code : record008.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record008 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record008_literal : RawGraphSemanticCertificate.LiteralFacts record008.data :=
  literal_facts record008 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record008_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record008 SharedSix0CellPool.entry record008_vertex_width record008_vertex_code)

theorem record008_cells_exact : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c) :=
  literal_cells record008 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record008_aligned

#print axioms record008_validity
#print axioms record008_literal

theorem record009_alignment_0 : Interval (alignedCheck record009 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record009_alignment_1 : Interval (alignedCheck record009 SharedSix0CellPool.entry) 64 77 :=
  interval_of_check _ 64 13 (by decide +kernel)

theorem record009_alignment_checked : Interval (alignedCheck record009 SharedSix0CellPool.entry) 0 77 :=
  (interval_append _ 0 64 77 record009_alignment_0 record009_alignment_1)
theorem record009_aligned : ∀ c, Aligned record009 SharedSix0CellPool.entry c :=
  aligned_of_interval record009 SharedSix0CellPool.entry record009_alignment_checked

theorem record009_local_0 : Interval (localCheck record009) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record009_local_1 : Interval (localCheck record009) 64 77 :=
  interval_of_check _ 64 13 (by decide +kernel)

theorem record009_local_checked : Interval (localCheck record009) 0 77 :=
  (interval_append _ 0 64 77 record009_local_0 record009_local_1)
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
  matrix_checked record009 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record009_aligned (by decide +kernel) record009_local_checked
    record009_kind_checked record009_ridge_matrix record009_edge_matrix record009_missing_matrix

theorem record009_validity : GraphGrowthInputs.Valid record009.inputs :=
  valid_of_matrix record009 record009_matrix_checked

theorem record009_vertex_width : record009.vertexRows.width = record009.n := by decide +kernel

theorem record009_vertex_code : record009.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record009 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record009_literal : RawGraphSemanticCertificate.LiteralFacts record009.data :=
  literal_facts record009 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record009_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record009 SharedSix0CellPool.entry record009_vertex_width record009_vertex_code)

theorem record009_cells_exact : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c) :=
  literal_cells record009 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record009_aligned

#print axioms record009_validity
#print axioms record009_literal

theorem record010_alignment_0 : Interval (alignedCheck record010 SharedSix0CellPool.entry) 0 62 :=
  interval_of_check _ 0 62 (by decide +kernel)

theorem record010_alignment_checked : Interval (alignedCheck record010 SharedSix0CellPool.entry) 0 62 :=
  record010_alignment_0
theorem record010_aligned : ∀ c, Aligned record010 SharedSix0CellPool.entry c :=
  aligned_of_interval record010 SharedSix0CellPool.entry record010_alignment_checked

theorem record010_local_0 : Interval (localCheck record010) 0 62 :=
  interval_of_check _ 0 62 (by decide +kernel)

theorem record010_local_checked : Interval (localCheck record010) 0 62 :=
  record010_local_0
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
  matrix_checked record010 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record010_aligned (by decide +kernel) record010_local_checked
    record010_kind_checked record010_ridge_matrix record010_edge_matrix record010_missing_matrix

theorem record010_validity : GraphGrowthInputs.Valid record010.inputs :=
  valid_of_matrix record010 record010_matrix_checked

theorem record010_vertex_width : record010.vertexRows.width = record010.n := by decide +kernel

theorem record010_vertex_code : record010.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record010 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record010_literal : RawGraphSemanticCertificate.LiteralFacts record010.data :=
  literal_facts record010 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record010_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record010 SharedSix0CellPool.entry record010_vertex_width record010_vertex_code)

theorem record010_cells_exact : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c) :=
  literal_cells record010 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record010_aligned

#print axioms record010_validity
#print axioms record010_literal

theorem record011_alignment_0 : Interval (alignedCheck record011 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record011_alignment_1 : Interval (alignedCheck record011 SharedSix0CellPool.entry) 64 78 :=
  interval_of_check _ 64 14 (by decide +kernel)

theorem record011_alignment_checked : Interval (alignedCheck record011 SharedSix0CellPool.entry) 0 78 :=
  (interval_append _ 0 64 78 record011_alignment_0 record011_alignment_1)
theorem record011_aligned : ∀ c, Aligned record011 SharedSix0CellPool.entry c :=
  aligned_of_interval record011 SharedSix0CellPool.entry record011_alignment_checked

theorem record011_local_0 : Interval (localCheck record011) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record011_local_1 : Interval (localCheck record011) 64 78 :=
  interval_of_check _ 64 14 (by decide +kernel)

theorem record011_local_checked : Interval (localCheck record011) 0 78 :=
  (interval_append _ 0 64 78 record011_local_0 record011_local_1)
theorem record011_kind_checked : Interval record011.data.kindTest 0 record011.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record011_ridge_matrix :
    record011.data.candidateMatrix = PackedIncidenceMatrix.code record011.data.ridgeList := by
  decide +kernel

theorem record011_edge_matrix :
    record011.data.edgeMatrix = PackedIncidenceMatrix.code record011.data.edgeLists := by
  decide +kernel

theorem record011_missing_matrix :
    record011.data.missingMatrix = PackedIncidenceMatrix.code record011.data.missingLists := by
  decide +kernel

theorem record011_matrix_checked : MatrixGraphProblem.Checked record011.data :=
  matrix_checked record011 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record011_aligned (by decide +kernel) record011_local_checked
    record011_kind_checked record011_ridge_matrix record011_edge_matrix record011_missing_matrix

theorem record011_validity : GraphGrowthInputs.Valid record011.inputs :=
  valid_of_matrix record011 record011_matrix_checked

theorem record011_vertex_width : record011.vertexRows.width = record011.n := by decide +kernel

theorem record011_vertex_code : record011.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record011 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record011_literal : RawGraphSemanticCertificate.LiteralFacts record011.data :=
  literal_facts record011 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record011_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record011 SharedSix0CellPool.entry record011_vertex_width record011_vertex_code)

theorem record011_cells_exact : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c) :=
  literal_cells record011 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record011_aligned

#print axioms record011_validity
#print axioms record011_literal

theorem record012_alignment_0 : Interval (alignedCheck record012 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record012_alignment_1 : Interval (alignedCheck record012 SharedSix0CellPool.entry) 64 69 :=
  interval_of_check _ 64 5 (by decide +kernel)

theorem record012_alignment_checked : Interval (alignedCheck record012 SharedSix0CellPool.entry) 0 69 :=
  (interval_append _ 0 64 69 record012_alignment_0 record012_alignment_1)
theorem record012_aligned : ∀ c, Aligned record012 SharedSix0CellPool.entry c :=
  aligned_of_interval record012 SharedSix0CellPool.entry record012_alignment_checked

theorem record012_local_0 : Interval (localCheck record012) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record012_local_1 : Interval (localCheck record012) 64 69 :=
  interval_of_check _ 64 5 (by decide +kernel)

theorem record012_local_checked : Interval (localCheck record012) 0 69 :=
  (interval_append _ 0 64 69 record012_local_0 record012_local_1)
theorem record012_kind_checked : Interval record012.data.kindTest 0 record012.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record012_ridge_matrix :
    record012.data.candidateMatrix = PackedIncidenceMatrix.code record012.data.ridgeList := by
  decide +kernel

theorem record012_edge_matrix :
    record012.data.edgeMatrix = PackedIncidenceMatrix.code record012.data.edgeLists := by
  decide +kernel

theorem record012_missing_matrix :
    record012.data.missingMatrix = PackedIncidenceMatrix.code record012.data.missingLists := by
  decide +kernel

theorem record012_matrix_checked : MatrixGraphProblem.Checked record012.data :=
  matrix_checked record012 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record012_aligned (by decide +kernel) record012_local_checked
    record012_kind_checked record012_ridge_matrix record012_edge_matrix record012_missing_matrix

theorem record012_validity : GraphGrowthInputs.Valid record012.inputs :=
  valid_of_matrix record012 record012_matrix_checked

theorem record012_vertex_width : record012.vertexRows.width = record012.n := by decide +kernel

theorem record012_vertex_code : record012.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record012 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record012_literal : RawGraphSemanticCertificate.LiteralFacts record012.data :=
  literal_facts record012 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record012_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record012 SharedSix0CellPool.entry record012_vertex_width record012_vertex_code)

theorem record012_cells_exact : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c) :=
  literal_cells record012 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record012_aligned

#print axioms record012_validity
#print axioms record012_literal

theorem record013_alignment_0 : Interval (alignedCheck record013 SharedSix0CellPool.entry) 0 47 :=
  interval_of_check _ 0 47 (by decide +kernel)

theorem record013_alignment_checked : Interval (alignedCheck record013 SharedSix0CellPool.entry) 0 47 :=
  record013_alignment_0
theorem record013_aligned : ∀ c, Aligned record013 SharedSix0CellPool.entry c :=
  aligned_of_interval record013 SharedSix0CellPool.entry record013_alignment_checked

theorem record013_local_0 : Interval (localCheck record013) 0 47 :=
  interval_of_check _ 0 47 (by decide +kernel)

theorem record013_local_checked : Interval (localCheck record013) 0 47 :=
  record013_local_0
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
  matrix_checked record013 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record013_aligned (by decide +kernel) record013_local_checked
    record013_kind_checked record013_ridge_matrix record013_edge_matrix record013_missing_matrix

theorem record013_validity : GraphGrowthInputs.Valid record013.inputs :=
  valid_of_matrix record013 record013_matrix_checked

theorem record013_vertex_width : record013.vertexRows.width = record013.n := by decide +kernel

theorem record013_vertex_code : record013.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record013 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record013_literal : RawGraphSemanticCertificate.LiteralFacts record013.data :=
  literal_facts record013 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record013_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record013 SharedSix0CellPool.entry record013_vertex_width record013_vertex_code)

theorem record013_cells_exact : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c) :=
  literal_cells record013 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record013_aligned

#print axioms record013_validity
#print axioms record013_literal

theorem record014_alignment_0 : Interval (alignedCheck record014 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record014_alignment_1 : Interval (alignedCheck record014 SharedSix0CellPool.entry) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)

theorem record014_alignment_checked : Interval (alignedCheck record014 SharedSix0CellPool.entry) 0 86 :=
  (interval_append _ 0 64 86 record014_alignment_0 record014_alignment_1)
theorem record014_aligned : ∀ c, Aligned record014 SharedSix0CellPool.entry c :=
  aligned_of_interval record014 SharedSix0CellPool.entry record014_alignment_checked

theorem record014_local_0 : Interval (localCheck record014) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record014_local_1 : Interval (localCheck record014) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)

theorem record014_local_checked : Interval (localCheck record014) 0 86 :=
  (interval_append _ 0 64 86 record014_local_0 record014_local_1)
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
  matrix_checked record014 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record014_aligned (by decide +kernel) record014_local_checked
    record014_kind_checked record014_ridge_matrix record014_edge_matrix record014_missing_matrix

theorem record014_validity : GraphGrowthInputs.Valid record014.inputs :=
  valid_of_matrix record014 record014_matrix_checked

theorem record014_vertex_width : record014.vertexRows.width = record014.n := by decide +kernel

theorem record014_vertex_code : record014.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record014 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record014_literal : RawGraphSemanticCertificate.LiteralFacts record014.data :=
  literal_facts record014 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record014_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record014 SharedSix0CellPool.entry record014_vertex_width record014_vertex_code)

theorem record014_cells_exact : ∀ c, record014.data.cells c = FacetUniverses.FullSix0.cells (embedding record014 c) :=
  literal_cells record014 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record014_aligned

#print axioms record014_validity
#print axioms record014_literal

theorem record015_alignment_0 : Interval (alignedCheck record015 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record015_alignment_1 : Interval (alignedCheck record015 SharedSix0CellPool.entry) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)

theorem record015_alignment_checked : Interval (alignedCheck record015 SharedSix0CellPool.entry) 0 90 :=
  (interval_append _ 0 64 90 record015_alignment_0 record015_alignment_1)
theorem record015_aligned : ∀ c, Aligned record015 SharedSix0CellPool.entry c :=
  aligned_of_interval record015 SharedSix0CellPool.entry record015_alignment_checked

theorem record015_local_0 : Interval (localCheck record015) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record015_local_1 : Interval (localCheck record015) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)

theorem record015_local_checked : Interval (localCheck record015) 0 90 :=
  (interval_append _ 0 64 90 record015_local_0 record015_local_1)
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
  matrix_checked record015 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record015_aligned (by decide +kernel) record015_local_checked
    record015_kind_checked record015_ridge_matrix record015_edge_matrix record015_missing_matrix

theorem record015_validity : GraphGrowthInputs.Valid record015.inputs :=
  valid_of_matrix record015 record015_matrix_checked

theorem record015_vertex_width : record015.vertexRows.width = record015.n := by decide +kernel

theorem record015_vertex_code : record015.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record015 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record015_literal : RawGraphSemanticCertificate.LiteralFacts record015.data :=
  literal_facts record015 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record015_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record015 SharedSix0CellPool.entry record015_vertex_width record015_vertex_code)

theorem record015_cells_exact : ∀ c, record015.data.cells c = FacetUniverses.FullSix0.cells (embedding record015 c) :=
  literal_cells record015 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record015_aligned

#print axioms record015_validity
#print axioms record015_literal

theorem record016_alignment_0 : Interval (alignedCheck record016 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record016_alignment_1 : Interval (alignedCheck record016 SharedSix0CellPool.entry) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)

theorem record016_alignment_checked : Interval (alignedCheck record016 SharedSix0CellPool.entry) 0 75 :=
  (interval_append _ 0 64 75 record016_alignment_0 record016_alignment_1)
theorem record016_aligned : ∀ c, Aligned record016 SharedSix0CellPool.entry c :=
  aligned_of_interval record016 SharedSix0CellPool.entry record016_alignment_checked

theorem record016_local_0 : Interval (localCheck record016) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record016_local_1 : Interval (localCheck record016) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)

theorem record016_local_checked : Interval (localCheck record016) 0 75 :=
  (interval_append _ 0 64 75 record016_local_0 record016_local_1)
theorem record016_kind_checked : Interval record016.data.kindTest 0 record016.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record016_ridge_matrix :
    record016.data.candidateMatrix = PackedIncidenceMatrix.code record016.data.ridgeList := by
  decide +kernel

theorem record016_edge_matrix :
    record016.data.edgeMatrix = PackedIncidenceMatrix.code record016.data.edgeLists := by
  decide +kernel

theorem record016_missing_matrix :
    record016.data.missingMatrix = PackedIncidenceMatrix.code record016.data.missingLists := by
  decide +kernel

theorem record016_matrix_checked : MatrixGraphProblem.Checked record016.data :=
  matrix_checked record016 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record016_aligned (by decide +kernel) record016_local_checked
    record016_kind_checked record016_ridge_matrix record016_edge_matrix record016_missing_matrix

theorem record016_validity : GraphGrowthInputs.Valid record016.inputs :=
  valid_of_matrix record016 record016_matrix_checked

theorem record016_vertex_width : record016.vertexRows.width = record016.n := by decide +kernel

theorem record016_vertex_code : record016.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record016 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record016_literal : RawGraphSemanticCertificate.LiteralFacts record016.data :=
  literal_facts record016 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record016_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record016 SharedSix0CellPool.entry record016_vertex_width record016_vertex_code)

theorem record016_cells_exact : ∀ c, record016.data.cells c = FacetUniverses.FullSix0.cells (embedding record016 c) :=
  literal_cells record016 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record016_aligned

#print axioms record016_validity
#print axioms record016_literal

theorem record017_alignment_0 : Interval (alignedCheck record017 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record017_alignment_1 : Interval (alignedCheck record017 SharedSix0CellPool.entry) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)

theorem record017_alignment_checked : Interval (alignedCheck record017 SharedSix0CellPool.entry) 0 82 :=
  (interval_append _ 0 64 82 record017_alignment_0 record017_alignment_1)
theorem record017_aligned : ∀ c, Aligned record017 SharedSix0CellPool.entry c :=
  aligned_of_interval record017 SharedSix0CellPool.entry record017_alignment_checked

theorem record017_local_0 : Interval (localCheck record017) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record017_local_1 : Interval (localCheck record017) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)

theorem record017_local_checked : Interval (localCheck record017) 0 82 :=
  (interval_append _ 0 64 82 record017_local_0 record017_local_1)
theorem record017_kind_checked : Interval record017.data.kindTest 0 record017.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record017_ridge_matrix :
    record017.data.candidateMatrix = PackedIncidenceMatrix.code record017.data.ridgeList := by
  decide +kernel

theorem record017_edge_matrix :
    record017.data.edgeMatrix = PackedIncidenceMatrix.code record017.data.edgeLists := by
  decide +kernel

theorem record017_missing_matrix :
    record017.data.missingMatrix = PackedIncidenceMatrix.code record017.data.missingLists := by
  decide +kernel

theorem record017_matrix_checked : MatrixGraphProblem.Checked record017.data :=
  matrix_checked record017 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record017_aligned (by decide +kernel) record017_local_checked
    record017_kind_checked record017_ridge_matrix record017_edge_matrix record017_missing_matrix

theorem record017_validity : GraphGrowthInputs.Valid record017.inputs :=
  valid_of_matrix record017 record017_matrix_checked

theorem record017_vertex_width : record017.vertexRows.width = record017.n := by decide +kernel

theorem record017_vertex_code : record017.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record017 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record017_literal : RawGraphSemanticCertificate.LiteralFacts record017.data :=
  literal_facts record017 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record017_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record017 SharedSix0CellPool.entry record017_vertex_width record017_vertex_code)

theorem record017_cells_exact : ∀ c, record017.data.cells c = FacetUniverses.FullSix0.cells (embedding record017 c) :=
  literal_cells record017 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record017_aligned

#print axioms record017_validity
#print axioms record017_literal

theorem record018_alignment_0 : Interval (alignedCheck record018 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record018_alignment_1 : Interval (alignedCheck record018 SharedSix0CellPool.entry) 64 71 :=
  interval_of_check _ 64 7 (by decide +kernel)

theorem record018_alignment_checked : Interval (alignedCheck record018 SharedSix0CellPool.entry) 0 71 :=
  (interval_append _ 0 64 71 record018_alignment_0 record018_alignment_1)
theorem record018_aligned : ∀ c, Aligned record018 SharedSix0CellPool.entry c :=
  aligned_of_interval record018 SharedSix0CellPool.entry record018_alignment_checked

theorem record018_local_0 : Interval (localCheck record018) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record018_local_1 : Interval (localCheck record018) 64 71 :=
  interval_of_check _ 64 7 (by decide +kernel)

theorem record018_local_checked : Interval (localCheck record018) 0 71 :=
  (interval_append _ 0 64 71 record018_local_0 record018_local_1)
theorem record018_kind_checked : Interval record018.data.kindTest 0 record018.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record018_ridge_matrix :
    record018.data.candidateMatrix = PackedIncidenceMatrix.code record018.data.ridgeList := by
  decide +kernel

theorem record018_edge_matrix :
    record018.data.edgeMatrix = PackedIncidenceMatrix.code record018.data.edgeLists := by
  decide +kernel

theorem record018_missing_matrix :
    record018.data.missingMatrix = PackedIncidenceMatrix.code record018.data.missingLists := by
  decide +kernel

theorem record018_matrix_checked : MatrixGraphProblem.Checked record018.data :=
  matrix_checked record018 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record018_aligned (by decide +kernel) record018_local_checked
    record018_kind_checked record018_ridge_matrix record018_edge_matrix record018_missing_matrix

theorem record018_validity : GraphGrowthInputs.Valid record018.inputs :=
  valid_of_matrix record018 record018_matrix_checked

theorem record018_vertex_width : record018.vertexRows.width = record018.n := by decide +kernel

theorem record018_vertex_code : record018.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record018 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record018_literal : RawGraphSemanticCertificate.LiteralFacts record018.data :=
  literal_facts record018 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record018_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record018 SharedSix0CellPool.entry record018_vertex_width record018_vertex_code)

theorem record018_cells_exact : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c) :=
  literal_cells record018 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record018_aligned

#print axioms record018_validity
#print axioms record018_literal

theorem record019_alignment_0 : Interval (alignedCheck record019 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record019_alignment_1 : Interval (alignedCheck record019 SharedSix0CellPool.entry) 64 74 :=
  interval_of_check _ 64 10 (by decide +kernel)

theorem record019_alignment_checked : Interval (alignedCheck record019 SharedSix0CellPool.entry) 0 74 :=
  (interval_append _ 0 64 74 record019_alignment_0 record019_alignment_1)
theorem record019_aligned : ∀ c, Aligned record019 SharedSix0CellPool.entry c :=
  aligned_of_interval record019 SharedSix0CellPool.entry record019_alignment_checked

theorem record019_local_0 : Interval (localCheck record019) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record019_local_1 : Interval (localCheck record019) 64 74 :=
  interval_of_check _ 64 10 (by decide +kernel)

theorem record019_local_checked : Interval (localCheck record019) 0 74 :=
  (interval_append _ 0 64 74 record019_local_0 record019_local_1)
theorem record019_kind_checked : Interval record019.data.kindTest 0 record019.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record019_ridge_matrix :
    record019.data.candidateMatrix = PackedIncidenceMatrix.code record019.data.ridgeList := by
  decide +kernel

theorem record019_edge_matrix :
    record019.data.edgeMatrix = PackedIncidenceMatrix.code record019.data.edgeLists := by
  decide +kernel

theorem record019_missing_matrix :
    record019.data.missingMatrix = PackedIncidenceMatrix.code record019.data.missingLists := by
  decide +kernel

theorem record019_matrix_checked : MatrixGraphProblem.Checked record019.data :=
  matrix_checked record019 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record019_aligned (by decide +kernel) record019_local_checked
    record019_kind_checked record019_ridge_matrix record019_edge_matrix record019_missing_matrix

theorem record019_validity : GraphGrowthInputs.Valid record019.inputs :=
  valid_of_matrix record019 record019_matrix_checked

theorem record019_vertex_width : record019.vertexRows.width = record019.n := by decide +kernel

theorem record019_vertex_code : record019.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record019 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record019_literal : RawGraphSemanticCertificate.LiteralFacts record019.data :=
  literal_facts record019 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record019_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record019 SharedSix0CellPool.entry record019_vertex_width record019_vertex_code)

theorem record019_cells_exact : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c) :=
  literal_cells record019 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record019_aligned

#print axioms record019_validity
#print axioms record019_literal

theorem record020_alignment_0 : Interval (alignedCheck record020 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record020_alignment_1 : Interval (alignedCheck record020 SharedSix0CellPool.entry) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)

theorem record020_alignment_checked : Interval (alignedCheck record020 SharedSix0CellPool.entry) 0 80 :=
  (interval_append _ 0 64 80 record020_alignment_0 record020_alignment_1)
theorem record020_aligned : ∀ c, Aligned record020 SharedSix0CellPool.entry c :=
  aligned_of_interval record020 SharedSix0CellPool.entry record020_alignment_checked

theorem record020_local_0 : Interval (localCheck record020) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record020_local_1 : Interval (localCheck record020) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)

theorem record020_local_checked : Interval (localCheck record020) 0 80 :=
  (interval_append _ 0 64 80 record020_local_0 record020_local_1)
theorem record020_kind_checked : Interval record020.data.kindTest 0 record020.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record020_ridge_matrix :
    record020.data.candidateMatrix = PackedIncidenceMatrix.code record020.data.ridgeList := by
  decide +kernel

theorem record020_edge_matrix :
    record020.data.edgeMatrix = PackedIncidenceMatrix.code record020.data.edgeLists := by
  decide +kernel

theorem record020_missing_matrix :
    record020.data.missingMatrix = PackedIncidenceMatrix.code record020.data.missingLists := by
  decide +kernel

theorem record020_matrix_checked : MatrixGraphProblem.Checked record020.data :=
  matrix_checked record020 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record020_aligned (by decide +kernel) record020_local_checked
    record020_kind_checked record020_ridge_matrix record020_edge_matrix record020_missing_matrix

theorem record020_validity : GraphGrowthInputs.Valid record020.inputs :=
  valid_of_matrix record020 record020_matrix_checked

theorem record020_vertex_width : record020.vertexRows.width = record020.n := by decide +kernel

theorem record020_vertex_code : record020.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record020 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record020_literal : RawGraphSemanticCertificate.LiteralFacts record020.data :=
  literal_facts record020 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record020_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record020 SharedSix0CellPool.entry record020_vertex_width record020_vertex_code)

theorem record020_cells_exact : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c) :=
  literal_cells record020 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record020_aligned

#print axioms record020_validity
#print axioms record020_literal

theorem record021_alignment_0 : Interval (alignedCheck record021 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record021_alignment_1 : Interval (alignedCheck record021 SharedSix0CellPool.entry) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)

theorem record021_alignment_checked : Interval (alignedCheck record021 SharedSix0CellPool.entry) 0 87 :=
  (interval_append _ 0 64 87 record021_alignment_0 record021_alignment_1)
theorem record021_aligned : ∀ c, Aligned record021 SharedSix0CellPool.entry c :=
  aligned_of_interval record021 SharedSix0CellPool.entry record021_alignment_checked

theorem record021_local_0 : Interval (localCheck record021) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record021_local_1 : Interval (localCheck record021) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)

theorem record021_local_checked : Interval (localCheck record021) 0 87 :=
  (interval_append _ 0 64 87 record021_local_0 record021_local_1)
theorem record021_kind_checked : Interval record021.data.kindTest 0 record021.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record021_ridge_matrix :
    record021.data.candidateMatrix = PackedIncidenceMatrix.code record021.data.ridgeList := by
  decide +kernel

theorem record021_edge_matrix :
    record021.data.edgeMatrix = PackedIncidenceMatrix.code record021.data.edgeLists := by
  decide +kernel

theorem record021_missing_matrix :
    record021.data.missingMatrix = PackedIncidenceMatrix.code record021.data.missingLists := by
  decide +kernel

theorem record021_matrix_checked : MatrixGraphProblem.Checked record021.data :=
  matrix_checked record021 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record021_aligned (by decide +kernel) record021_local_checked
    record021_kind_checked record021_ridge_matrix record021_edge_matrix record021_missing_matrix

theorem record021_validity : GraphGrowthInputs.Valid record021.inputs :=
  valid_of_matrix record021 record021_matrix_checked

theorem record021_vertex_width : record021.vertexRows.width = record021.n := by decide +kernel

theorem record021_vertex_code : record021.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record021 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record021_literal : RawGraphSemanticCertificate.LiteralFacts record021.data :=
  literal_facts record021 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record021_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record021 SharedSix0CellPool.entry record021_vertex_width record021_vertex_code)

theorem record021_cells_exact : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c) :=
  literal_cells record021 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record021_aligned

#print axioms record021_validity
#print axioms record021_literal

theorem record022_alignment_0 : Interval (alignedCheck record022 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record022_alignment_1 : Interval (alignedCheck record022 SharedSix0CellPool.entry) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)

theorem record022_alignment_checked : Interval (alignedCheck record022 SharedSix0CellPool.entry) 0 91 :=
  (interval_append _ 0 64 91 record022_alignment_0 record022_alignment_1)
theorem record022_aligned : ∀ c, Aligned record022 SharedSix0CellPool.entry c :=
  aligned_of_interval record022 SharedSix0CellPool.entry record022_alignment_checked

theorem record022_local_0 : Interval (localCheck record022) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record022_local_1 : Interval (localCheck record022) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)

theorem record022_local_checked : Interval (localCheck record022) 0 91 :=
  (interval_append _ 0 64 91 record022_local_0 record022_local_1)
theorem record022_kind_checked : Interval record022.data.kindTest 0 record022.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record022_ridge_matrix :
    record022.data.candidateMatrix = PackedIncidenceMatrix.code record022.data.ridgeList := by
  decide +kernel

theorem record022_edge_matrix :
    record022.data.edgeMatrix = PackedIncidenceMatrix.code record022.data.edgeLists := by
  decide +kernel

theorem record022_missing_matrix :
    record022.data.missingMatrix = PackedIncidenceMatrix.code record022.data.missingLists := by
  decide +kernel

theorem record022_matrix_checked : MatrixGraphProblem.Checked record022.data :=
  matrix_checked record022 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record022_aligned (by decide +kernel) record022_local_checked
    record022_kind_checked record022_ridge_matrix record022_edge_matrix record022_missing_matrix

theorem record022_validity : GraphGrowthInputs.Valid record022.inputs :=
  valid_of_matrix record022 record022_matrix_checked

theorem record022_vertex_width : record022.vertexRows.width = record022.n := by decide +kernel

theorem record022_vertex_code : record022.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record022 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record022_literal : RawGraphSemanticCertificate.LiteralFacts record022.data :=
  literal_facts record022 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record022_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record022 SharedSix0CellPool.entry record022_vertex_width record022_vertex_code)

theorem record022_cells_exact : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c) :=
  literal_cells record022 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record022_aligned

#print axioms record022_validity
#print axioms record022_literal

theorem record023_alignment_0 : Interval (alignedCheck record023 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record023_alignment_1 : Interval (alignedCheck record023 SharedSix0CellPool.entry) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)

theorem record023_alignment_checked : Interval (alignedCheck record023 SharedSix0CellPool.entry) 0 95 :=
  (interval_append _ 0 64 95 record023_alignment_0 record023_alignment_1)
theorem record023_aligned : ∀ c, Aligned record023 SharedSix0CellPool.entry c :=
  aligned_of_interval record023 SharedSix0CellPool.entry record023_alignment_checked

theorem record023_local_0 : Interval (localCheck record023) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record023_local_1 : Interval (localCheck record023) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)

theorem record023_local_checked : Interval (localCheck record023) 0 95 :=
  (interval_append _ 0 64 95 record023_local_0 record023_local_1)
theorem record023_kind_checked : Interval record023.data.kindTest 0 record023.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record023_ridge_matrix :
    record023.data.candidateMatrix = PackedIncidenceMatrix.code record023.data.ridgeList := by
  decide +kernel

theorem record023_edge_matrix :
    record023.data.edgeMatrix = PackedIncidenceMatrix.code record023.data.edgeLists := by
  decide +kernel

theorem record023_missing_matrix :
    record023.data.missingMatrix = PackedIncidenceMatrix.code record023.data.missingLists := by
  decide +kernel

theorem record023_matrix_checked : MatrixGraphProblem.Checked record023.data :=
  matrix_checked record023 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record023_aligned (by decide +kernel) record023_local_checked
    record023_kind_checked record023_ridge_matrix record023_edge_matrix record023_missing_matrix

theorem record023_validity : GraphGrowthInputs.Valid record023.inputs :=
  valid_of_matrix record023 record023_matrix_checked

theorem record023_vertex_width : record023.vertexRows.width = record023.n := by decide +kernel

theorem record023_vertex_code : record023.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record023 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record023_literal : RawGraphSemanticCertificate.LiteralFacts record023.data :=
  literal_facts record023 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record023_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record023 SharedSix0CellPool.entry record023_vertex_width record023_vertex_code)

theorem record023_cells_exact : ∀ c, record023.data.cells c = FacetUniverses.FullSix0.cells (embedding record023 c) :=
  literal_cells record023 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record023_aligned

#print axioms record023_validity
#print axioms record023_literal

theorem record024_alignment_0 : Interval (alignedCheck record024 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record024_alignment_1 : Interval (alignedCheck record024 SharedSix0CellPool.entry) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)

theorem record024_alignment_checked : Interval (alignedCheck record024 SharedSix0CellPool.entry) 0 95 :=
  (interval_append _ 0 64 95 record024_alignment_0 record024_alignment_1)
theorem record024_aligned : ∀ c, Aligned record024 SharedSix0CellPool.entry c :=
  aligned_of_interval record024 SharedSix0CellPool.entry record024_alignment_checked

theorem record024_local_0 : Interval (localCheck record024) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record024_local_1 : Interval (localCheck record024) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)

theorem record024_local_checked : Interval (localCheck record024) 0 95 :=
  (interval_append _ 0 64 95 record024_local_0 record024_local_1)
theorem record024_kind_checked : Interval record024.data.kindTest 0 record024.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record024_ridge_matrix :
    record024.data.candidateMatrix = PackedIncidenceMatrix.code record024.data.ridgeList := by
  decide +kernel

theorem record024_edge_matrix :
    record024.data.edgeMatrix = PackedIncidenceMatrix.code record024.data.edgeLists := by
  decide +kernel

theorem record024_missing_matrix :
    record024.data.missingMatrix = PackedIncidenceMatrix.code record024.data.missingLists := by
  decide +kernel

theorem record024_matrix_checked : MatrixGraphProblem.Checked record024.data :=
  matrix_checked record024 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record024_aligned (by decide +kernel) record024_local_checked
    record024_kind_checked record024_ridge_matrix record024_edge_matrix record024_missing_matrix

theorem record024_validity : GraphGrowthInputs.Valid record024.inputs :=
  valid_of_matrix record024 record024_matrix_checked

theorem record024_vertex_width : record024.vertexRows.width = record024.n := by decide +kernel

theorem record024_vertex_code : record024.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record024 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record024_literal : RawGraphSemanticCertificate.LiteralFacts record024.data :=
  literal_facts record024 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record024_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record024 SharedSix0CellPool.entry record024_vertex_width record024_vertex_code)

theorem record024_cells_exact : ∀ c, record024.data.cells c = FacetUniverses.FullSix0.cells (embedding record024 c) :=
  literal_cells record024 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record024_aligned

#print axioms record024_validity
#print axioms record024_literal

theorem record025_alignment_0 : Interval (alignedCheck record025 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record025_alignment_1 : Interval (alignedCheck record025 SharedSix0CellPool.entry) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)

theorem record025_alignment_checked : Interval (alignedCheck record025 SharedSix0CellPool.entry) 0 94 :=
  (interval_append _ 0 64 94 record025_alignment_0 record025_alignment_1)
theorem record025_aligned : ∀ c, Aligned record025 SharedSix0CellPool.entry c :=
  aligned_of_interval record025 SharedSix0CellPool.entry record025_alignment_checked

theorem record025_local_0 : Interval (localCheck record025) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record025_local_1 : Interval (localCheck record025) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)

theorem record025_local_checked : Interval (localCheck record025) 0 94 :=
  (interval_append _ 0 64 94 record025_local_0 record025_local_1)
theorem record025_kind_checked : Interval record025.data.kindTest 0 record025.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record025_ridge_matrix :
    record025.data.candidateMatrix = PackedIncidenceMatrix.code record025.data.ridgeList := by
  decide +kernel

theorem record025_edge_matrix :
    record025.data.edgeMatrix = PackedIncidenceMatrix.code record025.data.edgeLists := by
  decide +kernel

theorem record025_missing_matrix :
    record025.data.missingMatrix = PackedIncidenceMatrix.code record025.data.missingLists := by
  decide +kernel

theorem record025_matrix_checked : MatrixGraphProblem.Checked record025.data :=
  matrix_checked record025 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record025_aligned (by decide +kernel) record025_local_checked
    record025_kind_checked record025_ridge_matrix record025_edge_matrix record025_missing_matrix

theorem record025_validity : GraphGrowthInputs.Valid record025.inputs :=
  valid_of_matrix record025 record025_matrix_checked

theorem record025_vertex_width : record025.vertexRows.width = record025.n := by decide +kernel

theorem record025_vertex_code : record025.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record025 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record025_literal : RawGraphSemanticCertificate.LiteralFacts record025.data :=
  literal_facts record025 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record025_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record025 SharedSix0CellPool.entry record025_vertex_width record025_vertex_code)

theorem record025_cells_exact : ∀ c, record025.data.cells c = FacetUniverses.FullSix0.cells (embedding record025 c) :=
  literal_cells record025 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record025_aligned

#print axioms record025_validity
#print axioms record025_literal

theorem record026_alignment_0 : Interval (alignedCheck record026 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record026_alignment_1 : Interval (alignedCheck record026 SharedSix0CellPool.entry) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)

theorem record026_alignment_checked : Interval (alignedCheck record026 SharedSix0CellPool.entry) 0 87 :=
  (interval_append _ 0 64 87 record026_alignment_0 record026_alignment_1)
theorem record026_aligned : ∀ c, Aligned record026 SharedSix0CellPool.entry c :=
  aligned_of_interval record026 SharedSix0CellPool.entry record026_alignment_checked

theorem record026_local_0 : Interval (localCheck record026) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record026_local_1 : Interval (localCheck record026) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)

theorem record026_local_checked : Interval (localCheck record026) 0 87 :=
  (interval_append _ 0 64 87 record026_local_0 record026_local_1)
theorem record026_kind_checked : Interval record026.data.kindTest 0 record026.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record026_ridge_matrix :
    record026.data.candidateMatrix = PackedIncidenceMatrix.code record026.data.ridgeList := by
  decide +kernel

theorem record026_edge_matrix :
    record026.data.edgeMatrix = PackedIncidenceMatrix.code record026.data.edgeLists := by
  decide +kernel

theorem record026_missing_matrix :
    record026.data.missingMatrix = PackedIncidenceMatrix.code record026.data.missingLists := by
  decide +kernel

theorem record026_matrix_checked : MatrixGraphProblem.Checked record026.data :=
  matrix_checked record026 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record026_aligned (by decide +kernel) record026_local_checked
    record026_kind_checked record026_ridge_matrix record026_edge_matrix record026_missing_matrix

theorem record026_validity : GraphGrowthInputs.Valid record026.inputs :=
  valid_of_matrix record026 record026_matrix_checked

theorem record026_vertex_width : record026.vertexRows.width = record026.n := by decide +kernel

theorem record026_vertex_code : record026.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record026 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record026_literal : RawGraphSemanticCertificate.LiteralFacts record026.data :=
  literal_facts record026 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record026_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record026 SharedSix0CellPool.entry record026_vertex_width record026_vertex_code)

theorem record026_cells_exact : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c) :=
  literal_cells record026 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record026_aligned

#print axioms record026_validity
#print axioms record026_literal

theorem record027_alignment_0 : Interval (alignedCheck record027 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record027_alignment_1 : Interval (alignedCheck record027 SharedSix0CellPool.entry) 64 73 :=
  interval_of_check _ 64 9 (by decide +kernel)

theorem record027_alignment_checked : Interval (alignedCheck record027 SharedSix0CellPool.entry) 0 73 :=
  (interval_append _ 0 64 73 record027_alignment_0 record027_alignment_1)
theorem record027_aligned : ∀ c, Aligned record027 SharedSix0CellPool.entry c :=
  aligned_of_interval record027 SharedSix0CellPool.entry record027_alignment_checked

theorem record027_local_0 : Interval (localCheck record027) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record027_local_1 : Interval (localCheck record027) 64 73 :=
  interval_of_check _ 64 9 (by decide +kernel)

theorem record027_local_checked : Interval (localCheck record027) 0 73 :=
  (interval_append _ 0 64 73 record027_local_0 record027_local_1)
theorem record027_kind_checked : Interval record027.data.kindTest 0 record027.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record027_ridge_matrix :
    record027.data.candidateMatrix = PackedIncidenceMatrix.code record027.data.ridgeList := by
  decide +kernel

theorem record027_edge_matrix :
    record027.data.edgeMatrix = PackedIncidenceMatrix.code record027.data.edgeLists := by
  decide +kernel

theorem record027_missing_matrix :
    record027.data.missingMatrix = PackedIncidenceMatrix.code record027.data.missingLists := by
  decide +kernel

theorem record027_matrix_checked : MatrixGraphProblem.Checked record027.data :=
  matrix_checked record027 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record027_aligned (by decide +kernel) record027_local_checked
    record027_kind_checked record027_ridge_matrix record027_edge_matrix record027_missing_matrix

theorem record027_validity : GraphGrowthInputs.Valid record027.inputs :=
  valid_of_matrix record027 record027_matrix_checked

theorem record027_vertex_width : record027.vertexRows.width = record027.n := by decide +kernel

theorem record027_vertex_code : record027.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record027 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record027_literal : RawGraphSemanticCertificate.LiteralFacts record027.data :=
  literal_facts record027 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record027_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record027 SharedSix0CellPool.entry record027_vertex_width record027_vertex_code)

theorem record027_cells_exact : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c) :=
  literal_cells record027 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record027_aligned

#print axioms record027_validity
#print axioms record027_literal

theorem record028_alignment_0 : Interval (alignedCheck record028 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record028_alignment_1 : Interval (alignedCheck record028 SharedSix0CellPool.entry) 64 78 :=
  interval_of_check _ 64 14 (by decide +kernel)

theorem record028_alignment_checked : Interval (alignedCheck record028 SharedSix0CellPool.entry) 0 78 :=
  (interval_append _ 0 64 78 record028_alignment_0 record028_alignment_1)
theorem record028_aligned : ∀ c, Aligned record028 SharedSix0CellPool.entry c :=
  aligned_of_interval record028 SharedSix0CellPool.entry record028_alignment_checked

theorem record028_local_0 : Interval (localCheck record028) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record028_local_1 : Interval (localCheck record028) 64 78 :=
  interval_of_check _ 64 14 (by decide +kernel)

theorem record028_local_checked : Interval (localCheck record028) 0 78 :=
  (interval_append _ 0 64 78 record028_local_0 record028_local_1)
theorem record028_kind_checked : Interval record028.data.kindTest 0 record028.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record028_ridge_matrix :
    record028.data.candidateMatrix = PackedIncidenceMatrix.code record028.data.ridgeList := by
  decide +kernel

theorem record028_edge_matrix :
    record028.data.edgeMatrix = PackedIncidenceMatrix.code record028.data.edgeLists := by
  decide +kernel

theorem record028_missing_matrix :
    record028.data.missingMatrix = PackedIncidenceMatrix.code record028.data.missingLists := by
  decide +kernel

theorem record028_matrix_checked : MatrixGraphProblem.Checked record028.data :=
  matrix_checked record028 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record028_aligned (by decide +kernel) record028_local_checked
    record028_kind_checked record028_ridge_matrix record028_edge_matrix record028_missing_matrix

theorem record028_validity : GraphGrowthInputs.Valid record028.inputs :=
  valid_of_matrix record028 record028_matrix_checked

theorem record028_vertex_width : record028.vertexRows.width = record028.n := by decide +kernel

theorem record028_vertex_code : record028.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record028 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record028_literal : RawGraphSemanticCertificate.LiteralFacts record028.data :=
  literal_facts record028 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record028_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record028 SharedSix0CellPool.entry record028_vertex_width record028_vertex_code)

theorem record028_cells_exact : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c) :=
  literal_cells record028 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record028_aligned

#print axioms record028_validity
#print axioms record028_literal

theorem record029_alignment_0 : Interval (alignedCheck record029 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record029_alignment_1 : Interval (alignedCheck record029 SharedSix0CellPool.entry) 64 77 :=
  interval_of_check _ 64 13 (by decide +kernel)

theorem record029_alignment_checked : Interval (alignedCheck record029 SharedSix0CellPool.entry) 0 77 :=
  (interval_append _ 0 64 77 record029_alignment_0 record029_alignment_1)
theorem record029_aligned : ∀ c, Aligned record029 SharedSix0CellPool.entry c :=
  aligned_of_interval record029 SharedSix0CellPool.entry record029_alignment_checked

theorem record029_local_0 : Interval (localCheck record029) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record029_local_1 : Interval (localCheck record029) 64 77 :=
  interval_of_check _ 64 13 (by decide +kernel)

theorem record029_local_checked : Interval (localCheck record029) 0 77 :=
  (interval_append _ 0 64 77 record029_local_0 record029_local_1)
theorem record029_kind_checked : Interval record029.data.kindTest 0 record029.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record029_ridge_matrix :
    record029.data.candidateMatrix = PackedIncidenceMatrix.code record029.data.ridgeList := by
  decide +kernel

theorem record029_edge_matrix :
    record029.data.edgeMatrix = PackedIncidenceMatrix.code record029.data.edgeLists := by
  decide +kernel

theorem record029_missing_matrix :
    record029.data.missingMatrix = PackedIncidenceMatrix.code record029.data.missingLists := by
  decide +kernel

theorem record029_matrix_checked : MatrixGraphProblem.Checked record029.data :=
  matrix_checked record029 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record029_aligned (by decide +kernel) record029_local_checked
    record029_kind_checked record029_ridge_matrix record029_edge_matrix record029_missing_matrix

theorem record029_validity : GraphGrowthInputs.Valid record029.inputs :=
  valid_of_matrix record029 record029_matrix_checked

theorem record029_vertex_width : record029.vertexRows.width = record029.n := by decide +kernel

theorem record029_vertex_code : record029.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record029 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record029_literal : RawGraphSemanticCertificate.LiteralFacts record029.data :=
  literal_facts record029 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record029_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record029 SharedSix0CellPool.entry record029_vertex_width record029_vertex_code)

theorem record029_cells_exact : ∀ c, record029.data.cells c = FacetUniverses.FullSix0.cells (embedding record029 c) :=
  literal_cells record029 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record029_aligned

#print axioms record029_validity
#print axioms record029_literal

theorem record030_alignment_0 : Interval (alignedCheck record030 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record030_alignment_1 : Interval (alignedCheck record030 SharedSix0CellPool.entry) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)

theorem record030_alignment_checked : Interval (alignedCheck record030 SharedSix0CellPool.entry) 0 86 :=
  (interval_append _ 0 64 86 record030_alignment_0 record030_alignment_1)
theorem record030_aligned : ∀ c, Aligned record030 SharedSix0CellPool.entry c :=
  aligned_of_interval record030 SharedSix0CellPool.entry record030_alignment_checked

theorem record030_local_0 : Interval (localCheck record030) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record030_local_1 : Interval (localCheck record030) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)

theorem record030_local_checked : Interval (localCheck record030) 0 86 :=
  (interval_append _ 0 64 86 record030_local_0 record030_local_1)
theorem record030_kind_checked : Interval record030.data.kindTest 0 record030.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record030_ridge_matrix :
    record030.data.candidateMatrix = PackedIncidenceMatrix.code record030.data.ridgeList := by
  decide +kernel

theorem record030_edge_matrix :
    record030.data.edgeMatrix = PackedIncidenceMatrix.code record030.data.edgeLists := by
  decide +kernel

theorem record030_missing_matrix :
    record030.data.missingMatrix = PackedIncidenceMatrix.code record030.data.missingLists := by
  decide +kernel

theorem record030_matrix_checked : MatrixGraphProblem.Checked record030.data :=
  matrix_checked record030 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record030_aligned (by decide +kernel) record030_local_checked
    record030_kind_checked record030_ridge_matrix record030_edge_matrix record030_missing_matrix

theorem record030_validity : GraphGrowthInputs.Valid record030.inputs :=
  valid_of_matrix record030 record030_matrix_checked

theorem record030_vertex_width : record030.vertexRows.width = record030.n := by decide +kernel

theorem record030_vertex_code : record030.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record030 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record030_literal : RawGraphSemanticCertificate.LiteralFacts record030.data :=
  literal_facts record030 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record030_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record030 SharedSix0CellPool.entry record030_vertex_width record030_vertex_code)

theorem record030_cells_exact : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c) :=
  literal_cells record030 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record030_aligned

#print axioms record030_validity
#print axioms record030_literal

theorem record031_alignment_0 : Interval (alignedCheck record031 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record031_alignment_1 : Interval (alignedCheck record031 SharedSix0CellPool.entry) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)

theorem record031_alignment_checked : Interval (alignedCheck record031 SharedSix0CellPool.entry) 0 84 :=
  (interval_append _ 0 64 84 record031_alignment_0 record031_alignment_1)
theorem record031_aligned : ∀ c, Aligned record031 SharedSix0CellPool.entry c :=
  aligned_of_interval record031 SharedSix0CellPool.entry record031_alignment_checked

theorem record031_local_0 : Interval (localCheck record031) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record031_local_1 : Interval (localCheck record031) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)

theorem record031_local_checked : Interval (localCheck record031) 0 84 :=
  (interval_append _ 0 64 84 record031_local_0 record031_local_1)
theorem record031_kind_checked : Interval record031.data.kindTest 0 record031.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record031_ridge_matrix :
    record031.data.candidateMatrix = PackedIncidenceMatrix.code record031.data.ridgeList := by
  decide +kernel

theorem record031_edge_matrix :
    record031.data.edgeMatrix = PackedIncidenceMatrix.code record031.data.edgeLists := by
  decide +kernel

theorem record031_missing_matrix :
    record031.data.missingMatrix = PackedIncidenceMatrix.code record031.data.missingLists := by
  decide +kernel

theorem record031_matrix_checked : MatrixGraphProblem.Checked record031.data :=
  matrix_checked record031 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record031_aligned (by decide +kernel) record031_local_checked
    record031_kind_checked record031_ridge_matrix record031_edge_matrix record031_missing_matrix

theorem record031_validity : GraphGrowthInputs.Valid record031.inputs :=
  valid_of_matrix record031 record031_matrix_checked

theorem record031_vertex_width : record031.vertexRows.width = record031.n := by decide +kernel

theorem record031_vertex_code : record031.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record031 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record031_literal : RawGraphSemanticCertificate.LiteralFacts record031.data :=
  literal_facts record031 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record031_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record031 SharedSix0CellPool.entry record031_vertex_width record031_vertex_code)

theorem record031_cells_exact : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c) :=
  literal_cells record031 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record031_aligned

#print axioms record031_validity
#print axioms record031_literal

theorem record032_alignment_0 : Interval (alignedCheck record032 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record032_alignment_1 : Interval (alignedCheck record032 SharedSix0CellPool.entry) 64 65 :=
  interval_of_check _ 64 1 (by decide +kernel)

theorem record032_alignment_checked : Interval (alignedCheck record032 SharedSix0CellPool.entry) 0 65 :=
  (interval_append _ 0 64 65 record032_alignment_0 record032_alignment_1)
theorem record032_aligned : ∀ c, Aligned record032 SharedSix0CellPool.entry c :=
  aligned_of_interval record032 SharedSix0CellPool.entry record032_alignment_checked

theorem record032_local_0 : Interval (localCheck record032) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record032_local_1 : Interval (localCheck record032) 64 65 :=
  interval_of_check _ 64 1 (by decide +kernel)

theorem record032_local_checked : Interval (localCheck record032) 0 65 :=
  (interval_append _ 0 64 65 record032_local_0 record032_local_1)
theorem record032_kind_checked : Interval record032.data.kindTest 0 record032.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record032_ridge_matrix :
    record032.data.candidateMatrix = PackedIncidenceMatrix.code record032.data.ridgeList := by
  decide +kernel

theorem record032_edge_matrix :
    record032.data.edgeMatrix = PackedIncidenceMatrix.code record032.data.edgeLists := by
  decide +kernel

theorem record032_missing_matrix :
    record032.data.missingMatrix = PackedIncidenceMatrix.code record032.data.missingLists := by
  decide +kernel

theorem record032_matrix_checked : MatrixGraphProblem.Checked record032.data :=
  matrix_checked record032 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record032_aligned (by decide +kernel) record032_local_checked
    record032_kind_checked record032_ridge_matrix record032_edge_matrix record032_missing_matrix

theorem record032_validity : GraphGrowthInputs.Valid record032.inputs :=
  valid_of_matrix record032 record032_matrix_checked

theorem record032_vertex_width : record032.vertexRows.width = record032.n := by decide +kernel

theorem record032_vertex_code : record032.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record032 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record032_literal : RawGraphSemanticCertificate.LiteralFacts record032.data :=
  literal_facts record032 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record032_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record032 SharedSix0CellPool.entry record032_vertex_width record032_vertex_code)

theorem record032_cells_exact : ∀ c, record032.data.cells c = FacetUniverses.FullSix0.cells (embedding record032 c) :=
  literal_cells record032 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record032_aligned

#print axioms record032_validity
#print axioms record032_literal

theorem record033_alignment_0 : Interval (alignedCheck record033 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record033_alignment_1 : Interval (alignedCheck record033 SharedSix0CellPool.entry) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)

theorem record033_alignment_checked : Interval (alignedCheck record033 SharedSix0CellPool.entry) 0 80 :=
  (interval_append _ 0 64 80 record033_alignment_0 record033_alignment_1)
theorem record033_aligned : ∀ c, Aligned record033 SharedSix0CellPool.entry c :=
  aligned_of_interval record033 SharedSix0CellPool.entry record033_alignment_checked

theorem record033_local_0 : Interval (localCheck record033) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record033_local_1 : Interval (localCheck record033) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)

theorem record033_local_checked : Interval (localCheck record033) 0 80 :=
  (interval_append _ 0 64 80 record033_local_0 record033_local_1)
theorem record033_kind_checked : Interval record033.data.kindTest 0 record033.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record033_ridge_matrix :
    record033.data.candidateMatrix = PackedIncidenceMatrix.code record033.data.ridgeList := by
  decide +kernel

theorem record033_edge_matrix :
    record033.data.edgeMatrix = PackedIncidenceMatrix.code record033.data.edgeLists := by
  decide +kernel

theorem record033_missing_matrix :
    record033.data.missingMatrix = PackedIncidenceMatrix.code record033.data.missingLists := by
  decide +kernel

theorem record033_matrix_checked : MatrixGraphProblem.Checked record033.data :=
  matrix_checked record033 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record033_aligned (by decide +kernel) record033_local_checked
    record033_kind_checked record033_ridge_matrix record033_edge_matrix record033_missing_matrix

theorem record033_validity : GraphGrowthInputs.Valid record033.inputs :=
  valid_of_matrix record033 record033_matrix_checked

theorem record033_vertex_width : record033.vertexRows.width = record033.n := by decide +kernel

theorem record033_vertex_code : record033.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record033 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record033_literal : RawGraphSemanticCertificate.LiteralFacts record033.data :=
  literal_facts record033 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record033_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record033 SharedSix0CellPool.entry record033_vertex_width record033_vertex_code)

theorem record033_cells_exact : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c) :=
  literal_cells record033 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record033_aligned

#print axioms record033_validity
#print axioms record033_literal

theorem record034_alignment_0 : Interval (alignedCheck record034 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record034_alignment_1 : Interval (alignedCheck record034 SharedSix0CellPool.entry) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)

theorem record034_alignment_checked : Interval (alignedCheck record034 SharedSix0CellPool.entry) 0 82 :=
  (interval_append _ 0 64 82 record034_alignment_0 record034_alignment_1)
theorem record034_aligned : ∀ c, Aligned record034 SharedSix0CellPool.entry c :=
  aligned_of_interval record034 SharedSix0CellPool.entry record034_alignment_checked

theorem record034_local_0 : Interval (localCheck record034) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record034_local_1 : Interval (localCheck record034) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)

theorem record034_local_checked : Interval (localCheck record034) 0 82 :=
  (interval_append _ 0 64 82 record034_local_0 record034_local_1)
theorem record034_kind_checked : Interval record034.data.kindTest 0 record034.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record034_ridge_matrix :
    record034.data.candidateMatrix = PackedIncidenceMatrix.code record034.data.ridgeList := by
  decide +kernel

theorem record034_edge_matrix :
    record034.data.edgeMatrix = PackedIncidenceMatrix.code record034.data.edgeLists := by
  decide +kernel

theorem record034_missing_matrix :
    record034.data.missingMatrix = PackedIncidenceMatrix.code record034.data.missingLists := by
  decide +kernel

theorem record034_matrix_checked : MatrixGraphProblem.Checked record034.data :=
  matrix_checked record034 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record034_aligned (by decide +kernel) record034_local_checked
    record034_kind_checked record034_ridge_matrix record034_edge_matrix record034_missing_matrix

theorem record034_validity : GraphGrowthInputs.Valid record034.inputs :=
  valid_of_matrix record034 record034_matrix_checked

theorem record034_vertex_width : record034.vertexRows.width = record034.n := by decide +kernel

theorem record034_vertex_code : record034.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record034 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record034_literal : RawGraphSemanticCertificate.LiteralFacts record034.data :=
  literal_facts record034 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record034_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record034 SharedSix0CellPool.entry record034_vertex_width record034_vertex_code)

theorem record034_cells_exact : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c) :=
  literal_cells record034 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record034_aligned

#print axioms record034_validity
#print axioms record034_literal

theorem record035_alignment_0 : Interval (alignedCheck record035 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record035_alignment_1 : Interval (alignedCheck record035 SharedSix0CellPool.entry) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)

theorem record035_alignment_checked : Interval (alignedCheck record035 SharedSix0CellPool.entry) 0 85 :=
  (interval_append _ 0 64 85 record035_alignment_0 record035_alignment_1)
theorem record035_aligned : ∀ c, Aligned record035 SharedSix0CellPool.entry c :=
  aligned_of_interval record035 SharedSix0CellPool.entry record035_alignment_checked

theorem record035_local_0 : Interval (localCheck record035) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record035_local_1 : Interval (localCheck record035) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)

theorem record035_local_checked : Interval (localCheck record035) 0 85 :=
  (interval_append _ 0 64 85 record035_local_0 record035_local_1)
theorem record035_kind_checked : Interval record035.data.kindTest 0 record035.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record035_ridge_matrix :
    record035.data.candidateMatrix = PackedIncidenceMatrix.code record035.data.ridgeList := by
  decide +kernel

theorem record035_edge_matrix :
    record035.data.edgeMatrix = PackedIncidenceMatrix.code record035.data.edgeLists := by
  decide +kernel

theorem record035_missing_matrix :
    record035.data.missingMatrix = PackedIncidenceMatrix.code record035.data.missingLists := by
  decide +kernel

theorem record035_matrix_checked : MatrixGraphProblem.Checked record035.data :=
  matrix_checked record035 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record035_aligned (by decide +kernel) record035_local_checked
    record035_kind_checked record035_ridge_matrix record035_edge_matrix record035_missing_matrix

theorem record035_validity : GraphGrowthInputs.Valid record035.inputs :=
  valid_of_matrix record035 record035_matrix_checked

theorem record035_vertex_width : record035.vertexRows.width = record035.n := by decide +kernel

theorem record035_vertex_code : record035.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record035 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record035_literal : RawGraphSemanticCertificate.LiteralFacts record035.data :=
  literal_facts record035 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record035_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record035 SharedSix0CellPool.entry record035_vertex_width record035_vertex_code)

theorem record035_cells_exact : ∀ c, record035.data.cells c = FacetUniverses.FullSix0.cells (embedding record035 c) :=
  literal_cells record035 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record035_aligned

#print axioms record035_validity
#print axioms record035_literal

theorem record036_alignment_0 : Interval (alignedCheck record036 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record036_alignment_1 : Interval (alignedCheck record036 SharedSix0CellPool.entry) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)

theorem record036_alignment_checked : Interval (alignedCheck record036 SharedSix0CellPool.entry) 0 87 :=
  (interval_append _ 0 64 87 record036_alignment_0 record036_alignment_1)
theorem record036_aligned : ∀ c, Aligned record036 SharedSix0CellPool.entry c :=
  aligned_of_interval record036 SharedSix0CellPool.entry record036_alignment_checked

theorem record036_local_0 : Interval (localCheck record036) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record036_local_1 : Interval (localCheck record036) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)

theorem record036_local_checked : Interval (localCheck record036) 0 87 :=
  (interval_append _ 0 64 87 record036_local_0 record036_local_1)
theorem record036_kind_checked : Interval record036.data.kindTest 0 record036.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record036_ridge_matrix :
    record036.data.candidateMatrix = PackedIncidenceMatrix.code record036.data.ridgeList := by
  decide +kernel

theorem record036_edge_matrix :
    record036.data.edgeMatrix = PackedIncidenceMatrix.code record036.data.edgeLists := by
  decide +kernel

theorem record036_missing_matrix :
    record036.data.missingMatrix = PackedIncidenceMatrix.code record036.data.missingLists := by
  decide +kernel

theorem record036_matrix_checked : MatrixGraphProblem.Checked record036.data :=
  matrix_checked record036 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record036_aligned (by decide +kernel) record036_local_checked
    record036_kind_checked record036_ridge_matrix record036_edge_matrix record036_missing_matrix

theorem record036_validity : GraphGrowthInputs.Valid record036.inputs :=
  valid_of_matrix record036 record036_matrix_checked

theorem record036_vertex_width : record036.vertexRows.width = record036.n := by decide +kernel

theorem record036_vertex_code : record036.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record036 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record036_literal : RawGraphSemanticCertificate.LiteralFacts record036.data :=
  literal_facts record036 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record036_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record036 SharedSix0CellPool.entry record036_vertex_width record036_vertex_code)

theorem record036_cells_exact : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c) :=
  literal_cells record036 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record036_aligned

#print axioms record036_validity
#print axioms record036_literal

theorem record037_alignment_0 : Interval (alignedCheck record037 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record037_alignment_1 : Interval (alignedCheck record037 SharedSix0CellPool.entry) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)

theorem record037_alignment_checked : Interval (alignedCheck record037 SharedSix0CellPool.entry) 0 80 :=
  (interval_append _ 0 64 80 record037_alignment_0 record037_alignment_1)
theorem record037_aligned : ∀ c, Aligned record037 SharedSix0CellPool.entry c :=
  aligned_of_interval record037 SharedSix0CellPool.entry record037_alignment_checked

theorem record037_local_0 : Interval (localCheck record037) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record037_local_1 : Interval (localCheck record037) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)

theorem record037_local_checked : Interval (localCheck record037) 0 80 :=
  (interval_append _ 0 64 80 record037_local_0 record037_local_1)
theorem record037_kind_checked : Interval record037.data.kindTest 0 record037.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record037_ridge_matrix :
    record037.data.candidateMatrix = PackedIncidenceMatrix.code record037.data.ridgeList := by
  decide +kernel

theorem record037_edge_matrix :
    record037.data.edgeMatrix = PackedIncidenceMatrix.code record037.data.edgeLists := by
  decide +kernel

theorem record037_missing_matrix :
    record037.data.missingMatrix = PackedIncidenceMatrix.code record037.data.missingLists := by
  decide +kernel

theorem record037_matrix_checked : MatrixGraphProblem.Checked record037.data :=
  matrix_checked record037 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record037_aligned (by decide +kernel) record037_local_checked
    record037_kind_checked record037_ridge_matrix record037_edge_matrix record037_missing_matrix

theorem record037_validity : GraphGrowthInputs.Valid record037.inputs :=
  valid_of_matrix record037 record037_matrix_checked

theorem record037_vertex_width : record037.vertexRows.width = record037.n := by decide +kernel

theorem record037_vertex_code : record037.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record037 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record037_literal : RawGraphSemanticCertificate.LiteralFacts record037.data :=
  literal_facts record037 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record037_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record037 SharedSix0CellPool.entry record037_vertex_width record037_vertex_code)

theorem record037_cells_exact : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c) :=
  literal_cells record037 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record037_aligned

#print axioms record037_validity
#print axioms record037_literal

theorem record038_alignment_0 : Interval (alignedCheck record038 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record038_alignment_1 : Interval (alignedCheck record038 SharedSix0CellPool.entry) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)

theorem record038_alignment_checked : Interval (alignedCheck record038 SharedSix0CellPool.entry) 0 86 :=
  (interval_append _ 0 64 86 record038_alignment_0 record038_alignment_1)
theorem record038_aligned : ∀ c, Aligned record038 SharedSix0CellPool.entry c :=
  aligned_of_interval record038 SharedSix0CellPool.entry record038_alignment_checked

theorem record038_local_0 : Interval (localCheck record038) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record038_local_1 : Interval (localCheck record038) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)

theorem record038_local_checked : Interval (localCheck record038) 0 86 :=
  (interval_append _ 0 64 86 record038_local_0 record038_local_1)
theorem record038_kind_checked : Interval record038.data.kindTest 0 record038.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record038_ridge_matrix :
    record038.data.candidateMatrix = PackedIncidenceMatrix.code record038.data.ridgeList := by
  decide +kernel

theorem record038_edge_matrix :
    record038.data.edgeMatrix = PackedIncidenceMatrix.code record038.data.edgeLists := by
  decide +kernel

theorem record038_missing_matrix :
    record038.data.missingMatrix = PackedIncidenceMatrix.code record038.data.missingLists := by
  decide +kernel

theorem record038_matrix_checked : MatrixGraphProblem.Checked record038.data :=
  matrix_checked record038 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record038_aligned (by decide +kernel) record038_local_checked
    record038_kind_checked record038_ridge_matrix record038_edge_matrix record038_missing_matrix

theorem record038_validity : GraphGrowthInputs.Valid record038.inputs :=
  valid_of_matrix record038 record038_matrix_checked

theorem record038_vertex_width : record038.vertexRows.width = record038.n := by decide +kernel

theorem record038_vertex_code : record038.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record038 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record038_literal : RawGraphSemanticCertificate.LiteralFacts record038.data :=
  literal_facts record038 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record038_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record038 SharedSix0CellPool.entry record038_vertex_width record038_vertex_code)

theorem record038_cells_exact : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c) :=
  literal_cells record038 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record038_aligned

#print axioms record038_validity
#print axioms record038_literal

theorem record039_alignment_0 : Interval (alignedCheck record039 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record039_alignment_1 : Interval (alignedCheck record039 SharedSix0CellPool.entry) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)

theorem record039_alignment_checked : Interval (alignedCheck record039 SharedSix0CellPool.entry) 0 88 :=
  (interval_append _ 0 64 88 record039_alignment_0 record039_alignment_1)
theorem record039_aligned : ∀ c, Aligned record039 SharedSix0CellPool.entry c :=
  aligned_of_interval record039 SharedSix0CellPool.entry record039_alignment_checked

theorem record039_local_0 : Interval (localCheck record039) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record039_local_1 : Interval (localCheck record039) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)

theorem record039_local_checked : Interval (localCheck record039) 0 88 :=
  (interval_append _ 0 64 88 record039_local_0 record039_local_1)
theorem record039_kind_checked : Interval record039.data.kindTest 0 record039.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record039_ridge_matrix :
    record039.data.candidateMatrix = PackedIncidenceMatrix.code record039.data.ridgeList := by
  decide +kernel

theorem record039_edge_matrix :
    record039.data.edgeMatrix = PackedIncidenceMatrix.code record039.data.edgeLists := by
  decide +kernel

theorem record039_missing_matrix :
    record039.data.missingMatrix = PackedIncidenceMatrix.code record039.data.missingLists := by
  decide +kernel

theorem record039_matrix_checked : MatrixGraphProblem.Checked record039.data :=
  matrix_checked record039 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record039_aligned (by decide +kernel) record039_local_checked
    record039_kind_checked record039_ridge_matrix record039_edge_matrix record039_missing_matrix

theorem record039_validity : GraphGrowthInputs.Valid record039.inputs :=
  valid_of_matrix record039 record039_matrix_checked

theorem record039_vertex_width : record039.vertexRows.width = record039.n := by decide +kernel

theorem record039_vertex_code : record039.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record039 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record039_literal : RawGraphSemanticCertificate.LiteralFacts record039.data :=
  literal_facts record039 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record039_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record039 SharedSix0CellPool.entry record039_vertex_width record039_vertex_code)

theorem record039_cells_exact : ∀ c, record039.data.cells c = FacetUniverses.FullSix0.cells (embedding record039 c) :=
  literal_cells record039 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record039_aligned

#print axioms record039_validity
#print axioms record039_literal

theorem record040_alignment_0 : Interval (alignedCheck record040 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record040_alignment_1 : Interval (alignedCheck record040 SharedSix0CellPool.entry) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)

theorem record040_alignment_checked : Interval (alignedCheck record040 SharedSix0CellPool.entry) 0 86 :=
  (interval_append _ 0 64 86 record040_alignment_0 record040_alignment_1)
theorem record040_aligned : ∀ c, Aligned record040 SharedSix0CellPool.entry c :=
  aligned_of_interval record040 SharedSix0CellPool.entry record040_alignment_checked

theorem record040_local_0 : Interval (localCheck record040) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record040_local_1 : Interval (localCheck record040) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)

theorem record040_local_checked : Interval (localCheck record040) 0 86 :=
  (interval_append _ 0 64 86 record040_local_0 record040_local_1)
theorem record040_kind_checked : Interval record040.data.kindTest 0 record040.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record040_ridge_matrix :
    record040.data.candidateMatrix = PackedIncidenceMatrix.code record040.data.ridgeList := by
  decide +kernel

theorem record040_edge_matrix :
    record040.data.edgeMatrix = PackedIncidenceMatrix.code record040.data.edgeLists := by
  decide +kernel

theorem record040_missing_matrix :
    record040.data.missingMatrix = PackedIncidenceMatrix.code record040.data.missingLists := by
  decide +kernel

theorem record040_matrix_checked : MatrixGraphProblem.Checked record040.data :=
  matrix_checked record040 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record040_aligned (by decide +kernel) record040_local_checked
    record040_kind_checked record040_ridge_matrix record040_edge_matrix record040_missing_matrix

theorem record040_validity : GraphGrowthInputs.Valid record040.inputs :=
  valid_of_matrix record040 record040_matrix_checked

theorem record040_vertex_width : record040.vertexRows.width = record040.n := by decide +kernel

theorem record040_vertex_code : record040.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record040 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record040_literal : RawGraphSemanticCertificate.LiteralFacts record040.data :=
  literal_facts record040 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record040_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record040 SharedSix0CellPool.entry record040_vertex_width record040_vertex_code)

theorem record040_cells_exact : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c) :=
  literal_cells record040 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record040_aligned

#print axioms record040_validity
#print axioms record040_literal

theorem record041_alignment_0 : Interval (alignedCheck record041 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record041_alignment_1 : Interval (alignedCheck record041 SharedSix0CellPool.entry) 64 72 :=
  interval_of_check _ 64 8 (by decide +kernel)

theorem record041_alignment_checked : Interval (alignedCheck record041 SharedSix0CellPool.entry) 0 72 :=
  (interval_append _ 0 64 72 record041_alignment_0 record041_alignment_1)
theorem record041_aligned : ∀ c, Aligned record041 SharedSix0CellPool.entry c :=
  aligned_of_interval record041 SharedSix0CellPool.entry record041_alignment_checked

theorem record041_local_0 : Interval (localCheck record041) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record041_local_1 : Interval (localCheck record041) 64 72 :=
  interval_of_check _ 64 8 (by decide +kernel)

theorem record041_local_checked : Interval (localCheck record041) 0 72 :=
  (interval_append _ 0 64 72 record041_local_0 record041_local_1)
theorem record041_kind_checked : Interval record041.data.kindTest 0 record041.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record041_ridge_matrix :
    record041.data.candidateMatrix = PackedIncidenceMatrix.code record041.data.ridgeList := by
  decide +kernel

theorem record041_edge_matrix :
    record041.data.edgeMatrix = PackedIncidenceMatrix.code record041.data.edgeLists := by
  decide +kernel

theorem record041_missing_matrix :
    record041.data.missingMatrix = PackedIncidenceMatrix.code record041.data.missingLists := by
  decide +kernel

theorem record041_matrix_checked : MatrixGraphProblem.Checked record041.data :=
  matrix_checked record041 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record041_aligned (by decide +kernel) record041_local_checked
    record041_kind_checked record041_ridge_matrix record041_edge_matrix record041_missing_matrix

theorem record041_validity : GraphGrowthInputs.Valid record041.inputs :=
  valid_of_matrix record041 record041_matrix_checked

theorem record041_vertex_width : record041.vertexRows.width = record041.n := by decide +kernel

theorem record041_vertex_code : record041.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record041 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record041_literal : RawGraphSemanticCertificate.LiteralFacts record041.data :=
  literal_facts record041 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record041_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record041 SharedSix0CellPool.entry record041_vertex_width record041_vertex_code)

theorem record041_cells_exact : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c) :=
  literal_cells record041 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record041_aligned

#print axioms record041_validity
#print axioms record041_literal

theorem record042_alignment_0 : Interval (alignedCheck record042 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record042_alignment_1 : Interval (alignedCheck record042 SharedSix0CellPool.entry) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)

theorem record042_alignment_checked : Interval (alignedCheck record042 SharedSix0CellPool.entry) 0 93 :=
  (interval_append _ 0 64 93 record042_alignment_0 record042_alignment_1)
theorem record042_aligned : ∀ c, Aligned record042 SharedSix0CellPool.entry c :=
  aligned_of_interval record042 SharedSix0CellPool.entry record042_alignment_checked

theorem record042_local_0 : Interval (localCheck record042) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record042_local_1 : Interval (localCheck record042) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)

theorem record042_local_checked : Interval (localCheck record042) 0 93 :=
  (interval_append _ 0 64 93 record042_local_0 record042_local_1)
theorem record042_kind_checked : Interval record042.data.kindTest 0 record042.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record042_ridge_matrix :
    record042.data.candidateMatrix = PackedIncidenceMatrix.code record042.data.ridgeList := by
  decide +kernel

theorem record042_edge_matrix :
    record042.data.edgeMatrix = PackedIncidenceMatrix.code record042.data.edgeLists := by
  decide +kernel

theorem record042_missing_matrix :
    record042.data.missingMatrix = PackedIncidenceMatrix.code record042.data.missingLists := by
  decide +kernel

theorem record042_matrix_checked : MatrixGraphProblem.Checked record042.data :=
  matrix_checked record042 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record042_aligned (by decide +kernel) record042_local_checked
    record042_kind_checked record042_ridge_matrix record042_edge_matrix record042_missing_matrix

theorem record042_validity : GraphGrowthInputs.Valid record042.inputs :=
  valid_of_matrix record042 record042_matrix_checked

theorem record042_vertex_width : record042.vertexRows.width = record042.n := by decide +kernel

theorem record042_vertex_code : record042.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record042 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record042_literal : RawGraphSemanticCertificate.LiteralFacts record042.data :=
  literal_facts record042 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record042_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record042 SharedSix0CellPool.entry record042_vertex_width record042_vertex_code)

theorem record042_cells_exact : ∀ c, record042.data.cells c = FacetUniverses.FullSix0.cells (embedding record042 c) :=
  literal_cells record042 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record042_aligned

#print axioms record042_validity
#print axioms record042_literal

theorem record043_alignment_0 : Interval (alignedCheck record043 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record043_alignment_1 : Interval (alignedCheck record043 SharedSix0CellPool.entry) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)

theorem record043_alignment_checked : Interval (alignedCheck record043 SharedSix0CellPool.entry) 0 87 :=
  (interval_append _ 0 64 87 record043_alignment_0 record043_alignment_1)
theorem record043_aligned : ∀ c, Aligned record043 SharedSix0CellPool.entry c :=
  aligned_of_interval record043 SharedSix0CellPool.entry record043_alignment_checked

theorem record043_local_0 : Interval (localCheck record043) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record043_local_1 : Interval (localCheck record043) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)

theorem record043_local_checked : Interval (localCheck record043) 0 87 :=
  (interval_append _ 0 64 87 record043_local_0 record043_local_1)
theorem record043_kind_checked : Interval record043.data.kindTest 0 record043.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record043_ridge_matrix :
    record043.data.candidateMatrix = PackedIncidenceMatrix.code record043.data.ridgeList := by
  decide +kernel

theorem record043_edge_matrix :
    record043.data.edgeMatrix = PackedIncidenceMatrix.code record043.data.edgeLists := by
  decide +kernel

theorem record043_missing_matrix :
    record043.data.missingMatrix = PackedIncidenceMatrix.code record043.data.missingLists := by
  decide +kernel

theorem record043_matrix_checked : MatrixGraphProblem.Checked record043.data :=
  matrix_checked record043 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record043_aligned (by decide +kernel) record043_local_checked
    record043_kind_checked record043_ridge_matrix record043_edge_matrix record043_missing_matrix

theorem record043_validity : GraphGrowthInputs.Valid record043.inputs :=
  valid_of_matrix record043 record043_matrix_checked

theorem record043_vertex_width : record043.vertexRows.width = record043.n := by decide +kernel

theorem record043_vertex_code : record043.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record043 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record043_literal : RawGraphSemanticCertificate.LiteralFacts record043.data :=
  literal_facts record043 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record043_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record043 SharedSix0CellPool.entry record043_vertex_width record043_vertex_code)

theorem record043_cells_exact : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c) :=
  literal_cells record043 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record043_aligned

#print axioms record043_validity
#print axioms record043_literal

theorem record044_alignment_0 : Interval (alignedCheck record044 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record044_alignment_1 : Interval (alignedCheck record044 SharedSix0CellPool.entry) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)

theorem record044_alignment_checked : Interval (alignedCheck record044 SharedSix0CellPool.entry) 0 87 :=
  (interval_append _ 0 64 87 record044_alignment_0 record044_alignment_1)
theorem record044_aligned : ∀ c, Aligned record044 SharedSix0CellPool.entry c :=
  aligned_of_interval record044 SharedSix0CellPool.entry record044_alignment_checked

theorem record044_local_0 : Interval (localCheck record044) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record044_local_1 : Interval (localCheck record044) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)

theorem record044_local_checked : Interval (localCheck record044) 0 87 :=
  (interval_append _ 0 64 87 record044_local_0 record044_local_1)
theorem record044_kind_checked : Interval record044.data.kindTest 0 record044.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record044_ridge_matrix :
    record044.data.candidateMatrix = PackedIncidenceMatrix.code record044.data.ridgeList := by
  decide +kernel

theorem record044_edge_matrix :
    record044.data.edgeMatrix = PackedIncidenceMatrix.code record044.data.edgeLists := by
  decide +kernel

theorem record044_missing_matrix :
    record044.data.missingMatrix = PackedIncidenceMatrix.code record044.data.missingLists := by
  decide +kernel

theorem record044_matrix_checked : MatrixGraphProblem.Checked record044.data :=
  matrix_checked record044 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record044_aligned (by decide +kernel) record044_local_checked
    record044_kind_checked record044_ridge_matrix record044_edge_matrix record044_missing_matrix

theorem record044_validity : GraphGrowthInputs.Valid record044.inputs :=
  valid_of_matrix record044 record044_matrix_checked

theorem record044_vertex_width : record044.vertexRows.width = record044.n := by decide +kernel

theorem record044_vertex_code : record044.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record044 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record044_literal : RawGraphSemanticCertificate.LiteralFacts record044.data :=
  literal_facts record044 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record044_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record044 SharedSix0CellPool.entry record044_vertex_width record044_vertex_code)

theorem record044_cells_exact : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c) :=
  literal_cells record044 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record044_aligned

#print axioms record044_validity
#print axioms record044_literal

theorem record045_alignment_0 : Interval (alignedCheck record045 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record045_alignment_1 : Interval (alignedCheck record045 SharedSix0CellPool.entry) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)

theorem record045_alignment_checked : Interval (alignedCheck record045 SharedSix0CellPool.entry) 0 90 :=
  (interval_append _ 0 64 90 record045_alignment_0 record045_alignment_1)
theorem record045_aligned : ∀ c, Aligned record045 SharedSix0CellPool.entry c :=
  aligned_of_interval record045 SharedSix0CellPool.entry record045_alignment_checked

theorem record045_local_0 : Interval (localCheck record045) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record045_local_1 : Interval (localCheck record045) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)

theorem record045_local_checked : Interval (localCheck record045) 0 90 :=
  (interval_append _ 0 64 90 record045_local_0 record045_local_1)
theorem record045_kind_checked : Interval record045.data.kindTest 0 record045.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record045_ridge_matrix :
    record045.data.candidateMatrix = PackedIncidenceMatrix.code record045.data.ridgeList := by
  decide +kernel

theorem record045_edge_matrix :
    record045.data.edgeMatrix = PackedIncidenceMatrix.code record045.data.edgeLists := by
  decide +kernel

theorem record045_missing_matrix :
    record045.data.missingMatrix = PackedIncidenceMatrix.code record045.data.missingLists := by
  decide +kernel

theorem record045_matrix_checked : MatrixGraphProblem.Checked record045.data :=
  matrix_checked record045 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record045_aligned (by decide +kernel) record045_local_checked
    record045_kind_checked record045_ridge_matrix record045_edge_matrix record045_missing_matrix

theorem record045_validity : GraphGrowthInputs.Valid record045.inputs :=
  valid_of_matrix record045 record045_matrix_checked

theorem record045_vertex_width : record045.vertexRows.width = record045.n := by decide +kernel

theorem record045_vertex_code : record045.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record045 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record045_literal : RawGraphSemanticCertificate.LiteralFacts record045.data :=
  literal_facts record045 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record045_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record045 SharedSix0CellPool.entry record045_vertex_width record045_vertex_code)

theorem record045_cells_exact : ∀ c, record045.data.cells c = FacetUniverses.FullSix0.cells (embedding record045 c) :=
  literal_cells record045 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record045_aligned

#print axioms record045_validity
#print axioms record045_literal

theorem record046_alignment_0 : Interval (alignedCheck record046 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record046_alignment_1 : Interval (alignedCheck record046 SharedSix0CellPool.entry) 64 77 :=
  interval_of_check _ 64 13 (by decide +kernel)

theorem record046_alignment_checked : Interval (alignedCheck record046 SharedSix0CellPool.entry) 0 77 :=
  (interval_append _ 0 64 77 record046_alignment_0 record046_alignment_1)
theorem record046_aligned : ∀ c, Aligned record046 SharedSix0CellPool.entry c :=
  aligned_of_interval record046 SharedSix0CellPool.entry record046_alignment_checked

theorem record046_local_0 : Interval (localCheck record046) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record046_local_1 : Interval (localCheck record046) 64 77 :=
  interval_of_check _ 64 13 (by decide +kernel)

theorem record046_local_checked : Interval (localCheck record046) 0 77 :=
  (interval_append _ 0 64 77 record046_local_0 record046_local_1)
theorem record046_kind_checked : Interval record046.data.kindTest 0 record046.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record046_ridge_matrix :
    record046.data.candidateMatrix = PackedIncidenceMatrix.code record046.data.ridgeList := by
  decide +kernel

theorem record046_edge_matrix :
    record046.data.edgeMatrix = PackedIncidenceMatrix.code record046.data.edgeLists := by
  decide +kernel

theorem record046_missing_matrix :
    record046.data.missingMatrix = PackedIncidenceMatrix.code record046.data.missingLists := by
  decide +kernel

theorem record046_matrix_checked : MatrixGraphProblem.Checked record046.data :=
  matrix_checked record046 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record046_aligned (by decide +kernel) record046_local_checked
    record046_kind_checked record046_ridge_matrix record046_edge_matrix record046_missing_matrix

theorem record046_validity : GraphGrowthInputs.Valid record046.inputs :=
  valid_of_matrix record046 record046_matrix_checked

theorem record046_vertex_width : record046.vertexRows.width = record046.n := by decide +kernel

theorem record046_vertex_code : record046.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record046 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record046_literal : RawGraphSemanticCertificate.LiteralFacts record046.data :=
  literal_facts record046 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record046_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record046 SharedSix0CellPool.entry record046_vertex_width record046_vertex_code)

theorem record046_cells_exact : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c) :=
  literal_cells record046 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record046_aligned

#print axioms record046_validity
#print axioms record046_literal

theorem record047_alignment_0 : Interval (alignedCheck record047 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record047_alignment_1 : Interval (alignedCheck record047 SharedSix0CellPool.entry) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)

theorem record047_alignment_checked : Interval (alignedCheck record047 SharedSix0CellPool.entry) 0 96 :=
  (interval_append _ 0 64 96 record047_alignment_0 record047_alignment_1)
theorem record047_aligned : ∀ c, Aligned record047 SharedSix0CellPool.entry c :=
  aligned_of_interval record047 SharedSix0CellPool.entry record047_alignment_checked

theorem record047_local_0 : Interval (localCheck record047) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record047_local_1 : Interval (localCheck record047) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)

theorem record047_local_checked : Interval (localCheck record047) 0 96 :=
  (interval_append _ 0 64 96 record047_local_0 record047_local_1)
theorem record047_kind_checked : Interval record047.data.kindTest 0 record047.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record047_ridge_matrix :
    record047.data.candidateMatrix = PackedIncidenceMatrix.code record047.data.ridgeList := by
  decide +kernel

theorem record047_edge_matrix :
    record047.data.edgeMatrix = PackedIncidenceMatrix.code record047.data.edgeLists := by
  decide +kernel

theorem record047_missing_matrix :
    record047.data.missingMatrix = PackedIncidenceMatrix.code record047.data.missingLists := by
  decide +kernel

theorem record047_matrix_checked : MatrixGraphProblem.Checked record047.data :=
  matrix_checked record047 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record047_aligned (by decide +kernel) record047_local_checked
    record047_kind_checked record047_ridge_matrix record047_edge_matrix record047_missing_matrix

theorem record047_validity : GraphGrowthInputs.Valid record047.inputs :=
  valid_of_matrix record047 record047_matrix_checked

theorem record047_vertex_width : record047.vertexRows.width = record047.n := by decide +kernel

theorem record047_vertex_code : record047.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record047 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record047_literal : RawGraphSemanticCertificate.LiteralFacts record047.data :=
  literal_facts record047 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record047_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record047 SharedSix0CellPool.entry record047_vertex_width record047_vertex_code)

theorem record047_cells_exact : ∀ c, record047.data.cells c = FacetUniverses.FullSix0.cells (embedding record047 c) :=
  literal_cells record047 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record047_aligned

#print axioms record047_validity
#print axioms record047_literal

theorem record048_alignment_0 : Interval (alignedCheck record048 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record048_alignment_1 : Interval (alignedCheck record048 SharedSix0CellPool.entry) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)

theorem record048_alignment_checked : Interval (alignedCheck record048 SharedSix0CellPool.entry) 0 94 :=
  (interval_append _ 0 64 94 record048_alignment_0 record048_alignment_1)
theorem record048_aligned : ∀ c, Aligned record048 SharedSix0CellPool.entry c :=
  aligned_of_interval record048 SharedSix0CellPool.entry record048_alignment_checked

theorem record048_local_0 : Interval (localCheck record048) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record048_local_1 : Interval (localCheck record048) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)

theorem record048_local_checked : Interval (localCheck record048) 0 94 :=
  (interval_append _ 0 64 94 record048_local_0 record048_local_1)
theorem record048_kind_checked : Interval record048.data.kindTest 0 record048.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record048_ridge_matrix :
    record048.data.candidateMatrix = PackedIncidenceMatrix.code record048.data.ridgeList := by
  decide +kernel

theorem record048_edge_matrix :
    record048.data.edgeMatrix = PackedIncidenceMatrix.code record048.data.edgeLists := by
  decide +kernel

theorem record048_missing_matrix :
    record048.data.missingMatrix = PackedIncidenceMatrix.code record048.data.missingLists := by
  decide +kernel

theorem record048_matrix_checked : MatrixGraphProblem.Checked record048.data :=
  matrix_checked record048 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record048_aligned (by decide +kernel) record048_local_checked
    record048_kind_checked record048_ridge_matrix record048_edge_matrix record048_missing_matrix

theorem record048_validity : GraphGrowthInputs.Valid record048.inputs :=
  valid_of_matrix record048 record048_matrix_checked

theorem record048_vertex_width : record048.vertexRows.width = record048.n := by decide +kernel

theorem record048_vertex_code : record048.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record048 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record048_literal : RawGraphSemanticCertificate.LiteralFacts record048.data :=
  literal_facts record048 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record048_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record048 SharedSix0CellPool.entry record048_vertex_width record048_vertex_code)

theorem record048_cells_exact : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c) :=
  literal_cells record048 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record048_aligned

#print axioms record048_validity
#print axioms record048_literal

theorem record049_alignment_0 : Interval (alignedCheck record049 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record049_alignment_1 : Interval (alignedCheck record049 SharedSix0CellPool.entry) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)

theorem record049_alignment_checked : Interval (alignedCheck record049 SharedSix0CellPool.entry) 0 102 :=
  (interval_append _ 0 64 102 record049_alignment_0 record049_alignment_1)
theorem record049_aligned : ∀ c, Aligned record049 SharedSix0CellPool.entry c :=
  aligned_of_interval record049 SharedSix0CellPool.entry record049_alignment_checked

theorem record049_local_0 : Interval (localCheck record049) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record049_local_1 : Interval (localCheck record049) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)

theorem record049_local_checked : Interval (localCheck record049) 0 102 :=
  (interval_append _ 0 64 102 record049_local_0 record049_local_1)
theorem record049_kind_checked : Interval record049.data.kindTest 0 record049.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record049_ridge_matrix :
    record049.data.candidateMatrix = PackedIncidenceMatrix.code record049.data.ridgeList := by
  decide +kernel

theorem record049_edge_matrix :
    record049.data.edgeMatrix = PackedIncidenceMatrix.code record049.data.edgeLists := by
  decide +kernel

theorem record049_missing_matrix :
    record049.data.missingMatrix = PackedIncidenceMatrix.code record049.data.missingLists := by
  decide +kernel

theorem record049_matrix_checked : MatrixGraphProblem.Checked record049.data :=
  matrix_checked record049 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record049_aligned (by decide +kernel) record049_local_checked
    record049_kind_checked record049_ridge_matrix record049_edge_matrix record049_missing_matrix

theorem record049_validity : GraphGrowthInputs.Valid record049.inputs :=
  valid_of_matrix record049 record049_matrix_checked

theorem record049_vertex_width : record049.vertexRows.width = record049.n := by decide +kernel

theorem record049_vertex_code : record049.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record049 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record049_literal : RawGraphSemanticCertificate.LiteralFacts record049.data :=
  literal_facts record049 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record049_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record049 SharedSix0CellPool.entry record049_vertex_width record049_vertex_code)

theorem record049_cells_exact : ∀ c, record049.data.cells c = FacetUniverses.FullSix0.cells (embedding record049 c) :=
  literal_cells record049 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record049_aligned

#print axioms record049_validity
#print axioms record049_literal

theorem record050_alignment_0 : Interval (alignedCheck record050 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record050_alignment_1 : Interval (alignedCheck record050 SharedSix0CellPool.entry) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)

theorem record050_alignment_checked : Interval (alignedCheck record050 SharedSix0CellPool.entry) 0 106 :=
  (interval_append _ 0 64 106 record050_alignment_0 record050_alignment_1)
theorem record050_aligned : ∀ c, Aligned record050 SharedSix0CellPool.entry c :=
  aligned_of_interval record050 SharedSix0CellPool.entry record050_alignment_checked

theorem record050_local_0 : Interval (localCheck record050) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record050_local_1 : Interval (localCheck record050) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)

theorem record050_local_checked : Interval (localCheck record050) 0 106 :=
  (interval_append _ 0 64 106 record050_local_0 record050_local_1)
theorem record050_kind_checked : Interval record050.data.kindTest 0 record050.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record050_ridge_matrix :
    record050.data.candidateMatrix = PackedIncidenceMatrix.code record050.data.ridgeList := by
  decide +kernel

theorem record050_edge_matrix :
    record050.data.edgeMatrix = PackedIncidenceMatrix.code record050.data.edgeLists := by
  decide +kernel

theorem record050_missing_matrix :
    record050.data.missingMatrix = PackedIncidenceMatrix.code record050.data.missingLists := by
  decide +kernel

theorem record050_matrix_checked : MatrixGraphProblem.Checked record050.data :=
  matrix_checked record050 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record050_aligned (by decide +kernel) record050_local_checked
    record050_kind_checked record050_ridge_matrix record050_edge_matrix record050_missing_matrix

theorem record050_validity : GraphGrowthInputs.Valid record050.inputs :=
  valid_of_matrix record050 record050_matrix_checked

theorem record050_vertex_width : record050.vertexRows.width = record050.n := by decide +kernel

theorem record050_vertex_code : record050.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record050 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record050_literal : RawGraphSemanticCertificate.LiteralFacts record050.data :=
  literal_facts record050 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record050_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record050 SharedSix0CellPool.entry record050_vertex_width record050_vertex_code)

theorem record050_cells_exact : ∀ c, record050.data.cells c = FacetUniverses.FullSix0.cells (embedding record050 c) :=
  literal_cells record050 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record050_aligned

#print axioms record050_validity
#print axioms record050_literal

theorem record051_alignment_0 : Interval (alignedCheck record051 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record051_alignment_1 : Interval (alignedCheck record051 SharedSix0CellPool.entry) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)

theorem record051_alignment_checked : Interval (alignedCheck record051 SharedSix0CellPool.entry) 0 112 :=
  (interval_append _ 0 64 112 record051_alignment_0 record051_alignment_1)
theorem record051_aligned : ∀ c, Aligned record051 SharedSix0CellPool.entry c :=
  aligned_of_interval record051 SharedSix0CellPool.entry record051_alignment_checked

theorem record051_local_0 : Interval (localCheck record051) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record051_local_1 : Interval (localCheck record051) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)

theorem record051_local_checked : Interval (localCheck record051) 0 112 :=
  (interval_append _ 0 64 112 record051_local_0 record051_local_1)
theorem record051_kind_checked : Interval record051.data.kindTest 0 record051.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record051_ridge_matrix :
    record051.data.candidateMatrix = PackedIncidenceMatrix.code record051.data.ridgeList := by
  decide +kernel

theorem record051_edge_matrix :
    record051.data.edgeMatrix = PackedIncidenceMatrix.code record051.data.edgeLists := by
  decide +kernel

theorem record051_missing_matrix :
    record051.data.missingMatrix = PackedIncidenceMatrix.code record051.data.missingLists := by
  decide +kernel

theorem record051_matrix_checked : MatrixGraphProblem.Checked record051.data :=
  matrix_checked record051 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record051_aligned (by decide +kernel) record051_local_checked
    record051_kind_checked record051_ridge_matrix record051_edge_matrix record051_missing_matrix

theorem record051_validity : GraphGrowthInputs.Valid record051.inputs :=
  valid_of_matrix record051 record051_matrix_checked

theorem record051_vertex_width : record051.vertexRows.width = record051.n := by decide +kernel

theorem record051_vertex_code : record051.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record051 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record051_literal : RawGraphSemanticCertificate.LiteralFacts record051.data :=
  literal_facts record051 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record051_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record051 SharedSix0CellPool.entry record051_vertex_width record051_vertex_code)

theorem record051_cells_exact : ∀ c, record051.data.cells c = FacetUniverses.FullSix0.cells (embedding record051 c) :=
  literal_cells record051 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record051_aligned

#print axioms record051_validity
#print axioms record051_literal

theorem record052_alignment_0 : Interval (alignedCheck record052 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record052_alignment_1 : Interval (alignedCheck record052 SharedSix0CellPool.entry) 64 71 :=
  interval_of_check _ 64 7 (by decide +kernel)

theorem record052_alignment_checked : Interval (alignedCheck record052 SharedSix0CellPool.entry) 0 71 :=
  (interval_append _ 0 64 71 record052_alignment_0 record052_alignment_1)
theorem record052_aligned : ∀ c, Aligned record052 SharedSix0CellPool.entry c :=
  aligned_of_interval record052 SharedSix0CellPool.entry record052_alignment_checked

theorem record052_local_0 : Interval (localCheck record052) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record052_local_1 : Interval (localCheck record052) 64 71 :=
  interval_of_check _ 64 7 (by decide +kernel)

theorem record052_local_checked : Interval (localCheck record052) 0 71 :=
  (interval_append _ 0 64 71 record052_local_0 record052_local_1)
theorem record052_kind_checked : Interval record052.data.kindTest 0 record052.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record052_ridge_matrix :
    record052.data.candidateMatrix = PackedIncidenceMatrix.code record052.data.ridgeList := by
  decide +kernel

theorem record052_edge_matrix :
    record052.data.edgeMatrix = PackedIncidenceMatrix.code record052.data.edgeLists := by
  decide +kernel

theorem record052_missing_matrix :
    record052.data.missingMatrix = PackedIncidenceMatrix.code record052.data.missingLists := by
  decide +kernel

theorem record052_matrix_checked : MatrixGraphProblem.Checked record052.data :=
  matrix_checked record052 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record052_aligned (by decide +kernel) record052_local_checked
    record052_kind_checked record052_ridge_matrix record052_edge_matrix record052_missing_matrix

theorem record052_validity : GraphGrowthInputs.Valid record052.inputs :=
  valid_of_matrix record052 record052_matrix_checked

theorem record052_vertex_width : record052.vertexRows.width = record052.n := by decide +kernel

theorem record052_vertex_code : record052.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record052 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record052_literal : RawGraphSemanticCertificate.LiteralFacts record052.data :=
  literal_facts record052 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record052_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record052 SharedSix0CellPool.entry record052_vertex_width record052_vertex_code)

theorem record052_cells_exact : ∀ c, record052.data.cells c = FacetUniverses.FullSix0.cells (embedding record052 c) :=
  literal_cells record052 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record052_aligned

#print axioms record052_validity
#print axioms record052_literal

theorem record053_alignment_0 : Interval (alignedCheck record053 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record053_alignment_1 : Interval (alignedCheck record053 SharedSix0CellPool.entry) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)

theorem record053_alignment_checked : Interval (alignedCheck record053 SharedSix0CellPool.entry) 0 88 :=
  (interval_append _ 0 64 88 record053_alignment_0 record053_alignment_1)
theorem record053_aligned : ∀ c, Aligned record053 SharedSix0CellPool.entry c :=
  aligned_of_interval record053 SharedSix0CellPool.entry record053_alignment_checked

theorem record053_local_0 : Interval (localCheck record053) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record053_local_1 : Interval (localCheck record053) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)

theorem record053_local_checked : Interval (localCheck record053) 0 88 :=
  (interval_append _ 0 64 88 record053_local_0 record053_local_1)
theorem record053_kind_checked : Interval record053.data.kindTest 0 record053.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record053_ridge_matrix :
    record053.data.candidateMatrix = PackedIncidenceMatrix.code record053.data.ridgeList := by
  decide +kernel

theorem record053_edge_matrix :
    record053.data.edgeMatrix = PackedIncidenceMatrix.code record053.data.edgeLists := by
  decide +kernel

theorem record053_missing_matrix :
    record053.data.missingMatrix = PackedIncidenceMatrix.code record053.data.missingLists := by
  decide +kernel

theorem record053_matrix_checked : MatrixGraphProblem.Checked record053.data :=
  matrix_checked record053 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record053_aligned (by decide +kernel) record053_local_checked
    record053_kind_checked record053_ridge_matrix record053_edge_matrix record053_missing_matrix

theorem record053_validity : GraphGrowthInputs.Valid record053.inputs :=
  valid_of_matrix record053 record053_matrix_checked

theorem record053_vertex_width : record053.vertexRows.width = record053.n := by decide +kernel

theorem record053_vertex_code : record053.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record053 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record053_literal : RawGraphSemanticCertificate.LiteralFacts record053.data :=
  literal_facts record053 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record053_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record053 SharedSix0CellPool.entry record053_vertex_width record053_vertex_code)

theorem record053_cells_exact : ∀ c, record053.data.cells c = FacetUniverses.FullSix0.cells (embedding record053 c) :=
  literal_cells record053 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record053_aligned

#print axioms record053_validity
#print axioms record053_literal

theorem record054_alignment_0 : Interval (alignedCheck record054 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record054_alignment_1 : Interval (alignedCheck record054 SharedSix0CellPool.entry) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)

theorem record054_alignment_checked : Interval (alignedCheck record054 SharedSix0CellPool.entry) 0 76 :=
  (interval_append _ 0 64 76 record054_alignment_0 record054_alignment_1)
theorem record054_aligned : ∀ c, Aligned record054 SharedSix0CellPool.entry c :=
  aligned_of_interval record054 SharedSix0CellPool.entry record054_alignment_checked

theorem record054_local_0 : Interval (localCheck record054) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record054_local_1 : Interval (localCheck record054) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)

theorem record054_local_checked : Interval (localCheck record054) 0 76 :=
  (interval_append _ 0 64 76 record054_local_0 record054_local_1)
theorem record054_kind_checked : Interval record054.data.kindTest 0 record054.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record054_ridge_matrix :
    record054.data.candidateMatrix = PackedIncidenceMatrix.code record054.data.ridgeList := by
  decide +kernel

theorem record054_edge_matrix :
    record054.data.edgeMatrix = PackedIncidenceMatrix.code record054.data.edgeLists := by
  decide +kernel

theorem record054_missing_matrix :
    record054.data.missingMatrix = PackedIncidenceMatrix.code record054.data.missingLists := by
  decide +kernel

theorem record054_matrix_checked : MatrixGraphProblem.Checked record054.data :=
  matrix_checked record054 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record054_aligned (by decide +kernel) record054_local_checked
    record054_kind_checked record054_ridge_matrix record054_edge_matrix record054_missing_matrix

theorem record054_validity : GraphGrowthInputs.Valid record054.inputs :=
  valid_of_matrix record054 record054_matrix_checked

theorem record054_vertex_width : record054.vertexRows.width = record054.n := by decide +kernel

theorem record054_vertex_code : record054.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record054 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record054_literal : RawGraphSemanticCertificate.LiteralFacts record054.data :=
  literal_facts record054 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record054_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record054 SharedSix0CellPool.entry record054_vertex_width record054_vertex_code)

theorem record054_cells_exact : ∀ c, record054.data.cells c = FacetUniverses.FullSix0.cells (embedding record054 c) :=
  literal_cells record054 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record054_aligned

#print axioms record054_validity
#print axioms record054_literal

theorem record055_alignment_0 : Interval (alignedCheck record055 SharedSix0CellPool.entry) 0 62 :=
  interval_of_check _ 0 62 (by decide +kernel)

theorem record055_alignment_checked : Interval (alignedCheck record055 SharedSix0CellPool.entry) 0 62 :=
  record055_alignment_0
theorem record055_aligned : ∀ c, Aligned record055 SharedSix0CellPool.entry c :=
  aligned_of_interval record055 SharedSix0CellPool.entry record055_alignment_checked

theorem record055_local_0 : Interval (localCheck record055) 0 62 :=
  interval_of_check _ 0 62 (by decide +kernel)

theorem record055_local_checked : Interval (localCheck record055) 0 62 :=
  record055_local_0
theorem record055_kind_checked : Interval record055.data.kindTest 0 record055.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record055_ridge_matrix :
    record055.data.candidateMatrix = PackedIncidenceMatrix.code record055.data.ridgeList := by
  decide +kernel

theorem record055_edge_matrix :
    record055.data.edgeMatrix = PackedIncidenceMatrix.code record055.data.edgeLists := by
  decide +kernel

theorem record055_missing_matrix :
    record055.data.missingMatrix = PackedIncidenceMatrix.code record055.data.missingLists := by
  decide +kernel

theorem record055_matrix_checked : MatrixGraphProblem.Checked record055.data :=
  matrix_checked record055 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record055_aligned (by decide +kernel) record055_local_checked
    record055_kind_checked record055_ridge_matrix record055_edge_matrix record055_missing_matrix

theorem record055_validity : GraphGrowthInputs.Valid record055.inputs :=
  valid_of_matrix record055 record055_matrix_checked

theorem record055_vertex_width : record055.vertexRows.width = record055.n := by decide +kernel

theorem record055_vertex_code : record055.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record055 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record055_literal : RawGraphSemanticCertificate.LiteralFacts record055.data :=
  literal_facts record055 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record055_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record055 SharedSix0CellPool.entry record055_vertex_width record055_vertex_code)

theorem record055_cells_exact : ∀ c, record055.data.cells c = FacetUniverses.FullSix0.cells (embedding record055 c) :=
  literal_cells record055 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record055_aligned

#print axioms record055_validity
#print axioms record055_literal

theorem record056_alignment_0 : Interval (alignedCheck record056 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record056_alignment_1 : Interval (alignedCheck record056 SharedSix0CellPool.entry) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)

theorem record056_alignment_checked : Interval (alignedCheck record056 SharedSix0CellPool.entry) 0 96 :=
  (interval_append _ 0 64 96 record056_alignment_0 record056_alignment_1)
theorem record056_aligned : ∀ c, Aligned record056 SharedSix0CellPool.entry c :=
  aligned_of_interval record056 SharedSix0CellPool.entry record056_alignment_checked

theorem record056_local_0 : Interval (localCheck record056) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record056_local_1 : Interval (localCheck record056) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)

theorem record056_local_checked : Interval (localCheck record056) 0 96 :=
  (interval_append _ 0 64 96 record056_local_0 record056_local_1)
theorem record056_kind_checked : Interval record056.data.kindTest 0 record056.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record056_ridge_matrix :
    record056.data.candidateMatrix = PackedIncidenceMatrix.code record056.data.ridgeList := by
  decide +kernel

theorem record056_edge_matrix :
    record056.data.edgeMatrix = PackedIncidenceMatrix.code record056.data.edgeLists := by
  decide +kernel

theorem record056_missing_matrix :
    record056.data.missingMatrix = PackedIncidenceMatrix.code record056.data.missingLists := by
  decide +kernel

theorem record056_matrix_checked : MatrixGraphProblem.Checked record056.data :=
  matrix_checked record056 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record056_aligned (by decide +kernel) record056_local_checked
    record056_kind_checked record056_ridge_matrix record056_edge_matrix record056_missing_matrix

theorem record056_validity : GraphGrowthInputs.Valid record056.inputs :=
  valid_of_matrix record056 record056_matrix_checked

theorem record056_vertex_width : record056.vertexRows.width = record056.n := by decide +kernel

theorem record056_vertex_code : record056.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record056 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record056_literal : RawGraphSemanticCertificate.LiteralFacts record056.data :=
  literal_facts record056 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record056_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record056 SharedSix0CellPool.entry record056_vertex_width record056_vertex_code)

theorem record056_cells_exact : ∀ c, record056.data.cells c = FacetUniverses.FullSix0.cells (embedding record056 c) :=
  literal_cells record056 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record056_aligned

#print axioms record056_validity
#print axioms record056_literal

theorem record057_alignment_0 : Interval (alignedCheck record057 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record057_alignment_1 : Interval (alignedCheck record057 SharedSix0CellPool.entry) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)

theorem record057_alignment_checked : Interval (alignedCheck record057 SharedSix0CellPool.entry) 0 87 :=
  (interval_append _ 0 64 87 record057_alignment_0 record057_alignment_1)
theorem record057_aligned : ∀ c, Aligned record057 SharedSix0CellPool.entry c :=
  aligned_of_interval record057 SharedSix0CellPool.entry record057_alignment_checked

theorem record057_local_0 : Interval (localCheck record057) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record057_local_1 : Interval (localCheck record057) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)

theorem record057_local_checked : Interval (localCheck record057) 0 87 :=
  (interval_append _ 0 64 87 record057_local_0 record057_local_1)
theorem record057_kind_checked : Interval record057.data.kindTest 0 record057.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record057_ridge_matrix :
    record057.data.candidateMatrix = PackedIncidenceMatrix.code record057.data.ridgeList := by
  decide +kernel

theorem record057_edge_matrix :
    record057.data.edgeMatrix = PackedIncidenceMatrix.code record057.data.edgeLists := by
  decide +kernel

theorem record057_missing_matrix :
    record057.data.missingMatrix = PackedIncidenceMatrix.code record057.data.missingLists := by
  decide +kernel

theorem record057_matrix_checked : MatrixGraphProblem.Checked record057.data :=
  matrix_checked record057 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record057_aligned (by decide +kernel) record057_local_checked
    record057_kind_checked record057_ridge_matrix record057_edge_matrix record057_missing_matrix

theorem record057_validity : GraphGrowthInputs.Valid record057.inputs :=
  valid_of_matrix record057 record057_matrix_checked

theorem record057_vertex_width : record057.vertexRows.width = record057.n := by decide +kernel

theorem record057_vertex_code : record057.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record057 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record057_literal : RawGraphSemanticCertificate.LiteralFacts record057.data :=
  literal_facts record057 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record057_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record057 SharedSix0CellPool.entry record057_vertex_width record057_vertex_code)

theorem record057_cells_exact : ∀ c, record057.data.cells c = FacetUniverses.FullSix0.cells (embedding record057 c) :=
  literal_cells record057 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record057_aligned

#print axioms record057_validity
#print axioms record057_literal

theorem record058_alignment_0 : Interval (alignedCheck record058 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record058_alignment_1 : Interval (alignedCheck record058 SharedSix0CellPool.entry) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)

theorem record058_alignment_checked : Interval (alignedCheck record058 SharedSix0CellPool.entry) 0 102 :=
  (interval_append _ 0 64 102 record058_alignment_0 record058_alignment_1)
theorem record058_aligned : ∀ c, Aligned record058 SharedSix0CellPool.entry c :=
  aligned_of_interval record058 SharedSix0CellPool.entry record058_alignment_checked

theorem record058_local_0 : Interval (localCheck record058) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record058_local_1 : Interval (localCheck record058) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)

theorem record058_local_checked : Interval (localCheck record058) 0 102 :=
  (interval_append _ 0 64 102 record058_local_0 record058_local_1)
theorem record058_kind_checked : Interval record058.data.kindTest 0 record058.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record058_ridge_matrix :
    record058.data.candidateMatrix = PackedIncidenceMatrix.code record058.data.ridgeList := by
  decide +kernel

theorem record058_edge_matrix :
    record058.data.edgeMatrix = PackedIncidenceMatrix.code record058.data.edgeLists := by
  decide +kernel

theorem record058_missing_matrix :
    record058.data.missingMatrix = PackedIncidenceMatrix.code record058.data.missingLists := by
  decide +kernel

theorem record058_matrix_checked : MatrixGraphProblem.Checked record058.data :=
  matrix_checked record058 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record058_aligned (by decide +kernel) record058_local_checked
    record058_kind_checked record058_ridge_matrix record058_edge_matrix record058_missing_matrix

theorem record058_validity : GraphGrowthInputs.Valid record058.inputs :=
  valid_of_matrix record058 record058_matrix_checked

theorem record058_vertex_width : record058.vertexRows.width = record058.n := by decide +kernel

theorem record058_vertex_code : record058.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record058 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record058_literal : RawGraphSemanticCertificate.LiteralFacts record058.data :=
  literal_facts record058 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record058_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record058 SharedSix0CellPool.entry record058_vertex_width record058_vertex_code)

theorem record058_cells_exact : ∀ c, record058.data.cells c = FacetUniverses.FullSix0.cells (embedding record058 c) :=
  literal_cells record058 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record058_aligned

#print axioms record058_validity
#print axioms record058_literal

theorem record059_alignment_0 : Interval (alignedCheck record059 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record059_alignment_1 : Interval (alignedCheck record059 SharedSix0CellPool.entry) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)

theorem record059_alignment_checked : Interval (alignedCheck record059 SharedSix0CellPool.entry) 0 101 :=
  (interval_append _ 0 64 101 record059_alignment_0 record059_alignment_1)
theorem record059_aligned : ∀ c, Aligned record059 SharedSix0CellPool.entry c :=
  aligned_of_interval record059 SharedSix0CellPool.entry record059_alignment_checked

theorem record059_local_0 : Interval (localCheck record059) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record059_local_1 : Interval (localCheck record059) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)

theorem record059_local_checked : Interval (localCheck record059) 0 101 :=
  (interval_append _ 0 64 101 record059_local_0 record059_local_1)
theorem record059_kind_checked : Interval record059.data.kindTest 0 record059.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record059_ridge_matrix :
    record059.data.candidateMatrix = PackedIncidenceMatrix.code record059.data.ridgeList := by
  decide +kernel

theorem record059_edge_matrix :
    record059.data.edgeMatrix = PackedIncidenceMatrix.code record059.data.edgeLists := by
  decide +kernel

theorem record059_missing_matrix :
    record059.data.missingMatrix = PackedIncidenceMatrix.code record059.data.missingLists := by
  decide +kernel

theorem record059_matrix_checked : MatrixGraphProblem.Checked record059.data :=
  matrix_checked record059 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record059_aligned (by decide +kernel) record059_local_checked
    record059_kind_checked record059_ridge_matrix record059_edge_matrix record059_missing_matrix

theorem record059_validity : GraphGrowthInputs.Valid record059.inputs :=
  valid_of_matrix record059 record059_matrix_checked

theorem record059_vertex_width : record059.vertexRows.width = record059.n := by decide +kernel

theorem record059_vertex_code : record059.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record059 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record059_literal : RawGraphSemanticCertificate.LiteralFacts record059.data :=
  literal_facts record059 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record059_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record059 SharedSix0CellPool.entry record059_vertex_width record059_vertex_code)

theorem record059_cells_exact : ∀ c, record059.data.cells c = FacetUniverses.FullSix0.cells (embedding record059 c) :=
  literal_cells record059 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record059_aligned

#print axioms record059_validity
#print axioms record059_literal

theorem record060_alignment_0 : Interval (alignedCheck record060 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record060_alignment_1 : Interval (alignedCheck record060 SharedSix0CellPool.entry) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)

theorem record060_alignment_checked : Interval (alignedCheck record060 SharedSix0CellPool.entry) 0 109 :=
  (interval_append _ 0 64 109 record060_alignment_0 record060_alignment_1)
theorem record060_aligned : ∀ c, Aligned record060 SharedSix0CellPool.entry c :=
  aligned_of_interval record060 SharedSix0CellPool.entry record060_alignment_checked

theorem record060_local_0 : Interval (localCheck record060) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record060_local_1 : Interval (localCheck record060) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)

theorem record060_local_checked : Interval (localCheck record060) 0 109 :=
  (interval_append _ 0 64 109 record060_local_0 record060_local_1)
theorem record060_kind_checked : Interval record060.data.kindTest 0 record060.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record060_ridge_matrix :
    record060.data.candidateMatrix = PackedIncidenceMatrix.code record060.data.ridgeList := by
  decide +kernel

theorem record060_edge_matrix :
    record060.data.edgeMatrix = PackedIncidenceMatrix.code record060.data.edgeLists := by
  decide +kernel

theorem record060_missing_matrix :
    record060.data.missingMatrix = PackedIncidenceMatrix.code record060.data.missingLists := by
  decide +kernel

theorem record060_matrix_checked : MatrixGraphProblem.Checked record060.data :=
  matrix_checked record060 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record060_aligned (by decide +kernel) record060_local_checked
    record060_kind_checked record060_ridge_matrix record060_edge_matrix record060_missing_matrix

theorem record060_validity : GraphGrowthInputs.Valid record060.inputs :=
  valid_of_matrix record060 record060_matrix_checked

theorem record060_vertex_width : record060.vertexRows.width = record060.n := by decide +kernel

theorem record060_vertex_code : record060.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record060 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record060_literal : RawGraphSemanticCertificate.LiteralFacts record060.data :=
  literal_facts record060 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record060_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record060 SharedSix0CellPool.entry record060_vertex_width record060_vertex_code)

theorem record060_cells_exact : ∀ c, record060.data.cells c = FacetUniverses.FullSix0.cells (embedding record060 c) :=
  literal_cells record060 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record060_aligned

#print axioms record060_validity
#print axioms record060_literal

theorem record061_alignment_0 : Interval (alignedCheck record061 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record061_alignment_1 : Interval (alignedCheck record061 SharedSix0CellPool.entry) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)

theorem record061_alignment_checked : Interval (alignedCheck record061 SharedSix0CellPool.entry) 0 108 :=
  (interval_append _ 0 64 108 record061_alignment_0 record061_alignment_1)
theorem record061_aligned : ∀ c, Aligned record061 SharedSix0CellPool.entry c :=
  aligned_of_interval record061 SharedSix0CellPool.entry record061_alignment_checked

theorem record061_local_0 : Interval (localCheck record061) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record061_local_1 : Interval (localCheck record061) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)

theorem record061_local_checked : Interval (localCheck record061) 0 108 :=
  (interval_append _ 0 64 108 record061_local_0 record061_local_1)
theorem record061_kind_checked : Interval record061.data.kindTest 0 record061.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record061_ridge_matrix :
    record061.data.candidateMatrix = PackedIncidenceMatrix.code record061.data.ridgeList := by
  decide +kernel

theorem record061_edge_matrix :
    record061.data.edgeMatrix = PackedIncidenceMatrix.code record061.data.edgeLists := by
  decide +kernel

theorem record061_missing_matrix :
    record061.data.missingMatrix = PackedIncidenceMatrix.code record061.data.missingLists := by
  decide +kernel

theorem record061_matrix_checked : MatrixGraphProblem.Checked record061.data :=
  matrix_checked record061 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record061_aligned (by decide +kernel) record061_local_checked
    record061_kind_checked record061_ridge_matrix record061_edge_matrix record061_missing_matrix

theorem record061_validity : GraphGrowthInputs.Valid record061.inputs :=
  valid_of_matrix record061 record061_matrix_checked

theorem record061_vertex_width : record061.vertexRows.width = record061.n := by decide +kernel

theorem record061_vertex_code : record061.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record061 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record061_literal : RawGraphSemanticCertificate.LiteralFacts record061.data :=
  literal_facts record061 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record061_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record061 SharedSix0CellPool.entry record061_vertex_width record061_vertex_code)

theorem record061_cells_exact : ∀ c, record061.data.cells c = FacetUniverses.FullSix0.cells (embedding record061 c) :=
  literal_cells record061 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record061_aligned

#print axioms record061_validity
#print axioms record061_literal

theorem record062_alignment_0 : Interval (alignedCheck record062 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record062_alignment_1 : Interval (alignedCheck record062 SharedSix0CellPool.entry) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)

theorem record062_alignment_checked : Interval (alignedCheck record062 SharedSix0CellPool.entry) 0 119 :=
  (interval_append _ 0 64 119 record062_alignment_0 record062_alignment_1)
theorem record062_aligned : ∀ c, Aligned record062 SharedSix0CellPool.entry c :=
  aligned_of_interval record062 SharedSix0CellPool.entry record062_alignment_checked

theorem record062_local_0 : Interval (localCheck record062) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record062_local_1 : Interval (localCheck record062) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)

theorem record062_local_checked : Interval (localCheck record062) 0 119 :=
  (interval_append _ 0 64 119 record062_local_0 record062_local_1)
theorem record062_kind_checked : Interval record062.data.kindTest 0 record062.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record062_ridge_matrix :
    record062.data.candidateMatrix = PackedIncidenceMatrix.code record062.data.ridgeList := by
  decide +kernel

theorem record062_edge_matrix :
    record062.data.edgeMatrix = PackedIncidenceMatrix.code record062.data.edgeLists := by
  decide +kernel

theorem record062_missing_matrix :
    record062.data.missingMatrix = PackedIncidenceMatrix.code record062.data.missingLists := by
  decide +kernel

theorem record062_matrix_checked : MatrixGraphProblem.Checked record062.data :=
  matrix_checked record062 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record062_aligned (by decide +kernel) record062_local_checked
    record062_kind_checked record062_ridge_matrix record062_edge_matrix record062_missing_matrix

theorem record062_validity : GraphGrowthInputs.Valid record062.inputs :=
  valid_of_matrix record062 record062_matrix_checked

theorem record062_vertex_width : record062.vertexRows.width = record062.n := by decide +kernel

theorem record062_vertex_code : record062.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record062 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record062_literal : RawGraphSemanticCertificate.LiteralFacts record062.data :=
  literal_facts record062 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record062_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record062 SharedSix0CellPool.entry record062_vertex_width record062_vertex_code)

theorem record062_cells_exact : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c) :=
  literal_cells record062 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record062_aligned

#print axioms record062_validity
#print axioms record062_literal

theorem record063_alignment_0 : Interval (alignedCheck record063 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record063_alignment_1 : Interval (alignedCheck record063 SharedSix0CellPool.entry) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)

theorem record063_alignment_checked : Interval (alignedCheck record063 SharedSix0CellPool.entry) 0 114 :=
  (interval_append _ 0 64 114 record063_alignment_0 record063_alignment_1)
theorem record063_aligned : ∀ c, Aligned record063 SharedSix0CellPool.entry c :=
  aligned_of_interval record063 SharedSix0CellPool.entry record063_alignment_checked

theorem record063_local_0 : Interval (localCheck record063) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record063_local_1 : Interval (localCheck record063) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)

theorem record063_local_checked : Interval (localCheck record063) 0 114 :=
  (interval_append _ 0 64 114 record063_local_0 record063_local_1)
theorem record063_kind_checked : Interval record063.data.kindTest 0 record063.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record063_ridge_matrix :
    record063.data.candidateMatrix = PackedIncidenceMatrix.code record063.data.ridgeList := by
  decide +kernel

theorem record063_edge_matrix :
    record063.data.edgeMatrix = PackedIncidenceMatrix.code record063.data.edgeLists := by
  decide +kernel

theorem record063_missing_matrix :
    record063.data.missingMatrix = PackedIncidenceMatrix.code record063.data.missingLists := by
  decide +kernel

theorem record063_matrix_checked : MatrixGraphProblem.Checked record063.data :=
  matrix_checked record063 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record063_aligned (by decide +kernel) record063_local_checked
    record063_kind_checked record063_ridge_matrix record063_edge_matrix record063_missing_matrix

theorem record063_validity : GraphGrowthInputs.Valid record063.inputs :=
  valid_of_matrix record063 record063_matrix_checked

theorem record063_vertex_width : record063.vertexRows.width = record063.n := by decide +kernel

theorem record063_vertex_code : record063.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record063 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record063_literal : RawGraphSemanticCertificate.LiteralFacts record063.data :=
  literal_facts record063 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record063_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record063 SharedSix0CellPool.entry record063_vertex_width record063_vertex_code)

theorem record063_cells_exact : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c) :=
  literal_cells record063 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record063_aligned

#print axioms record063_validity
#print axioms record063_literal

theorem record064_alignment_0 : Interval (alignedCheck record064 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record064_alignment_1 : Interval (alignedCheck record064 SharedSix0CellPool.entry) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)

theorem record064_alignment_checked : Interval (alignedCheck record064 SharedSix0CellPool.entry) 0 90 :=
  (interval_append _ 0 64 90 record064_alignment_0 record064_alignment_1)
theorem record064_aligned : ∀ c, Aligned record064 SharedSix0CellPool.entry c :=
  aligned_of_interval record064 SharedSix0CellPool.entry record064_alignment_checked

theorem record064_local_0 : Interval (localCheck record064) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record064_local_1 : Interval (localCheck record064) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)

theorem record064_local_checked : Interval (localCheck record064) 0 90 :=
  (interval_append _ 0 64 90 record064_local_0 record064_local_1)
theorem record064_kind_checked : Interval record064.data.kindTest 0 record064.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record064_ridge_matrix :
    record064.data.candidateMatrix = PackedIncidenceMatrix.code record064.data.ridgeList := by
  decide +kernel

theorem record064_edge_matrix :
    record064.data.edgeMatrix = PackedIncidenceMatrix.code record064.data.edgeLists := by
  decide +kernel

theorem record064_missing_matrix :
    record064.data.missingMatrix = PackedIncidenceMatrix.code record064.data.missingLists := by
  decide +kernel

theorem record064_matrix_checked : MatrixGraphProblem.Checked record064.data :=
  matrix_checked record064 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record064_aligned (by decide +kernel) record064_local_checked
    record064_kind_checked record064_ridge_matrix record064_edge_matrix record064_missing_matrix

theorem record064_validity : GraphGrowthInputs.Valid record064.inputs :=
  valid_of_matrix record064 record064_matrix_checked

theorem record064_vertex_width : record064.vertexRows.width = record064.n := by decide +kernel

theorem record064_vertex_code : record064.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record064 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record064_literal : RawGraphSemanticCertificate.LiteralFacts record064.data :=
  literal_facts record064 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record064_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record064 SharedSix0CellPool.entry record064_vertex_width record064_vertex_code)

theorem record064_cells_exact : ∀ c, record064.data.cells c = FacetUniverses.FullSix0.cells (embedding record064 c) :=
  literal_cells record064 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record064_aligned

#print axioms record064_validity
#print axioms record064_literal

theorem record065_alignment_0 : Interval (alignedCheck record065 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record065_alignment_1 : Interval (alignedCheck record065 SharedSix0CellPool.entry) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)

theorem record065_alignment_checked : Interval (alignedCheck record065 SharedSix0CellPool.entry) 0 86 :=
  (interval_append _ 0 64 86 record065_alignment_0 record065_alignment_1)
theorem record065_aligned : ∀ c, Aligned record065 SharedSix0CellPool.entry c :=
  aligned_of_interval record065 SharedSix0CellPool.entry record065_alignment_checked

theorem record065_local_0 : Interval (localCheck record065) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record065_local_1 : Interval (localCheck record065) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)

theorem record065_local_checked : Interval (localCheck record065) 0 86 :=
  (interval_append _ 0 64 86 record065_local_0 record065_local_1)
theorem record065_kind_checked : Interval record065.data.kindTest 0 record065.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record065_ridge_matrix :
    record065.data.candidateMatrix = PackedIncidenceMatrix.code record065.data.ridgeList := by
  decide +kernel

theorem record065_edge_matrix :
    record065.data.edgeMatrix = PackedIncidenceMatrix.code record065.data.edgeLists := by
  decide +kernel

theorem record065_missing_matrix :
    record065.data.missingMatrix = PackedIncidenceMatrix.code record065.data.missingLists := by
  decide +kernel

theorem record065_matrix_checked : MatrixGraphProblem.Checked record065.data :=
  matrix_checked record065 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record065_aligned (by decide +kernel) record065_local_checked
    record065_kind_checked record065_ridge_matrix record065_edge_matrix record065_missing_matrix

theorem record065_validity : GraphGrowthInputs.Valid record065.inputs :=
  valid_of_matrix record065 record065_matrix_checked

theorem record065_vertex_width : record065.vertexRows.width = record065.n := by decide +kernel

theorem record065_vertex_code : record065.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record065 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record065_literal : RawGraphSemanticCertificate.LiteralFacts record065.data :=
  literal_facts record065 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record065_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record065 SharedSix0CellPool.entry record065_vertex_width record065_vertex_code)

theorem record065_cells_exact : ∀ c, record065.data.cells c = FacetUniverses.FullSix0.cells (embedding record065 c) :=
  literal_cells record065 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record065_aligned

#print axioms record065_validity
#print axioms record065_literal

theorem record066_alignment_0 : Interval (alignedCheck record066 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record066_alignment_1 : Interval (alignedCheck record066 SharedSix0CellPool.entry) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)

theorem record066_alignment_checked : Interval (alignedCheck record066 SharedSix0CellPool.entry) 0 87 :=
  (interval_append _ 0 64 87 record066_alignment_0 record066_alignment_1)
theorem record066_aligned : ∀ c, Aligned record066 SharedSix0CellPool.entry c :=
  aligned_of_interval record066 SharedSix0CellPool.entry record066_alignment_checked

theorem record066_local_0 : Interval (localCheck record066) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record066_local_1 : Interval (localCheck record066) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)

theorem record066_local_checked : Interval (localCheck record066) 0 87 :=
  (interval_append _ 0 64 87 record066_local_0 record066_local_1)
theorem record066_kind_checked : Interval record066.data.kindTest 0 record066.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record066_ridge_matrix :
    record066.data.candidateMatrix = PackedIncidenceMatrix.code record066.data.ridgeList := by
  decide +kernel

theorem record066_edge_matrix :
    record066.data.edgeMatrix = PackedIncidenceMatrix.code record066.data.edgeLists := by
  decide +kernel

theorem record066_missing_matrix :
    record066.data.missingMatrix = PackedIncidenceMatrix.code record066.data.missingLists := by
  decide +kernel

theorem record066_matrix_checked : MatrixGraphProblem.Checked record066.data :=
  matrix_checked record066 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record066_aligned (by decide +kernel) record066_local_checked
    record066_kind_checked record066_ridge_matrix record066_edge_matrix record066_missing_matrix

theorem record066_validity : GraphGrowthInputs.Valid record066.inputs :=
  valid_of_matrix record066 record066_matrix_checked

theorem record066_vertex_width : record066.vertexRows.width = record066.n := by decide +kernel

theorem record066_vertex_code : record066.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record066 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record066_literal : RawGraphSemanticCertificate.LiteralFacts record066.data :=
  literal_facts record066 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record066_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record066 SharedSix0CellPool.entry record066_vertex_width record066_vertex_code)

theorem record066_cells_exact : ∀ c, record066.data.cells c = FacetUniverses.FullSix0.cells (embedding record066 c) :=
  literal_cells record066 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record066_aligned

#print axioms record066_validity
#print axioms record066_literal

theorem record067_alignment_0 : Interval (alignedCheck record067 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record067_alignment_1 : Interval (alignedCheck record067 SharedSix0CellPool.entry) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)

theorem record067_alignment_checked : Interval (alignedCheck record067 SharedSix0CellPool.entry) 0 87 :=
  (interval_append _ 0 64 87 record067_alignment_0 record067_alignment_1)
theorem record067_aligned : ∀ c, Aligned record067 SharedSix0CellPool.entry c :=
  aligned_of_interval record067 SharedSix0CellPool.entry record067_alignment_checked

theorem record067_local_0 : Interval (localCheck record067) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record067_local_1 : Interval (localCheck record067) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)

theorem record067_local_checked : Interval (localCheck record067) 0 87 :=
  (interval_append _ 0 64 87 record067_local_0 record067_local_1)
theorem record067_kind_checked : Interval record067.data.kindTest 0 record067.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record067_ridge_matrix :
    record067.data.candidateMatrix = PackedIncidenceMatrix.code record067.data.ridgeList := by
  decide +kernel

theorem record067_edge_matrix :
    record067.data.edgeMatrix = PackedIncidenceMatrix.code record067.data.edgeLists := by
  decide +kernel

theorem record067_missing_matrix :
    record067.data.missingMatrix = PackedIncidenceMatrix.code record067.data.missingLists := by
  decide +kernel

theorem record067_matrix_checked : MatrixGraphProblem.Checked record067.data :=
  matrix_checked record067 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record067_aligned (by decide +kernel) record067_local_checked
    record067_kind_checked record067_ridge_matrix record067_edge_matrix record067_missing_matrix

theorem record067_validity : GraphGrowthInputs.Valid record067.inputs :=
  valid_of_matrix record067 record067_matrix_checked

theorem record067_vertex_width : record067.vertexRows.width = record067.n := by decide +kernel

theorem record067_vertex_code : record067.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record067 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record067_literal : RawGraphSemanticCertificate.LiteralFacts record067.data :=
  literal_facts record067 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record067_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record067 SharedSix0CellPool.entry record067_vertex_width record067_vertex_code)

theorem record067_cells_exact : ∀ c, record067.data.cells c = FacetUniverses.FullSix0.cells (embedding record067 c) :=
  literal_cells record067 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record067_aligned

#print axioms record067_validity
#print axioms record067_literal

theorem record068_alignment_0 : Interval (alignedCheck record068 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record068_alignment_1 : Interval (alignedCheck record068 SharedSix0CellPool.entry) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)

theorem record068_alignment_checked : Interval (alignedCheck record068 SharedSix0CellPool.entry) 0 89 :=
  (interval_append _ 0 64 89 record068_alignment_0 record068_alignment_1)
theorem record068_aligned : ∀ c, Aligned record068 SharedSix0CellPool.entry c :=
  aligned_of_interval record068 SharedSix0CellPool.entry record068_alignment_checked

theorem record068_local_0 : Interval (localCheck record068) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record068_local_1 : Interval (localCheck record068) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)

theorem record068_local_checked : Interval (localCheck record068) 0 89 :=
  (interval_append _ 0 64 89 record068_local_0 record068_local_1)
theorem record068_kind_checked : Interval record068.data.kindTest 0 record068.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record068_ridge_matrix :
    record068.data.candidateMatrix = PackedIncidenceMatrix.code record068.data.ridgeList := by
  decide +kernel

theorem record068_edge_matrix :
    record068.data.edgeMatrix = PackedIncidenceMatrix.code record068.data.edgeLists := by
  decide +kernel

theorem record068_missing_matrix :
    record068.data.missingMatrix = PackedIncidenceMatrix.code record068.data.missingLists := by
  decide +kernel

theorem record068_matrix_checked : MatrixGraphProblem.Checked record068.data :=
  matrix_checked record068 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record068_aligned (by decide +kernel) record068_local_checked
    record068_kind_checked record068_ridge_matrix record068_edge_matrix record068_missing_matrix

theorem record068_validity : GraphGrowthInputs.Valid record068.inputs :=
  valid_of_matrix record068 record068_matrix_checked

theorem record068_vertex_width : record068.vertexRows.width = record068.n := by decide +kernel

theorem record068_vertex_code : record068.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record068 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record068_literal : RawGraphSemanticCertificate.LiteralFacts record068.data :=
  literal_facts record068 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record068_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record068 SharedSix0CellPool.entry record068_vertex_width record068_vertex_code)

theorem record068_cells_exact : ∀ c, record068.data.cells c = FacetUniverses.FullSix0.cells (embedding record068 c) :=
  literal_cells record068 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record068_aligned

#print axioms record068_validity
#print axioms record068_literal

theorem record069_alignment_0 : Interval (alignedCheck record069 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record069_alignment_1 : Interval (alignedCheck record069 SharedSix0CellPool.entry) 64 71 :=
  interval_of_check _ 64 7 (by decide +kernel)

theorem record069_alignment_checked : Interval (alignedCheck record069 SharedSix0CellPool.entry) 0 71 :=
  (interval_append _ 0 64 71 record069_alignment_0 record069_alignment_1)
theorem record069_aligned : ∀ c, Aligned record069 SharedSix0CellPool.entry c :=
  aligned_of_interval record069 SharedSix0CellPool.entry record069_alignment_checked

theorem record069_local_0 : Interval (localCheck record069) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record069_local_1 : Interval (localCheck record069) 64 71 :=
  interval_of_check _ 64 7 (by decide +kernel)

theorem record069_local_checked : Interval (localCheck record069) 0 71 :=
  (interval_append _ 0 64 71 record069_local_0 record069_local_1)
theorem record069_kind_checked : Interval record069.data.kindTest 0 record069.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record069_ridge_matrix :
    record069.data.candidateMatrix = PackedIncidenceMatrix.code record069.data.ridgeList := by
  decide +kernel

theorem record069_edge_matrix :
    record069.data.edgeMatrix = PackedIncidenceMatrix.code record069.data.edgeLists := by
  decide +kernel

theorem record069_missing_matrix :
    record069.data.missingMatrix = PackedIncidenceMatrix.code record069.data.missingLists := by
  decide +kernel

theorem record069_matrix_checked : MatrixGraphProblem.Checked record069.data :=
  matrix_checked record069 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record069_aligned (by decide +kernel) record069_local_checked
    record069_kind_checked record069_ridge_matrix record069_edge_matrix record069_missing_matrix

theorem record069_validity : GraphGrowthInputs.Valid record069.inputs :=
  valid_of_matrix record069 record069_matrix_checked

theorem record069_vertex_width : record069.vertexRows.width = record069.n := by decide +kernel

theorem record069_vertex_code : record069.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record069 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record069_literal : RawGraphSemanticCertificate.LiteralFacts record069.data :=
  literal_facts record069 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record069_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record069 SharedSix0CellPool.entry record069_vertex_width record069_vertex_code)

theorem record069_cells_exact : ∀ c, record069.data.cells c = FacetUniverses.FullSix0.cells (embedding record069 c) :=
  literal_cells record069 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record069_aligned

#print axioms record069_validity
#print axioms record069_literal

theorem record070_alignment_0 : Interval (alignedCheck record070 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record070_alignment_1 : Interval (alignedCheck record070 SharedSix0CellPool.entry) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)

theorem record070_alignment_checked : Interval (alignedCheck record070 SharedSix0CellPool.entry) 0 91 :=
  (interval_append _ 0 64 91 record070_alignment_0 record070_alignment_1)
theorem record070_aligned : ∀ c, Aligned record070 SharedSix0CellPool.entry c :=
  aligned_of_interval record070 SharedSix0CellPool.entry record070_alignment_checked

theorem record070_local_0 : Interval (localCheck record070) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record070_local_1 : Interval (localCheck record070) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)

theorem record070_local_checked : Interval (localCheck record070) 0 91 :=
  (interval_append _ 0 64 91 record070_local_0 record070_local_1)
theorem record070_kind_checked : Interval record070.data.kindTest 0 record070.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record070_ridge_matrix :
    record070.data.candidateMatrix = PackedIncidenceMatrix.code record070.data.ridgeList := by
  decide +kernel

theorem record070_edge_matrix :
    record070.data.edgeMatrix = PackedIncidenceMatrix.code record070.data.edgeLists := by
  decide +kernel

theorem record070_missing_matrix :
    record070.data.missingMatrix = PackedIncidenceMatrix.code record070.data.missingLists := by
  decide +kernel

theorem record070_matrix_checked : MatrixGraphProblem.Checked record070.data :=
  matrix_checked record070 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record070_aligned (by decide +kernel) record070_local_checked
    record070_kind_checked record070_ridge_matrix record070_edge_matrix record070_missing_matrix

theorem record070_validity : GraphGrowthInputs.Valid record070.inputs :=
  valid_of_matrix record070 record070_matrix_checked

theorem record070_vertex_width : record070.vertexRows.width = record070.n := by decide +kernel

theorem record070_vertex_code : record070.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record070 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record070_literal : RawGraphSemanticCertificate.LiteralFacts record070.data :=
  literal_facts record070 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record070_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record070 SharedSix0CellPool.entry record070_vertex_width record070_vertex_code)

theorem record070_cells_exact : ∀ c, record070.data.cells c = FacetUniverses.FullSix0.cells (embedding record070 c) :=
  literal_cells record070 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record070_aligned

#print axioms record070_validity
#print axioms record070_literal

theorem record071_alignment_0 : Interval (alignedCheck record071 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record071_alignment_1 : Interval (alignedCheck record071 SharedSix0CellPool.entry) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)

theorem record071_alignment_checked : Interval (alignedCheck record071 SharedSix0CellPool.entry) 0 90 :=
  (interval_append _ 0 64 90 record071_alignment_0 record071_alignment_1)
theorem record071_aligned : ∀ c, Aligned record071 SharedSix0CellPool.entry c :=
  aligned_of_interval record071 SharedSix0CellPool.entry record071_alignment_checked

theorem record071_local_0 : Interval (localCheck record071) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record071_local_1 : Interval (localCheck record071) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)

theorem record071_local_checked : Interval (localCheck record071) 0 90 :=
  (interval_append _ 0 64 90 record071_local_0 record071_local_1)
theorem record071_kind_checked : Interval record071.data.kindTest 0 record071.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record071_ridge_matrix :
    record071.data.candidateMatrix = PackedIncidenceMatrix.code record071.data.ridgeList := by
  decide +kernel

theorem record071_edge_matrix :
    record071.data.edgeMatrix = PackedIncidenceMatrix.code record071.data.edgeLists := by
  decide +kernel

theorem record071_missing_matrix :
    record071.data.missingMatrix = PackedIncidenceMatrix.code record071.data.missingLists := by
  decide +kernel

theorem record071_matrix_checked : MatrixGraphProblem.Checked record071.data :=
  matrix_checked record071 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record071_aligned (by decide +kernel) record071_local_checked
    record071_kind_checked record071_ridge_matrix record071_edge_matrix record071_missing_matrix

theorem record071_validity : GraphGrowthInputs.Valid record071.inputs :=
  valid_of_matrix record071 record071_matrix_checked

theorem record071_vertex_width : record071.vertexRows.width = record071.n := by decide +kernel

theorem record071_vertex_code : record071.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record071 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record071_literal : RawGraphSemanticCertificate.LiteralFacts record071.data :=
  literal_facts record071 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record071_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record071 SharedSix0CellPool.entry record071_vertex_width record071_vertex_code)

theorem record071_cells_exact : ∀ c, record071.data.cells c = FacetUniverses.FullSix0.cells (embedding record071 c) :=
  literal_cells record071 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record071_aligned

#print axioms record071_validity
#print axioms record071_literal

theorem record072_alignment_0 : Interval (alignedCheck record072 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record072_alignment_1 : Interval (alignedCheck record072 SharedSix0CellPool.entry) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)

theorem record072_alignment_checked : Interval (alignedCheck record072 SharedSix0CellPool.entry) 0 92 :=
  (interval_append _ 0 64 92 record072_alignment_0 record072_alignment_1)
theorem record072_aligned : ∀ c, Aligned record072 SharedSix0CellPool.entry c :=
  aligned_of_interval record072 SharedSix0CellPool.entry record072_alignment_checked

theorem record072_local_0 : Interval (localCheck record072) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record072_local_1 : Interval (localCheck record072) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)

theorem record072_local_checked : Interval (localCheck record072) 0 92 :=
  (interval_append _ 0 64 92 record072_local_0 record072_local_1)
theorem record072_kind_checked : Interval record072.data.kindTest 0 record072.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record072_ridge_matrix :
    record072.data.candidateMatrix = PackedIncidenceMatrix.code record072.data.ridgeList := by
  decide +kernel

theorem record072_edge_matrix :
    record072.data.edgeMatrix = PackedIncidenceMatrix.code record072.data.edgeLists := by
  decide +kernel

theorem record072_missing_matrix :
    record072.data.missingMatrix = PackedIncidenceMatrix.code record072.data.missingLists := by
  decide +kernel

theorem record072_matrix_checked : MatrixGraphProblem.Checked record072.data :=
  matrix_checked record072 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record072_aligned (by decide +kernel) record072_local_checked
    record072_kind_checked record072_ridge_matrix record072_edge_matrix record072_missing_matrix

theorem record072_validity : GraphGrowthInputs.Valid record072.inputs :=
  valid_of_matrix record072 record072_matrix_checked

theorem record072_vertex_width : record072.vertexRows.width = record072.n := by decide +kernel

theorem record072_vertex_code : record072.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record072 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record072_literal : RawGraphSemanticCertificate.LiteralFacts record072.data :=
  literal_facts record072 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record072_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record072 SharedSix0CellPool.entry record072_vertex_width record072_vertex_code)

theorem record072_cells_exact : ∀ c, record072.data.cells c = FacetUniverses.FullSix0.cells (embedding record072 c) :=
  literal_cells record072 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record072_aligned

#print axioms record072_validity
#print axioms record072_literal

theorem record073_alignment_0 : Interval (alignedCheck record073 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record073_alignment_1 : Interval (alignedCheck record073 SharedSix0CellPool.entry) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)

theorem record073_alignment_checked : Interval (alignedCheck record073 SharedSix0CellPool.entry) 0 95 :=
  (interval_append _ 0 64 95 record073_alignment_0 record073_alignment_1)
theorem record073_aligned : ∀ c, Aligned record073 SharedSix0CellPool.entry c :=
  aligned_of_interval record073 SharedSix0CellPool.entry record073_alignment_checked

theorem record073_local_0 : Interval (localCheck record073) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record073_local_1 : Interval (localCheck record073) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)

theorem record073_local_checked : Interval (localCheck record073) 0 95 :=
  (interval_append _ 0 64 95 record073_local_0 record073_local_1)
theorem record073_kind_checked : Interval record073.data.kindTest 0 record073.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record073_ridge_matrix :
    record073.data.candidateMatrix = PackedIncidenceMatrix.code record073.data.ridgeList := by
  decide +kernel

theorem record073_edge_matrix :
    record073.data.edgeMatrix = PackedIncidenceMatrix.code record073.data.edgeLists := by
  decide +kernel

theorem record073_missing_matrix :
    record073.data.missingMatrix = PackedIncidenceMatrix.code record073.data.missingLists := by
  decide +kernel

theorem record073_matrix_checked : MatrixGraphProblem.Checked record073.data :=
  matrix_checked record073 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record073_aligned (by decide +kernel) record073_local_checked
    record073_kind_checked record073_ridge_matrix record073_edge_matrix record073_missing_matrix

theorem record073_validity : GraphGrowthInputs.Valid record073.inputs :=
  valid_of_matrix record073 record073_matrix_checked

theorem record073_vertex_width : record073.vertexRows.width = record073.n := by decide +kernel

theorem record073_vertex_code : record073.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record073 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record073_literal : RawGraphSemanticCertificate.LiteralFacts record073.data :=
  literal_facts record073 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record073_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record073 SharedSix0CellPool.entry record073_vertex_width record073_vertex_code)

theorem record073_cells_exact : ∀ c, record073.data.cells c = FacetUniverses.FullSix0.cells (embedding record073 c) :=
  literal_cells record073 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record073_aligned

#print axioms record073_validity
#print axioms record073_literal

theorem record074_alignment_0 : Interval (alignedCheck record074 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record074_alignment_1 : Interval (alignedCheck record074 SharedSix0CellPool.entry) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)

theorem record074_alignment_checked : Interval (alignedCheck record074 SharedSix0CellPool.entry) 0 83 :=
  (interval_append _ 0 64 83 record074_alignment_0 record074_alignment_1)
theorem record074_aligned : ∀ c, Aligned record074 SharedSix0CellPool.entry c :=
  aligned_of_interval record074 SharedSix0CellPool.entry record074_alignment_checked

theorem record074_local_0 : Interval (localCheck record074) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record074_local_1 : Interval (localCheck record074) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)

theorem record074_local_checked : Interval (localCheck record074) 0 83 :=
  (interval_append _ 0 64 83 record074_local_0 record074_local_1)
theorem record074_kind_checked : Interval record074.data.kindTest 0 record074.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record074_ridge_matrix :
    record074.data.candidateMatrix = PackedIncidenceMatrix.code record074.data.ridgeList := by
  decide +kernel

theorem record074_edge_matrix :
    record074.data.edgeMatrix = PackedIncidenceMatrix.code record074.data.edgeLists := by
  decide +kernel

theorem record074_missing_matrix :
    record074.data.missingMatrix = PackedIncidenceMatrix.code record074.data.missingLists := by
  decide +kernel

theorem record074_matrix_checked : MatrixGraphProblem.Checked record074.data :=
  matrix_checked record074 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record074_aligned (by decide +kernel) record074_local_checked
    record074_kind_checked record074_ridge_matrix record074_edge_matrix record074_missing_matrix

theorem record074_validity : GraphGrowthInputs.Valid record074.inputs :=
  valid_of_matrix record074 record074_matrix_checked

theorem record074_vertex_width : record074.vertexRows.width = record074.n := by decide +kernel

theorem record074_vertex_code : record074.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record074 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record074_literal : RawGraphSemanticCertificate.LiteralFacts record074.data :=
  literal_facts record074 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record074_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record074 SharedSix0CellPool.entry record074_vertex_width record074_vertex_code)

theorem record074_cells_exact : ∀ c, record074.data.cells c = FacetUniverses.FullSix0.cells (embedding record074 c) :=
  literal_cells record074 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record074_aligned

#print axioms record074_validity
#print axioms record074_literal

theorem record075_alignment_0 : Interval (alignedCheck record075 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record075_alignment_1 : Interval (alignedCheck record075 SharedSix0CellPool.entry) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)

theorem record075_alignment_checked : Interval (alignedCheck record075 SharedSix0CellPool.entry) 0 86 :=
  (interval_append _ 0 64 86 record075_alignment_0 record075_alignment_1)
theorem record075_aligned : ∀ c, Aligned record075 SharedSix0CellPool.entry c :=
  aligned_of_interval record075 SharedSix0CellPool.entry record075_alignment_checked

theorem record075_local_0 : Interval (localCheck record075) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record075_local_1 : Interval (localCheck record075) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)

theorem record075_local_checked : Interval (localCheck record075) 0 86 :=
  (interval_append _ 0 64 86 record075_local_0 record075_local_1)
theorem record075_kind_checked : Interval record075.data.kindTest 0 record075.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record075_ridge_matrix :
    record075.data.candidateMatrix = PackedIncidenceMatrix.code record075.data.ridgeList := by
  decide +kernel

theorem record075_edge_matrix :
    record075.data.edgeMatrix = PackedIncidenceMatrix.code record075.data.edgeLists := by
  decide +kernel

theorem record075_missing_matrix :
    record075.data.missingMatrix = PackedIncidenceMatrix.code record075.data.missingLists := by
  decide +kernel

theorem record075_matrix_checked : MatrixGraphProblem.Checked record075.data :=
  matrix_checked record075 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record075_aligned (by decide +kernel) record075_local_checked
    record075_kind_checked record075_ridge_matrix record075_edge_matrix record075_missing_matrix

theorem record075_validity : GraphGrowthInputs.Valid record075.inputs :=
  valid_of_matrix record075 record075_matrix_checked

theorem record075_vertex_width : record075.vertexRows.width = record075.n := by decide +kernel

theorem record075_vertex_code : record075.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record075 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record075_literal : RawGraphSemanticCertificate.LiteralFacts record075.data :=
  literal_facts record075 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record075_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record075 SharedSix0CellPool.entry record075_vertex_width record075_vertex_code)

theorem record075_cells_exact : ∀ c, record075.data.cells c = FacetUniverses.FullSix0.cells (embedding record075 c) :=
  literal_cells record075 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record075_aligned

#print axioms record075_validity
#print axioms record075_literal

theorem record076_alignment_0 : Interval (alignedCheck record076 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record076_alignment_1 : Interval (alignedCheck record076 SharedSix0CellPool.entry) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)

theorem record076_alignment_checked : Interval (alignedCheck record076 SharedSix0CellPool.entry) 0 92 :=
  (interval_append _ 0 64 92 record076_alignment_0 record076_alignment_1)
theorem record076_aligned : ∀ c, Aligned record076 SharedSix0CellPool.entry c :=
  aligned_of_interval record076 SharedSix0CellPool.entry record076_alignment_checked

theorem record076_local_0 : Interval (localCheck record076) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record076_local_1 : Interval (localCheck record076) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)

theorem record076_local_checked : Interval (localCheck record076) 0 92 :=
  (interval_append _ 0 64 92 record076_local_0 record076_local_1)
theorem record076_kind_checked : Interval record076.data.kindTest 0 record076.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record076_ridge_matrix :
    record076.data.candidateMatrix = PackedIncidenceMatrix.code record076.data.ridgeList := by
  decide +kernel

theorem record076_edge_matrix :
    record076.data.edgeMatrix = PackedIncidenceMatrix.code record076.data.edgeLists := by
  decide +kernel

theorem record076_missing_matrix :
    record076.data.missingMatrix = PackedIncidenceMatrix.code record076.data.missingLists := by
  decide +kernel

theorem record076_matrix_checked : MatrixGraphProblem.Checked record076.data :=
  matrix_checked record076 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record076_aligned (by decide +kernel) record076_local_checked
    record076_kind_checked record076_ridge_matrix record076_edge_matrix record076_missing_matrix

theorem record076_validity : GraphGrowthInputs.Valid record076.inputs :=
  valid_of_matrix record076 record076_matrix_checked

theorem record076_vertex_width : record076.vertexRows.width = record076.n := by decide +kernel

theorem record076_vertex_code : record076.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record076 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record076_literal : RawGraphSemanticCertificate.LiteralFacts record076.data :=
  literal_facts record076 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record076_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record076 SharedSix0CellPool.entry record076_vertex_width record076_vertex_code)

theorem record076_cells_exact : ∀ c, record076.data.cells c = FacetUniverses.FullSix0.cells (embedding record076 c) :=
  literal_cells record076 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record076_aligned

#print axioms record076_validity
#print axioms record076_literal

theorem record077_alignment_0 : Interval (alignedCheck record077 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record077_alignment_1 : Interval (alignedCheck record077 SharedSix0CellPool.entry) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)

theorem record077_alignment_checked : Interval (alignedCheck record077 SharedSix0CellPool.entry) 0 92 :=
  (interval_append _ 0 64 92 record077_alignment_0 record077_alignment_1)
theorem record077_aligned : ∀ c, Aligned record077 SharedSix0CellPool.entry c :=
  aligned_of_interval record077 SharedSix0CellPool.entry record077_alignment_checked

theorem record077_local_0 : Interval (localCheck record077) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record077_local_1 : Interval (localCheck record077) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)

theorem record077_local_checked : Interval (localCheck record077) 0 92 :=
  (interval_append _ 0 64 92 record077_local_0 record077_local_1)
theorem record077_kind_checked : Interval record077.data.kindTest 0 record077.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record077_ridge_matrix :
    record077.data.candidateMatrix = PackedIncidenceMatrix.code record077.data.ridgeList := by
  decide +kernel

theorem record077_edge_matrix :
    record077.data.edgeMatrix = PackedIncidenceMatrix.code record077.data.edgeLists := by
  decide +kernel

theorem record077_missing_matrix :
    record077.data.missingMatrix = PackedIncidenceMatrix.code record077.data.missingLists := by
  decide +kernel

theorem record077_matrix_checked : MatrixGraphProblem.Checked record077.data :=
  matrix_checked record077 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record077_aligned (by decide +kernel) record077_local_checked
    record077_kind_checked record077_ridge_matrix record077_edge_matrix record077_missing_matrix

theorem record077_validity : GraphGrowthInputs.Valid record077.inputs :=
  valid_of_matrix record077 record077_matrix_checked

theorem record077_vertex_width : record077.vertexRows.width = record077.n := by decide +kernel

theorem record077_vertex_code : record077.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record077 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record077_literal : RawGraphSemanticCertificate.LiteralFacts record077.data :=
  literal_facts record077 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record077_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record077 SharedSix0CellPool.entry record077_vertex_width record077_vertex_code)

theorem record077_cells_exact : ∀ c, record077.data.cells c = FacetUniverses.FullSix0.cells (embedding record077 c) :=
  literal_cells record077 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record077_aligned

#print axioms record077_validity
#print axioms record077_literal

theorem record078_alignment_0 : Interval (alignedCheck record078 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record078_alignment_1 : Interval (alignedCheck record078 SharedSix0CellPool.entry) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)

theorem record078_alignment_checked : Interval (alignedCheck record078 SharedSix0CellPool.entry) 0 76 :=
  (interval_append _ 0 64 76 record078_alignment_0 record078_alignment_1)
theorem record078_aligned : ∀ c, Aligned record078 SharedSix0CellPool.entry c :=
  aligned_of_interval record078 SharedSix0CellPool.entry record078_alignment_checked

theorem record078_local_0 : Interval (localCheck record078) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record078_local_1 : Interval (localCheck record078) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)

theorem record078_local_checked : Interval (localCheck record078) 0 76 :=
  (interval_append _ 0 64 76 record078_local_0 record078_local_1)
theorem record078_kind_checked : Interval record078.data.kindTest 0 record078.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record078_ridge_matrix :
    record078.data.candidateMatrix = PackedIncidenceMatrix.code record078.data.ridgeList := by
  decide +kernel

theorem record078_edge_matrix :
    record078.data.edgeMatrix = PackedIncidenceMatrix.code record078.data.edgeLists := by
  decide +kernel

theorem record078_missing_matrix :
    record078.data.missingMatrix = PackedIncidenceMatrix.code record078.data.missingLists := by
  decide +kernel

theorem record078_matrix_checked : MatrixGraphProblem.Checked record078.data :=
  matrix_checked record078 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record078_aligned (by decide +kernel) record078_local_checked
    record078_kind_checked record078_ridge_matrix record078_edge_matrix record078_missing_matrix

theorem record078_validity : GraphGrowthInputs.Valid record078.inputs :=
  valid_of_matrix record078 record078_matrix_checked

theorem record078_vertex_width : record078.vertexRows.width = record078.n := by decide +kernel

theorem record078_vertex_code : record078.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record078 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record078_literal : RawGraphSemanticCertificate.LiteralFacts record078.data :=
  literal_facts record078 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record078_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record078 SharedSix0CellPool.entry record078_vertex_width record078_vertex_code)

theorem record078_cells_exact : ∀ c, record078.data.cells c = FacetUniverses.FullSix0.cells (embedding record078 c) :=
  literal_cells record078 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record078_aligned

#print axioms record078_validity
#print axioms record078_literal

theorem record079_alignment_0 : Interval (alignedCheck record079 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record079_alignment_1 : Interval (alignedCheck record079 SharedSix0CellPool.entry) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)

theorem record079_alignment_checked : Interval (alignedCheck record079 SharedSix0CellPool.entry) 0 91 :=
  (interval_append _ 0 64 91 record079_alignment_0 record079_alignment_1)
theorem record079_aligned : ∀ c, Aligned record079 SharedSix0CellPool.entry c :=
  aligned_of_interval record079 SharedSix0CellPool.entry record079_alignment_checked

theorem record079_local_0 : Interval (localCheck record079) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record079_local_1 : Interval (localCheck record079) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)

theorem record079_local_checked : Interval (localCheck record079) 0 91 :=
  (interval_append _ 0 64 91 record079_local_0 record079_local_1)
theorem record079_kind_checked : Interval record079.data.kindTest 0 record079.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record079_ridge_matrix :
    record079.data.candidateMatrix = PackedIncidenceMatrix.code record079.data.ridgeList := by
  decide +kernel

theorem record079_edge_matrix :
    record079.data.edgeMatrix = PackedIncidenceMatrix.code record079.data.edgeLists := by
  decide +kernel

theorem record079_missing_matrix :
    record079.data.missingMatrix = PackedIncidenceMatrix.code record079.data.missingLists := by
  decide +kernel

theorem record079_matrix_checked : MatrixGraphProblem.Checked record079.data :=
  matrix_checked record079 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record079_aligned (by decide +kernel) record079_local_checked
    record079_kind_checked record079_ridge_matrix record079_edge_matrix record079_missing_matrix

theorem record079_validity : GraphGrowthInputs.Valid record079.inputs :=
  valid_of_matrix record079 record079_matrix_checked

theorem record079_vertex_width : record079.vertexRows.width = record079.n := by decide +kernel

theorem record079_vertex_code : record079.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record079 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record079_literal : RawGraphSemanticCertificate.LiteralFacts record079.data :=
  literal_facts record079 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record079_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record079 SharedSix0CellPool.entry record079_vertex_width record079_vertex_code)

theorem record079_cells_exact : ∀ c, record079.data.cells c = FacetUniverses.FullSix0.cells (embedding record079 c) :=
  literal_cells record079 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record079_aligned

#print axioms record079_validity
#print axioms record079_literal

theorem record080_alignment_0 : Interval (alignedCheck record080 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record080_alignment_1 : Interval (alignedCheck record080 SharedSix0CellPool.entry) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)

theorem record080_alignment_checked : Interval (alignedCheck record080 SharedSix0CellPool.entry) 0 82 :=
  (interval_append _ 0 64 82 record080_alignment_0 record080_alignment_1)
theorem record080_aligned : ∀ c, Aligned record080 SharedSix0CellPool.entry c :=
  aligned_of_interval record080 SharedSix0CellPool.entry record080_alignment_checked

theorem record080_local_0 : Interval (localCheck record080) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record080_local_1 : Interval (localCheck record080) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)

theorem record080_local_checked : Interval (localCheck record080) 0 82 :=
  (interval_append _ 0 64 82 record080_local_0 record080_local_1)
theorem record080_kind_checked : Interval record080.data.kindTest 0 record080.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record080_ridge_matrix :
    record080.data.candidateMatrix = PackedIncidenceMatrix.code record080.data.ridgeList := by
  decide +kernel

theorem record080_edge_matrix :
    record080.data.edgeMatrix = PackedIncidenceMatrix.code record080.data.edgeLists := by
  decide +kernel

theorem record080_missing_matrix :
    record080.data.missingMatrix = PackedIncidenceMatrix.code record080.data.missingLists := by
  decide +kernel

theorem record080_matrix_checked : MatrixGraphProblem.Checked record080.data :=
  matrix_checked record080 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record080_aligned (by decide +kernel) record080_local_checked
    record080_kind_checked record080_ridge_matrix record080_edge_matrix record080_missing_matrix

theorem record080_validity : GraphGrowthInputs.Valid record080.inputs :=
  valid_of_matrix record080 record080_matrix_checked

theorem record080_vertex_width : record080.vertexRows.width = record080.n := by decide +kernel

theorem record080_vertex_code : record080.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record080 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record080_literal : RawGraphSemanticCertificate.LiteralFacts record080.data :=
  literal_facts record080 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record080_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record080 SharedSix0CellPool.entry record080_vertex_width record080_vertex_code)

theorem record080_cells_exact : ∀ c, record080.data.cells c = FacetUniverses.FullSix0.cells (embedding record080 c) :=
  literal_cells record080 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record080_aligned

#print axioms record080_validity
#print axioms record080_literal

theorem record081_alignment_0 : Interval (alignedCheck record081 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record081_alignment_1 : Interval (alignedCheck record081 SharedSix0CellPool.entry) 64 77 :=
  interval_of_check _ 64 13 (by decide +kernel)

theorem record081_alignment_checked : Interval (alignedCheck record081 SharedSix0CellPool.entry) 0 77 :=
  (interval_append _ 0 64 77 record081_alignment_0 record081_alignment_1)
theorem record081_aligned : ∀ c, Aligned record081 SharedSix0CellPool.entry c :=
  aligned_of_interval record081 SharedSix0CellPool.entry record081_alignment_checked

theorem record081_local_0 : Interval (localCheck record081) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record081_local_1 : Interval (localCheck record081) 64 77 :=
  interval_of_check _ 64 13 (by decide +kernel)

theorem record081_local_checked : Interval (localCheck record081) 0 77 :=
  (interval_append _ 0 64 77 record081_local_0 record081_local_1)
theorem record081_kind_checked : Interval record081.data.kindTest 0 record081.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record081_ridge_matrix :
    record081.data.candidateMatrix = PackedIncidenceMatrix.code record081.data.ridgeList := by
  decide +kernel

theorem record081_edge_matrix :
    record081.data.edgeMatrix = PackedIncidenceMatrix.code record081.data.edgeLists := by
  decide +kernel

theorem record081_missing_matrix :
    record081.data.missingMatrix = PackedIncidenceMatrix.code record081.data.missingLists := by
  decide +kernel

theorem record081_matrix_checked : MatrixGraphProblem.Checked record081.data :=
  matrix_checked record081 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record081_aligned (by decide +kernel) record081_local_checked
    record081_kind_checked record081_ridge_matrix record081_edge_matrix record081_missing_matrix

theorem record081_validity : GraphGrowthInputs.Valid record081.inputs :=
  valid_of_matrix record081 record081_matrix_checked

theorem record081_vertex_width : record081.vertexRows.width = record081.n := by decide +kernel

theorem record081_vertex_code : record081.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record081 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record081_literal : RawGraphSemanticCertificate.LiteralFacts record081.data :=
  literal_facts record081 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record081_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record081 SharedSix0CellPool.entry record081_vertex_width record081_vertex_code)

theorem record081_cells_exact : ∀ c, record081.data.cells c = FacetUniverses.FullSix0.cells (embedding record081 c) :=
  literal_cells record081 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record081_aligned

#print axioms record081_validity
#print axioms record081_literal

theorem record082_alignment_0 : Interval (alignedCheck record082 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record082_alignment_1 : Interval (alignedCheck record082 SharedSix0CellPool.entry) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)

theorem record082_alignment_checked : Interval (alignedCheck record082 SharedSix0CellPool.entry) 0 92 :=
  (interval_append _ 0 64 92 record082_alignment_0 record082_alignment_1)
theorem record082_aligned : ∀ c, Aligned record082 SharedSix0CellPool.entry c :=
  aligned_of_interval record082 SharedSix0CellPool.entry record082_alignment_checked

theorem record082_local_0 : Interval (localCheck record082) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record082_local_1 : Interval (localCheck record082) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)

theorem record082_local_checked : Interval (localCheck record082) 0 92 :=
  (interval_append _ 0 64 92 record082_local_0 record082_local_1)
theorem record082_kind_checked : Interval record082.data.kindTest 0 record082.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record082_ridge_matrix :
    record082.data.candidateMatrix = PackedIncidenceMatrix.code record082.data.ridgeList := by
  decide +kernel

theorem record082_edge_matrix :
    record082.data.edgeMatrix = PackedIncidenceMatrix.code record082.data.edgeLists := by
  decide +kernel

theorem record082_missing_matrix :
    record082.data.missingMatrix = PackedIncidenceMatrix.code record082.data.missingLists := by
  decide +kernel

theorem record082_matrix_checked : MatrixGraphProblem.Checked record082.data :=
  matrix_checked record082 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record082_aligned (by decide +kernel) record082_local_checked
    record082_kind_checked record082_ridge_matrix record082_edge_matrix record082_missing_matrix

theorem record082_validity : GraphGrowthInputs.Valid record082.inputs :=
  valid_of_matrix record082 record082_matrix_checked

theorem record082_vertex_width : record082.vertexRows.width = record082.n := by decide +kernel

theorem record082_vertex_code : record082.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record082 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record082_literal : RawGraphSemanticCertificate.LiteralFacts record082.data :=
  literal_facts record082 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record082_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record082 SharedSix0CellPool.entry record082_vertex_width record082_vertex_code)

theorem record082_cells_exact : ∀ c, record082.data.cells c = FacetUniverses.FullSix0.cells (embedding record082 c) :=
  literal_cells record082 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record082_aligned

#print axioms record082_validity
#print axioms record082_literal

theorem record083_alignment_0 : Interval (alignedCheck record083 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record083_alignment_1 : Interval (alignedCheck record083 SharedSix0CellPool.entry) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)

theorem record083_alignment_checked : Interval (alignedCheck record083 SharedSix0CellPool.entry) 0 89 :=
  (interval_append _ 0 64 89 record083_alignment_0 record083_alignment_1)
theorem record083_aligned : ∀ c, Aligned record083 SharedSix0CellPool.entry c :=
  aligned_of_interval record083 SharedSix0CellPool.entry record083_alignment_checked

theorem record083_local_0 : Interval (localCheck record083) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record083_local_1 : Interval (localCheck record083) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)

theorem record083_local_checked : Interval (localCheck record083) 0 89 :=
  (interval_append _ 0 64 89 record083_local_0 record083_local_1)
theorem record083_kind_checked : Interval record083.data.kindTest 0 record083.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record083_ridge_matrix :
    record083.data.candidateMatrix = PackedIncidenceMatrix.code record083.data.ridgeList := by
  decide +kernel

theorem record083_edge_matrix :
    record083.data.edgeMatrix = PackedIncidenceMatrix.code record083.data.edgeLists := by
  decide +kernel

theorem record083_missing_matrix :
    record083.data.missingMatrix = PackedIncidenceMatrix.code record083.data.missingLists := by
  decide +kernel

theorem record083_matrix_checked : MatrixGraphProblem.Checked record083.data :=
  matrix_checked record083 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record083_aligned (by decide +kernel) record083_local_checked
    record083_kind_checked record083_ridge_matrix record083_edge_matrix record083_missing_matrix

theorem record083_validity : GraphGrowthInputs.Valid record083.inputs :=
  valid_of_matrix record083 record083_matrix_checked

theorem record083_vertex_width : record083.vertexRows.width = record083.n := by decide +kernel

theorem record083_vertex_code : record083.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record083 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record083_literal : RawGraphSemanticCertificate.LiteralFacts record083.data :=
  literal_facts record083 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record083_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record083 SharedSix0CellPool.entry record083_vertex_width record083_vertex_code)

theorem record083_cells_exact : ∀ c, record083.data.cells c = FacetUniverses.FullSix0.cells (embedding record083 c) :=
  literal_cells record083 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record083_aligned

#print axioms record083_validity
#print axioms record083_literal

theorem record084_alignment_0 : Interval (alignedCheck record084 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record084_alignment_1 : Interval (alignedCheck record084 SharedSix0CellPool.entry) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)

theorem record084_alignment_checked : Interval (alignedCheck record084 SharedSix0CellPool.entry) 0 87 :=
  (interval_append _ 0 64 87 record084_alignment_0 record084_alignment_1)
theorem record084_aligned : ∀ c, Aligned record084 SharedSix0CellPool.entry c :=
  aligned_of_interval record084 SharedSix0CellPool.entry record084_alignment_checked

theorem record084_local_0 : Interval (localCheck record084) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record084_local_1 : Interval (localCheck record084) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)

theorem record084_local_checked : Interval (localCheck record084) 0 87 :=
  (interval_append _ 0 64 87 record084_local_0 record084_local_1)
theorem record084_kind_checked : Interval record084.data.kindTest 0 record084.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record084_ridge_matrix :
    record084.data.candidateMatrix = PackedIncidenceMatrix.code record084.data.ridgeList := by
  decide +kernel

theorem record084_edge_matrix :
    record084.data.edgeMatrix = PackedIncidenceMatrix.code record084.data.edgeLists := by
  decide +kernel

theorem record084_missing_matrix :
    record084.data.missingMatrix = PackedIncidenceMatrix.code record084.data.missingLists := by
  decide +kernel

theorem record084_matrix_checked : MatrixGraphProblem.Checked record084.data :=
  matrix_checked record084 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record084_aligned (by decide +kernel) record084_local_checked
    record084_kind_checked record084_ridge_matrix record084_edge_matrix record084_missing_matrix

theorem record084_validity : GraphGrowthInputs.Valid record084.inputs :=
  valid_of_matrix record084 record084_matrix_checked

theorem record084_vertex_width : record084.vertexRows.width = record084.n := by decide +kernel

theorem record084_vertex_code : record084.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record084 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record084_literal : RawGraphSemanticCertificate.LiteralFacts record084.data :=
  literal_facts record084 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record084_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record084 SharedSix0CellPool.entry record084_vertex_width record084_vertex_code)

theorem record084_cells_exact : ∀ c, record084.data.cells c = FacetUniverses.FullSix0.cells (embedding record084 c) :=
  literal_cells record084 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record084_aligned

#print axioms record084_validity
#print axioms record084_literal

theorem record085_alignment_0 : Interval (alignedCheck record085 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record085_alignment_1 : Interval (alignedCheck record085 SharedSix0CellPool.entry) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)

theorem record085_alignment_checked : Interval (alignedCheck record085 SharedSix0CellPool.entry) 0 94 :=
  (interval_append _ 0 64 94 record085_alignment_0 record085_alignment_1)
theorem record085_aligned : ∀ c, Aligned record085 SharedSix0CellPool.entry c :=
  aligned_of_interval record085 SharedSix0CellPool.entry record085_alignment_checked

theorem record085_local_0 : Interval (localCheck record085) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record085_local_1 : Interval (localCheck record085) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)

theorem record085_local_checked : Interval (localCheck record085) 0 94 :=
  (interval_append _ 0 64 94 record085_local_0 record085_local_1)
theorem record085_kind_checked : Interval record085.data.kindTest 0 record085.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record085_ridge_matrix :
    record085.data.candidateMatrix = PackedIncidenceMatrix.code record085.data.ridgeList := by
  decide +kernel

theorem record085_edge_matrix :
    record085.data.edgeMatrix = PackedIncidenceMatrix.code record085.data.edgeLists := by
  decide +kernel

theorem record085_missing_matrix :
    record085.data.missingMatrix = PackedIncidenceMatrix.code record085.data.missingLists := by
  decide +kernel

theorem record085_matrix_checked : MatrixGraphProblem.Checked record085.data :=
  matrix_checked record085 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record085_aligned (by decide +kernel) record085_local_checked
    record085_kind_checked record085_ridge_matrix record085_edge_matrix record085_missing_matrix

theorem record085_validity : GraphGrowthInputs.Valid record085.inputs :=
  valid_of_matrix record085 record085_matrix_checked

theorem record085_vertex_width : record085.vertexRows.width = record085.n := by decide +kernel

theorem record085_vertex_code : record085.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record085 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record085_literal : RawGraphSemanticCertificate.LiteralFacts record085.data :=
  literal_facts record085 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record085_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record085 SharedSix0CellPool.entry record085_vertex_width record085_vertex_code)

theorem record085_cells_exact : ∀ c, record085.data.cells c = FacetUniverses.FullSix0.cells (embedding record085 c) :=
  literal_cells record085 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record085_aligned

#print axioms record085_validity
#print axioms record085_literal

theorem record086_alignment_0 : Interval (alignedCheck record086 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record086_alignment_1 : Interval (alignedCheck record086 SharedSix0CellPool.entry) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)

theorem record086_alignment_checked : Interval (alignedCheck record086 SharedSix0CellPool.entry) 0 107 :=
  (interval_append _ 0 64 107 record086_alignment_0 record086_alignment_1)
theorem record086_aligned : ∀ c, Aligned record086 SharedSix0CellPool.entry c :=
  aligned_of_interval record086 SharedSix0CellPool.entry record086_alignment_checked

theorem record086_local_0 : Interval (localCheck record086) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record086_local_1 : Interval (localCheck record086) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)

theorem record086_local_checked : Interval (localCheck record086) 0 107 :=
  (interval_append _ 0 64 107 record086_local_0 record086_local_1)
theorem record086_kind_checked : Interval record086.data.kindTest 0 record086.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record086_ridge_matrix :
    record086.data.candidateMatrix = PackedIncidenceMatrix.code record086.data.ridgeList := by
  decide +kernel

theorem record086_edge_matrix :
    record086.data.edgeMatrix = PackedIncidenceMatrix.code record086.data.edgeLists := by
  decide +kernel

theorem record086_missing_matrix :
    record086.data.missingMatrix = PackedIncidenceMatrix.code record086.data.missingLists := by
  decide +kernel

theorem record086_matrix_checked : MatrixGraphProblem.Checked record086.data :=
  matrix_checked record086 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record086_aligned (by decide +kernel) record086_local_checked
    record086_kind_checked record086_ridge_matrix record086_edge_matrix record086_missing_matrix

theorem record086_validity : GraphGrowthInputs.Valid record086.inputs :=
  valid_of_matrix record086 record086_matrix_checked

theorem record086_vertex_width : record086.vertexRows.width = record086.n := by decide +kernel

theorem record086_vertex_code : record086.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record086 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record086_literal : RawGraphSemanticCertificate.LiteralFacts record086.data :=
  literal_facts record086 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record086_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record086 SharedSix0CellPool.entry record086_vertex_width record086_vertex_code)

theorem record086_cells_exact : ∀ c, record086.data.cells c = FacetUniverses.FullSix0.cells (embedding record086 c) :=
  literal_cells record086 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record086_aligned

#print axioms record086_validity
#print axioms record086_literal

theorem record087_alignment_0 : Interval (alignedCheck record087 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record087_alignment_1 : Interval (alignedCheck record087 SharedSix0CellPool.entry) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)

theorem record087_alignment_checked : Interval (alignedCheck record087 SharedSix0CellPool.entry) 0 97 :=
  (interval_append _ 0 64 97 record087_alignment_0 record087_alignment_1)
theorem record087_aligned : ∀ c, Aligned record087 SharedSix0CellPool.entry c :=
  aligned_of_interval record087 SharedSix0CellPool.entry record087_alignment_checked

theorem record087_local_0 : Interval (localCheck record087) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record087_local_1 : Interval (localCheck record087) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)

theorem record087_local_checked : Interval (localCheck record087) 0 97 :=
  (interval_append _ 0 64 97 record087_local_0 record087_local_1)
theorem record087_kind_checked : Interval record087.data.kindTest 0 record087.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record087_ridge_matrix :
    record087.data.candidateMatrix = PackedIncidenceMatrix.code record087.data.ridgeList := by
  decide +kernel

theorem record087_edge_matrix :
    record087.data.edgeMatrix = PackedIncidenceMatrix.code record087.data.edgeLists := by
  decide +kernel

theorem record087_missing_matrix :
    record087.data.missingMatrix = PackedIncidenceMatrix.code record087.data.missingLists := by
  decide +kernel

theorem record087_matrix_checked : MatrixGraphProblem.Checked record087.data :=
  matrix_checked record087 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record087_aligned (by decide +kernel) record087_local_checked
    record087_kind_checked record087_ridge_matrix record087_edge_matrix record087_missing_matrix

theorem record087_validity : GraphGrowthInputs.Valid record087.inputs :=
  valid_of_matrix record087 record087_matrix_checked

theorem record087_vertex_width : record087.vertexRows.width = record087.n := by decide +kernel

theorem record087_vertex_code : record087.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record087 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record087_literal : RawGraphSemanticCertificate.LiteralFacts record087.data :=
  literal_facts record087 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record087_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record087 SharedSix0CellPool.entry record087_vertex_width record087_vertex_code)

theorem record087_cells_exact : ∀ c, record087.data.cells c = FacetUniverses.FullSix0.cells (embedding record087 c) :=
  literal_cells record087 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record087_aligned

#print axioms record087_validity
#print axioms record087_literal

theorem record088_alignment_0 : Interval (alignedCheck record088 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record088_alignment_1 : Interval (alignedCheck record088 SharedSix0CellPool.entry) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)

theorem record088_alignment_checked : Interval (alignedCheck record088 SharedSix0CellPool.entry) 0 108 :=
  (interval_append _ 0 64 108 record088_alignment_0 record088_alignment_1)
theorem record088_aligned : ∀ c, Aligned record088 SharedSix0CellPool.entry c :=
  aligned_of_interval record088 SharedSix0CellPool.entry record088_alignment_checked

theorem record088_local_0 : Interval (localCheck record088) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record088_local_1 : Interval (localCheck record088) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)

theorem record088_local_checked : Interval (localCheck record088) 0 108 :=
  (interval_append _ 0 64 108 record088_local_0 record088_local_1)
theorem record088_kind_checked : Interval record088.data.kindTest 0 record088.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record088_ridge_matrix :
    record088.data.candidateMatrix = PackedIncidenceMatrix.code record088.data.ridgeList := by
  decide +kernel

theorem record088_edge_matrix :
    record088.data.edgeMatrix = PackedIncidenceMatrix.code record088.data.edgeLists := by
  decide +kernel

theorem record088_missing_matrix :
    record088.data.missingMatrix = PackedIncidenceMatrix.code record088.data.missingLists := by
  decide +kernel

theorem record088_matrix_checked : MatrixGraphProblem.Checked record088.data :=
  matrix_checked record088 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record088_aligned (by decide +kernel) record088_local_checked
    record088_kind_checked record088_ridge_matrix record088_edge_matrix record088_missing_matrix

theorem record088_validity : GraphGrowthInputs.Valid record088.inputs :=
  valid_of_matrix record088 record088_matrix_checked

theorem record088_vertex_width : record088.vertexRows.width = record088.n := by decide +kernel

theorem record088_vertex_code : record088.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record088 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record088_literal : RawGraphSemanticCertificate.LiteralFacts record088.data :=
  literal_facts record088 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record088_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record088 SharedSix0CellPool.entry record088_vertex_width record088_vertex_code)

theorem record088_cells_exact : ∀ c, record088.data.cells c = FacetUniverses.FullSix0.cells (embedding record088 c) :=
  literal_cells record088 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record088_aligned

#print axioms record088_validity
#print axioms record088_literal

theorem record089_alignment_0 : Interval (alignedCheck record089 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record089_alignment_1 : Interval (alignedCheck record089 SharedSix0CellPool.entry) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)

theorem record089_alignment_checked : Interval (alignedCheck record089 SharedSix0CellPool.entry) 0 97 :=
  (interval_append _ 0 64 97 record089_alignment_0 record089_alignment_1)
theorem record089_aligned : ∀ c, Aligned record089 SharedSix0CellPool.entry c :=
  aligned_of_interval record089 SharedSix0CellPool.entry record089_alignment_checked

theorem record089_local_0 : Interval (localCheck record089) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record089_local_1 : Interval (localCheck record089) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)

theorem record089_local_checked : Interval (localCheck record089) 0 97 :=
  (interval_append _ 0 64 97 record089_local_0 record089_local_1)
theorem record089_kind_checked : Interval record089.data.kindTest 0 record089.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record089_ridge_matrix :
    record089.data.candidateMatrix = PackedIncidenceMatrix.code record089.data.ridgeList := by
  decide +kernel

theorem record089_edge_matrix :
    record089.data.edgeMatrix = PackedIncidenceMatrix.code record089.data.edgeLists := by
  decide +kernel

theorem record089_missing_matrix :
    record089.data.missingMatrix = PackedIncidenceMatrix.code record089.data.missingLists := by
  decide +kernel

theorem record089_matrix_checked : MatrixGraphProblem.Checked record089.data :=
  matrix_checked record089 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record089_aligned (by decide +kernel) record089_local_checked
    record089_kind_checked record089_ridge_matrix record089_edge_matrix record089_missing_matrix

theorem record089_validity : GraphGrowthInputs.Valid record089.inputs :=
  valid_of_matrix record089 record089_matrix_checked

theorem record089_vertex_width : record089.vertexRows.width = record089.n := by decide +kernel

theorem record089_vertex_code : record089.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record089 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record089_literal : RawGraphSemanticCertificate.LiteralFacts record089.data :=
  literal_facts record089 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record089_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record089 SharedSix0CellPool.entry record089_vertex_width record089_vertex_code)

theorem record089_cells_exact : ∀ c, record089.data.cells c = FacetUniverses.FullSix0.cells (embedding record089 c) :=
  literal_cells record089 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record089_aligned

#print axioms record089_validity
#print axioms record089_literal

theorem record090_alignment_0 : Interval (alignedCheck record090 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record090_alignment_1 : Interval (alignedCheck record090 SharedSix0CellPool.entry) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)

theorem record090_alignment_checked : Interval (alignedCheck record090 SharedSix0CellPool.entry) 0 107 :=
  (interval_append _ 0 64 107 record090_alignment_0 record090_alignment_1)
theorem record090_aligned : ∀ c, Aligned record090 SharedSix0CellPool.entry c :=
  aligned_of_interval record090 SharedSix0CellPool.entry record090_alignment_checked

theorem record090_local_0 : Interval (localCheck record090) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record090_local_1 : Interval (localCheck record090) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)

theorem record090_local_checked : Interval (localCheck record090) 0 107 :=
  (interval_append _ 0 64 107 record090_local_0 record090_local_1)
theorem record090_kind_checked : Interval record090.data.kindTest 0 record090.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record090_ridge_matrix :
    record090.data.candidateMatrix = PackedIncidenceMatrix.code record090.data.ridgeList := by
  decide +kernel

theorem record090_edge_matrix :
    record090.data.edgeMatrix = PackedIncidenceMatrix.code record090.data.edgeLists := by
  decide +kernel

theorem record090_missing_matrix :
    record090.data.missingMatrix = PackedIncidenceMatrix.code record090.data.missingLists := by
  decide +kernel

theorem record090_matrix_checked : MatrixGraphProblem.Checked record090.data :=
  matrix_checked record090 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record090_aligned (by decide +kernel) record090_local_checked
    record090_kind_checked record090_ridge_matrix record090_edge_matrix record090_missing_matrix

theorem record090_validity : GraphGrowthInputs.Valid record090.inputs :=
  valid_of_matrix record090 record090_matrix_checked

theorem record090_vertex_width : record090.vertexRows.width = record090.n := by decide +kernel

theorem record090_vertex_code : record090.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record090 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record090_literal : RawGraphSemanticCertificate.LiteralFacts record090.data :=
  literal_facts record090 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record090_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record090 SharedSix0CellPool.entry record090_vertex_width record090_vertex_code)

theorem record090_cells_exact : ∀ c, record090.data.cells c = FacetUniverses.FullSix0.cells (embedding record090 c) :=
  literal_cells record090 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record090_aligned

#print axioms record090_validity
#print axioms record090_literal

theorem record091_alignment_0 : Interval (alignedCheck record091 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record091_alignment_1 : Interval (alignedCheck record091 SharedSix0CellPool.entry) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)

theorem record091_alignment_checked : Interval (alignedCheck record091 SharedSix0CellPool.entry) 0 89 :=
  (interval_append _ 0 64 89 record091_alignment_0 record091_alignment_1)
theorem record091_aligned : ∀ c, Aligned record091 SharedSix0CellPool.entry c :=
  aligned_of_interval record091 SharedSix0CellPool.entry record091_alignment_checked

theorem record091_local_0 : Interval (localCheck record091) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record091_local_1 : Interval (localCheck record091) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)

theorem record091_local_checked : Interval (localCheck record091) 0 89 :=
  (interval_append _ 0 64 89 record091_local_0 record091_local_1)
theorem record091_kind_checked : Interval record091.data.kindTest 0 record091.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record091_ridge_matrix :
    record091.data.candidateMatrix = PackedIncidenceMatrix.code record091.data.ridgeList := by
  decide +kernel

theorem record091_edge_matrix :
    record091.data.edgeMatrix = PackedIncidenceMatrix.code record091.data.edgeLists := by
  decide +kernel

theorem record091_missing_matrix :
    record091.data.missingMatrix = PackedIncidenceMatrix.code record091.data.missingLists := by
  decide +kernel

theorem record091_matrix_checked : MatrixGraphProblem.Checked record091.data :=
  matrix_checked record091 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record091_aligned (by decide +kernel) record091_local_checked
    record091_kind_checked record091_ridge_matrix record091_edge_matrix record091_missing_matrix

theorem record091_validity : GraphGrowthInputs.Valid record091.inputs :=
  valid_of_matrix record091 record091_matrix_checked

theorem record091_vertex_width : record091.vertexRows.width = record091.n := by decide +kernel

theorem record091_vertex_code : record091.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record091 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record091_literal : RawGraphSemanticCertificate.LiteralFacts record091.data :=
  literal_facts record091 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record091_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record091 SharedSix0CellPool.entry record091_vertex_width record091_vertex_code)

theorem record091_cells_exact : ∀ c, record091.data.cells c = FacetUniverses.FullSix0.cells (embedding record091 c) :=
  literal_cells record091 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record091_aligned

#print axioms record091_validity
#print axioms record091_literal

theorem record092_alignment_0 : Interval (alignedCheck record092 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record092_alignment_1 : Interval (alignedCheck record092 SharedSix0CellPool.entry) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)

theorem record092_alignment_checked : Interval (alignedCheck record092 SharedSix0CellPool.entry) 0 87 :=
  (interval_append _ 0 64 87 record092_alignment_0 record092_alignment_1)
theorem record092_aligned : ∀ c, Aligned record092 SharedSix0CellPool.entry c :=
  aligned_of_interval record092 SharedSix0CellPool.entry record092_alignment_checked

theorem record092_local_0 : Interval (localCheck record092) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record092_local_1 : Interval (localCheck record092) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)

theorem record092_local_checked : Interval (localCheck record092) 0 87 :=
  (interval_append _ 0 64 87 record092_local_0 record092_local_1)
theorem record092_kind_checked : Interval record092.data.kindTest 0 record092.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record092_ridge_matrix :
    record092.data.candidateMatrix = PackedIncidenceMatrix.code record092.data.ridgeList := by
  decide +kernel

theorem record092_edge_matrix :
    record092.data.edgeMatrix = PackedIncidenceMatrix.code record092.data.edgeLists := by
  decide +kernel

theorem record092_missing_matrix :
    record092.data.missingMatrix = PackedIncidenceMatrix.code record092.data.missingLists := by
  decide +kernel

theorem record092_matrix_checked : MatrixGraphProblem.Checked record092.data :=
  matrix_checked record092 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record092_aligned (by decide +kernel) record092_local_checked
    record092_kind_checked record092_ridge_matrix record092_edge_matrix record092_missing_matrix

theorem record092_validity : GraphGrowthInputs.Valid record092.inputs :=
  valid_of_matrix record092 record092_matrix_checked

theorem record092_vertex_width : record092.vertexRows.width = record092.n := by decide +kernel

theorem record092_vertex_code : record092.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record092 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record092_literal : RawGraphSemanticCertificate.LiteralFacts record092.data :=
  literal_facts record092 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record092_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record092 SharedSix0CellPool.entry record092_vertex_width record092_vertex_code)

theorem record092_cells_exact : ∀ c, record092.data.cells c = FacetUniverses.FullSix0.cells (embedding record092 c) :=
  literal_cells record092 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record092_aligned

#print axioms record092_validity
#print axioms record092_literal

theorem record093_alignment_0 : Interval (alignedCheck record093 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record093_alignment_1 : Interval (alignedCheck record093 SharedSix0CellPool.entry) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)

theorem record093_alignment_checked : Interval (alignedCheck record093 SharedSix0CellPool.entry) 0 80 :=
  (interval_append _ 0 64 80 record093_alignment_0 record093_alignment_1)
theorem record093_aligned : ∀ c, Aligned record093 SharedSix0CellPool.entry c :=
  aligned_of_interval record093 SharedSix0CellPool.entry record093_alignment_checked

theorem record093_local_0 : Interval (localCheck record093) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record093_local_1 : Interval (localCheck record093) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)

theorem record093_local_checked : Interval (localCheck record093) 0 80 :=
  (interval_append _ 0 64 80 record093_local_0 record093_local_1)
theorem record093_kind_checked : Interval record093.data.kindTest 0 record093.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record093_ridge_matrix :
    record093.data.candidateMatrix = PackedIncidenceMatrix.code record093.data.ridgeList := by
  decide +kernel

theorem record093_edge_matrix :
    record093.data.edgeMatrix = PackedIncidenceMatrix.code record093.data.edgeLists := by
  decide +kernel

theorem record093_missing_matrix :
    record093.data.missingMatrix = PackedIncidenceMatrix.code record093.data.missingLists := by
  decide +kernel

theorem record093_matrix_checked : MatrixGraphProblem.Checked record093.data :=
  matrix_checked record093 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record093_aligned (by decide +kernel) record093_local_checked
    record093_kind_checked record093_ridge_matrix record093_edge_matrix record093_missing_matrix

theorem record093_validity : GraphGrowthInputs.Valid record093.inputs :=
  valid_of_matrix record093 record093_matrix_checked

theorem record093_vertex_width : record093.vertexRows.width = record093.n := by decide +kernel

theorem record093_vertex_code : record093.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record093 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record093_literal : RawGraphSemanticCertificate.LiteralFacts record093.data :=
  literal_facts record093 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record093_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record093 SharedSix0CellPool.entry record093_vertex_width record093_vertex_code)

theorem record093_cells_exact : ∀ c, record093.data.cells c = FacetUniverses.FullSix0.cells (embedding record093 c) :=
  literal_cells record093 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record093_aligned

#print axioms record093_validity
#print axioms record093_literal

theorem record094_alignment_0 : Interval (alignedCheck record094 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record094_alignment_1 : Interval (alignedCheck record094 SharedSix0CellPool.entry) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)

theorem record094_alignment_checked : Interval (alignedCheck record094 SharedSix0CellPool.entry) 0 92 :=
  (interval_append _ 0 64 92 record094_alignment_0 record094_alignment_1)
theorem record094_aligned : ∀ c, Aligned record094 SharedSix0CellPool.entry c :=
  aligned_of_interval record094 SharedSix0CellPool.entry record094_alignment_checked

theorem record094_local_0 : Interval (localCheck record094) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record094_local_1 : Interval (localCheck record094) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)

theorem record094_local_checked : Interval (localCheck record094) 0 92 :=
  (interval_append _ 0 64 92 record094_local_0 record094_local_1)
theorem record094_kind_checked : Interval record094.data.kindTest 0 record094.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record094_ridge_matrix :
    record094.data.candidateMatrix = PackedIncidenceMatrix.code record094.data.ridgeList := by
  decide +kernel

theorem record094_edge_matrix :
    record094.data.edgeMatrix = PackedIncidenceMatrix.code record094.data.edgeLists := by
  decide +kernel

theorem record094_missing_matrix :
    record094.data.missingMatrix = PackedIncidenceMatrix.code record094.data.missingLists := by
  decide +kernel

theorem record094_matrix_checked : MatrixGraphProblem.Checked record094.data :=
  matrix_checked record094 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record094_aligned (by decide +kernel) record094_local_checked
    record094_kind_checked record094_ridge_matrix record094_edge_matrix record094_missing_matrix

theorem record094_validity : GraphGrowthInputs.Valid record094.inputs :=
  valid_of_matrix record094 record094_matrix_checked

theorem record094_vertex_width : record094.vertexRows.width = record094.n := by decide +kernel

theorem record094_vertex_code : record094.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record094 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record094_literal : RawGraphSemanticCertificate.LiteralFacts record094.data :=
  literal_facts record094 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record094_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record094 SharedSix0CellPool.entry record094_vertex_width record094_vertex_code)

theorem record094_cells_exact : ∀ c, record094.data.cells c = FacetUniverses.FullSix0.cells (embedding record094 c) :=
  literal_cells record094 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record094_aligned

#print axioms record094_validity
#print axioms record094_literal

theorem record095_alignment_0 : Interval (alignedCheck record095 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record095_alignment_1 : Interval (alignedCheck record095 SharedSix0CellPool.entry) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)

theorem record095_alignment_checked : Interval (alignedCheck record095 SharedSix0CellPool.entry) 0 101 :=
  (interval_append _ 0 64 101 record095_alignment_0 record095_alignment_1)
theorem record095_aligned : ∀ c, Aligned record095 SharedSix0CellPool.entry c :=
  aligned_of_interval record095 SharedSix0CellPool.entry record095_alignment_checked

theorem record095_local_0 : Interval (localCheck record095) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record095_local_1 : Interval (localCheck record095) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)

theorem record095_local_checked : Interval (localCheck record095) 0 101 :=
  (interval_append _ 0 64 101 record095_local_0 record095_local_1)
theorem record095_kind_checked : Interval record095.data.kindTest 0 record095.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record095_ridge_matrix :
    record095.data.candidateMatrix = PackedIncidenceMatrix.code record095.data.ridgeList := by
  decide +kernel

theorem record095_edge_matrix :
    record095.data.edgeMatrix = PackedIncidenceMatrix.code record095.data.edgeLists := by
  decide +kernel

theorem record095_missing_matrix :
    record095.data.missingMatrix = PackedIncidenceMatrix.code record095.data.missingLists := by
  decide +kernel

theorem record095_matrix_checked : MatrixGraphProblem.Checked record095.data :=
  matrix_checked record095 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record095_aligned (by decide +kernel) record095_local_checked
    record095_kind_checked record095_ridge_matrix record095_edge_matrix record095_missing_matrix

theorem record095_validity : GraphGrowthInputs.Valid record095.inputs :=
  valid_of_matrix record095 record095_matrix_checked

theorem record095_vertex_width : record095.vertexRows.width = record095.n := by decide +kernel

theorem record095_vertex_code : record095.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record095 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record095_literal : RawGraphSemanticCertificate.LiteralFacts record095.data :=
  literal_facts record095 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record095_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record095 SharedSix0CellPool.entry record095_vertex_width record095_vertex_code)

theorem record095_cells_exact : ∀ c, record095.data.cells c = FacetUniverses.FullSix0.cells (embedding record095 c) :=
  literal_cells record095 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record095_aligned

#print axioms record095_validity
#print axioms record095_literal

theorem record096_alignment_0 : Interval (alignedCheck record096 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record096_alignment_1 : Interval (alignedCheck record096 SharedSix0CellPool.entry) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)

theorem record096_alignment_checked : Interval (alignedCheck record096 SharedSix0CellPool.entry) 0 116 :=
  (interval_append _ 0 64 116 record096_alignment_0 record096_alignment_1)
theorem record096_aligned : ∀ c, Aligned record096 SharedSix0CellPool.entry c :=
  aligned_of_interval record096 SharedSix0CellPool.entry record096_alignment_checked

theorem record096_local_0 : Interval (localCheck record096) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record096_local_1 : Interval (localCheck record096) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)

theorem record096_local_checked : Interval (localCheck record096) 0 116 :=
  (interval_append _ 0 64 116 record096_local_0 record096_local_1)
theorem record096_kind_checked : Interval record096.data.kindTest 0 record096.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record096_ridge_matrix :
    record096.data.candidateMatrix = PackedIncidenceMatrix.code record096.data.ridgeList := by
  decide +kernel

theorem record096_edge_matrix :
    record096.data.edgeMatrix = PackedIncidenceMatrix.code record096.data.edgeLists := by
  decide +kernel

theorem record096_missing_matrix :
    record096.data.missingMatrix = PackedIncidenceMatrix.code record096.data.missingLists := by
  decide +kernel

theorem record096_matrix_checked : MatrixGraphProblem.Checked record096.data :=
  matrix_checked record096 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record096_aligned (by decide +kernel) record096_local_checked
    record096_kind_checked record096_ridge_matrix record096_edge_matrix record096_missing_matrix

theorem record096_validity : GraphGrowthInputs.Valid record096.inputs :=
  valid_of_matrix record096 record096_matrix_checked

theorem record096_vertex_width : record096.vertexRows.width = record096.n := by decide +kernel

theorem record096_vertex_code : record096.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record096 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record096_literal : RawGraphSemanticCertificate.LiteralFacts record096.data :=
  literal_facts record096 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record096_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record096 SharedSix0CellPool.entry record096_vertex_width record096_vertex_code)

theorem record096_cells_exact : ∀ c, record096.data.cells c = FacetUniverses.FullSix0.cells (embedding record096 c) :=
  literal_cells record096 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record096_aligned

#print axioms record096_validity
#print axioms record096_literal

theorem record097_alignment_0 : Interval (alignedCheck record097 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record097_alignment_1 : Interval (alignedCheck record097 SharedSix0CellPool.entry) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)

theorem record097_alignment_checked : Interval (alignedCheck record097 SharedSix0CellPool.entry) 0 112 :=
  (interval_append _ 0 64 112 record097_alignment_0 record097_alignment_1)
theorem record097_aligned : ∀ c, Aligned record097 SharedSix0CellPool.entry c :=
  aligned_of_interval record097 SharedSix0CellPool.entry record097_alignment_checked

theorem record097_local_0 : Interval (localCheck record097) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record097_local_1 : Interval (localCheck record097) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)

theorem record097_local_checked : Interval (localCheck record097) 0 112 :=
  (interval_append _ 0 64 112 record097_local_0 record097_local_1)
theorem record097_kind_checked : Interval record097.data.kindTest 0 record097.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record097_ridge_matrix :
    record097.data.candidateMatrix = PackedIncidenceMatrix.code record097.data.ridgeList := by
  decide +kernel

theorem record097_edge_matrix :
    record097.data.edgeMatrix = PackedIncidenceMatrix.code record097.data.edgeLists := by
  decide +kernel

theorem record097_missing_matrix :
    record097.data.missingMatrix = PackedIncidenceMatrix.code record097.data.missingLists := by
  decide +kernel

theorem record097_matrix_checked : MatrixGraphProblem.Checked record097.data :=
  matrix_checked record097 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record097_aligned (by decide +kernel) record097_local_checked
    record097_kind_checked record097_ridge_matrix record097_edge_matrix record097_missing_matrix

theorem record097_validity : GraphGrowthInputs.Valid record097.inputs :=
  valid_of_matrix record097 record097_matrix_checked

theorem record097_vertex_width : record097.vertexRows.width = record097.n := by decide +kernel

theorem record097_vertex_code : record097.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record097 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record097_literal : RawGraphSemanticCertificate.LiteralFacts record097.data :=
  literal_facts record097 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record097_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record097 SharedSix0CellPool.entry record097_vertex_width record097_vertex_code)

theorem record097_cells_exact : ∀ c, record097.data.cells c = FacetUniverses.FullSix0.cells (embedding record097 c) :=
  literal_cells record097 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record097_aligned

#print axioms record097_validity
#print axioms record097_literal

theorem record098_alignment_0 : Interval (alignedCheck record098 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record098_alignment_1 : Interval (alignedCheck record098 SharedSix0CellPool.entry) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)

theorem record098_alignment_checked : Interval (alignedCheck record098 SharedSix0CellPool.entry) 0 114 :=
  (interval_append _ 0 64 114 record098_alignment_0 record098_alignment_1)
theorem record098_aligned : ∀ c, Aligned record098 SharedSix0CellPool.entry c :=
  aligned_of_interval record098 SharedSix0CellPool.entry record098_alignment_checked

theorem record098_local_0 : Interval (localCheck record098) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record098_local_1 : Interval (localCheck record098) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)

theorem record098_local_checked : Interval (localCheck record098) 0 114 :=
  (interval_append _ 0 64 114 record098_local_0 record098_local_1)
theorem record098_kind_checked : Interval record098.data.kindTest 0 record098.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record098_ridge_matrix :
    record098.data.candidateMatrix = PackedIncidenceMatrix.code record098.data.ridgeList := by
  decide +kernel

theorem record098_edge_matrix :
    record098.data.edgeMatrix = PackedIncidenceMatrix.code record098.data.edgeLists := by
  decide +kernel

theorem record098_missing_matrix :
    record098.data.missingMatrix = PackedIncidenceMatrix.code record098.data.missingLists := by
  decide +kernel

theorem record098_matrix_checked : MatrixGraphProblem.Checked record098.data :=
  matrix_checked record098 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record098_aligned (by decide +kernel) record098_local_checked
    record098_kind_checked record098_ridge_matrix record098_edge_matrix record098_missing_matrix

theorem record098_validity : GraphGrowthInputs.Valid record098.inputs :=
  valid_of_matrix record098 record098_matrix_checked

theorem record098_vertex_width : record098.vertexRows.width = record098.n := by decide +kernel

theorem record098_vertex_code : record098.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record098 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record098_literal : RawGraphSemanticCertificate.LiteralFacts record098.data :=
  literal_facts record098 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record098_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record098 SharedSix0CellPool.entry record098_vertex_width record098_vertex_code)

theorem record098_cells_exact : ∀ c, record098.data.cells c = FacetUniverses.FullSix0.cells (embedding record098 c) :=
  literal_cells record098 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record098_aligned

#print axioms record098_validity
#print axioms record098_literal

theorem record099_alignment_0 : Interval (alignedCheck record099 SharedSix0CellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record099_alignment_1 : Interval (alignedCheck record099 SharedSix0CellPool.entry) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)

theorem record099_alignment_checked : Interval (alignedCheck record099 SharedSix0CellPool.entry) 0 75 :=
  (interval_append _ 0 64 75 record099_alignment_0 record099_alignment_1)
theorem record099_aligned : ∀ c, Aligned record099 SharedSix0CellPool.entry c :=
  aligned_of_interval record099 SharedSix0CellPool.entry record099_alignment_checked

theorem record099_local_0 : Interval (localCheck record099) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record099_local_1 : Interval (localCheck record099) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)

theorem record099_local_checked : Interval (localCheck record099) 0 75 :=
  (interval_append _ 0 64 75 record099_local_0 record099_local_1)
theorem record099_kind_checked : Interval record099.data.kindTest 0 record099.k :=
  interval_of_check _ 0 5 (by decide +kernel)

theorem record099_ridge_matrix :
    record099.data.candidateMatrix = PackedIncidenceMatrix.code record099.data.ridgeList := by
  decide +kernel

theorem record099_edge_matrix :
    record099.data.edgeMatrix = PackedIncidenceMatrix.code record099.data.edgeLists := by
  decide +kernel

theorem record099_missing_matrix :
    record099.data.missingMatrix = PackedIncidenceMatrix.code record099.data.missingLists := by
  decide +kernel

theorem record099_matrix_checked : MatrixGraphProblem.Checked record099.data :=
  matrix_checked record099 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record099_aligned (by decide +kernel) record099_local_checked
    record099_kind_checked record099_ridge_matrix record099_edge_matrix record099_missing_matrix

theorem record099_validity : GraphGrowthInputs.Valid record099.inputs :=
  valid_of_matrix record099 record099_matrix_checked

theorem record099_vertex_width : record099.vertexRows.width = record099.n := by decide +kernel

theorem record099_vertex_code : record099.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record099 SharedSix0CellPool.entry c).vertices) := by decide +kernel

theorem record099_literal : RawGraphSemanticCertificate.LiteralFacts record099.data :=
  literal_facts record099 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record099_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record099 SharedSix0CellPool.entry record099_vertex_width record099_vertex_code)

theorem record099_cells_exact : ∀ c, record099.data.cells c = FacetUniverses.FullSix0.cells (embedding record099 c) :=
  literal_cells record099 SharedSix0CellPool.entry FacetUniverses.FullSix0.cells SharedSmallGraph.withinMask
    SharedSix0CellPool.facts record099_aligned

#print axioms record099_validity
#print axioms record099_literal

end Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000
