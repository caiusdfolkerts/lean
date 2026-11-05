module
prelude
public import GraphInputsRow29Part00252Data
public import SharedGraphCellPool
public import SharedSmallCellPoolChecked
public import GraphInputsRow25Part00022Metadata

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00252
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool FiniteChecks

theorem record000_alignment_0 : Interval (alignedCheck record000 SharedSmallCellPool.entry) 0 64 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record033_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record000_alignment_1 : Interval (alignedCheck record000 SharedSmallCellPool.entry) 64 116 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record033_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record000_alignment_checked : Interval (alignedCheck record000 SharedSmallCellPool.entry) 0 116 :=
  (interval_append _ 0 64 116 record000_alignment_0 record000_alignment_1)
theorem record000_aligned : ∀ c, Aligned record000 SharedSmallCellPool.entry c :=
  aligned_of_interval record000 SharedSmallCellPool.entry record000_alignment_checked

theorem record000_local_0 : Interval (localCheck record000) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record000_local_1 : Interval (localCheck record000) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)

theorem record000_local_checked : Interval (localCheck record000) 0 116 :=
  (interval_append _ 0 64 116 record000_local_0 record000_local_1)
theorem record000_kind_checked : Interval record000.data.kindTest 0 record000.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record033_kind_checked

theorem record000_ridge_matrix :
    record000.data.candidateMatrix = PackedIncidenceMatrix.code record000.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record033_ridge_matrix

theorem record000_edge_matrix :
    record000.data.edgeMatrix = PackedIncidenceMatrix.code record000.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record033_edge_matrix

theorem record000_missing_matrix :
    record000.data.missingMatrix = PackedIncidenceMatrix.code record000.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record033_missing_matrix

theorem record000_matrix_checked : MatrixGraphProblem.Checked record000.data :=
  matrix_checked record000 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record000_aligned (by decide +kernel) record000_local_checked
    record000_kind_checked record000_ridge_matrix record000_edge_matrix record000_missing_matrix

theorem record000_validity : GraphGrowthInputs.Valid record000.inputs :=
  valid_of_matrix record000 record000_matrix_checked

theorem record000_vertex_width : record000.vertexRows.width = record000.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record033_vertex_width

theorem record000_vertex_code : record000.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record000 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record033_vertex_code

theorem record000_literal : RawGraphSemanticCertificate.LiteralFacts record000.data :=
  literal_facts record000 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record000_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record000 SharedSmallCellPool.entry record000_vertex_width record000_vertex_code)

theorem record000_cells_exact : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c) :=
  literal_cells record000 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record000_aligned

#print axioms record000_validity
#print axioms record000_literal

theorem record001_alignment_0 : Interval (alignedCheck record001 SharedSmallCellPool.entry) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record001_alignment_1 : Interval (alignedCheck record001 SharedSmallCellPool.entry) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)

theorem record001_alignment_checked : Interval (alignedCheck record001 SharedSmallCellPool.entry) 0 100 :=
  (interval_append _ 0 64 100 record001_alignment_0 record001_alignment_1)
theorem record001_aligned : ∀ c, Aligned record001 SharedSmallCellPool.entry c :=
  aligned_of_interval record001 SharedSmallCellPool.entry record001_alignment_checked

theorem record001_local_0 : Interval (localCheck record001) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record001_local_1 : Interval (localCheck record001) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)

theorem record001_local_checked : Interval (localCheck record001) 0 100 :=
  (interval_append _ 0 64 100 record001_local_0 record001_local_1)
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
  matrix_checked record001 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record001_aligned (by decide +kernel) record001_local_checked
    record001_kind_checked record001_ridge_matrix record001_edge_matrix record001_missing_matrix

theorem record001_validity : GraphGrowthInputs.Valid record001.inputs :=
  valid_of_matrix record001 record001_matrix_checked

theorem record001_vertex_width : record001.vertexRows.width = record001.n := by decide +kernel

theorem record001_vertex_code : record001.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record001 SharedSmallCellPool.entry c).vertices) := by decide +kernel

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
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record034_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record002_alignment_1 : Interval (alignedCheck record002 SharedSmallCellPool.entry) 64 103 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record034_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record002_alignment_checked : Interval (alignedCheck record002 SharedSmallCellPool.entry) 0 103 :=
  (interval_append _ 0 64 103 record002_alignment_0 record002_alignment_1)
theorem record002_aligned : ∀ c, Aligned record002 SharedSmallCellPool.entry c :=
  aligned_of_interval record002 SharedSmallCellPool.entry record002_alignment_checked

theorem record002_local_0 : Interval (localCheck record002) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

theorem record002_local_1 : Interval (localCheck record002) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)

theorem record002_local_checked : Interval (localCheck record002) 0 103 :=
  (interval_append _ 0 64 103 record002_local_0 record002_local_1)
theorem record002_kind_checked : Interval record002.data.kindTest 0 record002.k :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record034_kind_checked

theorem record002_ridge_matrix :
    record002.data.candidateMatrix = PackedIncidenceMatrix.code record002.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record034_ridge_matrix

theorem record002_edge_matrix :
    record002.data.edgeMatrix = PackedIncidenceMatrix.code record002.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record034_edge_matrix

theorem record002_missing_matrix :
    record002.data.missingMatrix = PackedIncidenceMatrix.code record002.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record034_missing_matrix

theorem record002_matrix_checked : MatrixGraphProblem.Checked record002.data :=
  matrix_checked record002 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record002_aligned (by decide +kernel) record002_local_checked
    record002_kind_checked record002_ridge_matrix record002_edge_matrix record002_missing_matrix

theorem record002_validity : GraphGrowthInputs.Valid record002.inputs :=
  valid_of_matrix record002 record002_matrix_checked

theorem record002_vertex_width : record002.vertexRows.width = record002.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record034_vertex_width

theorem record002_vertex_code : record002.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record002 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record034_vertex_code

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
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record035_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

theorem record003_alignment_1 : Interval (alignedCheck record003 SharedSmallCellPool.entry) 64 105 := by
  intro i hlo hhi
  exact Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record035_alignment_checked i (Nat.zero_le i) (Nat.lt_of_lt_of_le hhi (by decide +kernel))

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
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record035_kind_checked

theorem record003_ridge_matrix :
    record003.data.candidateMatrix = PackedIncidenceMatrix.code record003.data.ridgeList :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record035_ridge_matrix

theorem record003_edge_matrix :
    record003.data.edgeMatrix = PackedIncidenceMatrix.code record003.data.edgeLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record035_edge_matrix

theorem record003_missing_matrix :
    record003.data.missingMatrix = PackedIncidenceMatrix.code record003.data.missingLists :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record035_missing_matrix

theorem record003_matrix_checked : MatrixGraphProblem.Checked record003.data :=
  matrix_checked record003 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record003_aligned (by decide +kernel) record003_local_checked
    record003_kind_checked record003_ridge_matrix record003_edge_matrix record003_missing_matrix

theorem record003_validity : GraphGrowthInputs.Valid record003.inputs :=
  valid_of_matrix record003 record003_matrix_checked

theorem record003_vertex_width : record003.vertexRows.width = record003.n :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record035_vertex_width

theorem record003_vertex_code : record003.vertexRows.code = PackedIncidenceMatrix.code
    (fun c => (localEntry record003 SharedSmallCellPool.entry c).vertices) :=
  Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record035_vertex_code

theorem record003_literal : RawGraphSemanticCertificate.LiteralFacts record003.data :=
  literal_facts record003 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record003_aligned SharedSmallGraph.within_mask_exact
    (vertex_rows_of_code record003 SharedSmallCellPool.entry record003_vertex_width record003_vertex_code)

theorem record003_cells_exact : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c) :=
  literal_cells record003 SharedSmallCellPool.entry FacetUniverses.FullSmall.cells SharedSmallGraph.withinMask
    SharedSmallCellPool.facts record003_aligned

#print axioms record003_validity
#print axioms record003_literal

end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00252
