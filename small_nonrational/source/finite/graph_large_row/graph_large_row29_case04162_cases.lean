module
prelude
public import GraphLargeRow29Case04162Checked
public import GraphLargeRow29Case04162Metadata
public import GraphLargeRow29Case04162Leaves
public import GraphLargeRow29Case04162Frames
public import IncreasingEmbedding

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphLargeRow29Case04162
open Papers.RationalityTen GraphCaseCertificate GraphRowSpecifications

theorem record000_core : Core record000 where
  matrix := record000_matrix_checked
  valid := record000_validity
  literal := record000_literal
  nodes := record000_raw_node_checks record000_validity
  leaf_nodup := record000_leaves_nodup
  frames := record000_frames_supported record000_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record000_certificates, record000_leaf_certificates_checked⟩

theorem record000_parameters : Parameters record000 (rowOfCode 29) 32780335513600 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32780335513600 :=
  GraphEmbeddingCoverage.coverage_of_mask record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    32780335513600 (SharedSmallGraph.allowedMask record000.data.quota) record000_cells_exact
    (GraphCoverageDescriptions.nodup_of_increasing _ (by decide +kernel))
    (GraphEmbeddingCoverage.small_allowed record000.data.quota) (by decide +kernel) GraphEmbeddingCoverage.small_edges

theorem record000_result : Result (29, 32780335513600) :=
  of_small 29 32780335513600 (by decide) ⟨record000, record000_core, record000_parameters, record000_coverage⟩
#print axioms record000_result
end Papers.RationalityTen.CompactReplay.GraphLargeRow29Case04162
