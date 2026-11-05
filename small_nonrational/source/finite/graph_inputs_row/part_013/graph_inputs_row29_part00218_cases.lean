module
prelude
public import GraphInputsRow29Part00218Checked
public import GraphInputsRow29Part00218Metadata
public import GraphInputsRow29Part00218Frames
public import GraphInputsRow29Part00218Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch120
public import GraphCoverageBatch154


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00218
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_core : Core record000 where
  matrix := record000_matrix_checked
  valid := record000_validity
  literal := record000_literal
  nodes := record000_raw_node_checks record000_validity
  leaf_nodup := record000_leaves_nodup
  frames := record000_frames_supported record000_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record000_certificates, record000_leaf_certificates_checked⟩

theorem record000_parameters : Parameters record000 (rowOfCode 29) 29693928018048 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29693928018048 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12028 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29693928018048
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch120.candidate12028_checked

theorem record000_result : Result (29, 29693928018048) :=
  of_small 29 29693928018048 (by decide) ⟨record000, record000_core, record000_parameters, record000_coverage⟩
#print axioms record000_result

theorem record001_core : Core record001 where
  matrix := record001_matrix_checked
  valid := record001_validity
  literal := record001_literal
  nodes := record001_raw_node_checks record001_validity
  leaf_nodup := record001_leaves_nodup
  frames := record001_frames_supported record001_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record001_certificates, record001_leaf_certificates_checked⟩

theorem record001_parameters : Parameters record001 (rowOfCode 29) 29725620207872 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29725620207872 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15439 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29725620207872
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch154.candidate15439_checked

theorem record001_result : Result (29, 29725620207872) :=
  of_small 29 29725620207872 (by decide) ⟨record001, record001_core, record001_parameters, record001_coverage⟩
#print axioms record001_result

theorem record002_core : Core record002 where
  matrix := record002_matrix_checked
  valid := record002_validity
  literal := record002_literal
  nodes := record002_raw_node_checks record002_validity
  leaf_nodup := record002_leaves_nodup
  frames := record002_frames_supported record002_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record002_certificates, record002_leaf_certificates_checked⟩

theorem record002_parameters : Parameters record002 (rowOfCode 29) 29725628596224 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29725628596224 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12029 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29725628596224
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch120.candidate12029_checked

theorem record002_result : Result (29, 29725628596224) :=
  of_small 29 29725628596224 (by decide) ⟨record002, record002_core, record002_parameters, record002_coverage⟩
#print axioms record002_result

theorem record003_core : Core record003 where
  matrix := record003_matrix_checked
  valid := record003_validity
  literal := record003_literal
  nodes := record003_raw_node_checks record003_validity
  leaf_nodup := record003_leaves_nodup
  frames := record003_frames_supported record003_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record003_certificates, record003_leaf_certificates_checked⟩

theorem record003_parameters : Parameters record003 (rowOfCode 29) 29726140010624 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29726140010624 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12030 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29726140010624
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch120.candidate12030_checked

theorem record003_result : Result (29, 29726140010624) :=
  of_small 29 29726140010624 (by decide) ⟨record003, record003_core, record003_parameters, record003_coverage⟩
#print axioms record003_result

theorem record004_core : Core record004 where
  matrix := record004_matrix_checked
  valid := record004_validity
  literal := record004_literal
  nodes := record004_raw_node_checks record004_validity
  leaf_nodup := record004_leaves_nodup
  frames := record004_frames_supported record004_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record004_certificates, record004_leaf_certificates_checked⟩

theorem record004_parameters : Parameters record004 (rowOfCode 29) 29727213486720 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29727213486720 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12031 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29727213486720
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch120.candidate12031_checked

theorem record004_result : Result (29, 29727213486720) :=
  of_small 29 29727213486720 (by decide) ⟨record004, record004_core, record004_parameters, record004_coverage⟩
#print axioms record004_result

theorem record005_core : Core record005 where
  matrix := record005_matrix_checked
  valid := record005_validity
  literal := record005_literal
  nodes := record005_raw_node_checks record005_validity
  leaf_nodup := record005_leaves_nodup
  frames := record005_frames_supported record005_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record005_certificates, record005_leaf_certificates_checked⟩

theorem record005_parameters : Parameters record005 (rowOfCode 29) 29731242180608 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29731242180608 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15440 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29731242180608
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch154.candidate15440_checked

theorem record005_result : Result (29, 29731242180608) :=
  of_small 29 29731242180608 (by decide) ⟨record005, record005_core, record005_parameters, record005_coverage⟩
#print axioms record005_result

theorem record006_core : Core record006 where
  matrix := record006_matrix_checked
  valid := record006_validity
  literal := record006_literal
  nodes := record006_raw_node_checks record006_validity
  leaf_nodup := record006_leaves_nodup
  frames := record006_frames_supported record006_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record006_certificates, record006_leaf_certificates_checked⟩

theorem record006_parameters : Parameters record006 (rowOfCode 29) 29757832462592 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29757832462592 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12032 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29757832462592
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch120.candidate12032_checked

theorem record006_result : Result (29, 29757832462592) :=
  of_small 29 29757832462592 (by decide) ⟨record006, record006_core, record006_parameters, record006_coverage⟩
#print axioms record006_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00218
