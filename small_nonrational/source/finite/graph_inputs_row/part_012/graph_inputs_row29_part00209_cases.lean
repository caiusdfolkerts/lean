module
prelude
public import GraphInputsRow29Part00209Checked
public import GraphInputsRow29Part00209Metadata
public import GraphInputsRow29Part00209Frames
public import GraphInputsRow29Part00209Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch119
public import GraphCoverageBatch154


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209
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

theorem record000_parameters : Parameters record000 (rowOfCode 29) 29176267047040 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29176267047040 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15414 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29176267047040
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch154.candidate15414_checked

theorem record000_result : Result (29, 29176267047040) :=
  of_small 29 29176267047040 (by decide) ⟨record000, record000_core, record000_parameters, record000_coverage⟩
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

theorem record001_parameters : Parameters record001 (rowOfCode 29) 29176518414464 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29176518414464 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11995 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29176518414464
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch119.candidate11995_checked

theorem record001_result : Result (29, 29176518414464) :=
  of_small 29 29176518414464 (by decide) ⟨record001, record001_core, record001_parameters, record001_coverage⟩
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

theorem record002_parameters : Parameters record002 (rowOfCode 29) 29177059409920 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29177059409920 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15415 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29177059409920
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch154.candidate15415_checked

theorem record002_result : Result (29, 29177059409920) :=
  of_small 29 29177059409920 (by decide) ⟨record002, record002_core, record002_parameters, record002_coverage⟩
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

theorem record003_parameters : Parameters record003 (rowOfCode 29) 29177591890560 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29177591890560 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11996 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29177591890560
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch119.candidate11996_checked

theorem record003_result : Result (29, 29177591890560) :=
  of_small 29 29177591890560 (by decide) ⟨record003, record003_core, record003_parameters, record003_coverage⟩
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

theorem record004_parameters : Parameters record004 (rowOfCode 29) 29180303511552 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29180303511552 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15416 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29180303511552
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch154.candidate15416_checked

theorem record004_result : Result (29, 29180303511552) :=
  of_small 29 29180303511552 (by decide) ⟨record004, record004_core, record004_parameters, record004_coverage⟩
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

theorem record005_parameters : Parameters record005 (rowOfCode 29) 29180410728704 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29180410728704 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15417 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29180410728704
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch154.candidate15417_checked

theorem record005_result : Result (29, 29180410728704) :=
  of_small 29 29180410728704 (by decide) ⟨record005, record005_core, record005_parameters, record005_coverage⟩
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

theorem record006_parameters : Parameters record006 (rowOfCode 29) 29180561997952 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29180561997952 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15418 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29180561997952
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch154.candidate15418_checked

theorem record006_result : Result (29, 29180561997952) :=
  of_small 29 29180561997952 (by decide) ⟨record006, record006_core, record006_parameters, record006_coverage⟩
#print axioms record006_result

theorem record007_core : Core record007 where
  matrix := record007_matrix_checked
  valid := record007_validity
  literal := record007_literal
  nodes := record007_raw_node_checks record007_validity
  leaf_nodup := record007_leaves_nodup
  frames := record007_frames_supported record007_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record007_certificates, record007_leaf_certificates_checked⟩

theorem record007_parameters : Parameters record007 (rowOfCode 29) 29180567752704 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29180567752704 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15419 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29180567752704
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch154.candidate15419_checked

theorem record007_result : Result (29, 29180567752704) :=
  of_small 29 29180567752704 (by decide) ⟨record007, record007_core, record007_parameters, record007_coverage⟩
#print axioms record007_result

theorem record008_core : Core record008 where
  matrix := record008_matrix_checked
  valid := record008_validity
  literal := record008_literal
  nodes := record008_raw_node_checks record008_validity
  leaf_nodup := record008_leaves_nodup
  frames := record008_frames_supported record008_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record008_certificates, record008_leaf_certificates_checked⟩

theorem record008_parameters : Parameters record008 (rowOfCode 29) 29180679164032 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29180679164032 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15420 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29180679164032
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch154.candidate15420_checked

theorem record008_result : Result (29, 29180679164032) :=
  of_small 29 29180679164032 (by decide) ⟨record008, record008_core, record008_parameters, record008_coverage⟩
#print axioms record008_result

theorem record009_core : Core record009 where
  matrix := record009_matrix_checked
  valid := record009_validity
  literal := record009_literal
  nodes := record009_raw_node_checks record009_validity
  leaf_nodup := record009_leaves_nodup
  frames := record009_frames_supported record009_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record009_certificates, record009_leaf_certificates_checked⟩

theorem record009_parameters : Parameters record009 (rowOfCode 29) 29181484204800 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29181484204800 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15421 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29181484204800
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch154.candidate15421_checked

theorem record009_result : Result (29, 29181484204800) :=
  of_small 29 29181484204800 (by decide) ⟨record009, record009_core, record009_parameters, record009_coverage⟩
#print axioms record009_result

theorem record010_core : Core record010 where
  matrix := record010_matrix_checked
  valid := record010_validity
  literal := record010_literal
  nodes := record010_raw_node_checks record010_validity
  leaf_nodup := record010_leaves_nodup
  frames := record010_frames_supported record010_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record010_certificates, record010_leaf_certificates_checked⟩

theorem record010_parameters : Parameters record010 (rowOfCode 29) 29181752640128 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29181752640128 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15422 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29181752640128
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch154.candidate15422_checked

theorem record010_result : Result (29, 29181752640128) :=
  of_small 29 29181752640128 (by decide) ⟨record010, record010_core, record010_parameters, record010_coverage⟩
#print axioms record010_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209
