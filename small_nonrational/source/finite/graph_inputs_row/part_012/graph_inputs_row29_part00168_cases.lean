module
prelude
public import GraphInputsRow29Part00168Checked
public import GraphInputsRow29Part00168Metadata
public import GraphInputsRow29Part00168Frames
public import GraphInputsRow29Part00168Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch118
public import GraphCoverageBatch152


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00168
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

theorem record000_parameters : Parameters record000 (rowOfCode 29) 25574418432256 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25574418432256 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15255 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25574418432256
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch152.candidate15255_checked

theorem record000_result : Result (29, 25574418432256) :=
  of_small 29 25574418432256 (by decide) ⟨record000, record000_core, record000_parameters, record000_coverage⟩
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

theorem record001_parameters : Parameters record001 (rowOfCode 29) 25575054393344 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25575054393344 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15256 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25575054393344
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch152.candidate15256_checked

theorem record001_result : Result (29, 25575054393344) :=
  of_small 29 25575054393344 (by decide) ⟨record001, record001_core, record001_parameters, record001_coverage⟩
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

theorem record002_parameters : Parameters record002 (rowOfCode 29) 25576564867328 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25576564867328 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11836 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25576564867328
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch118.candidate11836_checked

theorem record002_result : Result (29, 25576564867328) :=
  of_small 29 25576564867328 (by decide) ⟨record002, record002_core, record002_parameters, record002_coverage⟩
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

theorem record003_parameters : Parameters record003 (rowOfCode 29) 25582106574848 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25582106574848 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11837 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25582106574848
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch118.candidate11837_checked

theorem record003_result : Result (29, 25582106574848) :=
  of_small 29 25582106574848 (by decide) ⟨record003, record003_core, record003_parameters, record003_coverage⟩
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

theorem record004_parameters : Parameters record004 (rowOfCode 29) 25582236614656 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25582236614656 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15257 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25582236614656
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch152.candidate15257_checked

theorem record004_result : Result (29, 25582236614656) :=
  of_small 29 25582236614656 (by decide) ⟨record004, record004_core, record004_parameters, record004_coverage⟩
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

theorem record005_parameters : Parameters record005 (rowOfCode 29) 25582302674944 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25582302674944 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11838 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25582302674944
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch118.candidate11838_checked

theorem record005_result : Result (29, 25582302674944) :=
  of_small 29 25582302674944 (by decide) ⟨record005, record005_core, record005_parameters, record005_coverage⟩
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

theorem record006_parameters : Parameters record006 (rowOfCode 29) 25583375892480 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25583375892480 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11839 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25583375892480
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch118.candidate11839_checked

theorem record006_result : Result (29, 25583375892480) :=
  of_small 29 25583375892480 (by decide) ⟨record006, record006_core, record006_parameters, record006_coverage⟩
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

theorem record007_parameters : Parameters record007 (rowOfCode 29) 25589449769024 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25589449769024 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15258 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25589449769024
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch152.candidate15258_checked

theorem record007_result : Result (29, 25589449769024) :=
  of_small 29 25589449769024 (by decide) ⟨record007, record007_core, record007_parameters, record007_coverage⟩
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

theorem record008_parameters : Parameters record008 (rowOfCode 29) 25610890133760 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25610890133760 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15259 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25610890133760
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch152.candidate15259_checked

theorem record008_result : Result (29, 25610890133760) :=
  of_small 29 25610890133760 (by decide) ⟨record008, record008_core, record008_parameters, record008_coverage⟩
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

theorem record009_parameters : Parameters record009 (rowOfCode 29) 25611561075200 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25611561075200 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15260 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25611561075200
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch152.candidate15260_checked

theorem record009_result : Result (29, 25611561075200) :=
  of_small 29 25611561075200 (by decide) ⟨record009, record009_core, record009_parameters, record009_coverage⟩
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

theorem record010_parameters : Parameters record010 (rowOfCode 29) 25623775035456 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25623775035456 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15261 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25623775035456
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch152.candidate15261_checked

theorem record010_result : Result (29, 25623775035456) :=
  of_small 29 25623775035456 (by decide) ⟨record010, record010_core, record010_parameters, record010_coverage⟩
#print axioms record010_result

theorem record011_core : Core record011 where
  matrix := record011_matrix_checked
  valid := record011_validity
  literal := record011_literal
  nodes := record011_raw_node_checks record011_validity
  leaf_nodup := record011_leaves_nodup
  frames := record011_frames_supported record011_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record011_certificates, record011_leaf_certificates_checked⟩

theorem record011_parameters : Parameters record011 (rowOfCode 29) 25642097770496 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record011_coverage : Coverage record011 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25642097770496 :=
  GraphCoverageDescriptions.coverage_of_checked record011 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11840 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25642097770496
    (by rfl) record011_cells_exact
    (GraphCoverageDescriptions.small_allowed record011 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch118.candidate11840_checked

theorem record011_result : Result (29, 25642097770496) :=
  of_small 29 25642097770496 (by decide) ⟨record011, record011_core, record011_parameters, record011_coverage⟩
#print axioms record011_result

theorem record012_core : Core record012 where
  matrix := record012_matrix_checked
  valid := record012_validity
  literal := record012_literal
  nodes := record012_raw_node_checks record012_validity
  leaf_nodup := record012_leaves_nodup
  frames := record012_frames_supported record012_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record012_certificates, record012_leaf_certificates_checked⟩

theorem record012_parameters : Parameters record012 (rowOfCode 29) 25658134765632 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record012_coverage : Coverage record012 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25658134765632 :=
  GraphCoverageDescriptions.coverage_of_checked record012 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15262 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25658134765632
    (by rfl) record012_cells_exact
    (GraphCoverageDescriptions.small_allowed record012 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch152.candidate15262_checked

theorem record012_result : Result (29, 25658134765632) :=
  of_small 29 25658134765632 (by decide) ⟨record012, record012_core, record012_parameters, record012_coverage⟩
#print axioms record012_result

theorem record013_core : Core record013 where
  matrix := record013_matrix_checked
  valid := record013_validity
  literal := record013_literal
  nodes := record013_raw_node_checks record013_validity
  leaf_nodup := record013_leaves_nodup
  frames := record013_frames_supported record013_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record013_certificates, record013_leaf_certificates_checked⟩

theorem record013_parameters : Parameters record013 (rowOfCode 29) 25659277574144 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record013_coverage : Coverage record013 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25659277574144 :=
  GraphCoverageDescriptions.coverage_of_checked record013 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11841 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25659277574144
    (by rfl) record013_cells_exact
    (GraphCoverageDescriptions.small_allowed record013 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch118.candidate11841_checked

theorem record013_result : Result (29, 25659277574144) :=
  of_small 29 25659277574144 (by decide) ⟨record013, record013_core, record013_parameters, record013_coverage⟩
#print axioms record013_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00168
