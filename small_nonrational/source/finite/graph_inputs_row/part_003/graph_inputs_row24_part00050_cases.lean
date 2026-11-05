module
prelude
public import GraphInputsRow24Part00050Checked
public import GraphInputsRow24Part00050Metadata
public import GraphInputsRow24Part00050Frames
public import GraphInputsRow24Part00050Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch080
public import GraphCoverageBatch081


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00050
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

theorem record000_parameters : Parameters record000 (rowOfCode 24) 19612768927744 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19612768927744 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08089 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19612768927744
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch080.candidate08089_checked

theorem record000_result : Result (24, 19612768927744) :=
  of_small 24 19612768927744 (by decide) ⟨record000, record000_core, record000_parameters, record000_coverage⟩
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

theorem record001_parameters : Parameters record001 (rowOfCode 24) 19619570286848 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19619570286848 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08090 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19619570286848
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch080.candidate08090_checked

theorem record001_result : Result (24, 19619570286848) :=
  of_small 24 19619570286848 (by decide) ⟨record001, record001_core, record001_parameters, record001_coverage⟩
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

theorem record002_parameters : Parameters record002 (rowOfCode 24) 19619974744192 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19619974744192 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08091 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19619974744192
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch080.candidate08091_checked

theorem record002_result : Result (24, 19619974744192) :=
  of_small 24 19619974744192 (by decide) ⟨record002, record002_core, record002_parameters, record002_coverage⟩
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

theorem record003_parameters : Parameters record003 (rowOfCode 24) 19623995048192 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19623995048192 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08092 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19623995048192
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch080.candidate08092_checked

theorem record003_result : Result (24, 19623995048192) :=
  of_small 24 19623995048192 (by decide) ⟨record003, record003_core, record003_parameters, record003_coverage⟩
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

theorem record004_parameters : Parameters record004 (rowOfCode 24) 19624003436544 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19624003436544 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08093 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19624003436544
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch080.candidate08093_checked

theorem record004_result : Result (24, 19624003436544) :=
  of_small 24 19624003436544 (by decide) ⟨record004, record004_core, record004_parameters, record004_coverage⟩
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

theorem record005_parameters : Parameters record005 (rowOfCode 24) 19624523466752 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19624523466752 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08094 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19624523466752
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch080.candidate08094_checked

theorem record005_result : Result (24, 19624523466752) :=
  of_small 24 19624523466752 (by decide) ⟨record005, record005_core, record005_parameters, record005_coverage⟩
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

theorem record006_parameters : Parameters record006 (rowOfCode 24) 19628287918336 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19628287918336 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08095 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19628287918336
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch080.candidate08095_checked

theorem record006_result : Result (24, 19628287918336) :=
  of_small 24 19628287918336 (by decide) ⟨record006, record006_core, record006_parameters, record006_coverage⟩
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

theorem record007_parameters : Parameters record007 (rowOfCode 24) 19628296306688 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19628296306688 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08096 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19628296306688
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch080.candidate08096_checked

theorem record007_result : Result (24, 19628296306688) :=
  of_small 24 19628296306688 (by decide) ⟨record007, record007_core, record007_parameters, record007_coverage⟩
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

theorem record008_parameters : Parameters record008 (rowOfCode 24) 19628403523840 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19628403523840 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08097 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19628403523840
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch080.candidate08097_checked

theorem record008_result : Result (24, 19628403523840) :=
  of_small 24 19628403523840 (by decide) ⟨record008, record008_core, record008_parameters, record008_coverage⟩
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

theorem record009_parameters : Parameters record009 (rowOfCode 24) 19628556321024 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19628556321024 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08098 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19628556321024
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch080.candidate08098_checked

theorem record009_result : Result (24, 19628556321024) :=
  of_small 24 19628556321024 (by decide) ⟨record009, record009_core, record009_parameters, record009_coverage⟩
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

theorem record010_parameters : Parameters record010 (rowOfCode 24) 19628560547840 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19628560547840 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08099 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19628560547840
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch080.candidate08099_checked

theorem record010_result : Result (24, 19628560547840) :=
  of_small 24 19628560547840 (by decide) ⟨record010, record010_core, record010_parameters, record010_coverage⟩
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

theorem record011_parameters : Parameters record011 (rowOfCode 24) 19628566790144 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record011_coverage : Coverage record011 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19628566790144 :=
  GraphCoverageDescriptions.coverage_of_checked record011 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08100 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19628566790144
    (by rfl) record011_cells_exact
    (GraphCoverageDescriptions.small_allowed record011 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch081.candidate08100_checked

theorem record011_result : Result (24, 19628566790144) :=
  of_small 24 19628566790144 (by decide) ⟨record011, record011_core, record011_parameters, record011_coverage⟩
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

theorem record012_parameters : Parameters record012 (rowOfCode 24) 19628671926528 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record012_coverage : Coverage record012 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19628671926528 :=
  GraphCoverageDescriptions.coverage_of_checked record012 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08101 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19628671926528
    (by rfl) record012_cells_exact
    (GraphCoverageDescriptions.small_allowed record012 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch081.candidate08101_checked

theorem record012_result : Result (24, 19628671926528) :=
  of_small 24 19628671926528 (by decide) ⟨record012, record012_core, record012_parameters, record012_coverage⟩
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

theorem record013_parameters : Parameters record013 (rowOfCode 24) 19628684216320 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record013_coverage : Coverage record013 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19628684216320 :=
  GraphCoverageDescriptions.coverage_of_checked record013 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08102 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19628684216320
    (by rfl) record013_cells_exact
    (GraphCoverageDescriptions.small_allowed record013 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch081.candidate08102_checked

theorem record013_result : Result (24, 19628684216320) :=
  of_small 24 19628684216320 (by decide) ⟨record013, record013_core, record013_parameters, record013_coverage⟩
#print axioms record013_result

theorem record014_core : Core record014 where
  matrix := record014_matrix_checked
  valid := record014_validity
  literal := record014_literal
  nodes := record014_raw_node_checks record014_validity
  leaf_nodup := record014_leaves_nodup
  frames := record014_frames_supported record014_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record014_certificates, record014_leaf_certificates_checked⟩

theorem record014_parameters : Parameters record014 (rowOfCode 24) 19628806127872 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record014_coverage : Coverage record014 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19628806127872 :=
  GraphCoverageDescriptions.coverage_of_checked record014 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08103 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19628806127872
    (by rfl) record014_cells_exact
    (GraphCoverageDescriptions.small_allowed record014 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch081.candidate08103_checked

theorem record014_result : Result (24, 19628806127872) :=
  of_small 24 19628806127872 (by decide) ⟨record014, record014_core, record014_parameters, record014_coverage⟩
#print axioms record014_result

theorem record015_core : Core record015 where
  matrix := record015_matrix_checked
  valid := record015_validity
  literal := record015_literal
  nodes := record015_raw_node_checks record015_validity
  leaf_nodup := record015_leaves_nodup
  frames := record015_frames_supported record015_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record015_certificates, record015_leaf_certificates_checked⟩

theorem record015_parameters : Parameters record015 (rowOfCode 24) 19632970858496 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record015_coverage : Coverage record015 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19632970858496 :=
  GraphCoverageDescriptions.coverage_of_checked record015 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08104 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19632970858496
    (by rfl) record015_cells_exact
    (GraphCoverageDescriptions.small_allowed record015 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch081.candidate08104_checked

theorem record015_result : Result (24, 19632970858496) :=
  of_small 24 19632970858496 (by decide) ⟨record015, record015_core, record015_parameters, record015_coverage⟩
#print axioms record015_result

theorem record016_core : Core record016 where
  matrix := record016_matrix_checked
  valid := record016_validity
  literal := record016_literal
  nodes := record016_raw_node_checks record016_validity
  leaf_nodup := record016_leaves_nodup
  frames := record016_frames_supported record016_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record016_certificates, record016_leaf_certificates_checked⟩

theorem record016_parameters : Parameters record016 (rowOfCode 24) 19636733216896 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record016_coverage : Coverage record016 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19636733216896 :=
  GraphCoverageDescriptions.coverage_of_checked record016 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08105 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19636733216896
    (by rfl) record016_cells_exact
    (GraphCoverageDescriptions.small_allowed record016 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch081.candidate08105_checked

theorem record016_result : Result (24, 19636733216896) :=
  of_small 24 19636733216896 (by decide) ⟨record016, record016_core, record016_parameters, record016_coverage⟩
#print axioms record016_result

theorem record017_core : Core record017 where
  matrix := record017_matrix_checked
  valid := record017_validity
  literal := record017_literal
  nodes := record017_raw_node_checks record017_validity
  leaf_nodup := record017_leaves_nodup
  frames := record017_frames_supported record017_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record017_certificates, record017_leaf_certificates_checked⟩

theorem record017_parameters : Parameters record017 (rowOfCode 24) 19645985718848 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record017_coverage : Coverage record017 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19645985718848 :=
  GraphCoverageDescriptions.coverage_of_checked record017 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08106 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19645985718848
    (by rfl) record017_cells_exact
    (GraphCoverageDescriptions.small_allowed record017 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch081.candidate08106_checked

theorem record017_result : Result (24, 19645985718848) :=
  of_small 24 19645985718848 (by decide) ⟨record017, record017_core, record017_parameters, record017_coverage⟩
#print axioms record017_result

theorem record018_core : Core record018 where
  matrix := record018_matrix_checked
  valid := record018_validity
  literal := record018_literal
  nodes := record018_raw_node_checks record018_validity
  leaf_nodup := record018_leaves_nodup
  frames := record018_frames_supported record018_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record018_certificates, record018_leaf_certificates_checked⟩

theorem record018_parameters : Parameters record018 (rowOfCode 24) 19646004592640 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record018_coverage : Coverage record018 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19646004592640 :=
  GraphCoverageDescriptions.coverage_of_checked record018 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08107 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19646004592640
    (by rfl) record018_cells_exact
    (GraphCoverageDescriptions.small_allowed record018 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch081.candidate08107_checked

theorem record018_result : Result (24, 19646004592640) :=
  of_small 24 19646004592640 (by decide) ⟨record018, record018_core, record018_parameters, record018_coverage⟩
#print axioms record018_result

theorem record019_core : Core record019 where
  matrix := record019_matrix_checked
  valid := record019_validity
  literal := record019_literal
  nodes := record019_raw_node_checks record019_validity
  leaf_nodup := record019_leaves_nodup
  frames := record019_frames_supported record019_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record019_certificates, record019_leaf_certificates_checked⟩

theorem record019_parameters : Parameters record019 (rowOfCode 24) 19649744011264 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record019_coverage : Coverage record019 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19649744011264 :=
  GraphCoverageDescriptions.coverage_of_checked record019 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08108 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19649744011264
    (by rfl) record019_cells_exact
    (GraphCoverageDescriptions.small_allowed record019 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch081.candidate08108_checked

theorem record019_result : Result (24, 19649744011264) :=
  of_small 24 19649744011264 (by decide) ⟨record019, record019_core, record019_parameters, record019_coverage⟩
#print axioms record019_result

theorem record020_core : Core record020 where
  matrix := record020_matrix_checked
  valid := record020_validity
  literal := record020_literal
  nodes := record020_raw_node_checks record020_validity
  leaf_nodup := record020_leaves_nodup
  frames := record020_frames_supported record020_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record020_certificates, record020_leaf_certificates_checked⟩

theorem record020_parameters : Parameters record020 (rowOfCode 24) 19649752334336 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record020_coverage : Coverage record020 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19649752334336 :=
  GraphCoverageDescriptions.coverage_of_checked record020 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08109 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19649752334336
    (by rfl) record020_cells_exact
    (GraphCoverageDescriptions.small_allowed record020 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch081.candidate08109_checked

theorem record020_result : Result (24, 19649752334336) :=
  of_small 24 19649752334336 (by decide) ⟨record020, record020_core, record020_parameters, record020_coverage⟩
#print axioms record020_result

theorem record021_core : Core record021 where
  matrix := record021_matrix_checked
  valid := record021_validity
  literal := record021_literal
  nodes := record021_raw_node_checks record021_validity
  leaf_nodup := record021_leaves_nodup
  frames := record021_frames_supported record021_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record021_certificates, record021_leaf_certificates_checked⟩

theorem record021_parameters : Parameters record021 (rowOfCode 24) 19650280686080 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record021_coverage : Coverage record021 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19650280686080 :=
  GraphCoverageDescriptions.coverage_of_checked record021 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08110 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19650280686080
    (by rfl) record021_cells_exact
    (GraphCoverageDescriptions.small_allowed record021 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch081.candidate08110_checked

theorem record021_result : Result (24, 19650280686080) :=
  of_small 24 19650280686080 (by decide) ⟨record021, record021_core, record021_parameters, record021_coverage⟩
#print axioms record021_result

theorem record022_core : Core record022 where
  matrix := record022_matrix_checked
  valid := record022_validity
  literal := record022_literal
  nodes := record022_raw_node_checks record022_validity
  leaf_nodup := record022_leaves_nodup
  frames := record022_frames_supported record022_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record022_certificates, record022_leaf_certificates_checked⟩

theorem record022_parameters : Parameters record022 (rowOfCode 24) 19657404776448 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record022_coverage : Coverage record022 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19657404776448 :=
  GraphCoverageDescriptions.coverage_of_checked record022 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08111 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19657404776448
    (by rfl) record022_cells_exact
    (GraphCoverageDescriptions.small_allowed record022 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch081.candidate08111_checked

theorem record022_result : Result (24, 19657404776448) :=
  of_small 24 19657404776448 (by decide) ⟨record022, record022_core, record022_parameters, record022_coverage⟩
#print axioms record022_result

theorem record023_core : Core record023 where
  matrix := record023_matrix_checked
  valid := record023_validity
  literal := record023_literal
  nodes := record023_raw_node_checks record023_validity
  leaf_nodup := record023_leaves_nodup
  frames := record023_frames_supported record023_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record023_certificates, record023_leaf_certificates_checked⟩

theorem record023_parameters : Parameters record023 (rowOfCode 24) 19657664790784 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record023_coverage : Coverage record023 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19657664790784 :=
  GraphCoverageDescriptions.coverage_of_checked record023 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08112 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19657664790784
    (by rfl) record023_cells_exact
    (GraphCoverageDescriptions.small_allowed record023 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch081.candidate08112_checked

theorem record023_result : Result (24, 19657664790784) :=
  of_small 24 19657664790784 (by decide) ⟨record023, record023_core, record023_parameters, record023_coverage⟩
#print axioms record023_result

theorem record024_core : Core record024 where
  matrix := record024_matrix_checked
  valid := record024_validity
  literal := record024_literal
  nodes := record024_raw_node_checks record024_validity
  leaf_nodup := record024_leaves_nodup
  frames := record024_frames_supported record024_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record024_certificates, record024_leaf_certificates_checked⟩

theorem record024_parameters : Parameters record024 (rowOfCode 24) 19657675259904 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record024_coverage : Coverage record024 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19657675259904 :=
  GraphCoverageDescriptions.coverage_of_checked record024 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08113 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19657675259904
    (by rfl) record024_cells_exact
    (GraphCoverageDescriptions.small_allowed record024 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch081.candidate08113_checked

theorem record024_result : Result (24, 19657675259904) :=
  of_small 24 19657675259904 (by decide) ⟨record024, record024_core, record024_parameters, record024_coverage⟩
#print axioms record024_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00050
