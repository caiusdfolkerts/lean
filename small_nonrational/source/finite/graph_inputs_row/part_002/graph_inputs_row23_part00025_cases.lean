module
prelude
public import GraphInputsRow23Part00025Checked
public import GraphInputsRow23Part00025Metadata
public import GraphInputsRow23Part00025Frames
public import GraphInputsRow23Part00025Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch058
public import GraphCoverageBatch059


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025
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

theorem record000_parameters : Parameters record000 (rowOfCode 23) 30943897722944 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 30943897722944 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch058.candidate05886 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 30943897722944
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch058.candidate05886_checked

theorem record000_result : Result (23, 30943897722944) :=
  of_small 23 30943897722944 (by decide) ⟨record000, record000_core, record000_parameters, record000_coverage⟩
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

theorem record001_parameters : Parameters record001 (rowOfCode 23) 30969467830272 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 30969467830272 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch058.candidate05887 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 30969467830272
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch058.candidate05887_checked

theorem record001_result : Result (23, 30969467830272) :=
  of_small 23 30969467830272 (by decide) ⟨record001, record001_core, record001_parameters, record001_coverage⟩
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

theorem record002_parameters : Parameters record002 (rowOfCode 23) 31014027034880 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31014027034880 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch058.candidate05888 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31014027034880
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch058.candidate05888_checked

theorem record002_result : Result (23, 31014027034880) :=
  of_small 23 31014027034880 (by decide) ⟨record002, record002_core, record002_parameters, record002_coverage⟩
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

theorem record003_parameters : Parameters record003 (rowOfCode 23) 31014765207552 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31014765207552 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch058.candidate05889 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31014765207552
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch058.candidate05889_checked

theorem record003_result : Result (23, 31014765207552) :=
  of_small 23 31014765207552 (by decide) ⟨record003, record003_core, record003_parameters, record003_coverage⟩
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

theorem record004_parameters : Parameters record004 (rowOfCode 23) 31065793105952 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31065793105952 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch058.candidate05890 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31065793105952
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch058.candidate05890_checked

theorem record004_result : Result (23, 31065793105952) :=
  of_small 23 31065793105952 (by decide) ⟨record004, record004_core, record004_parameters, record004_coverage⟩
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

theorem record005_parameters : Parameters record005 (rowOfCode 23) 31065842651168 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31065842651168 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch058.candidate05891 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31065842651168
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch058.candidate05891_checked

theorem record005_result : Result (23, 31065842651168) :=
  of_small 23 31065842651168 (by decide) ⟨record005, record005_core, record005_parameters, record005_coverage⟩
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

theorem record006_parameters : Parameters record006 (rowOfCode 23) 31072344088832 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31072344088832 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch058.candidate05892 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31072344088832
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch058.candidate05892_checked

theorem record006_result : Result (23, 31072344088832) :=
  of_small 23 31072344088832 (by decide) ⟨record006, record006_core, record006_parameters, record006_coverage⟩
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

theorem record007_parameters : Parameters record007 (rowOfCode 23) 31099390558208 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31099390558208 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch058.candidate05893 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31099390558208
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch058.candidate05893_checked

theorem record007_result : Result (23, 31099390558208) :=
  of_small 23 31099390558208 (by decide) ⟨record007, record007_core, record007_parameters, record007_coverage⟩
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

theorem record008_parameters : Parameters record008 (rowOfCode 23) 31244345671680 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31244345671680 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch058.candidate05894 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31244345671680
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch058.candidate05894_checked

theorem record008_result : Result (23, 31244345671680) :=
  of_small 23 31244345671680 (by decide) ⟨record008, record008_core, record008_parameters, record008_coverage⟩
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

theorem record009_parameters : Parameters record009 (rowOfCode 23) 31337717702784 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31337717702784 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch058.candidate05895 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31337717702784
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch058.candidate05895_checked

theorem record009_result : Result (23, 31337717702784) :=
  of_small 23 31337717702784 (by decide) ⟨record009, record009_core, record009_parameters, record009_coverage⟩
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

theorem record010_parameters : Parameters record010 (rowOfCode 23) 31346316574976 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31346316574976 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch058.candidate05896 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31346316574976
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch058.candidate05896_checked

theorem record010_result : Result (23, 31346316574976) :=
  of_small 23 31346316574976 (by decide) ⟨record010, record010_core, record010_parameters, record010_coverage⟩
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

theorem record011_parameters : Parameters record011 (rowOfCode 23) 31346328084480 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record011_coverage : Coverage record011 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31346328084480 :=
  GraphCoverageDescriptions.coverage_of_checked record011 GraphCoverageDescriptions.GraphCoverageBatch058.candidate05897 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31346328084480
    (by rfl) record011_cells_exact
    (GraphCoverageDescriptions.small_allowed record011 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch058.candidate05897_checked

theorem record011_result : Result (23, 31346328084480) :=
  of_small 23 31346328084480 (by decide) ⟨record011, record011_core, record011_parameters, record011_coverage⟩
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

theorem record012_parameters : Parameters record012 (rowOfCode 23) 31414535913728 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record012_coverage : Coverage record012 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31414535913728 :=
  GraphCoverageDescriptions.coverage_of_checked record012 GraphCoverageDescriptions.GraphCoverageBatch058.candidate05898 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31414535913728
    (by rfl) record012_cells_exact
    (GraphCoverageDescriptions.small_allowed record012 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch058.candidate05898_checked

theorem record012_result : Result (23, 31414535913728) :=
  of_small 23 31414535913728 (by decide) ⟨record012, record012_core, record012_parameters, record012_coverage⟩
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

theorem record013_parameters : Parameters record013 (rowOfCode 23) 31414808543232 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record013_coverage : Coverage record013 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31414808543232 :=
  GraphCoverageDescriptions.coverage_of_checked record013 GraphCoverageDescriptions.GraphCoverageBatch058.candidate05899 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31414808543232
    (by rfl) record013_cells_exact
    (GraphCoverageDescriptions.small_allowed record013 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch058.candidate05899_checked

theorem record013_result : Result (23, 31414808543232) :=
  of_small 23 31414808543232 (by decide) ⟨record013, record013_core, record013_parameters, record013_coverage⟩
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

theorem record014_parameters : Parameters record014 (rowOfCode 23) 31415072784384 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record014_coverage : Coverage record014 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31415072784384 :=
  GraphCoverageDescriptions.coverage_of_checked record014 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05900 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31415072784384
    (by rfl) record014_cells_exact
    (GraphCoverageDescriptions.small_allowed record014 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05900_checked

theorem record014_result : Result (23, 31415072784384) :=
  of_small 23 31415072784384 (by decide) ⟨record014, record014_core, record014_parameters, record014_coverage⟩
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

theorem record015_parameters : Parameters record015 (rowOfCode 23) 31415081107456 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record015_coverage : Coverage record015 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31415081107456 :=
  GraphCoverageDescriptions.coverage_of_checked record015 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05901 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31415081107456
    (by rfl) record015_cells_exact
    (GraphCoverageDescriptions.small_allowed record015 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05901_checked

theorem record015_result : Result (23, 31415081107456) :=
  of_small 23 31415081107456 (by decide) ⟨record015, record015_core, record015_parameters, record015_coverage⟩
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

theorem record016_parameters : Parameters record016 (rowOfCode 23) 31415270965248 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record016_coverage : Coverage record016 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31415270965248 :=
  GraphCoverageDescriptions.coverage_of_checked record016 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05902 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31415270965248
    (by rfl) record016_cells_exact
    (GraphCoverageDescriptions.small_allowed record016 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05902_checked

theorem record016_result : Result (23, 31415270965248) :=
  of_small 23 31415270965248 (by decide) ⟨record016, record016_core, record016_parameters, record016_coverage⟩
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

theorem record017_parameters : Parameters record017 (rowOfCode 23) 31430605308160 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record017_coverage : Coverage record017 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31430605308160 :=
  GraphCoverageDescriptions.coverage_of_checked record017 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05903 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31430605308160
    (by rfl) record017_cells_exact
    (GraphCoverageDescriptions.small_allowed record017 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05903_checked

theorem record017_result : Result (23, 31430605308160) :=
  of_small 23 31430605308160 (by decide) ⟨record017, record017_core, record017_parameters, record017_coverage⟩
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

theorem record018_parameters : Parameters record018 (rowOfCode 23) 31431376510976 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record018_coverage : Coverage record018 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31431376510976 :=
  GraphCoverageDescriptions.coverage_of_checked record018 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05904 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31431376510976
    (by rfl) record018_cells_exact
    (GraphCoverageDescriptions.small_allowed record018 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05904_checked

theorem record018_result : Result (23, 31431376510976) :=
  of_small 23 31431376510976 (by decide) ⟨record018, record018_core, record018_parameters, record018_coverage⟩
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

theorem record019_parameters : Parameters record019 (rowOfCode 23) 31441580785920 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record019_coverage : Coverage record019 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31441580785920 :=
  GraphCoverageDescriptions.coverage_of_checked record019 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05905 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31441580785920
    (by rfl) record019_cells_exact
    (GraphCoverageDescriptions.small_allowed record019 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05905_checked

theorem record019_result : Result (23, 31441580785920) :=
  of_small 23 31441580785920 (by decide) ⟨record019, record019_core, record019_parameters, record019_coverage⟩
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

theorem record020_parameters : Parameters record020 (rowOfCode 23) 31448308449280 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record020_coverage : Coverage record020 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31448308449280 :=
  GraphCoverageDescriptions.coverage_of_checked record020 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05906 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31448308449280
    (by rfl) record020_cells_exact
    (GraphCoverageDescriptions.small_allowed record020 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05906_checked

theorem record020_result : Result (23, 31448308449280) :=
  of_small 23 31448308449280 (by decide) ⟨record020, record020_core, record020_parameters, record020_coverage⟩
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

theorem record021_parameters : Parameters record021 (rowOfCode 23) 31448316772352 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record021_coverage : Coverage record021 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31448316772352 :=
  GraphCoverageDescriptions.coverage_of_checked record021 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05907 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31448316772352
    (by rfl) record021_cells_exact
    (GraphCoverageDescriptions.small_allowed record021 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05907_checked

theorem record021_result : Result (23, 31448316772352) :=
  of_small 23 31448316772352 (by decide) ⟨record021, record021_core, record021_parameters, record021_coverage⟩
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

theorem record022_parameters : Parameters record022 (rowOfCode 23) 31450174914560 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record022_coverage : Coverage record022 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31450174914560 :=
  GraphCoverageDescriptions.coverage_of_checked record022 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05908 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31450174914560
    (by rfl) record022_cells_exact
    (GraphCoverageDescriptions.small_allowed record022 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05908_checked

theorem record022_result : Result (23, 31450174914560) :=
  of_small 23 31450174914560 (by decide) ⟨record022, record022_core, record022_parameters, record022_coverage⟩
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

theorem record023_parameters : Parameters record023 (rowOfCode 23) 31450711719936 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record023_coverage : Coverage record023 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31450711719936 :=
  GraphCoverageDescriptions.coverage_of_checked record023 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05909 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31450711719936
    (by rfl) record023_cells_exact
    (GraphCoverageDescriptions.small_allowed record023 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05909_checked

theorem record023_result : Result (23, 31450711719936) :=
  of_small 23 31450711719936 (by decide) ⟨record023, record023_core, record023_parameters, record023_coverage⟩
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

theorem record024_parameters : Parameters record024 (rowOfCode 23) 31465001779200 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record024_coverage : Coverage record024 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31465001779200 :=
  GraphCoverageDescriptions.coverage_of_checked record024 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05910 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31465001779200
    (by rfl) record024_cells_exact
    (GraphCoverageDescriptions.small_allowed record024 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05910_checked

theorem record024_result : Result (23, 31465001779200) :=
  of_small 23 31465001779200 (by decide) ⟨record024, record024_core, record024_parameters, record024_coverage⟩
#print axioms record024_result

theorem record025_core : Core record025 where
  matrix := record025_matrix_checked
  valid := record025_validity
  literal := record025_literal
  nodes := record025_raw_node_checks record025_validity
  leaf_nodup := record025_leaves_nodup
  frames := record025_frames_supported record025_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record025_certificates, record025_leaf_certificates_checked⟩

theorem record025_parameters : Parameters record025 (rowOfCode 23) 31465736765440 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record025_coverage : Coverage record025 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31465736765440 :=
  GraphCoverageDescriptions.coverage_of_checked record025 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05911 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31465736765440
    (by rfl) record025_cells_exact
    (GraphCoverageDescriptions.small_allowed record025 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05911_checked

theorem record025_result : Result (23, 31465736765440) :=
  of_small 23 31465736765440 (by decide) ⟨record025, record025_core, record025_parameters, record025_coverage⟩
#print axioms record025_result

theorem record026_core : Core record026 where
  matrix := record026_matrix_checked
  valid := record026_validity
  literal := record026_literal
  nodes := record026_raw_node_checks record026_validity
  leaf_nodup := record026_leaves_nodup
  frames := record026_frames_supported record026_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record026_certificates, record026_leaf_certificates_checked⟩

theorem record026_parameters : Parameters record026 (rowOfCode 23) 31482672848896 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record026_coverage : Coverage record026 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31482672848896 :=
  GraphCoverageDescriptions.coverage_of_checked record026 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05912 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31482672848896
    (by rfl) record026_cells_exact
    (GraphCoverageDescriptions.small_allowed record026 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05912_checked

theorem record026_result : Result (23, 31482672848896) :=
  of_small 23 31482672848896 (by decide) ⟨record026, record026_core, record026_parameters, record026_coverage⟩
#print axioms record026_result

theorem record027_core : Core record027 where
  matrix := record027_matrix_checked
  valid := record027_validity
  literal := record027_literal
  nodes := record027_raw_node_checks record027_validity
  leaf_nodup := record027_leaves_nodup
  frames := record027_frames_supported record027_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record027_certificates, record027_leaf_certificates_checked⟩

theorem record027_parameters : Parameters record027 (rowOfCode 23) 31483729420288 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record027_coverage : Coverage record027 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31483729420288 :=
  GraphCoverageDescriptions.coverage_of_checked record027 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05913 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31483729420288
    (by rfl) record027_cells_exact
    (GraphCoverageDescriptions.small_allowed record027 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05913_checked

theorem record027_result : Result (23, 31483729420288) :=
  of_small 23 31483729420288 (by decide) ⟨record027, record027_core, record027_parameters, record027_coverage⟩
#print axioms record027_result

theorem record028_core : Core record028 where
  matrix := record028_matrix_checked
  valid := record028_validity
  literal := record028_literal
  nodes := record028_raw_node_checks record028_validity
  leaf_nodup := record028_leaves_nodup
  frames := record028_frames_supported record028_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record028_certificates, record028_leaf_certificates_checked⟩

theorem record028_parameters : Parameters record028 (rowOfCode 23) 31491843195136 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record028_coverage : Coverage record028 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31491843195136 :=
  GraphCoverageDescriptions.coverage_of_checked record028 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05914 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31491843195136
    (by rfl) record028_cells_exact
    (GraphCoverageDescriptions.small_allowed record028 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05914_checked

theorem record028_result : Result (23, 31491843195136) :=
  of_small 23 31491843195136 (by decide) ⟨record028, record028_core, record028_parameters, record028_coverage⟩
#print axioms record028_result

theorem record029_core : Core record029 where
  matrix := record029_matrix_checked
  valid := record029_validity
  literal := record029_literal
  nodes := record029_raw_node_checks record029_validity
  leaf_nodup := record029_leaves_nodup
  frames := record029_frames_supported record029_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record029_certificates, record029_leaf_certificates_checked⟩

theorem record029_parameters : Parameters record029 (rowOfCode 23) 31492177723392 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record029_coverage : Coverage record029 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31492177723392 :=
  GraphCoverageDescriptions.coverage_of_checked record029 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05915 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31492177723392
    (by rfl) record029_cells_exact
    (GraphCoverageDescriptions.small_allowed record029 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05915_checked

theorem record029_result : Result (23, 31492177723392) :=
  of_small 23 31492177723392 (by decide) ⟨record029, record029_core, record029_parameters, record029_coverage⟩
#print axioms record029_result

theorem record030_core : Core record030 where
  matrix := record030_matrix_checked
  valid := record030_validity
  literal := record030_literal
  nodes := record030_raw_node_checks record030_validity
  leaf_nodup := record030_leaves_nodup
  frames := record030_frames_supported record030_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record030_certificates, record030_leaf_certificates_checked⟩

theorem record030_parameters : Parameters record030 (rowOfCode 23) 31495029817600 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record030_coverage : Coverage record030 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31495029817600 :=
  GraphCoverageDescriptions.coverage_of_checked record030 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05916 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31495029817600
    (by rfl) record030_cells_exact
    (GraphCoverageDescriptions.small_allowed record030 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05916_checked

theorem record030_result : Result (23, 31495029817600) :=
  of_small 23 31495029817600 (by decide) ⟨record030, record030_core, record030_parameters, record030_coverage⟩
#print axioms record030_result

theorem record031_core : Core record031 where
  matrix := record031_matrix_checked
  valid := record031_validity
  literal := record031_literal
  nodes := record031_raw_node_checks record031_validity
  leaf_nodup := record031_leaves_nodup
  frames := record031_frames_supported record031_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record031_certificates, record031_leaf_certificates_checked⟩

theorem record031_parameters : Parameters record031 (rowOfCode 23) 31495801020416 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record031_coverage : Coverage record031 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31495801020416 :=
  GraphCoverageDescriptions.coverage_of_checked record031 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05917 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31495801020416
    (by rfl) record031_cells_exact
    (GraphCoverageDescriptions.small_allowed record031 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05917_checked

theorem record031_result : Result (23, 31495801020416) :=
  of_small 23 31495801020416 (by decide) ⟨record031, record031_core, record031_parameters, record031_coverage⟩
#print axioms record031_result

theorem record032_core : Core record032 where
  matrix := record032_matrix_checked
  valid := record032_validity
  literal := record032_literal
  nodes := record032_raw_node_checks record032_validity
  leaf_nodup := record032_leaves_nodup
  frames := record032_frames_supported record032_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record032_certificates, record032_leaf_certificates_checked⟩

theorem record032_parameters : Parameters record032 (rowOfCode 23) 31510166044928 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record032_coverage : Coverage record032 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31510166044928 :=
  GraphCoverageDescriptions.coverage_of_checked record032 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05918 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31510166044928
    (by rfl) record032_cells_exact
    (GraphCoverageDescriptions.small_allowed record032 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05918_checked

theorem record032_result : Result (23, 31510166044928) :=
  of_small 23 31510166044928 (by decide) ⟨record032, record032_core, record032_parameters, record032_coverage⟩
#print axioms record032_result

theorem record033_core : Core record033 where
  matrix := record033_matrix_checked
  valid := record033_validity
  literal := record033_literal
  nodes := record033_raw_node_checks record033_validity
  leaf_nodup := record033_leaves_nodup
  frames := record033_frames_supported record033_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record033_certificates, record033_leaf_certificates_checked⟩

theorem record033_parameters : Parameters record033 (rowOfCode 23) 31519296978944 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record033_coverage : Coverage record033 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31519296978944 :=
  GraphCoverageDescriptions.coverage_of_checked record033 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05919 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31519296978944
    (by rfl) record033_cells_exact
    (GraphCoverageDescriptions.small_allowed record033 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05919_checked

theorem record033_result : Result (23, 31519296978944) :=
  of_small 23 31519296978944 (by decide) ⟨record033, record033_core, record033_parameters, record033_coverage⟩
#print axioms record033_result

theorem record034_core : Core record034 where
  matrix := record034_matrix_checked
  valid := record034_validity
  literal := record034_literal
  nodes := record034_raw_node_checks record034_validity
  leaf_nodup := record034_leaves_nodup
  frames := record034_frames_supported record034_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record034_certificates, record034_leaf_certificates_checked⟩

theorem record034_parameters : Parameters record034 (rowOfCode 23) 31520840548352 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record034_coverage : Coverage record034 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31520840548352 :=
  GraphCoverageDescriptions.coverage_of_checked record034 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05920 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31520840548352
    (by rfl) record034_cells_exact
    (GraphCoverageDescriptions.small_allowed record034 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05920_checked

theorem record034_result : Result (23, 31520840548352) :=
  of_small 23 31520840548352 (by decide) ⟨record034, record034_core, record034_parameters, record034_coverage⟩
#print axioms record034_result

theorem record035_core : Core record035 where
  matrix := record035_matrix_checked
  valid := record035_validity
  literal := record035_literal
  nodes := record035_raw_node_checks record035_validity
  leaf_nodup := record035_leaves_nodup
  frames := record035_frames_supported record035_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record035_certificates, record035_leaf_certificates_checked⟩

theorem record035_parameters : Parameters record035 (rowOfCode 23) 31527345913856 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record035_coverage : Coverage record035 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31527345913856 :=
  GraphCoverageDescriptions.coverage_of_checked record035 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05921 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31527345913856
    (by rfl) record035_cells_exact
    (GraphCoverageDescriptions.small_allowed record035 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05921_checked

theorem record035_result : Result (23, 31527345913856) :=
  of_small 23 31527345913856 (by decide) ⟨record035, record035_core, record035_parameters, record035_coverage⟩
#print axioms record035_result

theorem record036_core : Core record036 where
  matrix := record036_matrix_checked
  valid := record036_validity
  literal := record036_literal
  nodes := record036_raw_node_checks record036_validity
  leaf_nodup := record036_leaves_nodup
  frames := record036_frames_supported record036_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record036_certificates, record036_leaf_certificates_checked⟩

theorem record036_parameters : Parameters record036 (rowOfCode 23) 31527618478080 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record036_coverage : Coverage record036 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31527618478080 :=
  GraphCoverageDescriptions.coverage_of_checked record036 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05922 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31527618478080
    (by rfl) record036_cells_exact
    (GraphCoverageDescriptions.small_allowed record036 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05922_checked

theorem record036_result : Result (23, 31527618478080) :=
  of_small 23 31527618478080 (by decide) ⟨record036, record036_core, record036_parameters, record036_coverage⟩
#print axioms record036_result

theorem record037_core : Core record037 where
  matrix := record037_matrix_checked
  valid := record037_validity
  literal := record037_literal
  nodes := record037_raw_node_checks record037_validity
  leaf_nodup := record037_leaves_nodup
  frames := record037_frames_supported record037_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record037_certificates, record037_leaf_certificates_checked⟩

theorem record037_parameters : Parameters record037 (rowOfCode 23) 31529426288640 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record037_coverage : Coverage record037 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31529426288640 :=
  GraphCoverageDescriptions.coverage_of_checked record037 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05923 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31529426288640
    (by rfl) record037_cells_exact
    (GraphCoverageDescriptions.small_allowed record037 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05923_checked

theorem record037_result : Result (23, 31529426288640) :=
  of_small 23 31529426288640 (by decide) ⟨record037, record037_core, record037_parameters, record037_coverage⟩
#print axioms record037_result

theorem record038_core : Core record038 where
  matrix := record038_matrix_checked
  valid := record038_validity
  literal := record038_literal
  nodes := record038_raw_node_checks record038_validity
  leaf_nodup := record038_leaves_nodup
  frames := record038_frames_supported record038_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record038_certificates, record038_leaf_certificates_checked⟩

theorem record038_parameters : Parameters record038 (rowOfCode 23) 31530160226816 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record038_coverage : Coverage record038 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31530160226816 :=
  GraphCoverageDescriptions.coverage_of_checked record038 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05924 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31530160226816
    (by rfl) record038_cells_exact
    (GraphCoverageDescriptions.small_allowed record038 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05924_checked

theorem record038_result : Result (23, 31530160226816) :=
  of_small 23 31530160226816 (by decide) ⟨record038, record038_core, record038_parameters, record038_coverage⟩
#print axioms record038_result

theorem record039_core : Core record039 where
  matrix := record039_matrix_checked
  valid := record039_validity
  literal := record039_literal
  nodes := record039_raw_node_checks record039_validity
  leaf_nodup := record039_leaves_nodup
  frames := record039_frames_supported record039_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record039_certificates, record039_leaf_certificates_checked⟩

theorem record039_parameters : Parameters record039 (rowOfCode 23) 31530161274880 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record039_coverage : Coverage record039 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31530161274880 :=
  GraphCoverageDescriptions.coverage_of_checked record039 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05925 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31530161274880
    (by rfl) record039_cells_exact
    (GraphCoverageDescriptions.small_allowed record039 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05925_checked

theorem record039_result : Result (23, 31530161274880) :=
  of_small 23 31530161274880 (by decide) ⟨record039, record039_core, record039_parameters, record039_coverage⟩
#print axioms record039_result

theorem record040_core : Core record040 where
  matrix := record040_matrix_checked
  valid := record040_validity
  literal := record040_literal
  nodes := record040_raw_node_checks record040_validity
  leaf_nodup := record040_leaves_nodup
  frames := record040_frames_supported record040_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record040_certificates, record040_leaf_certificates_checked⟩

theorem record040_parameters : Parameters record040 (rowOfCode 23) 31544458674432 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record040_coverage : Coverage record040 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31544458674432 :=
  GraphCoverageDescriptions.coverage_of_checked record040 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05926 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31544458674432
    (by rfl) record040_cells_exact
    (GraphCoverageDescriptions.small_allowed record040 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05926_checked

theorem record040_result : Result (23, 31544458674432) :=
  of_small 23 31544458674432 (by decide) ⟨record040, record040_core, record040_parameters, record040_coverage⟩
#print axioms record040_result

theorem record041_core : Core record041 where
  matrix := record041_matrix_checked
  valid := record041_validity
  literal := record041_literal
  nodes := record041_raw_node_checks record041_validity
  leaf_nodup := record041_leaves_nodup
  frames := record041_frames_supported record041_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record041_certificates, record041_leaf_certificates_checked⟩

theorem record041_parameters : Parameters record041 (rowOfCode 23) 31568077848576 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record041_coverage : Coverage record041 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31568077848576 :=
  GraphCoverageDescriptions.coverage_of_checked record041 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05927 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31568077848576
    (by rfl) record041_cells_exact
    (GraphCoverageDescriptions.small_allowed record041 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05927_checked

theorem record041_result : Result (23, 31568077848576) :=
  of_small 23 31568077848576 (by decide) ⟨record041, record041_core, record041_parameters, record041_coverage⟩
#print axioms record041_result

theorem record042_core : Core record042 where
  matrix := record042_matrix_checked
  valid := record042_validity
  literal := record042_literal
  nodes := record042_raw_node_checks record042_validity
  leaf_nodup := record042_leaves_nodup
  frames := record042_frames_supported record042_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record042_certificates, record042_leaf_certificates_checked⟩

theorem record042_parameters : Parameters record042 (rowOfCode 23) 31579023933440 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record042_coverage : Coverage record042 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31579023933440 :=
  GraphCoverageDescriptions.coverage_of_checked record042 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05928 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31579023933440
    (by rfl) record042_cells_exact
    (GraphCoverageDescriptions.small_allowed record042 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05928_checked

theorem record042_result : Result (23, 31579023933440) :=
  of_small 23 31579023933440 (by decide) ⟨record042, record042_core, record042_parameters, record042_coverage⟩
#print axioms record042_result

theorem record043_core : Core record043 where
  matrix := record043_matrix_checked
  valid := record043_validity
  literal := record043_literal
  nodes := record043_raw_node_checks record043_validity
  leaf_nodup := record043_leaves_nodup
  frames := record043_frames_supported record043_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record043_certificates, record043_leaf_certificates_checked⟩

theorem record043_parameters : Parameters record043 (rowOfCode 23) 31587882237952 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record043_coverage : Coverage record043 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31587882237952 :=
  GraphCoverageDescriptions.coverage_of_checked record043 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05929 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31587882237952
    (by rfl) record043_cells_exact
    (GraphCoverageDescriptions.small_allowed record043 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05929_checked

theorem record043_result : Result (23, 31587882237952) :=
  of_small 23 31587882237952 (by decide) ⟨record043, record043_core, record043_parameters, record043_coverage⟩
#print axioms record043_result

theorem record044_core : Core record044 where
  matrix := record044_matrix_checked
  valid := record044_validity
  literal := record044_literal
  nodes := record044_raw_node_checks record044_validity
  leaf_nodup := record044_leaves_nodup
  frames := record044_frames_supported record044_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record044_certificates, record044_leaf_certificates_checked⟩

theorem record044_parameters : Parameters record044 (rowOfCode 23) 31596203737088 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record044_coverage : Coverage record044 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31596203737088 :=
  GraphCoverageDescriptions.coverage_of_checked record044 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05930 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31596203737088
    (by rfl) record044_cells_exact
    (GraphCoverageDescriptions.small_allowed record044 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05930_checked

theorem record044_result : Result (23, 31596203737088) :=
  of_small 23 31596203737088 (by decide) ⟨record044, record044_core, record044_parameters, record044_coverage⟩
#print axioms record044_result

theorem record045_core : Core record045 where
  matrix := record045_matrix_checked
  valid := record045_validity
  literal := record045_literal
  nodes := record045_raw_node_checks record045_validity
  leaf_nodup := record045_leaves_nodup
  frames := record045_frames_supported record045_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record045_certificates, record045_leaf_certificates_checked⟩

theorem record045_parameters : Parameters record045 (rowOfCode 23) 31596732219392 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record045_coverage : Coverage record045 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31596732219392 :=
  GraphCoverageDescriptions.coverage_of_checked record045 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05931 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31596732219392
    (by rfl) record045_cells_exact
    (GraphCoverageDescriptions.small_allowed record045 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05931_checked

theorem record045_result : Result (23, 31596732219392) :=
  of_small 23 31596732219392 (by decide) ⟨record045, record045_core, record045_parameters, record045_coverage⟩
#print axioms record045_result

theorem record046_core : Core record046 where
  matrix := record046_matrix_checked
  valid := record046_validity
  literal := record046_literal
  nodes := record046_raw_node_checks record046_validity
  leaf_nodup := record046_leaves_nodup
  frames := record046_frames_supported record046_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record046_certificates, record046_leaf_certificates_checked⟩

theorem record046_parameters : Parameters record046 (rowOfCode 23) 31602444861440 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record046_coverage : Coverage record046 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31602444861440 :=
  GraphCoverageDescriptions.coverage_of_checked record046 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05932 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31602444861440
    (by rfl) record046_cells_exact
    (GraphCoverageDescriptions.small_allowed record046 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05932_checked

theorem record046_result : Result (23, 31602444861440) :=
  of_small 23 31602444861440 (by decide) ⟨record046, record046_core, record046_parameters, record046_coverage⟩
#print axioms record046_result

theorem record047_core : Core record047 where
  matrix := record047_matrix_checked
  valid := record047_validity
  literal := record047_literal
  nodes := record047_raw_node_checks record047_validity
  leaf_nodup := record047_leaves_nodup
  frames := record047_frames_supported record047_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record047_certificates, record047_leaf_certificates_checked⟩

theorem record047_parameters : Parameters record047 (rowOfCode 23) 31605053718528 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record047_coverage : Coverage record047 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31605053718528 :=
  GraphCoverageDescriptions.coverage_of_checked record047 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05933 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31605053718528
    (by rfl) record047_cells_exact
    (GraphCoverageDescriptions.small_allowed record047 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05933_checked

theorem record047_result : Result (23, 31605053718528) :=
  of_small 23 31605053718528 (by decide) ⟨record047, record047_core, record047_parameters, record047_coverage⟩
#print axioms record047_result

theorem record048_core : Core record048 where
  matrix := record048_matrix_checked
  valid := record048_validity
  literal := record048_literal
  nodes := record048_raw_node_checks record048_validity
  leaf_nodup := record048_leaves_nodup
  frames := record048_frames_supported record048_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record048_certificates, record048_leaf_certificates_checked⟩

theorem record048_parameters : Parameters record048 (rowOfCode 23) 31611253166112 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record048_coverage : Coverage record048 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31611253166112 :=
  GraphCoverageDescriptions.coverage_of_checked record048 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05934 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31611253166112
    (by rfl) record048_cells_exact
    (GraphCoverageDescriptions.small_allowed record048 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05934_checked

theorem record048_result : Result (23, 31611253166112) :=
  of_small 23 31611253166112 (by decide) ⟨record048, record048_core, record048_parameters, record048_coverage⟩
#print axioms record048_result

theorem record049_core : Core record049 where
  matrix := record049_matrix_checked
  valid := record049_validity
  literal := record049_literal
  nodes := record049_raw_node_checks record049_validity
  leaf_nodup := record049_leaves_nodup
  frames := record049_frames_supported record049_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record049_certificates, record049_leaf_certificates_checked⟩

theorem record049_parameters : Parameters record049 (rowOfCode 23) 31750614974720 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record049_coverage : Coverage record049 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31750614974720 :=
  GraphCoverageDescriptions.coverage_of_checked record049 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05935 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31750614974720
    (by rfl) record049_cells_exact
    (GraphCoverageDescriptions.small_allowed record049 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05935_checked

theorem record049_result : Result (23, 31750614974720) :=
  of_small 23 31750614974720 (by decide) ⟨record049, record049_core, record049_parameters, record049_coverage⟩
#print axioms record049_result

theorem record050_core : Core record050 where
  matrix := record050_matrix_checked
  valid := record050_validity
  literal := record050_literal
  nodes := record050_raw_node_checks record050_validity
  leaf_nodup := record050_leaves_nodup
  frames := record050_frames_supported record050_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record050_certificates, record050_leaf_certificates_checked⟩

theorem record050_parameters : Parameters record050 (rowOfCode 23) 31785043951616 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record050_coverage : Coverage record050 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31785043951616 :=
  GraphCoverageDescriptions.coverage_of_checked record050 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05936 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 31785043951616
    (by rfl) record050_cells_exact
    (GraphCoverageDescriptions.small_allowed record050 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05936_checked

theorem record050_result : Result (23, 31785043951616) :=
  of_small 23 31785043951616 (by decide) ⟨record050, record050_core, record050_parameters, record050_coverage⟩
#print axioms record050_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025
