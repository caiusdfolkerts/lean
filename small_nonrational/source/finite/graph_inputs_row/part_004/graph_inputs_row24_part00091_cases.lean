module
prelude
public import GraphInputsRow24Part00091Checked
public import GraphInputsRow24Part00091Metadata
public import GraphInputsRow24Part00091Frames
public import GraphInputsRow24Part00091Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch091


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091
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

theorem record000_parameters : Parameters record000 (rowOfCode 24) 24885603602496 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24885603602496 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09131 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24885603602496
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch091.candidate09131_checked

theorem record000_result : Result (24, 24885603602496) :=
  of_small 24 24885603602496 (by decide) ⟨record000, record000_core, record000_parameters, record000_coverage⟩
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

theorem record001_parameters : Parameters record001 (rowOfCode 24) 24885654980624 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24885654980624 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09132 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24885654980624
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch091.candidate09132_checked

theorem record001_result : Result (24, 24885654980624) :=
  of_small 24 24885654980624 (by decide) ⟨record001, record001_core, record001_parameters, record001_coverage⟩
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

theorem record002_parameters : Parameters record002 (rowOfCode 24) 24886685745408 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24886685745408 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09133 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24886685745408
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch091.candidate09133_checked

theorem record002_result : Result (24, 24886685745408) :=
  of_small 24 24886685745408 (by decide) ⟨record002, record002_core, record002_parameters, record002_coverage⟩
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

theorem record003_parameters : Parameters record003 (rowOfCode 24) 24886728720385 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24886728720385 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09134 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24886728720385
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch091.candidate09134_checked

theorem record003_result : Result (24, 24886728720385) :=
  of_small 24 24886728720385 (by decide) ⟨record003, record003_core, record003_parameters, record003_coverage⟩
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

theorem record004_parameters : Parameters record004 (rowOfCode 24) 24893844359184 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24893844359184 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09135 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24893844359184
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch091.candidate09135_checked

theorem record004_result : Result (24, 24893844359184) :=
  of_small 24 24893844359184 (by decide) ⟨record004, record004_core, record004_parameters, record004_coverage⟩
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

theorem record005_parameters : Parameters record005 (rowOfCode 24) 24894042540048 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24894042540048 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09136 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24894042540048
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch091.candidate09136_checked

theorem record005_result : Result (24, 24894042540048) :=
  of_small 24 24894042540048 (by decide) ⟨record005, record005_core, record005_parameters, record005_coverage⟩
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

theorem record006_parameters : Parameters record006 (rowOfCode 24) 24903865614336 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24903865614336 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09137 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24903865614336
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch091.candidate09137_checked

theorem record006_result : Result (24, 24903865614336) :=
  of_small 24 24903865614336 (by decide) ⟨record006, record006_core, record006_parameters, record006_coverage⟩
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

theorem record007_parameters : Parameters record007 (rowOfCode 24) 24950610133248 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24950610133248 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09138 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24950610133248
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch091.candidate09138_checked

theorem record007_result : Result (24, 24950610133248) :=
  of_small 24 24950610133248 (by decide) ⟨record007, record007_core, record007_parameters, record007_coverage⟩
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

theorem record008_parameters : Parameters record008 (rowOfCode 24) 24967790002176 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24967790002176 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09139 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24967790002176
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch091.candidate09139_checked

theorem record008_result : Result (24, 24967790002176) :=
  of_small 24 24967790002176 (by decide) ⟨record008, record008_core, record008_parameters, record008_coverage⟩
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

theorem record009_parameters : Parameters record009 (rowOfCode 24) 24968062566400 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24968062566400 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09140 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24968062566400
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch091.candidate09140_checked

theorem record009_result : Result (24, 24968062566400) :=
  of_small 24 24968062566400 (by decide) ⟨record009, record009_core, record009_parameters, record009_coverage⟩
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

theorem record010_parameters : Parameters record010 (rowOfCode 24) 24968524988416 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24968524988416 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09141 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24968524988416
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch091.candidate09141_checked

theorem record010_result : Result (24, 24968524988416) :=
  of_small 24 24968524988416 (by decide) ⟨record010, record010_core, record010_parameters, record010_coverage⟩
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

theorem record011_parameters : Parameters record011 (rowOfCode 24) 24986249134080 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record011_coverage : Coverage record011 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24986249134080 :=
  GraphCoverageDescriptions.coverage_of_checked record011 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09142 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24986249134080
    (by rfl) record011_cells_exact
    (GraphCoverageDescriptions.small_allowed record011 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch091.candidate09142_checked

theorem record011_result : Result (24, 24986249134080) :=
  of_small 24 24986249134080 (by decide) ⟨record011, record011_core, record011_parameters, record011_coverage⟩
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

theorem record012_parameters : Parameters record012 (rowOfCode 24) 25003428937728 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record012_coverage : Coverage record012 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25003428937728 :=
  GraphCoverageDescriptions.coverage_of_checked record012 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09143 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25003428937728
    (by rfl) record012_cells_exact
    (GraphCoverageDescriptions.small_allowed record012 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch091.candidate09143_checked

theorem record012_result : Result (24, 25003428937728) :=
  of_small 24 25003428937728 (by decide) ⟨record012, record012_core, record012_parameters, record012_coverage⟩
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

theorem record013_parameters : Parameters record013 (rowOfCode 24) 25003957420032 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record013_coverage : Coverage record013 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25003957420032 :=
  GraphCoverageDescriptions.coverage_of_checked record013 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09144 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25003957420032
    (by rfl) record013_cells_exact
    (GraphCoverageDescriptions.small_allowed record013 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch091.candidate09144_checked

theorem record013_result : Result (24, 25003957420032) :=
  of_small 24 25003957420032 (by decide) ⟨record013, record013_core, record013_parameters, record013_coverage⟩
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

theorem record014_parameters : Parameters record014 (rowOfCode 24) 25016328524032 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record014_coverage : Coverage record014 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25016328524032 :=
  GraphCoverageDescriptions.coverage_of_checked record014 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09145 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25016328524032
    (by rfl) record014_cells_exact
    (GraphCoverageDescriptions.small_allowed record014 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch091.candidate09145_checked

theorem record014_result : Result (24, 25016328524032) :=
  of_small 24 25016328524032 (by decide) ⟨record014, record014_core, record014_parameters, record014_coverage⟩
#print axioms record014_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091
