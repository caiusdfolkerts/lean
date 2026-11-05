module
prelude
public import GraphInputsSix0Part00069Checked
public import GraphInputsSix0Part00069Metadata
public import GraphInputsSix0Part00069Frames
public import GraphInputsSix0Part00069Leaves
public import GraphSixEmbeddingCoverage
public import GraphCoverageBatch236
public import GraphCoverageBatch237


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069
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

theorem record000_parameters : Parameters record000 (rowOfCode 32) 25634244141120 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25634244141120 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23663 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25634244141120
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.six_allowed record000 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23663_checked

theorem record000_result : Result (32, 25634244141120) :=
  of_six 25634244141120 ⟨record000, record000_core, record000_parameters, record000_coverage⟩
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

theorem record001_parameters : Parameters record001 (rowOfCode 32) 25641525452864 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25641525452864 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23664 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25641525452864
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.six_allowed record001 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23664_checked

theorem record001_result : Result (32, 25641525452864) :=
  of_six 25641525452864 ⟨record001, record001_core, record001_parameters, record001_coverage⟩
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

theorem record002_parameters : Parameters record002 (rowOfCode 32) 25658186022912 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25658186022912 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23665 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25658186022912
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.six_allowed record002 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23665_checked

theorem record002_result : Result (32, 25658186022912) :=
  of_six 25658186022912 ⟨record002, record002_core, record002_parameters, record002_coverage⟩
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

theorem record003_parameters : Parameters record003 (rowOfCode 32) 25659208507456 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25659208507456 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23666 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25659208507456
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.six_allowed record003 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23666_checked

theorem record003_result : Result (32, 25659208507456) :=
  of_six 25659208507456 ⟨record003, record003_core, record003_parameters, record003_coverage⟩
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

theorem record004_parameters : Parameters record004 (rowOfCode 32) 25659275624448 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25659275624448 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23667 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25659275624448
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.six_allowed record004 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23667_checked

theorem record004_result : Result (32, 25659275624448) :=
  of_six 25659275624448 ⟨record004, record004_core, record004_parameters, record004_coverage⟩
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

theorem record005_parameters : Parameters record005 (rowOfCode 32) 25659277705216 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25659277705216 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23668 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25659277705216
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.six_allowed record005 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23668_checked

theorem record005_result : Result (32, 25659277705216) :=
  of_six 25659277705216 ⟨record005, record005_core, record005_parameters, record005_coverage⟩
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

theorem record006_parameters : Parameters record006 (rowOfCode 32) 25659409695232 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25659409695232 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23669 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25659409695232
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.six_allowed record006 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23669_checked

theorem record006_result : Result (32, 25659409695232) :=
  of_six 25659409695232 ⟨record006, record006_core, record006_parameters, record006_coverage⟩
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

theorem record007_parameters : Parameters record007 (rowOfCode 32) 25702244040960 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25702244040960 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23670 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25702244040960
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.six_allowed record007 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23670_checked

theorem record007_result : Result (32, 25702244040960) :=
  of_six 25702244040960 ⟨record007, record007_core, record007_parameters, record007_coverage⟩
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

theorem record008_parameters : Parameters record008 (rowOfCode 32) 25702252429312 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25702252429312 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23671 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25702252429312
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.six_allowed record008 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23671_checked

theorem record008_result : Result (32, 25702252429312) :=
  of_six 25702252429312 ⟨record008, record008_core, record008_parameters, record008_coverage⟩
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

theorem record009_parameters : Parameters record009 (rowOfCode 32) 25702310101248 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25702310101248 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23672 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25702310101248
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.six_allowed record009 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23672_checked

theorem record009_result : Result (32, 25702310101248) :=
  of_six 25702310101248 ⟨record009, record009_core, record009_parameters, record009_coverage⟩
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

theorem record010_parameters : Parameters record010 (rowOfCode 32) 25702312247296 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25702312247296 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23673 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25702312247296
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.six_allowed record010 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23673_checked

theorem record010_result : Result (32, 25702312247296) :=
  of_six 25702312247296 ⟨record010, record010_core, record010_parameters, record010_coverage⟩
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

theorem record011_parameters : Parameters record011 (rowOfCode 32) 25702318489600 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record011_coverage : Coverage record011 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25702318489600 :=
  GraphCoverageDescriptions.coverage_of_checked record011 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23674 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25702318489600
    (by rfl) record011_cells_exact
    (GraphCoverageDescriptions.six_allowed record011 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23674_checked

theorem record011_result : Result (32, 25702318489600) :=
  of_six 25702318489600 ⟨record011, record011_core, record011_parameters, record011_coverage⟩
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

theorem record012_parameters : Parameters record012 (rowOfCode 32) 25702359646464 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record012_coverage : Coverage record012 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25702359646464 :=
  GraphCoverageDescriptions.coverage_of_checked record012 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23675 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25702359646464
    (by rfl) record012_cells_exact
    (GraphCoverageDescriptions.six_allowed record012 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23675_checked

theorem record012_result : Result (32, 25702359646464) :=
  of_six 25702359646464 ⟨record012, record012_core, record012_parameters, record012_coverage⟩
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

theorem record013_parameters : Parameters record013 (rowOfCode 32) 25702369855488 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record013_coverage : Coverage record013 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25702369855488 :=
  GraphCoverageDescriptions.coverage_of_checked record013 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23676 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25702369855488
    (by rfl) record013_cells_exact
    (GraphCoverageDescriptions.six_allowed record013 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23676_checked

theorem record013_result : Result (32, 25702369855488) :=
  of_six 25702369855488 ⟨record013, record013_core, record013_parameters, record013_coverage⟩
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

theorem record014_parameters : Parameters record014 (rowOfCode 32) 25702712754240 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record014_coverage : Coverage record014 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25702712754240 :=
  GraphCoverageDescriptions.coverage_of_checked record014 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23677 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25702712754240
    (by rfl) record014_cells_exact
    (GraphCoverageDescriptions.six_allowed record014 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23677_checked

theorem record014_result : Result (32, 25702712754240) :=
  of_six 25702712754240 ⟨record014, record014_core, record014_parameters, record014_coverage⟩
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

theorem record015_parameters : Parameters record015 (rowOfCode 32) 25702714851328 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record015_coverage : Coverage record015 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25702714851328 :=
  GraphCoverageDescriptions.coverage_of_checked record015 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23678 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25702714851328
    (by rfl) record015_cells_exact
    (GraphCoverageDescriptions.six_allowed record015 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23678_checked

theorem record015_result : Result (32, 25702714851328) :=
  of_six 25702714851328 ⟨record015, record015_core, record015_parameters, record015_coverage⟩
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

theorem record016_parameters : Parameters record016 (rowOfCode 32) 25702762299456 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record016_coverage : Coverage record016 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25702762299456 :=
  GraphCoverageDescriptions.coverage_of_checked record016 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23679 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25702762299456
    (by rfl) record016_cells_exact
    (GraphCoverageDescriptions.six_allowed record016 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23679_checked

theorem record016_result : Result (32, 25702762299456) :=
  of_six 25702762299456 ⟨record016, record016_core, record016_parameters, record016_coverage⟩
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

theorem record017_parameters : Parameters record017 (rowOfCode 32) 25702829400128 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record017_coverage : Coverage record017 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25702829400128 :=
  GraphCoverageDescriptions.coverage_of_checked record017 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23680 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25702829400128
    (by rfl) record017_cells_exact
    (GraphCoverageDescriptions.six_allowed record017 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23680_checked

theorem record017_result : Result (32, 25702829400128) :=
  of_six 25702829400128 ⟨record017, record017_core, record017_parameters, record017_coverage⟩
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

theorem record018_parameters : Parameters record018 (rowOfCode 32) 25704976613952 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record018_coverage : Coverage record018 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25704976613952 :=
  GraphCoverageDescriptions.coverage_of_checked record018 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23681 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25704976613952
    (by rfl) record018_cells_exact
    (GraphCoverageDescriptions.six_allowed record018 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23681_checked

theorem record018_result : Result (32, 25704976613952) :=
  of_six 25704976613952 ⟨record018, record018_core, record018_parameters, record018_coverage⟩
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

theorem record019_parameters : Parameters record019 (rowOfCode 32) 25705480208640 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record019_coverage : Coverage record019 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25705480208640 :=
  GraphCoverageDescriptions.coverage_of_checked record019 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23682 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25705480208640
    (by rfl) record019_cells_exact
    (GraphCoverageDescriptions.six_allowed record019 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23682_checked

theorem record019_result : Result (32, 25705480208640) :=
  of_six 25705480208640 ⟨record019, record019_core, record019_parameters, record019_coverage⟩
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

theorem record020_parameters : Parameters record020 (rowOfCode 32) 25705490417664 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record020_coverage : Coverage record020 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25705490417664 :=
  GraphCoverageDescriptions.coverage_of_checked record020 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23683 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25705490417664
    (by rfl) record020_cells_exact
    (GraphCoverageDescriptions.six_allowed record020 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23683_checked

theorem record020_result : Result (32, 25705490417664) :=
  of_six 25705490417664 ⟨record020, record020_core, record020_parameters, record020_coverage⟩
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

theorem record021_parameters : Parameters record021 (rowOfCode 32) 25705531899904 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record021_coverage : Coverage record021 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25705531899904 :=
  GraphCoverageDescriptions.coverage_of_checked record021 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23684 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25705531899904
    (by rfl) record021_cells_exact
    (GraphCoverageDescriptions.six_allowed record021 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23684_checked

theorem record021_result : Result (32, 25705531899904) :=
  of_six 25705531899904 ⟨record021, record021_core, record021_parameters, record021_coverage⟩
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

theorem record022_parameters : Parameters record022 (rowOfCode 32) 25705556477952 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record022_coverage : Coverage record022 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25705556477952 :=
  GraphCoverageDescriptions.coverage_of_checked record022 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23685 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25705556477952
    (by rfl) record022_cells_exact
    (GraphCoverageDescriptions.six_allowed record022 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23685_checked

theorem record022_result : Result (32, 25705556477952) :=
  of_six 25705556477952 ⟨record022, record022_core, record022_parameters, record022_coverage⟩
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

theorem record023_parameters : Parameters record023 (rowOfCode 32) 25705933447232 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record023_coverage : Coverage record023 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25705933447232 :=
  GraphCoverageDescriptions.coverage_of_checked record023 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23686 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25705933447232
    (by rfl) record023_cells_exact
    (GraphCoverageDescriptions.six_allowed record023 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23686_checked

theorem record023_result : Result (32, 25705933447232) :=
  of_six 25705933447232 ⟨record023, record023_core, record023_parameters, record023_coverage⟩
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

theorem record024_parameters : Parameters record024 (rowOfCode 32) 25705934503936 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record024_coverage : Coverage record024 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25705934503936 :=
  GraphCoverageDescriptions.coverage_of_checked record024 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23687 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25705934503936
    (by rfl) record024_cells_exact
    (GraphCoverageDescriptions.six_allowed record024 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23687_checked

theorem record024_result : Result (32, 25705934503936) :=
  of_six 25705934503936 ⟨record024, record024_core, record024_parameters, record024_coverage⟩
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

theorem record025_parameters : Parameters record025 (rowOfCode 32) 25705949962304 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record025_coverage : Coverage record025 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25705949962304 :=
  GraphCoverageDescriptions.coverage_of_checked record025 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23688 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25705949962304
    (by rfl) record025_cells_exact
    (GraphCoverageDescriptions.six_allowed record025 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23688_checked

theorem record025_result : Result (32, 25705949962304) :=
  of_six 25705949962304 ⟨record025, record025_core, record025_parameters, record025_coverage⟩
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

theorem record026_parameters : Parameters record026 (rowOfCode 32) 25706654335744 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record026_coverage : Coverage record026 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25706654335744 :=
  GraphCoverageDescriptions.coverage_of_checked record026 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23689 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25706654335744
    (by rfl) record026_cells_exact
    (GraphCoverageDescriptions.six_allowed record026 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23689_checked

theorem record026_result : Result (32, 25706654335744) :=
  of_six 25706654335744 ⟨record026, record026_core, record026_parameters, record026_coverage⟩
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

theorem record027_parameters : Parameters record027 (rowOfCode 32) 25707056988736 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record027_coverage : Coverage record027 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25707056988736 :=
  GraphCoverageDescriptions.coverage_of_checked record027 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23690 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25707056988736
    (by rfl) record027_cells_exact
    (GraphCoverageDescriptions.six_allowed record027 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23690_checked

theorem record027_result : Result (32, 25707056988736) :=
  of_six 25707056988736 ⟨record027, record027_core, record027_parameters, record027_coverage⟩
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

theorem record028_parameters : Parameters record028 (rowOfCode 32) 25718365110336 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record028_coverage : Coverage record028 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25718365110336 :=
  GraphCoverageDescriptions.coverage_of_checked record028 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23691 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25718365110336
    (by rfl) record028_cells_exact
    (GraphCoverageDescriptions.six_allowed record028 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23691_checked

theorem record028_result : Result (32, 25718365110336) :=
  of_six 25718365110336 ⟨record028, record028_core, record028_parameters, record028_coverage⟩
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

theorem record029_parameters : Parameters record029 (rowOfCode 32) 25718432211008 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record029_coverage : Coverage record029 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25718432211008 :=
  GraphCoverageDescriptions.coverage_of_checked record029 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23692 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25718432211008
    (by rfl) record029_cells_exact
    (GraphCoverageDescriptions.six_allowed record029 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23692_checked

theorem record029_result : Result (32, 25718432211008) :=
  of_six 25718432211008 ⟨record029, record029_core, record029_parameters, record029_coverage⟩
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

theorem record030_parameters : Parameters record030 (rowOfCode 32) 25718435088384 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record030_coverage : Coverage record030 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25718435088384 :=
  GraphCoverageDescriptions.coverage_of_checked record030 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23693 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25718435088384
    (by rfl) record030_cells_exact
    (GraphCoverageDescriptions.six_allowed record030 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23693_checked

theorem record030_result : Result (32, 25718435088384) :=
  of_six 25718435088384 ⟨record030, record030_core, record030_parameters, record030_coverage⟩
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

theorem record031_parameters : Parameters record031 (rowOfCode 32) 25735595311360 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record031_coverage : Coverage record031 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25735595311360 :=
  GraphCoverageDescriptions.coverage_of_checked record031 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23694 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25735595311360
    (by rfl) record031_cells_exact
    (GraphCoverageDescriptions.six_allowed record031 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23694_checked

theorem record031_result : Result (32, 25735595311360) :=
  of_six 25735595311360 ⟨record031, record031_core, record031_parameters, record031_coverage⟩
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

theorem record032_parameters : Parameters record032 (rowOfCode 32) 25735597457408 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record032_coverage : Coverage record032 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25735597457408 :=
  GraphCoverageDescriptions.coverage_of_checked record032 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23695 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25735597457408
    (by rfl) record032_cells_exact
    (GraphCoverageDescriptions.six_allowed record032 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23695_checked

theorem record032_result : Result (32, 25735597457408) :=
  of_six 25735597457408 ⟨record032, record032_core, record032_parameters, record032_coverage⟩
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

theorem record033_parameters : Parameters record033 (rowOfCode 32) 25735603699712 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record033_coverage : Coverage record033 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25735603699712 :=
  GraphCoverageDescriptions.coverage_of_checked record033 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23696 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25735603699712
    (by rfl) record033_cells_exact
    (GraphCoverageDescriptions.six_allowed record033 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23696_checked

theorem record033_result : Result (32, 25735603699712) :=
  of_six 25735603699712 ⟨record033, record033_core, record033_parameters, record033_coverage⟩
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

theorem record034_parameters : Parameters record034 (rowOfCode 32) 25735605520384 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record034_coverage : Coverage record034 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25735605520384 :=
  GraphCoverageDescriptions.coverage_of_checked record034 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23697 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25735605520384
    (by rfl) record034_cells_exact
    (GraphCoverageDescriptions.six_allowed record034 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23697_checked

theorem record034_result : Result (32, 25735605520384) :=
  of_six 25735605520384 ⟨record034, record034_core, record034_parameters, record034_coverage⟩
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

theorem record035_parameters : Parameters record035 (rowOfCode 32) 25735997964352 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record035_coverage : Coverage record035 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25735997964352 :=
  GraphCoverageDescriptions.coverage_of_checked record035 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23698 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25735997964352
    (by rfl) record035_cells_exact
    (GraphCoverageDescriptions.six_allowed record035 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23698_checked

theorem record035_result : Result (32, 25735997964352) :=
  of_six 25735997964352 ⟨record035, record035_core, record035_parameters, record035_coverage⟩
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

theorem record036_parameters : Parameters record036 (rowOfCode 32) 25736115390528 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record036_coverage : Coverage record036 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25736115390528 :=
  GraphCoverageDescriptions.coverage_of_checked record036 GraphCoverageDescriptions.GraphCoverageBatch236.candidate23699 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25736115390528
    (by rfl) record036_cells_exact
    (GraphCoverageDescriptions.six_allowed record036 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch236.candidate23699_checked

theorem record036_result : Result (32, 25736115390528) :=
  of_six 25736115390528 ⟨record036, record036_core, record036_parameters, record036_coverage⟩
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

theorem record037_parameters : Parameters record037 (rowOfCode 32) 25739873356032 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record037_coverage : Coverage record037 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25739873356032 :=
  GraphCoverageDescriptions.coverage_of_checked record037 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23700 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25739873356032
    (by rfl) record037_cells_exact
    (GraphCoverageDescriptions.six_allowed record037 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23700_checked

theorem record037_result : Result (32, 25739873356032) :=
  of_six 25739873356032 ⟨record037, record037_core, record037_parameters, record037_coverage⟩
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

theorem record038_parameters : Parameters record038 (rowOfCode 32) 25739881744384 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record038_coverage : Coverage record038 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25739881744384 :=
  GraphCoverageDescriptions.coverage_of_checked record038 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23701 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25739881744384
    (by rfl) record038_cells_exact
    (GraphCoverageDescriptions.six_allowed record038 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23701_checked

theorem record038_result : Result (32, 25739881744384) :=
  of_six 25739881744384 ⟨record038, record038_core, record038_parameters, record038_coverage⟩
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

theorem record039_parameters : Parameters record039 (rowOfCode 32) 25739890000640 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record039_coverage : Coverage record039 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25739890000640 :=
  GraphCoverageDescriptions.coverage_of_checked record039 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23702 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25739890000640
    (by rfl) record039_cells_exact
    (GraphCoverageDescriptions.six_allowed record039 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23702_checked

theorem record039_result : Result (32, 25739890000640) :=
  of_six 25739890000640 ⟨record039, record039_core, record039_parameters, record039_coverage⟩
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

theorem record040_parameters : Parameters record040 (rowOfCode 32) 25740276009024 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record040_coverage : Coverage record040 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25740276009024 :=
  GraphCoverageDescriptions.coverage_of_checked record040 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23703 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25740276009024
    (by rfl) record040_cells_exact
    (GraphCoverageDescriptions.six_allowed record040 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23703_checked

theorem record040_result : Result (32, 25740276009024) :=
  of_six 25740276009024 ⟨record040, record040_core, record040_parameters, record040_coverage⟩
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

theorem record041_parameters : Parameters record041 (rowOfCode 32) 25740292653632 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record041_coverage : Coverage record041 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25740292653632 :=
  GraphCoverageDescriptions.coverage_of_checked record041 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23704 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25740292653632
    (by rfl) record041_cells_exact
    (GraphCoverageDescriptions.six_allowed record041 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23704_checked

theorem record041_result : Result (32, 25740292653632) :=
  of_six 25740292653632 ⟨record041, record041_core, record041_parameters, record041_coverage⟩
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

theorem record042_parameters : Parameters record042 (rowOfCode 32) 25740410094088 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record042_coverage : Coverage record042 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25740410094088 :=
  GraphCoverageDescriptions.coverage_of_checked record042 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23705 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25740410094088
    (by rfl) record042_cells_exact
    (GraphCoverageDescriptions.six_allowed record042 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23705_checked

theorem record042_result : Result (32, 25740410094088) :=
  of_six 25740410094088 ⟨record042, record042_core, record042_parameters, record042_coverage⟩
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

theorem record043_parameters : Parameters record043 (rowOfCode 32) 25752760354816 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record043_coverage : Coverage record043 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25752760354816 :=
  GraphCoverageDescriptions.coverage_of_checked record043 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23706 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25752760354816
    (by rfl) record043_cells_exact
    (GraphCoverageDescriptions.six_allowed record043 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23706_checked

theorem record043_result : Result (32, 25752760354816) :=
  of_six 25752760354816 ⟨record043, record043_core, record043_parameters, record043_coverage⟩
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

theorem record044_parameters : Parameters record044 (rowOfCode 32) 25769887940864 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record044_coverage : Coverage record044 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25769887940864 :=
  GraphCoverageDescriptions.coverage_of_checked record044 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23707 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25769887940864
    (by rfl) record044_cells_exact
    (GraphCoverageDescriptions.six_allowed record044 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23707_checked

theorem record044_result : Result (32, 25769887940864) :=
  of_six 25769887940864 ⟨record044, record044_core, record044_parameters, record044_coverage⟩
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

theorem record045_parameters : Parameters record045 (rowOfCode 32) 25769890086912 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record045_coverage : Coverage record045 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25769890086912 :=
  GraphCoverageDescriptions.coverage_of_checked record045 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23708 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25769890086912
    (by rfl) record045_cells_exact
    (GraphCoverageDescriptions.six_allowed record045 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23708_checked

theorem record045_result : Result (32, 25769890086912) :=
  of_six 25769890086912 ⟨record045, record045_core, record045_parameters, record045_coverage⟩
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

theorem record046_parameters : Parameters record046 (rowOfCode 32) 25769896329216 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record046_coverage : Coverage record046 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25769896329216 :=
  GraphCoverageDescriptions.coverage_of_checked record046 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23709 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25769896329216
    (by rfl) record046_cells_exact
    (GraphCoverageDescriptions.six_allowed record046 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23709_checked

theorem record046_result : Result (32, 25769896329216) :=
  of_six 25769896329216 ⟨record046, record046_core, record046_parameters, record046_coverage⟩
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

theorem record047_parameters : Parameters record047 (rowOfCode 32) 25769898149888 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record047_coverage : Coverage record047 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25769898149888 :=
  GraphCoverageDescriptions.coverage_of_checked record047 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23710 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25769898149888
    (by rfl) record047_cells_exact
    (GraphCoverageDescriptions.six_allowed record047 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23710_checked

theorem record047_result : Result (32, 25769898149888) :=
  of_six 25769898149888 ⟨record047, record047_core, record047_parameters, record047_coverage⟩
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

theorem record048_parameters : Parameters record048 (rowOfCode 32) 25769964210176 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record048_coverage : Coverage record048 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25769964210176 :=
  GraphCoverageDescriptions.coverage_of_checked record048 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23711 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25769964210176
    (by rfl) record048_cells_exact
    (GraphCoverageDescriptions.six_allowed record048 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23711_checked

theorem record048_result : Result (32, 25769964210176) :=
  of_six 25769964210176 ⟨record048, record048_core, record048_parameters, record048_coverage⟩
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

theorem record049_parameters : Parameters record049 (rowOfCode 32) 25770005367040 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record049_coverage : Coverage record049 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25770005367040 :=
  GraphCoverageDescriptions.coverage_of_checked record049 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23712 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25770005367040
    (by rfl) record049_cells_exact
    (GraphCoverageDescriptions.six_allowed record049 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23712_checked

theorem record049_result : Result (32, 25770005367040) :=
  of_six 25770005367040 ⟨record049, record049_core, record049_parameters, record049_coverage⟩
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

theorem record050_parameters : Parameters record050 (rowOfCode 32) 25770357694528 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record050_coverage : Coverage record050 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25770357694528 :=
  GraphCoverageDescriptions.coverage_of_checked record050 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23713 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25770357694528
    (by rfl) record050_cells_exact
    (GraphCoverageDescriptions.six_allowed record050 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23713_checked

theorem record050_result : Result (32, 25770357694528) :=
  of_six 25770357694528 ⟨record050, record050_core, record050_parameters, record050_coverage⟩
#print axioms record050_result

theorem record051_core : Core record051 where
  matrix := record051_matrix_checked
  valid := record051_validity
  literal := record051_literal
  nodes := record051_raw_node_checks record051_validity
  leaf_nodup := record051_leaves_nodup
  frames := record051_frames_supported record051_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record051_certificates, record051_leaf_certificates_checked⟩

theorem record051_parameters : Parameters record051 (rowOfCode 32) 25770360571904 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record051_coverage : Coverage record051 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25770360571904 :=
  GraphCoverageDescriptions.coverage_of_checked record051 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23714 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25770360571904
    (by rfl) record051_cells_exact
    (GraphCoverageDescriptions.six_allowed record051 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23714_checked

theorem record051_result : Result (32, 25770360571904) :=
  of_six 25770360571904 ⟨record051, record051_core, record051_parameters, record051_coverage⟩
#print axioms record051_result

theorem record052_core : Core record052 where
  matrix := record052_matrix_checked
  valid := record052_validity
  literal := record052_literal
  nodes := record052_raw_node_checks record052_validity
  leaf_nodup := record052_leaves_nodup
  frames := record052_frames_supported record052_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record052_certificates, record052_leaf_certificates_checked⟩

theorem record052_parameters : Parameters record052 (rowOfCode 32) 25770408020032 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record052_coverage : Coverage record052 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25770408020032 :=
  GraphCoverageDescriptions.coverage_of_checked record052 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23715 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25770408020032
    (by rfl) record052_cells_exact
    (GraphCoverageDescriptions.six_allowed record052 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23715_checked

theorem record052_result : Result (32, 25770408020032) :=
  of_six 25770408020032 ⟨record052, record052_core, record052_parameters, record052_coverage⟩
#print axioms record052_result

theorem record053_core : Core record053 where
  matrix := record053_matrix_checked
  valid := record053_validity
  literal := record053_literal
  nodes := record053_raw_node_checks record053_validity
  leaf_nodup := record053_leaves_nodup
  frames := record053_frames_supported record053_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record053_certificates, record053_leaf_certificates_checked⟩

theorem record053_parameters : Parameters record053 (rowOfCode 32) 25772085610752 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record053_coverage : Coverage record053 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25772085610752 :=
  GraphCoverageDescriptions.coverage_of_checked record053 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23716 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25772085610752
    (by rfl) record053_cells_exact
    (GraphCoverageDescriptions.six_allowed record053 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23716_checked

theorem record053_result : Result (32, 25772085610752) :=
  of_six 25772085610752 ⟨record053, record053_core, record053_parameters, record053_coverage⟩
#print axioms record053_result

theorem record054_core : Core record054 where
  matrix := record054_matrix_checked
  valid := record054_validity
  literal := record054_literal
  nodes := record054_raw_node_checks record054_validity
  leaf_nodup := record054_leaves_nodup
  frames := record054_frames_supported record054_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record054_certificates, record054_leaf_certificates_checked⟩

theorem record054_parameters : Parameters record054 (rowOfCode 32) 25772093999104 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record054_coverage : Coverage record054 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25772093999104 :=
  GraphCoverageDescriptions.coverage_of_checked record054 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23717 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25772093999104
    (by rfl) record054_cells_exact
    (GraphCoverageDescriptions.six_allowed record054 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23717_checked

theorem record054_result : Result (32, 25772093999104) :=
  of_six 25772093999104 ⟨record054, record054_core, record054_parameters, record054_coverage⟩
#print axioms record054_result

theorem record055_core : Core record055 where
  matrix := record055_matrix_checked
  valid := record055_validity
  literal := record055_literal
  nodes := record055_raw_node_checks record055_validity
  leaf_nodup := record055_leaves_nodup
  frames := record055_frames_supported record055_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record055_certificates, record055_leaf_certificates_checked⟩

theorem record055_parameters : Parameters record055 (rowOfCode 32) 25772102255360 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record055_coverage : Coverage record055 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25772102255360 :=
  GraphCoverageDescriptions.coverage_of_checked record055 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23718 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25772102255360
    (by rfl) record055_cells_exact
    (GraphCoverageDescriptions.six_allowed record055 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23718_checked

theorem record055_result : Result (32, 25772102255360) :=
  of_six 25772102255360 ⟨record055, record055_core, record055_parameters, record055_coverage⟩
#print axioms record055_result

theorem record056_core : Core record056 where
  matrix := record056_matrix_checked
  valid := record056_validity
  literal := record056_literal
  nodes := record056_raw_node_checks record056_validity
  leaf_nodup := record056_leaves_nodup
  frames := record056_frames_supported record056_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record056_certificates, record056_leaf_certificates_checked⟩

theorem record056_parameters : Parameters record056 (rowOfCode 32) 25772488263744 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record056_coverage : Coverage record056 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25772488263744 :=
  GraphCoverageDescriptions.coverage_of_checked record056 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23719 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25772488263744
    (by rfl) record056_cells_exact
    (GraphCoverageDescriptions.six_allowed record056 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23719_checked

theorem record056_result : Result (32, 25772488263744) :=
  of_six 25772488263744 ⟨record056, record056_core, record056_parameters, record056_coverage⟩
#print axioms record056_result

theorem record057_core : Core record057 where
  matrix := record057_matrix_checked
  valid := record057_validity
  literal := record057_literal
  nodes := record057_raw_node_checks record057_validity
  leaf_nodup := record057_leaves_nodup
  frames := record057_frames_supported record057_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record057_certificates, record057_leaf_certificates_checked⟩

theorem record057_parameters : Parameters record057 (rowOfCode 32) 25772504908352 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record057_coverage : Coverage record057 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25772504908352 :=
  GraphCoverageDescriptions.coverage_of_checked record057 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23720 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25772504908352
    (by rfl) record057_cells_exact
    (GraphCoverageDescriptions.six_allowed record057 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23720_checked

theorem record057_result : Result (32, 25772504908352) :=
  of_six 25772504908352 ⟨record057, record057_core, record057_parameters, record057_coverage⟩
#print axioms record057_result

theorem record058_core : Core record058 where
  matrix := record058_matrix_checked
  valid := record058_validity
  literal := record058_literal
  nodes := record058_raw_node_checks record058_validity
  leaf_nodup := record058_leaves_nodup
  frames := record058_frames_supported record058_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record058_certificates, record058_leaf_certificates_checked⟩

theorem record058_parameters : Parameters record058 (rowOfCode 32) 25772622348808 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record058_coverage : Coverage record058 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25772622348808 :=
  GraphCoverageDescriptions.coverage_of_checked record058 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23721 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25772622348808
    (by rfl) record058_cells_exact
    (GraphCoverageDescriptions.six_allowed record058 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23721_checked

theorem record058_result : Result (32, 25772622348808) :=
  of_six 25772622348808 ⟨record058, record058_core, record058_parameters, record058_coverage⟩
#print axioms record058_result

theorem record059_core : Core record059 where
  matrix := record059_matrix_checked
  valid := record059_validity
  literal := record059_literal
  nodes := record059_raw_node_checks record059_validity
  leaf_nodup := record059_leaves_nodup
  frames := record059_frames_supported record059_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record059_certificates, record059_leaf_certificates_checked⟩

theorem record059_parameters : Parameters record059 (rowOfCode 32) 25774174373888 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record059_coverage : Coverage record059 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25774174373888 :=
  GraphCoverageDescriptions.coverage_of_checked record059 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23722 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25774174373888
    (by rfl) record059_cells_exact
    (GraphCoverageDescriptions.six_allowed record059 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23722_checked

theorem record059_result : Result (32, 25774174373888) :=
  of_six 25774174373888 ⟨record059, record059_core, record059_parameters, record059_coverage⟩
#print axioms record059_result

theorem record060_core : Core record060 where
  matrix := record060_matrix_checked
  valid := record060_validity
  literal := record060_literal
  nodes := record060_raw_node_checks record060_validity
  leaf_nodup := record060_leaves_nodup
  frames := record060_frames_supported record060_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record060_certificates, record060_leaf_certificates_checked⟩

theorem record060_parameters : Parameters record060 (rowOfCode 32) 25774702723592 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record060_coverage : Coverage record060 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25774702723592 :=
  GraphCoverageDescriptions.coverage_of_checked record060 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23723 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25774702723592
    (by rfl) record060_cells_exact
    (GraphCoverageDescriptions.six_allowed record060 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23723_checked

theorem record060_result : Result (32, 25774702723592) :=
  of_six 25774702723592 ⟨record060, record060_core, record060_parameters, record060_coverage⟩
#print axioms record060_result

theorem record061_core : Core record061 where
  matrix := record061_matrix_checked
  valid := record061_validity
  literal := record061_literal
  nodes := record061_raw_node_checks record061_validity
  leaf_nodup := record061_leaves_nodup
  frames := record061_frames_supported record061_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record061_certificates, record061_leaf_certificates_checked⟩

theorem record061_parameters : Parameters record061 (rowOfCode 32) 25787052984320 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record061_coverage : Coverage record061 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25787052984320 :=
  GraphCoverageDescriptions.coverage_of_checked record061 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23724 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25787052984320
    (by rfl) record061_cells_exact
    (GraphCoverageDescriptions.six_allowed record061 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23724_checked

theorem record061_result : Result (32, 25787052984320) :=
  of_six 25787052984320 ⟨record061, record061_core, record061_parameters, record061_coverage⟩
#print axioms record061_result

theorem record062_core : Core record062 where
  matrix := record062_matrix_checked
  valid := record062_validity
  literal := record062_literal
  nodes := record062_raw_node_checks record062_validity
  leaf_nodup := record062_leaves_nodup
  frames := record062_frames_supported record062_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record062_certificates, record062_leaf_certificates_checked⟩

theorem record062_parameters : Parameters record062 (rowOfCode 32) 25787184972296 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record062_coverage : Coverage record062 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25787184972296 :=
  GraphCoverageDescriptions.coverage_of_checked record062 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23725 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25787184972296
    (by rfl) record062_cells_exact
    (GraphCoverageDescriptions.six_allowed record062 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23725_checked

theorem record062_result : Result (32, 25787184972296) :=
  of_six 25787184972296 ⟨record062, record062_core, record062_parameters, record062_coverage⟩
#print axioms record062_result

theorem record063_core : Core record063 where
  matrix := record063_matrix_checked
  valid := record063_validity
  literal := record063_literal
  nodes := record063_raw_node_checks record063_validity
  leaf_nodup := record063_leaves_nodup
  frames := record063_frames_supported record063_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record063_certificates, record063_leaf_certificates_checked⟩

theorem record063_parameters : Parameters record063 (rowOfCode 32) 25839653683456 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record063_coverage : Coverage record063 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25839653683456 :=
  GraphCoverageDescriptions.coverage_of_checked record063 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23726 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25839653683456
    (by rfl) record063_cells_exact
    (GraphCoverageDescriptions.six_allowed record063 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23726_checked

theorem record063_result : Result (32, 25839653683456) :=
  of_six 25839653683456 ⟨record063, record063_core, record063_parameters, record063_coverage⟩
#print axioms record063_result

theorem record064_core : Core record064 where
  matrix := record064_matrix_checked
  valid := record064_validity
  literal := record064_literal
  nodes := record064_raw_node_checks record064_validity
  leaf_nodup := record064_leaves_nodup
  frames := record064_frames_supported record064_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record064_certificates, record064_leaf_certificates_checked⟩

theorem record064_parameters : Parameters record064 (rowOfCode 32) 25839657844992 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record064_coverage : Coverage record064 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25839657844992 :=
  GraphCoverageDescriptions.coverage_of_checked record064 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23727 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25839657844992
    (by rfl) record064_cells_exact
    (GraphCoverageDescriptions.six_allowed record064 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23727_checked

theorem record064_result : Result (32, 25839657844992) :=
  of_six 25839657844992 ⟨record064, record064_core, record064_parameters, record064_coverage⟩
#print axioms record064_result

theorem record065_core : Core record065 where
  matrix := record065_matrix_checked
  valid := record065_validity
  literal := record065_literal
  nodes := record065_raw_node_checks record065_validity
  leaf_nodup := record065_leaves_nodup
  frames := record065_frames_supported record065_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record065_certificates, record065_leaf_certificates_checked⟩

theorem record065_parameters : Parameters record065 (rowOfCode 32) 25839657910272 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record065_coverage : Coverage record065 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25839657910272 :=
  GraphCoverageDescriptions.coverage_of_checked record065 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23728 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25839657910272
    (by rfl) record065_cells_exact
    (GraphCoverageDescriptions.six_allowed record065 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23728_checked

theorem record065_result : Result (32, 25839657910272) :=
  of_six 25839657910272 ⟨record065, record065_core, record065_parameters, record065_coverage⟩
#print axioms record065_result

theorem record066_core : Core record066 where
  matrix := record066_matrix_checked
  valid := record066_validity
  literal := record066_literal
  nodes := record066_raw_node_checks record066_validity
  leaf_nodup := record066_leaves_nodup
  frames := record066_frames_supported record066_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record066_certificates, record066_leaf_certificates_checked⟩

theorem record066_parameters : Parameters record066 (rowOfCode 32) 25839659925760 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record066_coverage : Coverage record066 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25839659925760 :=
  GraphCoverageDescriptions.coverage_of_checked record066 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23729 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25839659925760
    (by rfl) record066_cells_exact
    (GraphCoverageDescriptions.six_allowed record066 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23729_checked

theorem record066_result : Result (32, 25839659925760) :=
  of_six 25839659925760 ⟨record066, record066_core, record066_parameters, record066_coverage⟩
#print axioms record066_result

theorem record067_core : Core record067 where
  matrix := record067_matrix_checked
  valid := record067_validity
  literal := record067_literal
  nodes := record067_raw_node_checks record067_validity
  leaf_nodup := record067_leaves_nodup
  frames := record067_frames_supported record067_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record067_certificates, record067_leaf_certificates_checked⟩

theorem record067_parameters : Parameters record067 (rowOfCode 32) 25839752773888 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record067_coverage : Coverage record067 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25839752773888 :=
  GraphCoverageDescriptions.coverage_of_checked record067 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23730 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25839752773888
    (by rfl) record067_cells_exact
    (GraphCoverageDescriptions.six_allowed record067 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23730_checked

theorem record067_result : Result (32, 25839752773888) :=
  of_six 25839752773888 ⟨record067, record067_core, record067_parameters, record067_coverage⟩
#print axioms record067_result

theorem record068_core : Core record068 where
  matrix := record068_matrix_checked
  valid := record068_validity
  literal := record068_literal
  nodes := record068_raw_node_checks record068_validity
  leaf_nodup := record068_leaves_nodup
  frames := record068_frames_supported record068_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record068_certificates, record068_leaf_certificates_checked⟩

theorem record068_parameters : Parameters record068 (rowOfCode 32) 25839756935424 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record068_coverage : Coverage record068 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25839756935424 :=
  GraphCoverageDescriptions.coverage_of_checked record068 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23731 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25839756935424
    (by rfl) record068_cells_exact
    (GraphCoverageDescriptions.six_allowed record068 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23731_checked

theorem record068_result : Result (32, 25839756935424) :=
  of_six 25839756935424 ⟨record068, record068_core, record068_parameters, record068_coverage⟩
#print axioms record068_result

theorem record069_core : Core record069 where
  matrix := record069_matrix_checked
  valid := record069_validity
  literal := record069_literal
  nodes := record069_raw_node_checks record069_validity
  leaf_nodup := record069_leaves_nodup
  frames := record069_frames_supported record069_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record069_certificates, record069_leaf_certificates_checked⟩

theorem record069_parameters : Parameters record069 (rowOfCode 32) 25839757000704 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record069_coverage : Coverage record069 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25839757000704 :=
  GraphCoverageDescriptions.coverage_of_checked record069 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23732 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25839757000704
    (by rfl) record069_cells_exact
    (GraphCoverageDescriptions.six_allowed record069 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23732_checked

theorem record069_result : Result (32, 25839757000704) :=
  of_six 25839757000704 ⟨record069, record069_core, record069_parameters, record069_coverage⟩
#print axioms record069_result

theorem record070_core : Core record070 where
  matrix := record070_matrix_checked
  valid := record070_validity
  literal := record070_literal
  nodes := record070_raw_node_checks record070_validity
  leaf_nodup := record070_leaves_nodup
  frames := record070_frames_supported record070_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record070_certificates, record070_leaf_certificates_checked⟩

theorem record070_parameters : Parameters record070 (rowOfCode 32) 25839760576768 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record070_coverage : Coverage record070 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25839760576768 :=
  GraphCoverageDescriptions.coverage_of_checked record070 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23733 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25839760576768
    (by rfl) record070_cells_exact
    (GraphCoverageDescriptions.six_allowed record070 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23733_checked

theorem record070_result : Result (32, 25839760576768) :=
  of_six 25839760576768 ⟨record070, record070_core, record070_parameters, record070_coverage⟩
#print axioms record070_result

theorem record071_core : Core record071 where
  matrix := record071_matrix_checked
  valid := record071_validity
  literal := record071_literal
  nodes := record071_raw_node_checks record071_validity
  leaf_nodup := record071_leaves_nodup
  frames := record071_frames_supported record071_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record071_certificates, record071_leaf_certificates_checked⟩

theorem record071_parameters : Parameters record071 (rowOfCode 32) 25839891136768 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record071_coverage : Coverage record071 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25839891136768 :=
  GraphCoverageDescriptions.coverage_of_checked record071 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23734 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25839891136768
    (by rfl) record071_cells_exact
    (GraphCoverageDescriptions.six_allowed record071 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23734_checked

theorem record071_result : Result (32, 25839891136768) :=
  of_six 25839891136768 ⟨record071, record071_core, record071_parameters, record071_coverage⟩
#print axioms record071_result

theorem record072_core : Core record072 where
  matrix := record072_matrix_checked
  valid := record072_validity
  literal := record072_literal
  nodes := record072_raw_node_checks record072_validity
  leaf_nodup := record072_leaves_nodup
  frames := record072_frames_supported record072_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record072_certificates, record072_leaf_certificates_checked⟩

theorem record072_parameters : Parameters record072 (rowOfCode 32) 25839891202048 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record072_coverage : Coverage record072 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25839891202048 :=
  GraphCoverageDescriptions.coverage_of_checked record072 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23735 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25839891202048
    (by rfl) record072_cells_exact
    (GraphCoverageDescriptions.six_allowed record072 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23735_checked

theorem record072_result : Result (32, 25839891202048) :=
  of_six 25839891202048 ⟨record072, record072_core, record072_parameters, record072_coverage⟩
#print axioms record072_result

theorem record073_core : Core record073 where
  matrix := record073_matrix_checked
  valid := record073_validity
  literal := record073_literal
  nodes := record073_raw_node_checks record073_validity
  leaf_nodup := record073_leaves_nodup
  frames := record073_frames_supported record073_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record073_certificates, record073_leaf_certificates_checked⟩

theorem record073_parameters : Parameters record073 (rowOfCode 32) 25839892697344 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record073_coverage : Coverage record073 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25839892697344 :=
  GraphCoverageDescriptions.coverage_of_checked record073 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23736 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25839892697344
    (by rfl) record073_cells_exact
    (GraphCoverageDescriptions.six_allowed record073 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23736_checked

theorem record073_result : Result (32, 25839892697344) :=
  of_six 25839892697344 ⟨record073, record073_core, record073_parameters, record073_coverage⟩
#print axioms record073_result

theorem record074_core : Core record074 where
  matrix := record074_matrix_checked
  valid := record074_validity
  literal := record074_literal
  nodes := record074_raw_node_checks record074_validity
  leaf_nodup := record074_leaves_nodup
  frames := record074_frames_supported record074_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record074_certificates, record074_leaf_certificates_checked⟩

theorem record074_parameters : Parameters record074 (rowOfCode 32) 25840156938496 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record074_coverage : Coverage record074 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25840156938496 :=
  GraphCoverageDescriptions.coverage_of_checked record074 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23737 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25840156938496
    (by rfl) record074_cells_exact
    (GraphCoverageDescriptions.six_allowed record074 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23737_checked

theorem record074_result : Result (32, 25840156938496) :=
  of_six 25840156938496 ⟨record074, record074_core, record074_parameters, record074_coverage⟩
#print axioms record074_result

theorem record075_core : Core record075 where
  matrix := record075_matrix_checked
  valid := record075_validity
  literal := record075_literal
  nodes := record075_raw_node_checks record075_validity
  leaf_nodup := record075_leaves_nodup
  frames := record075_frames_supported record075_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record075_certificates, record075_leaf_certificates_checked⟩

theorem record075_parameters : Parameters record075 (rowOfCode 32) 25840159604736 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record075_coverage : Coverage record075 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25840159604736 :=
  GraphCoverageDescriptions.coverage_of_checked record075 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23738 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25840159604736
    (by rfl) record075_cells_exact
    (GraphCoverageDescriptions.six_allowed record075 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23738_checked

theorem record075_result : Result (32, 25840159604736) :=
  of_six 25840159604736 ⟨record075, record075_core, record075_parameters, record075_coverage⟩
#print axioms record075_result

theorem record076_core : Core record076 where
  matrix := record076_matrix_checked
  valid := record076_validity
  literal := record076_literal
  nodes := record076_raw_node_checks record076_validity
  leaf_nodup := record076_leaves_nodup
  frames := record076_frames_supported record076_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record076_certificates, record076_leaf_certificates_checked⟩

theorem record076_parameters : Parameters record076 (rowOfCode 32) 25840163229760 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record076_coverage : Coverage record076 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25840163229760 :=
  GraphCoverageDescriptions.coverage_of_checked record076 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23739 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25840163229760
    (by rfl) record076_cells_exact
    (GraphCoverageDescriptions.six_allowed record076 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23739_checked

theorem record076_result : Result (32, 25840163229760) :=
  of_six 25840163229760 ⟨record076, record076_core, record076_parameters, record076_coverage⟩
#print axioms record076_result

theorem record077_core : Core record077 where
  matrix := record077_matrix_checked
  valid := record077_validity
  literal := record077_literal
  nodes := record077_raw_node_checks record077_validity
  leaf_nodup := record077_leaves_nodup
  frames := record077_frames_supported record077_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record077_certificates, record077_leaf_certificates_checked⟩

theorem record077_parameters : Parameters record077 (rowOfCode 32) 25840280668176 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record077_coverage : Coverage record077 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25840280668176 :=
  GraphCoverageDescriptions.coverage_of_checked record077 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23740 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25840280668176
    (by rfl) record077_cells_exact
    (GraphCoverageDescriptions.six_allowed record077 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23740_checked

theorem record077_result : Result (32, 25840280668176) :=
  of_six 25840280668176 ⟨record077, record077_core, record077_parameters, record077_coverage⟩
#print axioms record077_result

theorem record078_core : Core record078 where
  matrix := record078_matrix_checked
  valid := record078_validity
  literal := record078_literal
  nodes := record078_raw_node_checks record078_validity
  leaf_nodup := record078_leaves_nodup
  frames := record078_frames_supported record078_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record078_certificates, record078_leaf_certificates_checked⟩

theorem record078_parameters : Parameters record078 (rowOfCode 32) 25843112349952 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record078_coverage : Coverage record078 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25843112349952 :=
  GraphCoverageDescriptions.coverage_of_checked record078 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23741 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25843112349952
    (by rfl) record078_cells_exact
    (GraphCoverageDescriptions.six_allowed record078 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23741_checked

theorem record078_result : Result (32, 25843112349952) :=
  of_six 25843112349952 ⟨record078, record078_core, record078_parameters, record078_coverage⟩
#print axioms record078_result

theorem record079_core : Core record079 where
  matrix := record079_matrix_checked
  valid := record079_validity
  literal := record079_literal
  nodes := record079_raw_node_checks record079_validity
  leaf_nodup := record079_leaves_nodup
  frames := record079_frames_supported record079_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record079_certificates, record079_leaf_certificates_checked⟩

theorem record079_parameters : Parameters record079 (rowOfCode 32) 25843112415232 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record079_coverage : Coverage record079 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25843112415232 :=
  GraphCoverageDescriptions.coverage_of_checked record079 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23742 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25843112415232
    (by rfl) record079_cells_exact
    (GraphCoverageDescriptions.six_allowed record079 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23742_checked

theorem record079_result : Result (32, 25843112415232) :=
  of_six 25843112415232 ⟨record079, record079_core, record079_parameters, record079_coverage⟩
#print axioms record079_result

theorem record080_core : Core record080 where
  matrix := record080_matrix_checked
  valid := record080_validity
  literal := record080_literal
  nodes := record080_raw_node_checks record080_validity
  leaf_nodup := record080_leaves_nodup
  frames := record080_frames_supported record080_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record080_certificates, record080_leaf_certificates_checked⟩

theorem record080_parameters : Parameters record080 (rowOfCode 32) 25843376591104 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record080_coverage : Coverage record080 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25843376591104 :=
  GraphCoverageDescriptions.coverage_of_checked record080 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23743 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25843376591104
    (by rfl) record080_cells_exact
    (GraphCoverageDescriptions.six_allowed record080 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23743_checked

theorem record080_result : Result (32, 25843376591104) :=
  of_six 25843376591104 ⟨record080, record080_core, record080_parameters, record080_coverage⟩
#print axioms record080_result

theorem record081_core : Core record081 where
  matrix := record081_matrix_checked
  valid := record081_validity
  literal := record081_literal
  nodes := record081_raw_node_checks record081_validity
  leaf_nodup := record081_leaves_nodup
  frames := record081_frames_supported record081_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record081_certificates, record081_leaf_certificates_checked⟩

theorem record081_parameters : Parameters record081 (rowOfCode 32) 25843376656384 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record081_coverage : Coverage record081 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25843376656384 :=
  GraphCoverageDescriptions.coverage_of_checked record081 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23744 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25843376656384
    (by rfl) record081_cells_exact
    (GraphCoverageDescriptions.six_allowed record081 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23744_checked

theorem record081_result : Result (32, 25843376656384) :=
  of_six 25843376656384 ⟨record081, record081_core, record081_parameters, record081_coverage⟩
#print axioms record081_result

theorem record082_core : Core record082 where
  matrix := record082_matrix_checked
  valid := record082_validity
  literal := record082_literal
  nodes := record082_raw_node_checks record082_validity
  leaf_nodup := record082_leaves_nodup
  frames := record082_frames_supported record082_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record082_certificates, record082_leaf_certificates_checked⟩

theorem record082_parameters : Parameters record082 (rowOfCode 32) 25843384455184 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record082_coverage : Coverage record082 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25843384455184 :=
  GraphCoverageDescriptions.coverage_of_checked record082 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23745 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25843384455184
    (by rfl) record082_cells_exact
    (GraphCoverageDescriptions.six_allowed record082 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23745_checked

theorem record082_result : Result (32, 25843384455184) :=
  of_six 25843384455184 ⟨record082, record082_core, record082_parameters, record082_coverage⟩
#print axioms record082_result

theorem record083_core : Core record083 where
  matrix := record083_matrix_checked
  valid := record083_validity
  literal := record083_literal
  nodes := record083_raw_node_checks record083_validity
  leaf_nodup := record083_leaves_nodup
  frames := record083_frames_supported record083_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record083_certificates, record083_leaf_certificates_checked⟩

theorem record083_parameters : Parameters record083 (rowOfCode 32) 25843401230352 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record083_coverage : Coverage record083 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 25843401230352 :=
  GraphCoverageDescriptions.coverage_of_checked record083 GraphCoverageDescriptions.GraphCoverageBatch237.candidate23746 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 25843401230352
    (by rfl) record083_cells_exact
    (GraphCoverageDescriptions.six_allowed record083 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch237.candidate23746_checked

theorem record083_result : Result (32, 25843401230352) :=
  of_six 25843401230352 ⟨record083, record083_core, record083_parameters, record083_coverage⟩
#print axioms record083_result
end Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069
