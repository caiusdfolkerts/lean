module
prelude
public import GraphInputsSix0Part00090Checked
public import GraphInputsSix0Part00090Metadata
public import GraphInputsSix0Part00090Frames
public import GraphInputsSix0Part00090Leaves
public import GraphSixEmbeddingCoverage
public import GraphCoverageBatch252


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00090
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

theorem record000_parameters : Parameters record000 (rowOfCode 32) 34712462690320 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 34712462690320 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch252.candidate25220 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 34712462690320
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.six_allowed record000 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch252.candidate25220_checked

theorem record000_result : Result (32, 34712462690320) :=
  of_six 34712462690320 ⟨record000, record000_core, record000_parameters, record000_coverage⟩
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

theorem record001_parameters : Parameters record001 (rowOfCode 32) 34712479334928 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 34712479334928 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch252.candidate25221 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 34712479334928
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.six_allowed record001 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch252.candidate25221_checked

theorem record001_result : Result (32, 34712479334928) :=
  of_six 34712479334928 ⟨record001, record001_core, record001_parameters, record001_coverage⟩
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

theorem record002_parameters : Parameters record002 (rowOfCode 32) 34737712824576 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 34737712824576 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch252.candidate25222 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 34737712824576
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.six_allowed record002 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch252.candidate25222_checked

theorem record002_result : Result (32, 34737712824576) :=
  of_six 34737712824576 ⟨record002, record002_core, record002_parameters, record002_coverage⟩
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

theorem record003_parameters : Parameters record003 (rowOfCode 32) 34738790268928 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 34738790268928 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch252.candidate25223 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 34738790268928
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.six_allowed record003 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch252.candidate25223_checked

theorem record003_result : Result (32, 34738790268928) :=
  of_six 34738790268928 ⟨record003, record003_core, record003_parameters, record003_coverage⟩
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

theorem record004_parameters : Parameters record004 (rowOfCode 32) 34739062833152 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 34739062833152 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch252.candidate25224 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 34739062833152
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.six_allowed record004 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch252.candidate25224_checked

theorem record004_result : Result (32, 34739062833152) :=
  of_six 34739062833152 ⟨record004, record004_core, record004_parameters, record004_coverage⟩
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

theorem record005_parameters : Parameters record005 (rowOfCode 32) 34739574800384 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 34739574800384 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch252.candidate25225 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 34739574800384
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.six_allowed record005 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch252.candidate25225_checked

theorem record005_result : Result (32, 34739574800384) :=
  of_six 34739574800384 ⟨record005, record005_core, record005_parameters, record005_coverage⟩
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

theorem record006_parameters : Parameters record006 (rowOfCode 32) 34746302791680 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 34746302791680 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch252.candidate25226 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 34746302791680
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.six_allowed record006 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch252.candidate25226_checked

theorem record006_result : Result (32, 34746302791680) :=
  of_six 34746302791680 ⟨record006, record006_core, record006_parameters, record006_coverage⟩
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

theorem record007_parameters : Parameters record007 (rowOfCode 32) 34746839597056 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 34746839597056 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch252.candidate25227 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 34746839597056
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.six_allowed record007 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch252.candidate25227_checked

theorem record007_result : Result (32, 34746839597056) :=
  of_six 34746839597056 ⟨record007, record007_core, record007_parameters, record007_coverage⟩
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

theorem record008_parameters : Parameters record008 (rowOfCode 32) 34746856112128 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 34746856112128 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch252.candidate25228 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 34746856112128
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.six_allowed record008 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch252.candidate25228_checked

theorem record008_result : Result (32, 34746856112128) :=
  of_six 34746856112128 ⟨record008, record008_core, record008_parameters, record008_coverage⟩
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

theorem record009_parameters : Parameters record009 (rowOfCode 32) 34747359363072 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 34747359363072 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch252.candidate25229 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 34747359363072
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.six_allowed record009 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch252.candidate25229_checked

theorem record009_result : Result (32, 34747359363072) :=
  of_six 34747359363072 ⟨record009, record009_core, record009_parameters, record009_coverage⟩
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

theorem record010_parameters : Parameters record010 (rowOfCode 32) 34763465294340 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 34763465294340 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch252.candidate25230 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 34763465294340
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.six_allowed record010 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch252.candidate25230_checked

theorem record010_result : Result (32, 34763465294340) :=
  of_six 34763465294340 ⟨record010, record010_core, record010_parameters, record010_coverage⟩
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

theorem record011_parameters : Parameters record011 (rowOfCode 32) 34763465428992 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record011_coverage : Coverage record011 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 34763465428992 :=
  GraphCoverageDescriptions.coverage_of_checked record011 GraphCoverageDescriptions.GraphCoverageBatch252.candidate25231 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 34763465428992
    (by rfl) record011_cells_exact
    (GraphCoverageDescriptions.six_allowed record011 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch252.candidate25231_checked

theorem record011_result : Result (32, 34763465428992) :=
  of_six 34763465428992 ⟨record011, record011_core, record011_parameters, record011_coverage⟩
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

theorem record012_parameters : Parameters record012 (rowOfCode 32) 34763482595328 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record012_coverage : Coverage record012 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 34763482595328 :=
  GraphCoverageDescriptions.coverage_of_checked record012 GraphCoverageDescriptions.GraphCoverageBatch252.candidate25232 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 34763482595328
    (by rfl) record012_cells_exact
    (GraphCoverageDescriptions.six_allowed record012 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch252.candidate25232_checked

theorem record012_result : Result (32, 34763482595328) :=
  of_six 34763482595328 ⟨record012, record012_core, record012_parameters, record012_coverage⟩
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

theorem record013_parameters : Parameters record013 (rowOfCode 32) 34763515625472 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record013_coverage : Coverage record013 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 34763515625472 :=
  GraphCoverageDescriptions.coverage_of_checked record013 GraphCoverageDescriptions.GraphCoverageBatch252.candidate25233 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 34763515625472
    (by rfl) record013_cells_exact
    (GraphCoverageDescriptions.six_allowed record013 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch252.candidate25233_checked

theorem record013_result : Result (32, 34763515625472) :=
  of_six 34763515625472 ⟨record013, record013_core, record013_parameters, record013_coverage⟩
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

theorem record014_parameters : Parameters record014 (rowOfCode 32) 34764539166720 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record014_coverage : Coverage record014 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 34764539166720 :=
  GraphCoverageDescriptions.coverage_of_checked record014 GraphCoverageDescriptions.GraphCoverageBatch252.candidate25234 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 34764539166720
    (by rfl) record014_cells_exact
    (GraphCoverageDescriptions.six_allowed record014 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch252.candidate25234_checked

theorem record014_result : Result (32, 34764539166720) :=
  of_six 34764539166720 ⟨record014, record014_core, record014_parameters, record014_coverage⟩
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

theorem record015_parameters : Parameters record015 (rowOfCode 32) 34772072403200 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record015_coverage : Coverage record015 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 34772072403200 :=
  GraphCoverageDescriptions.coverage_of_checked record015 GraphCoverageDescriptions.GraphCoverageBatch252.candidate25235 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 34772072403200
    (by rfl) record015_cells_exact
    (GraphCoverageDescriptions.six_allowed record015 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch252.candidate25235_checked

theorem record015_result : Result (32, 34772072403200) :=
  of_six 34772072403200 ⟨record015, record015_core, record015_parameters, record015_coverage⟩
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

theorem record016_parameters : Parameters record016 (rowOfCode 32) 34875134576896 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record016_coverage : Coverage record016 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 34875134576896 :=
  GraphCoverageDescriptions.coverage_of_checked record016 GraphCoverageDescriptions.GraphCoverageBatch252.candidate25236 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 34875134576896
    (by rfl) record016_cells_exact
    (GraphCoverageDescriptions.six_allowed record016 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch252.candidate25236_checked

theorem record016_result : Result (32, 34875134576896) :=
  of_six 34875134576896 ⟨record016, record016_core, record016_parameters, record016_coverage⟩
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

theorem record017_parameters : Parameters record017 (rowOfCode 32) 34875151548416 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record017_coverage : Coverage record017 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 34875151548416 :=
  GraphCoverageDescriptions.coverage_of_checked record017 GraphCoverageDescriptions.GraphCoverageBatch252.candidate25237 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 34875151548416
    (by rfl) record017_cells_exact
    (GraphCoverageDescriptions.six_allowed record017 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch252.candidate25237_checked

theorem record017_result : Result (32, 34875151548416) :=
  of_six 34875151548416 ⟨record017, record017_core, record017_parameters, record017_coverage⟩
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

theorem record018_parameters : Parameters record018 (rowOfCode 32) 34875688353792 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record018_coverage : Coverage record018 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 34875688353792 :=
  GraphCoverageDescriptions.coverage_of_checked record018 GraphCoverageDescriptions.GraphCoverageBatch252.candidate25238 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 34875688353792
    (by rfl) record018_cells_exact
    (GraphCoverageDescriptions.six_allowed record018 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch252.candidate25238_checked

theorem record018_result : Result (32, 34875688353792) :=
  of_six 34875688353792 ⟨record018, record018_core, record018_parameters, record018_coverage⟩
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

theorem record019_parameters : Parameters record019 (rowOfCode 32) 34892314445824 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record019_coverage : Coverage record019 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 34892314445824 :=
  GraphCoverageDescriptions.coverage_of_checked record019 GraphCoverageDescriptions.GraphCoverageBatch252.candidate25239 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 34892314445824
    (by rfl) record019_cells_exact
    (GraphCoverageDescriptions.six_allowed record019 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch252.candidate25239_checked

theorem record019_result : Result (32, 34892314445824) :=
  of_six 34892314445824 ⟨record019, record019_core, record019_parameters, record019_coverage⟩
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

theorem record020_parameters : Parameters record020 (rowOfCode 32) 34909494578192 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record020_coverage : Coverage record020 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 34909494578192 :=
  GraphCoverageDescriptions.coverage_of_checked record020 GraphCoverageDescriptions.GraphCoverageBatch252.candidate25240 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 34909494578192
    (by rfl) record020_cells_exact
    (GraphCoverageDescriptions.six_allowed record020 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch252.candidate25240_checked

theorem record020_result : Result (32, 34909494578192) :=
  of_six 34909494578192 ⟨record020, record020_core, record020_parameters, record020_coverage⟩
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

theorem record021_parameters : Parameters record021 (rowOfCode 32) 35115652745224 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record021_coverage : Coverage record021 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 35115652745224 :=
  GraphCoverageDescriptions.coverage_of_checked record021 GraphCoverageDescriptions.GraphCoverageBatch252.candidate25241 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 35115652745224
    (by rfl) record021_cells_exact
    (GraphCoverageDescriptions.six_allowed record021 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch252.candidate25241_checked

theorem record021_result : Result (32, 35115652745224) :=
  of_six 35115652745224 ⟨record021, record021_core, record021_parameters, record021_coverage⟩
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

theorem record022_parameters : Parameters record022 (rowOfCode 32) 35115669522432 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record022_coverage : Coverage record022 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 35115669522432 :=
  GraphCoverageDescriptions.coverage_of_checked record022 GraphCoverageDescriptions.GraphCoverageBatch252.candidate25242 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 35115669522432
    (by rfl) record022_cells_exact
    (GraphCoverageDescriptions.six_allowed record022 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch252.candidate25242_checked

theorem record022_result : Result (32, 35115669522432) :=
  of_six 35115669522432 ⟨record022, record022_core, record022_parameters, record022_coverage⟩
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

theorem record023_parameters : Parameters record023 (rowOfCode 32) 35115669782528 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record023_coverage : Coverage record023 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 35115669782528 :=
  GraphCoverageDescriptions.coverage_of_checked record023 GraphCoverageDescriptions.GraphCoverageBatch252.candidate25243 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 35115669782528
    (by rfl) record023_cells_exact
    (GraphCoverageDescriptions.six_allowed record023 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch252.candidate25243_checked

theorem record023_result : Result (32, 35115669782528) :=
  of_six 35115669782528 ⟨record023, record023_core, record023_parameters, record023_coverage⟩
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

theorem record024_parameters : Parameters record024 (rowOfCode 32) 35150012483584 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record024_coverage : Coverage record024 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 35150012483584 :=
  GraphCoverageDescriptions.coverage_of_checked record024 GraphCoverageDescriptions.GraphCoverageBatch252.candidate25244 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 35150012483584
    (by rfl) record024_cells_exact
    (GraphCoverageDescriptions.six_allowed record024 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch252.candidate25244_checked

theorem record024_result : Result (32, 35150012483584) :=
  of_six 35150012483584 ⟨record024, record024_core, record024_parameters, record024_coverage⟩
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

theorem record025_parameters : Parameters record025 (rowOfCode 32) 35150029389824 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record025_coverage : Coverage record025 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows 35150029389824 :=
  GraphCoverageDescriptions.coverage_of_checked record025 GraphCoverageDescriptions.GraphCoverageBatch252.candidate25245 FacetUniverses.FullSix0.cells SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (GraphCoverageDescriptions.quota 30)) 35150029389824
    (by rfl) record025_cells_exact
    (GraphCoverageDescriptions.six_allowed record025 30 (by decide +kernel))
    GraphEmbeddingCoverage.six_edges GraphCoverageDescriptions.GraphCoverageBatch252.candidate25245_checked

theorem record025_result : Result (32, 35150029389824) :=
  of_six 35150029389824 ⟨record025, record025_core, record025_parameters, record025_coverage⟩
#print axioms record025_result
end Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00090
