module
prelude
public import GraphInputsRow29Part00132Checked
public import GraphInputsRow29Part00132Metadata
public import GraphInputsRow29Part00132Frames
public import GraphInputsRow29Part00132Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch116
public import GraphCoverageBatch150


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132
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

theorem record000_parameters : Parameters record000 (rowOfCode 29) 22030575501568 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22030575501568 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22030575501568
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15010_checked

theorem record000_result : Result (29, 22030575501568) :=
  of_small 29 22030575501568 (by decide) ⟨record000, record000_core, record000_parameters, record000_coverage⟩
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

theorem record001_parameters : Parameters record001 (rowOfCode 29) 22033744863296 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22033744863296 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15011 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22033744863296
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15011_checked

theorem record001_result : Result (29, 22033744863296) :=
  of_small 29 22033744863296 (by decide) ⟨record001, record001_core, record001_parameters, record001_coverage⟩
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

theorem record002_parameters : Parameters record002 (rowOfCode 29) 22034801434688 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22034801434688 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15012 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22034801434688
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15012_checked

theorem record002_result : Result (29, 22034801434688) :=
  of_small 29 22034801434688 (by decide) ⟨record002, record002_core, record002_parameters, record002_coverage⟩
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

theorem record003_parameters : Parameters record003 (rowOfCode 29) 22034872549632 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22034872549632 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15013 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22034872549632
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15013_checked

theorem record003_result : Result (29, 22034872549632) :=
  of_small 29 22034872549632 (by decide) ⟨record003, record003_core, record003_parameters, record003_coverage⟩
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

theorem record004_parameters : Parameters record004 (rowOfCode 29) 22065974378752 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22065974378752 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15014 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22065974378752
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15014_checked

theorem record004_result : Result (29, 22065974378752) :=
  of_small 29 22065974378752 (by decide) ⟨record004, record004_core, record004_parameters, record004_coverage⟩
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

theorem record005_parameters : Parameters record005 (rowOfCode 29) 22077820117120 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22077820117120 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15015 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22077820117120
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15015_checked

theorem record005_result : Result (29, 22077820117120) :=
  of_small 29 22077820117120 (by decide) ⟨record005, record005_core, record005_parameters, record005_coverage⟩
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

theorem record006_parameters : Parameters record006 (rowOfCode 29) 22100299645184 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22100299645184 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15016 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22100299645184
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15016_checked

theorem record006_result : Result (29, 22100299645184) :=
  of_small 29 22100299645184 (by decide) ⟨record006, record006_core, record006_parameters, record006_coverage⟩
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

theorem record007_parameters : Parameters record007 (rowOfCode 29) 22100563788032 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22100563788032 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15017 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22100563788032
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15017_checked

theorem record007_result : Result (29, 22100563788032) :=
  of_small 29 22100563788032 (by decide) ⟨record007, record007_core, record007_parameters, record007_coverage⟩
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

theorem record008_parameters : Parameters record008 (rowOfCode 29) 22100572176384 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22100572176384 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11684 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22100572176384
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch116.candidate11684_checked

theorem record008_result : Result (29, 22100572176384) :=
  of_small 29 22100572176384 (by decide) ⟨record008, record008_core, record008_parameters, record008_coverage⟩
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

theorem record009_parameters : Parameters record009 (rowOfCode 29) 22104460296448 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22104460296448 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15018 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22104460296448
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15018_checked

theorem record009_result : Result (29, 22104460296448) :=
  of_small 29 22104460296448 (by decide) ⟨record009, record009_core, record009_parameters, record009_coverage⟩
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

theorem record010_parameters : Parameters record010 (rowOfCode 29) 22104724537600 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22104724537600 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15019 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22104724537600
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15019_checked

theorem record010_result : Result (29, 22104724537600) :=
  of_small 29 22104724537600 (by decide) ⟨record010, record010_core, record010_parameters, record010_coverage⟩
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

theorem record011_parameters : Parameters record011 (rowOfCode 29) 22104732925952 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record011_coverage : Coverage record011 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22104732925952 :=
  GraphCoverageDescriptions.coverage_of_checked record011 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15020 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22104732925952
    (by rfl) record011_cells_exact
    (GraphCoverageDescriptions.small_allowed record011 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15020_checked

theorem record011_result : Result (29, 22104732925952) :=
  of_small 29 22104732925952 (by decide) ⟨record011, record011_core, record011_parameters, record011_coverage⟩
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

theorem record012_parameters : Parameters record012 (rowOfCode 29) 22104856658176 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record012_coverage : Coverage record012 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22104856658176 :=
  GraphCoverageDescriptions.coverage_of_checked record012 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15021 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22104856658176
    (by rfl) record012_cells_exact
    (GraphCoverageDescriptions.small_allowed record012 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15021_checked

theorem record012_result : Result (29, 22104856658176) :=
  of_small 29 22104856658176 (by decide) ⟨record012, record012_core, record012_parameters, record012_coverage⟩
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

theorem record013_parameters : Parameters record013 (rowOfCode 29) 22107003093248 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record013_coverage : Coverage record013 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22107003093248 :=
  GraphCoverageDescriptions.coverage_of_checked record013 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15022 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22107003093248
    (by rfl) record013_cells_exact
    (GraphCoverageDescriptions.small_allowed record013 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15022_checked

theorem record013_result : Result (29, 22107003093248) :=
  of_small 29 22107003093248 (by decide) ⟨record013, record013_core, record013_parameters, record013_coverage⟩
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

theorem record014_parameters : Parameters record014 (rowOfCode 29) 22111055782016 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record014_coverage : Coverage record014 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22111055782016 :=
  GraphCoverageDescriptions.coverage_of_checked record014 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15023 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22111055782016
    (by rfl) record014_cells_exact
    (GraphCoverageDescriptions.small_allowed record014 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15023_checked

theorem record014_result : Result (29, 22111055782016) :=
  of_small 29 22111055782016 (by decide) ⟨record014, record014_core, record014_parameters, record014_coverage⟩
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

theorem record015_parameters : Parameters record015 (rowOfCode 29) 22113046036736 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record015_coverage : Coverage record015 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22113046036736 :=
  GraphCoverageDescriptions.coverage_of_checked record015 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15024 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22113046036736
    (by rfl) record015_cells_exact
    (GraphCoverageDescriptions.small_allowed record015 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15024_checked

theorem record015_result : Result (29, 22113046036736) :=
  of_small 29 22113046036736 (by decide) ⟨record015, record015_core, record015_parameters, record015_coverage⟩
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

theorem record016_parameters : Parameters record016 (rowOfCode 29) 22113054425088 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record016_coverage : Coverage record016 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22113054425088 :=
  GraphCoverageDescriptions.coverage_of_checked record016 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15025 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22113054425088
    (by rfl) record016_cells_exact
    (GraphCoverageDescriptions.small_allowed record016 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15025_checked

theorem record016_result : Result (29, 22113054425088) :=
  of_small 29 22113054425088 (by decide) ⟨record016, record016_core, record016_parameters, record016_coverage⟩
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

theorem record017_parameters : Parameters record017 (rowOfCode 29) 22113457029120 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record017_coverage : Coverage record017 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22113457029120 :=
  GraphCoverageDescriptions.coverage_of_checked record017 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15026 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22113457029120
    (by rfl) record017_cells_exact
    (GraphCoverageDescriptions.small_allowed record017 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15026_checked

theorem record017_result : Result (29, 22113457029120) :=
  of_small 29 22113457029120 (by decide) ⟨record017, record017_core, record017_parameters, record017_coverage⟩
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

theorem record018_parameters : Parameters record018 (rowOfCode 29) 22115604504576 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record018_coverage : Coverage record018 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22115604504576 :=
  GraphCoverageDescriptions.coverage_of_checked record018 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15027 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22115604504576
    (by rfl) record018_cells_exact
    (GraphCoverageDescriptions.small_allowed record018 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15027_checked

theorem record018_result : Result (29, 22115604504576) :=
  of_small 29 22115604504576 (by decide) ⟨record018, record018_core, record018_parameters, record018_coverage⟩
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

theorem record019_parameters : Parameters record019 (rowOfCode 29) 22119887945984 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record019_coverage : Coverage record019 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22119887945984 :=
  GraphCoverageDescriptions.coverage_of_checked record019 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15028 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22119887945984
    (by rfl) record019_cells_exact
    (GraphCoverageDescriptions.small_allowed record019 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15028_checked

theorem record019_result : Result (29, 22119887945984) :=
  of_small 29 22119887945984 (by decide) ⟨record019, record019_core, record019_parameters, record019_coverage⟩
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

theorem record020_parameters : Parameters record020 (rowOfCode 29) 22137948619008 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record020_coverage : Coverage record020 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22137948619008 :=
  GraphCoverageDescriptions.coverage_of_checked record020 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15029 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22137948619008
    (by rfl) record020_cells_exact
    (GraphCoverageDescriptions.small_allowed record020 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15029_checked

theorem record020_result : Result (29, 22137948619008) :=
  of_small 29 22137948619008 (by decide) ⟨record020, record020_core, record020_parameters, record020_coverage⟩
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

theorem record021_parameters : Parameters record021 (rowOfCode 29) 22146270118144 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record021_coverage : Coverage record021 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22146270118144 :=
  GraphCoverageDescriptions.coverage_of_checked record021 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15030 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22146270118144
    (by rfl) record021_cells_exact
    (GraphCoverageDescriptions.small_allowed record021 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15030_checked

theorem record021_result : Result (29, 22146270118144) :=
  of_small 29 22146270118144 (by decide) ⟨record021, record021_core, record021_parameters, record021_coverage⟩
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

theorem record022_parameters : Parameters record022 (rowOfCode 29) 22173441917184 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record022_coverage : Coverage record022 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22173441917184 :=
  GraphCoverageDescriptions.coverage_of_checked record022 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15031 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22173441917184
    (by rfl) record022_cells_exact
    (GraphCoverageDescriptions.small_allowed record022 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15031_checked

theorem record022_result : Result (29, 22173441917184) :=
  of_small 29 22173441917184 (by decide) ⟨record022, record022_core, record022_parameters, record022_coverage⟩
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

theorem record023_parameters : Parameters record023 (rowOfCode 29) 22173450305536 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record023_coverage : Coverage record023 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22173450305536 :=
  GraphCoverageDescriptions.coverage_of_checked record023 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15032 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22173450305536
    (by rfl) record023_cells_exact
    (GraphCoverageDescriptions.small_allowed record023 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15032_checked

theorem record023_result : Result (29, 22173450305536) :=
  of_small 29 22173450305536 (by decide) ⟨record023, record023_core, record023_parameters, record023_coverage⟩
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

theorem record024_parameters : Parameters record024 (rowOfCode 29) 22175588352256 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record024_coverage : Coverage record024 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22175588352256 :=
  GraphCoverageDescriptions.coverage_of_checked record024 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15033 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22175588352256
    (by rfl) record024_cells_exact
    (GraphCoverageDescriptions.small_allowed record024 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15033_checked

theorem record024_result : Result (29, 22175588352256) :=
  of_small 29 22175588352256 (by decide) ⟨record024, record024_core, record024_parameters, record024_coverage⟩
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

theorem record025_parameters : Parameters record025 (rowOfCode 29) 22181763416320 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record025_coverage : Coverage record025 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22181763416320 :=
  GraphCoverageDescriptions.coverage_of_checked record025 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15034 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22181763416320
    (by rfl) record025_cells_exact
    (GraphCoverageDescriptions.small_allowed record025 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15034_checked

theorem record025_result : Result (29, 22181763416320) :=
  of_small 29 22181763416320 (by decide) ⟨record025, record025_core, record025_parameters, record025_coverage⟩
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

theorem record026_parameters : Parameters record026 (rowOfCode 29) 22181771804672 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record026_coverage : Coverage record026 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22181771804672 :=
  GraphCoverageDescriptions.coverage_of_checked record026 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15035 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22181771804672
    (by rfl) record026_cells_exact
    (GraphCoverageDescriptions.small_allowed record026 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15035_checked

theorem record026_result : Result (29, 22181771804672) :=
  of_small 29 22181771804672 (by decide) ⟨record026, record026_core, record026_parameters, record026_coverage⟩
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

theorem record027_parameters : Parameters record027 (rowOfCode 29) 22182042288128 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record027_coverage : Coverage record027 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22182042288128 :=
  GraphCoverageDescriptions.coverage_of_checked record027 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15036 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22182042288128
    (by rfl) record027_cells_exact
    (GraphCoverageDescriptions.small_allowed record027 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15036_checked

theorem record027_result : Result (29, 22182042288128) :=
  of_small 29 22182042288128 (by decide) ⟨record027, record027_core, record027_parameters, record027_coverage⟩
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

theorem record028_parameters : Parameters record028 (rowOfCode 29) 22182166020352 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record028_coverage : Coverage record028 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22182166020352 :=
  GraphCoverageDescriptions.coverage_of_checked record028 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15037 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22182166020352
    (by rfl) record028_cells_exact
    (GraphCoverageDescriptions.small_allowed record028 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15037_checked

theorem record028_result : Result (29, 22182166020352) :=
  of_small 29 22182166020352 (by decide) ⟨record028, record028_core, record028_parameters, record028_coverage⟩
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

theorem record029_parameters : Parameters record029 (rowOfCode 29) 22218672185600 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record029_coverage : Coverage record029 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22218672185600 :=
  GraphCoverageDescriptions.coverage_of_checked record029 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15038 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22218672185600
    (by rfl) record029_cells_exact
    (GraphCoverageDescriptions.small_allowed record029 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15038_checked

theorem record029_result : Result (29, 22218672185600) :=
  of_small 29 22218672185600 (by decide) ⟨record029, record029_core, record029_parameters, record029_coverage⟩
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

theorem record030_parameters : Parameters record030 (rowOfCode 29) 22283704877312 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record030_coverage : Coverage record030 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22283704877312 :=
  GraphCoverageDescriptions.coverage_of_checked record030 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15039 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22283704877312
    (by rfl) record030_cells_exact
    (GraphCoverageDescriptions.small_allowed record030 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15039_checked

theorem record030_result : Result (29, 22283704877312) :=
  of_small 29 22283704877312 (by decide) ⟨record030, record030_core, record030_parameters, record030_coverage⟩
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

theorem record031_parameters : Parameters record031 (rowOfCode 29) 22312758870272 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record031_coverage : Coverage record031 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22312758870272 :=
  GraphCoverageDescriptions.coverage_of_checked record031 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15040 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22312758870272
    (by rfl) record031_cells_exact
    (GraphCoverageDescriptions.small_allowed record031 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15040_checked

theorem record031_result : Result (29, 22312758870272) :=
  of_small 29 22312758870272 (by decide) ⟨record031, record031_core, record031_parameters, record031_coverage⟩
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

theorem record032_parameters : Parameters record032 (rowOfCode 29) 22313027272960 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record032_coverage : Coverage record032 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22313027272960 :=
  GraphCoverageDescriptions.coverage_of_checked record032 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15041 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22313027272960
    (by rfl) record032_cells_exact
    (GraphCoverageDescriptions.small_allowed record032 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15041_checked

theorem record032_result : Result (29, 22313027272960) :=
  of_small 29 22313027272960 (by decide) ⟨record032, record032_core, record032_parameters, record032_coverage⟩
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

theorem record033_parameters : Parameters record033 (rowOfCode 29) 22313038782464 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record033_coverage : Coverage record033 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22313038782464 :=
  GraphCoverageDescriptions.coverage_of_checked record033 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15042 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22313038782464
    (by rfl) record033_cells_exact
    (GraphCoverageDescriptions.small_allowed record033 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15042_checked

theorem record033_result : Result (29, 22313038782464) :=
  of_small 29 22313038782464 (by decide) ⟨record033, record033_core, record033_parameters, record033_coverage⟩
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

theorem record034_parameters : Parameters record034 (rowOfCode 29) 22313161474304 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record034_coverage : Coverage record034 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22313161474304 :=
  GraphCoverageDescriptions.coverage_of_checked record034 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15043 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22313161474304
    (by rfl) record034_cells_exact
    (GraphCoverageDescriptions.small_allowed record034 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15043_checked

theorem record034_result : Result (29, 22313161474304) :=
  of_small 29 22313161474304 (by decide) ⟨record034, record034_core, record034_parameters, record034_coverage⟩
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

theorem record035_parameters : Parameters record035 (rowOfCode 29) 22319202337024 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record035_coverage : Coverage record035 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22319202337024 :=
  GraphCoverageDescriptions.coverage_of_checked record035 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15044 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22319202337024
    (by rfl) record035_cells_exact
    (GraphCoverageDescriptions.small_allowed record035 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15044_checked

theorem record035_result : Result (29, 22319202337024) :=
  of_small 29 22319202337024 (by decide) ⟨record035, record035_core, record035_parameters, record035_coverage⟩
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

theorem record036_parameters : Parameters record036 (rowOfCode 29) 22319206563840 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record036_coverage : Coverage record036 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22319206563840 :=
  GraphCoverageDescriptions.coverage_of_checked record036 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15045 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22319206563840
    (by rfl) record036_cells_exact
    (GraphCoverageDescriptions.small_allowed record036 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15045_checked

theorem record036_result : Result (29, 22319206563840) :=
  of_small 29 22319206563840 (by decide) ⟨record036, record036_core, record036_parameters, record036_coverage⟩
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

theorem record037_parameters : Parameters record037 (rowOfCode 29) 22319212806144 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record037_coverage : Coverage record037 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22319212806144 :=
  GraphCoverageDescriptions.coverage_of_checked record037 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11685 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22319212806144
    (by rfl) record037_cells_exact
    (GraphCoverageDescriptions.small_allowed record037 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch116.candidate11685_checked

theorem record037_result : Result (29, 22319212806144) :=
  of_small 29 22319212806144 (by decide) ⟨record037, record037_core, record037_parameters, record037_coverage⟩
#print axioms record037_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132
