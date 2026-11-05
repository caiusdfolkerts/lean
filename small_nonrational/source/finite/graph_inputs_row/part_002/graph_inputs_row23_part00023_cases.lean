module
prelude
public import GraphInputsRow23Part00023Checked
public import GraphInputsRow23Part00023Metadata
public import GraphInputsRow23Part00023Frames
public import GraphInputsRow23Part00023Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch057


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023
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

theorem record000_parameters : Parameters record000 (rowOfCode 23) 28974137737216 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 28974137737216 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05717 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 28974137737216
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05717_checked

theorem record000_result : Result (23, 28974137737216) :=
  of_small 23 28974137737216 (by decide) ⟨record000, record000_core, record000_parameters, record000_coverage⟩
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

theorem record001_parameters : Parameters record001 (rowOfCode 23) 28975997010048 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 28975997010048 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05718 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 28975997010048
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05718_checked

theorem record001_result : Result (23, 28975997010048) :=
  of_small 23 28975997010048 (by decide) ⟨record001, record001_core, record001_parameters, record001_coverage⟩
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

theorem record002_parameters : Parameters record002 (rowOfCode 23) 28976399516160 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 28976399516160 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05719 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 28976399516160
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05719_checked

theorem record002_result : Result (23, 28976399516160) :=
  of_small 23 28976399516160 (by decide) ⟨record002, record002_core, record002_parameters, record002_coverage⟩
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

theorem record003_parameters : Parameters record003 (rowOfCode 23) 29038475509760 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29038475509760 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05720 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29038475509760
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05720_checked

theorem record003_result : Result (23, 29038475509760) :=
  of_small 23 29038475509760 (by decide) ⟨record003, record003_core, record003_parameters, record003_coverage⟩
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

theorem record004_parameters : Parameters record004 (rowOfCode 23) 29070572158976 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29070572158976 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05721 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29070572158976
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05721_checked

theorem record004_result : Result (23, 29070572158976) :=
  of_small 23 29070572158976 (by decide) ⟨record004, record004_core, record004_parameters, record004_coverage⟩
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

theorem record005_parameters : Parameters record005 (rowOfCode 23) 29140451361024 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29140451361024 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05722 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29140451361024
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05722_checked

theorem record005_result : Result (23, 29140451361024) :=
  of_small 23 29140451361024 (by decide) ⟨record005, record005_core, record005_parameters, record005_coverage⟩
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

theorem record006_parameters : Parameters record006 (rowOfCode 23) 29140459749376 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29140459749376 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05723 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29140459749376
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05723_checked

theorem record006_result : Result (23, 29140459749376) :=
  of_small 23 29140459749376 (by decide) ⟨record006, record006_core, record006_parameters, record006_coverage⟩
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

theorem record007_parameters : Parameters record007 (rowOfCode 23) 29140583481600 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29140583481600 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05724 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29140583481600
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05724_checked

theorem record007_result : Result (23, 29140583481600) :=
  of_small 23 29140583481600 (by decide) ⟨record007, record007_core, record007_parameters, record007_coverage⟩
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

theorem record008_parameters : Parameters record008 (rowOfCode 23) 29140587708416 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29140587708416 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05725 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29140587708416
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05725_checked

theorem record008_result : Result (23, 29140587708416) :=
  of_small 23 29140587708416 (by decide) ⟨record008, record008_core, record008_parameters, record008_coverage⟩
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

theorem record009_parameters : Parameters record009 (rowOfCode 23) 29140591869952 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29140591869952 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05726 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29140591869952
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05726_checked

theorem record009_result : Result (23, 29140591869952) :=
  of_small 23 29140591869952 (by decide) ⟨record009, record009_core, record009_parameters, record009_coverage⟩
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

theorem record010_parameters : Parameters record010 (rowOfCode 23) 29140682572032 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29140682572032 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05727 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29140682572032
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05727_checked

theorem record010_result : Result (23, 29140682572032) :=
  of_small 23 29140682572032 (by decide) ⟨record010, record010_core, record010_parameters, record010_coverage⟩
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

theorem record011_parameters : Parameters record011 (rowOfCode 23) 29140694601728 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record011_coverage : Coverage record011 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29140694601728 :=
  GraphCoverageDescriptions.coverage_of_checked record011 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05728 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29140694601728
    (by rfl) record011_cells_exact
    (GraphCoverageDescriptions.small_allowed record011 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05728_checked

theorem record011_result : Result (23, 29140694601728) :=
  of_small 23 29140694601728 (by decide) ⟨record011, record011_core, record011_parameters, record011_coverage⟩
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

theorem record012_parameters : Parameters record012 (rowOfCode 23) 29140851916928 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record012_coverage : Coverage record012 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29140851916928 :=
  GraphCoverageDescriptions.coverage_of_checked record012 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05729 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29140851916928
    (by rfl) record012_cells_exact
    (GraphCoverageDescriptions.small_allowed record012 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05729_checked

theorem record012_result : Result (23, 29140851916928) :=
  of_small 23 29140851916928 (by decide) ⟨record012, record012_core, record012_parameters, record012_coverage⟩
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

theorem record013_parameters : Parameters record013 (rowOfCode 23) 29140856111104 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record013_coverage : Coverage record013 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29140856111104 :=
  GraphCoverageDescriptions.coverage_of_checked record013 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05730 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29140856111104
    (by rfl) record013_cells_exact
    (GraphCoverageDescriptions.small_allowed record013 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05730_checked

theorem record013_result : Result (23, 29140856111104) :=
  of_small 23 29140856111104 (by decide) ⟨record013, record013_core, record013_parameters, record013_coverage⟩
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

theorem record014_parameters : Parameters record014 (rowOfCode 23) 29140951007360 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record014_coverage : Coverage record014 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29140951007360 :=
  GraphCoverageDescriptions.coverage_of_checked record014 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05731 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29140951007360
    (by rfl) record014_cells_exact
    (GraphCoverageDescriptions.small_allowed record014 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05731_checked

theorem record014_result : Result (23, 29140951007360) :=
  of_small 23 29140951007360 (by decide) ⟨record014, record014_core, record014_parameters, record014_coverage⟩
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

theorem record015_parameters : Parameters record015 (rowOfCode 23) 29141085208704 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record015_coverage : Coverage record015 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29141085208704 :=
  GraphCoverageDescriptions.coverage_of_checked record015 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05732 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29141085208704
    (by rfl) record015_cells_exact
    (GraphCoverageDescriptions.small_allowed record015 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05732_checked

theorem record015_result : Result (23, 29141085208704) :=
  of_small 23 29141085208704 (by decide) ⟨record015, record015_core, record015_parameters, record015_coverage⟩
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

theorem record016_parameters : Parameters record016 (rowOfCode 23) 29146923696384 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record016_coverage : Coverage record016 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29146923696384 :=
  GraphCoverageDescriptions.coverage_of_checked record016 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05733 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29146923696384
    (by rfl) record016_cells_exact
    (GraphCoverageDescriptions.small_allowed record016 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05733_checked

theorem record016_result : Result (23, 29146923696384) :=
  of_small 23 29146923696384 (by decide) ⟨record016, record016_core, record016_parameters, record016_coverage⟩
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

theorem record017_parameters : Parameters record017 (rowOfCode 23) 29146935726080 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record017_coverage : Coverage record017 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29146935726080 :=
  GraphCoverageDescriptions.coverage_of_checked record017 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05734 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29146935726080
    (by rfl) record017_cells_exact
    (GraphCoverageDescriptions.small_allowed record017 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05734_checked

theorem record017_result : Result (23, 29146935726080) :=
  of_small 23 29146935726080 (by decide) ⟨record017, record017_core, record017_parameters, record017_coverage⟩
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

theorem record018_parameters : Parameters record018 (rowOfCode 23) 29147027013632 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record018_coverage : Coverage record018 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29147027013632 :=
  GraphCoverageDescriptions.coverage_of_checked record018 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05735 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29147027013632
    (by rfl) record018_cells_exact
    (GraphCoverageDescriptions.small_allowed record018 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05735_checked

theorem record018_result : Result (23, 29147027013632) :=
  of_small 23 29147027013632 (by decide) ⟨record018, record018_core, record018_parameters, record018_coverage⟩
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

theorem record019_parameters : Parameters record019 (rowOfCode 23) 29147067846656 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record019_coverage : Coverage record019 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29147067846656 :=
  GraphCoverageDescriptions.coverage_of_checked record019 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05736 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29147067846656
    (by rfl) record019_cells_exact
    (GraphCoverageDescriptions.small_allowed record019 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05736_checked

theorem record019_result : Result (23, 29147067846656) :=
  of_small 23 29147067846656 (by decide) ⟨record019, record019_core, record019_parameters, record019_coverage⟩
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

theorem record020_parameters : Parameters record020 (rowOfCode 23) 29147293302912 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record020_coverage : Coverage record020 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29147293302912 :=
  GraphCoverageDescriptions.coverage_of_checked record020 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05737 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29147293302912
    (by rfl) record020_cells_exact
    (GraphCoverageDescriptions.small_allowed record020 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05737_checked

theorem record020_result : Result (23, 29147293302912) :=
  of_small 23 29147293302912 (by decide) ⟨record020, record020_core, record020_parameters, record020_coverage⟩
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

theorem record021_parameters : Parameters record021 (rowOfCode 23) 29147295416320 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record021_coverage : Coverage record021 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29147295416320 :=
  GraphCoverageDescriptions.coverage_of_checked record021 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05738 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29147295416320
    (by rfl) record021_cells_exact
    (GraphCoverageDescriptions.small_allowed record021 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05738_checked

theorem record021_result : Result (23, 29147295416320) :=
  of_small 23 29147295416320 (by decide) ⟨record021, record021_core, record021_parameters, record021_coverage⟩
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

theorem record022_parameters : Parameters record022 (rowOfCode 23) 29147326333056 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record022_coverage : Coverage record022 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29147326333056 :=
  GraphCoverageDescriptions.coverage_of_checked record022 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05739 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29147326333056
    (by rfl) record022_cells_exact
    (GraphCoverageDescriptions.small_allowed record022 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05739_checked

theorem record022_result : Result (23, 29147326333056) :=
  of_small 23 29147326333056 (by decide) ⟨record022, record022_core, record022_parameters, record022_coverage⟩
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

theorem record023_parameters : Parameters record023 (rowOfCode 23) 29148198736128 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record023_coverage : Coverage record023 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29148198736128 :=
  GraphCoverageDescriptions.coverage_of_checked record023 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05740 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29148198736128
    (by rfl) record023_cells_exact
    (GraphCoverageDescriptions.small_allowed record023 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05740_checked

theorem record023_result : Result (23, 29148198736128) :=
  of_small 23 29148198736128 (by decide) ⟨record023, record023_core, record023_parameters, record023_coverage⟩
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

theorem record024_parameters : Parameters record024 (rowOfCode 23) 29148467171456 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record024_coverage : Coverage record024 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29148467171456 :=
  GraphCoverageDescriptions.coverage_of_checked record024 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05741 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29148467171456
    (by rfl) record024_cells_exact
    (GraphCoverageDescriptions.small_allowed record024 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05741_checked

theorem record024_result : Result (23, 29148467171456) :=
  of_small 23 29148467171456 (by decide) ⟨record024, record024_core, record024_parameters, record024_coverage⟩
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

theorem record025_parameters : Parameters record025 (rowOfCode 23) 29155647832192 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record025_coverage : Coverage record025 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29155647832192 :=
  GraphCoverageDescriptions.coverage_of_checked record025 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05742 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29155647832192
    (by rfl) record025_cells_exact
    (GraphCoverageDescriptions.small_allowed record025 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05742_checked

theorem record025_result : Result (23, 29155647832192) :=
  of_small 23 29155647832192 (by decide) ⟨record025, record025_core, record025_parameters, record025_coverage⟩
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

theorem record026_parameters : Parameters record026 (rowOfCode 23) 29155653586944 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record026_coverage : Coverage record026 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29155653586944 :=
  GraphCoverageDescriptions.coverage_of_checked record026 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05743 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29155653586944
    (by rfl) record026_cells_exact
    (GraphCoverageDescriptions.small_allowed record026 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05743_checked

theorem record026_result : Result (23, 29155653586944) :=
  of_small 23 29155653586944 (by decide) ⟨record026, record026_core, record026_parameters, record026_coverage⟩
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

theorem record027_parameters : Parameters record027 (rowOfCode 23) 29175998611712 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record027_coverage : Coverage record027 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29175998611712 :=
  GraphCoverageDescriptions.coverage_of_checked record027 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05744 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29175998611712
    (by rfl) record027_cells_exact
    (GraphCoverageDescriptions.small_allowed record027 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05744_checked

theorem record027_result : Result (23, 29175998611712) :=
  of_small 23 29175998611712 (by decide) ⟨record027, record027_core, record027_parameters, record027_coverage⟩
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

theorem record028_parameters : Parameters record028 (rowOfCode 23) 29176002838528 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record028_coverage : Coverage record028 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29176002838528 :=
  GraphCoverageDescriptions.coverage_of_checked record028 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05745 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29176002838528
    (by rfl) record028_cells_exact
    (GraphCoverageDescriptions.small_allowed record028 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05745_checked

theorem record028_result : Result (23, 29176002838528) :=
  of_small 23 29176002838528 (by decide) ⟨record028, record028_core, record028_parameters, record028_coverage⟩
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

theorem record029_parameters : Parameters record029 (rowOfCode 23) 29176007000064 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record029_coverage : Coverage record029 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29176007000064 :=
  GraphCoverageDescriptions.coverage_of_checked record029 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05746 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29176007000064
    (by rfl) record029_cells_exact
    (GraphCoverageDescriptions.small_allowed record029 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05746_checked

theorem record029_result : Result (23, 29176007000064) :=
  of_small 23 29176007000064 (by decide) ⟨record029, record029_core, record029_parameters, record029_coverage⟩
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

theorem record030_parameters : Parameters record030 (rowOfCode 23) 29176010641408 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record030_coverage : Coverage record030 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29176010641408 :=
  GraphCoverageDescriptions.coverage_of_checked record030 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05747 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29176010641408
    (by rfl) record030_cells_exact
    (GraphCoverageDescriptions.small_allowed record030 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05747_checked

theorem record030_result : Result (23, 29176010641408) :=
  of_small 23 29176010641408 (by decide) ⟨record030, record030_core, record030_parameters, record030_coverage⟩
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

theorem record031_parameters : Parameters record031 (rowOfCode 23) 29176267047040 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record031_coverage : Coverage record031 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29176267047040 :=
  GraphCoverageDescriptions.coverage_of_checked record031 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05748 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29176267047040
    (by rfl) record031_cells_exact
    (GraphCoverageDescriptions.small_allowed record031 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05748_checked

theorem record031_result : Result (23, 29176267047040) :=
  of_small 23 29176267047040 (by decide) ⟨record031, record031_core, record031_parameters, record031_coverage⟩
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

theorem record032_parameters : Parameters record032 (rowOfCode 23) 29176518414464 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record032_coverage : Coverage record032 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29176518414464 :=
  GraphCoverageDescriptions.coverage_of_checked record032 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05749 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29176518414464
    (by rfl) record032_cells_exact
    (GraphCoverageDescriptions.small_allowed record032 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05749_checked

theorem record032_result : Result (23, 29176518414464) :=
  of_small 23 29176518414464 (by decide) ⟨record032, record032_core, record032_parameters, record032_coverage⟩
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

theorem record033_parameters : Parameters record033 (rowOfCode 23) 29177059409920 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record033_coverage : Coverage record033 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29177059409920 :=
  GraphCoverageDescriptions.coverage_of_checked record033 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05750 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29177059409920
    (by rfl) record033_cells_exact
    (GraphCoverageDescriptions.small_allowed record033 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05750_checked

theorem record033_result : Result (23, 29177059409920) :=
  of_small 23 29177059409920 (by decide) ⟨record033, record033_core, record033_parameters, record033_coverage⟩
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

theorem record034_parameters : Parameters record034 (rowOfCode 23) 29177591890560 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record034_coverage : Coverage record034 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29177591890560 :=
  GraphCoverageDescriptions.coverage_of_checked record034 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05751 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29177591890560
    (by rfl) record034_cells_exact
    (GraphCoverageDescriptions.small_allowed record034 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05751_checked

theorem record034_result : Result (23, 29177591890560) :=
  of_small 23 29177591890560 (by decide) ⟨record034, record034_core, record034_parameters, record034_coverage⟩
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

theorem record035_parameters : Parameters record035 (rowOfCode 23) 29180303511552 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record035_coverage : Coverage record035 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29180303511552 :=
  GraphCoverageDescriptions.coverage_of_checked record035 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05752 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29180303511552
    (by rfl) record035_cells_exact
    (GraphCoverageDescriptions.small_allowed record035 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05752_checked

theorem record035_result : Result (23, 29180303511552) :=
  of_small 23 29180303511552 (by decide) ⟨record035, record035_core, record035_parameters, record035_coverage⟩
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

theorem record036_parameters : Parameters record036 (rowOfCode 23) 29180561997952 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record036_coverage : Coverage record036 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29180561997952 :=
  GraphCoverageDescriptions.coverage_of_checked record036 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05753 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29180561997952
    (by rfl) record036_cells_exact
    (GraphCoverageDescriptions.small_allowed record036 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05753_checked

theorem record036_result : Result (23, 29180561997952) :=
  of_small 23 29180561997952 (by decide) ⟨record036, record036_core, record036_parameters, record036_coverage⟩
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

theorem record037_parameters : Parameters record037 (rowOfCode 23) 29180567752704 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record037_coverage : Coverage record037 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29180567752704 :=
  GraphCoverageDescriptions.coverage_of_checked record037 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05754 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29180567752704
    (by rfl) record037_cells_exact
    (GraphCoverageDescriptions.small_allowed record037 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05754_checked

theorem record037_result : Result (23, 29180567752704) :=
  of_small 23 29180567752704 (by decide) ⟨record037, record037_core, record037_parameters, record037_coverage⟩
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

theorem record038_parameters : Parameters record038 (rowOfCode 23) 29180679164032 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record038_coverage : Coverage record038 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29180679164032 :=
  GraphCoverageDescriptions.coverage_of_checked record038 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05755 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29180679164032
    (by rfl) record038_cells_exact
    (GraphCoverageDescriptions.small_allowed record038 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05755_checked

theorem record038_result : Result (23, 29180679164032) :=
  of_small 23 29180679164032 (by decide) ⟨record038, record038_core, record038_parameters, record038_coverage⟩
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

theorem record039_parameters : Parameters record039 (rowOfCode 23) 29181752640128 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record039_coverage : Coverage record039 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29181752640128 :=
  GraphCoverageDescriptions.coverage_of_checked record039 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05756 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29181752640128
    (by rfl) record039_cells_exact
    (GraphCoverageDescriptions.small_allowed record039 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05756_checked

theorem record039_result : Result (23, 29181752640128) :=
  of_small 23 29181752640128 (by decide) ⟨record039, record039_core, record039_parameters, record039_coverage⟩
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

theorem record040_parameters : Parameters record040 (rowOfCode 23) 29189000663168 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record040_coverage : Coverage record040 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29189000663168 :=
  GraphCoverageDescriptions.coverage_of_checked record040 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05757 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29189000663168
    (by rfl) record040_cells_exact
    (GraphCoverageDescriptions.small_allowed record040 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05757_checked

theorem record040_result : Result (23, 29189000663168) :=
  of_small 23 29189000663168 (by decide) ⟨record040, record040_core, record040_parameters, record040_coverage⟩
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

theorem record041_parameters : Parameters record041 (rowOfCode 23) 29190074139264 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record041_coverage : Coverage record041 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29190074139264 :=
  GraphCoverageDescriptions.coverage_of_checked record041 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05758 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29190074139264
    (by rfl) record041_cells_exact
    (GraphCoverageDescriptions.small_allowed record041 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05758_checked

theorem record041_result : Result (23, 29190074139264) :=
  of_small 23 29190074139264 (by decide) ⟨record041, record041_core, record041_parameters, record041_coverage⟩
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

theorem record042_parameters : Parameters record042 (rowOfCode 23) 29276796125440 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record042_coverage : Coverage record042 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29276796125440 :=
  GraphCoverageDescriptions.coverage_of_checked record042 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05759 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29276796125440
    (by rfl) record042_cells_exact
    (GraphCoverageDescriptions.small_allowed record042 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05759_checked

theorem record042_result : Result (23, 29276796125440) :=
  of_small 23 29276796125440 (by decide) ⟨record042, record042_core, record042_parameters, record042_coverage⟩
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

theorem record043_parameters : Parameters record043 (rowOfCode 23) 29276804513792 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record043_coverage : Coverage record043 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29276804513792 :=
  GraphCoverageDescriptions.coverage_of_checked record043 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05760 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29276804513792
    (by rfl) record043_cells_exact
    (GraphCoverageDescriptions.small_allowed record043 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05760_checked

theorem record043_result : Result (23, 29276804513792) :=
  of_small 23 29276804513792 (by decide) ⟨record043, record043_core, record043_parameters, record043_coverage⟩
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

theorem record044_parameters : Parameters record044 (rowOfCode 23) 29276808155136 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record044_coverage : Coverage record044 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29276808155136 :=
  GraphCoverageDescriptions.coverage_of_checked record044 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05761 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29276808155136
    (by rfl) record044_cells_exact
    (GraphCoverageDescriptions.small_allowed record044 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05761_checked

theorem record044_result : Result (23, 29276808155136) :=
  of_small 23 29276808155136 (by decide) ⟨record044, record044_core, record044_parameters, record044_coverage⟩
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

theorem record045_parameters : Parameters record045 (rowOfCode 23) 29276940275712 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record045_coverage : Coverage record045 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29276940275712 :=
  GraphCoverageDescriptions.coverage_of_checked record045 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05762 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29276940275712
    (by rfl) record045_cells_exact
    (GraphCoverageDescriptions.small_allowed record045 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05762_checked

theorem record045_result : Result (23, 29276940275712) :=
  of_small 23 29276940275712 (by decide) ⟨record045, record045_core, record045_parameters, record045_coverage⟩
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

theorem record046_parameters : Parameters record046 (rowOfCode 23) 29277198762112 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record046_coverage : Coverage record046 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29277198762112 :=
  GraphCoverageDescriptions.coverage_of_checked record046 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05763 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29277198762112
    (by rfl) record046_cells_exact
    (GraphCoverageDescriptions.small_allowed record046 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05763_checked

theorem record046_result : Result (23, 29277198762112) :=
  of_small 23 29277198762112 (by decide) ⟨record046, record046_core, record046_parameters, record046_coverage⟩
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

theorem record047_parameters : Parameters record047 (rowOfCode 23) 29277204516864 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record047_coverage : Coverage record047 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29277204516864 :=
  GraphCoverageDescriptions.coverage_of_checked record047 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05764 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29277204516864
    (by rfl) record047_cells_exact
    (GraphCoverageDescriptions.small_allowed record047 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05764_checked

theorem record047_result : Result (23, 29277204516864) :=
  of_small 23 29277204516864 (by decide) ⟨record047, record047_core, record047_parameters, record047_coverage⟩
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

theorem record048_parameters : Parameters record048 (rowOfCode 23) 29283643822080 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record048_coverage : Coverage record048 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29283643822080 :=
  GraphCoverageDescriptions.coverage_of_checked record048 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05765 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29283643822080
    (by rfl) record048_cells_exact
    (GraphCoverageDescriptions.small_allowed record048 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05765_checked

theorem record048_result : Result (23, 29283643822080) :=
  of_small 23 29283643822080 (by decide) ⟨record048, record048_core, record048_parameters, record048_coverage⟩
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

theorem record049_parameters : Parameters record049 (rowOfCode 23) 29284498472960 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record049_coverage : Coverage record049 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29284498472960 :=
  GraphCoverageDescriptions.coverage_of_checked record049 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05766 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29284498472960
    (by rfl) record049_cells_exact
    (GraphCoverageDescriptions.small_allowed record049 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05766_checked

theorem record049_result : Result (23, 29284498472960) :=
  of_small 23 29284498472960 (by decide) ⟨record049, record049_core, record049_parameters, record049_coverage⟩
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

theorem record050_parameters : Parameters record050 (rowOfCode 23) 29285637750784 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record050_coverage : Coverage record050 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29285637750784 :=
  GraphCoverageDescriptions.coverage_of_checked record050 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05767 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29285637750784
    (by rfl) record050_cells_exact
    (GraphCoverageDescriptions.small_allowed record050 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05767_checked

theorem record050_result : Result (23, 29285637750784) :=
  of_small 23 29285637750784 (by decide) ⟨record050, record050_core, record050_parameters, record050_coverage⟩
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

theorem record051_parameters : Parameters record051 (rowOfCode 23) 29291878551680 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record051_coverage : Coverage record051 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29291878551680 :=
  GraphCoverageDescriptions.coverage_of_checked record051 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05768 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29291878551680
    (by rfl) record051_cells_exact
    (GraphCoverageDescriptions.small_allowed record051 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05768_checked

theorem record051_result : Result (23, 29291878551680) :=
  of_small 23 29291878551680 (by decide) ⟨record051, record051_core, record051_parameters, record051_coverage⟩
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

theorem record052_parameters : Parameters record052 (rowOfCode 23) 29322152771584 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record052_coverage : Coverage record052 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29322152771584 :=
  GraphCoverageDescriptions.coverage_of_checked record052 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05769 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29322152771584
    (by rfl) record052_cells_exact
    (GraphCoverageDescriptions.small_allowed record052 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05769_checked

theorem record052_result : Result (23, 29322152771584) :=
  of_small 23 29322152771584 (by decide) ⟨record052, record052_core, record052_parameters, record052_coverage⟩
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

theorem record053_parameters : Parameters record053 (rowOfCode 23) 29414235078784 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record053_coverage : Coverage record053 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29414235078784 :=
  GraphCoverageDescriptions.coverage_of_checked record053 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05770 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29414235078784
    (by rfl) record053_cells_exact
    (GraphCoverageDescriptions.small_allowed record053 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05770_checked

theorem record053_result : Result (23, 29414235078784) :=
  of_small 23 29414235078784 (by decide) ⟨record053, record053_core, record053_parameters, record053_coverage⟩
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

theorem record054_parameters : Parameters record054 (rowOfCode 23) 29414369280128 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record054_coverage : Coverage record054 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29414369280128 :=
  GraphCoverageDescriptions.coverage_of_checked record054 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05771 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29414369280128
    (by rfl) record054_cells_exact
    (GraphCoverageDescriptions.small_allowed record054 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05771_checked

theorem record054_result : Result (23, 29414369280128) :=
  of_small 23 29414369280128 (by decide) ⟨record054, record054_core, record054_parameters, record054_coverage⟩
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

theorem record055_parameters : Parameters record055 (rowOfCode 23) 29414375034880 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record055_coverage : Coverage record055 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29414375034880 :=
  GraphCoverageDescriptions.coverage_of_checked record055 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05772 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29414375034880
    (by rfl) record055_cells_exact
    (GraphCoverageDescriptions.small_allowed record055 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05772_checked

theorem record055_result : Result (23, 29414375034880) :=
  of_small 23 29414375034880 (by decide) ⟨record055, record055_core, record055_parameters, record055_coverage⟩
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

theorem record056_parameters : Parameters record056 (rowOfCode 23) 29420814340096 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record056_coverage : Coverage record056 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29420814340096 :=
  GraphCoverageDescriptions.coverage_of_checked record056 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05773 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29420814340096
    (by rfl) record056_cells_exact
    (GraphCoverageDescriptions.small_allowed record056 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05773_checked

theorem record056_result : Result (23, 29420814340096) :=
  of_small 23 29420814340096 (by decide) ⟨record056, record056_core, record056_parameters, record056_coverage⟩
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

theorem record057_parameters : Parameters record057 (rowOfCode 23) 29423076114960 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record057_coverage : Coverage record057 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29423076114960 :=
  GraphCoverageDescriptions.coverage_of_checked record057 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05774 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29423076114960
    (by rfl) record057_cells_exact
    (GraphCoverageDescriptions.small_allowed record057 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05774_checked

theorem record057_result : Result (23, 29423076114960) :=
  of_small 23 29423076114960 (by decide) ⟨record057, record057_core, record057_parameters, record057_coverage⟩
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

theorem record058_parameters : Parameters record058 (rowOfCode 23) 29515300765696 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record058_coverage : Coverage record058 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29515300765696 :=
  GraphCoverageDescriptions.coverage_of_checked record058 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05775 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29515300765696
    (by rfl) record058_cells_exact
    (GraphCoverageDescriptions.small_allowed record058 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05775_checked

theorem record058_result : Result (23, 29515300765696) :=
  of_small 23 29515300765696 (by decide) ⟨record058, record058_core, record058_parameters, record058_coverage⟩
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

theorem record059_parameters : Parameters record059 (rowOfCode 23) 29515304927232 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record059_coverage : Coverage record059 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29515304927232 :=
  GraphCoverageDescriptions.coverage_of_checked record059 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05776 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29515304927232
    (by rfl) record059_cells_exact
    (GraphCoverageDescriptions.small_allowed record059 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05776_checked

theorem record059_result : Result (23, 29515304927232) :=
  of_small 23 29515304927232 (by decide) ⟨record059, record059_core, record059_parameters, record059_coverage⟩
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

theorem record060_parameters : Parameters record060 (rowOfCode 23) 29523873761280 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record060_coverage : Coverage record060 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29523873761280 :=
  GraphCoverageDescriptions.coverage_of_checked record060 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05777 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29523873761280
    (by rfl) record060_cells_exact
    (GraphCoverageDescriptions.small_allowed record060 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05777_checked

theorem record060_result : Result (23, 29523873761280) :=
  of_small 23 29523873761280 (by decide) ⟨record060, record060_core, record060_parameters, record060_coverage⟩
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

theorem record061_parameters : Parameters record061 (rowOfCode 23) 29550466580608 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record061_coverage : Coverage record061 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29550466580608 :=
  GraphCoverageDescriptions.coverage_of_checked record061 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05778 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29550466580608
    (by rfl) record061_cells_exact
    (GraphCoverageDescriptions.small_allowed record061 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05778_checked

theorem record061_result : Result (23, 29550466580608) :=
  of_small 23 29550466580608 (by decide) ⟨record061, record061_core, record061_parameters, record061_coverage⟩
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

theorem record062_parameters : Parameters record062 (rowOfCode 23) 29550534754304 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record062_coverage : Coverage record062 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29550534754304 :=
  GraphCoverageDescriptions.coverage_of_checked record062 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05779 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29550534754304
    (by rfl) record062_cells_exact
    (GraphCoverageDescriptions.small_allowed record062 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05779_checked

theorem record062_result : Result (23, 29550534754304) :=
  of_small 23 29550534754304 (by decide) ⟨record062, record062_core, record062_parameters, record062_coverage⟩
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

theorem record063_parameters : Parameters record063 (rowOfCode 23) 29550538915840 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record063_coverage : Coverage record063 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29550538915840 :=
  GraphCoverageDescriptions.coverage_of_checked record063 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05780 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29550538915840
    (by rfl) record063_cells_exact
    (GraphCoverageDescriptions.small_allowed record063 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05780_checked

theorem record063_result : Result (23, 29550538915840) :=
  of_small 23 29550538915840 (by decide) ⟨record063, record063_core, record063_parameters, record063_coverage⟩
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

theorem record064_parameters : Parameters record064 (rowOfCode 23) 29550650359808 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record064_coverage : Coverage record064 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29550650359808 :=
  GraphCoverageDescriptions.coverage_of_checked record064 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05781 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29550650359808
    (by rfl) record064_cells_exact
    (GraphCoverageDescriptions.small_allowed record064 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05781_checked

theorem record064_result : Result (23, 29550650359808) :=
  of_small 23 29550650359808 (by decide) ⟨record064, record064_core, record064_parameters, record064_coverage⟩
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

theorem record065_parameters : Parameters record065 (rowOfCode 23) 29552596369536 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record065_coverage : Coverage record065 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29552596369536 :=
  GraphCoverageDescriptions.coverage_of_checked record065 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05782 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29552596369536
    (by rfl) record065_cells_exact
    (GraphCoverageDescriptions.small_allowed record065 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05782_checked

theorem record065_result : Result (23, 29552596369536) :=
  of_small 23 29552596369536 (by decide) ⟨record065, record065_core, record065_parameters, record065_coverage⟩
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

theorem record066_parameters : Parameters record066 (rowOfCode 23) 29552998875648 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record066_coverage : Coverage record066 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29552998875648 :=
  GraphCoverageDescriptions.coverage_of_checked record066 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05783 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29552998875648
    (by rfl) record066_cells_exact
    (GraphCoverageDescriptions.small_allowed record066 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05783_checked

theorem record066_result : Result (23, 29552998875648) :=
  of_small 23 29552998875648 (by decide) ⟨record066, record066_core, record066_parameters, record066_coverage⟩
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

theorem record067_parameters : Parameters record067 (rowOfCode 23) 29583751790720 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record067_coverage : Coverage record067 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29583751790720 :=
  GraphCoverageDescriptions.coverage_of_checked record067 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05784 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29583751790720
    (by rfl) record067_cells_exact
    (GraphCoverageDescriptions.small_allowed record067 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05784_checked

theorem record067_result : Result (23, 29583751790720) :=
  of_small 23 29583751790720 (by decide) ⟨record067, record067_core, record067_parameters, record067_coverage⟩
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

theorem record068_parameters : Parameters record068 (rowOfCode 23) 29583886024704 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record068_coverage : Coverage record068 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29583886024704 :=
  GraphCoverageDescriptions.coverage_of_checked record068 GraphCoverageDescriptions.GraphCoverageBatch057.candidate05785 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 29583886024704
    (by rfl) record068_cells_exact
    (GraphCoverageDescriptions.small_allowed record068 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch057.candidate05785_checked

theorem record068_result : Result (23, 29583886024704) :=
  of_small 23 29583886024704 (by decide) ⟨record068, record068_core, record068_parameters, record068_coverage⟩
#print axioms record068_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023
