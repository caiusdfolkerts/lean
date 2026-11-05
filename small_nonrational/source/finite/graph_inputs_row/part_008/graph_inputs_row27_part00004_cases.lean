module
prelude
public import GraphInputsRow27Part00004Checked
public import GraphInputsRow27Part00004Metadata
public import GraphInputsRow27Part00004Frames
public import GraphInputsRow27Part00004Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch068
public import GraphCoverageBatch069
public import GraphCoverageBatch070
public import GraphCoverageBatch071
public import GraphCoverageBatch126
public import GraphCoverageBatch131


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004
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

theorem record000_parameters : Parameters record000 (rowOfCode 27) 8067632594944 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8067632594944 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch068.candidate06812 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8067632594944
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch068.candidate06812_checked

theorem record000_result : Result (27, 8067632594944) :=
  of_small 27 8067632594944 (by decide) ⟨record000, record000_core, record000_parameters, record000_coverage⟩
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

theorem record001_parameters : Parameters record001 (rowOfCode 27) 8135953612800 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8135953612800 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch068.candidate06819 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8135953612800
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch068.candidate06819_checked

theorem record001_result : Result (27, 8135953612800) :=
  of_small 27 8135953612800 (by decide) ⟨record001, record001_core, record001_parameters, record001_coverage⟩
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

theorem record002_parameters : Parameters record002 (rowOfCode 27) 8139074174976 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8139074174976 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch068.candidate06823 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8139074174976
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch068.candidate06823_checked

theorem record002_result : Result (27, 8139074174976) :=
  of_small 27 8139074174976 (by decide) ⟨record002, record002_core, record002_parameters, record002_coverage⟩
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

theorem record003_parameters : Parameters record003 (rowOfCode 27) 8139140235264 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8139140235264 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch068.candidate06824 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8139140235264
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch068.candidate06824_checked

theorem record003_result : Result (27, 8139140235264) :=
  of_small 27 8139140235264 (by decide) ⟨record003, record003_core, record003_parameters, record003_coverage⟩
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

theorem record004_parameters : Parameters record004 (rowOfCode 27) 8148236634112 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8148236634112 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch068.candidate06828 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8148236634112
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch068.candidate06828_checked

theorem record004_result : Result (27, 8148236634112) :=
  of_small 27 8148236634112 (by decide) ⟨record004, record004_core, record004_parameters, record004_coverage⟩
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

theorem record005_parameters : Parameters record005 (rowOfCode 27) 8152529504256 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8152529504256 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch068.candidate06831 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8152529504256
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch068.candidate06831_checked

theorem record005_result : Result (27, 8152529504256) :=
  of_small 27 8152529504256 (by decide) ⟨record005, record005_core, record005_parameters, record005_coverage⟩
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

theorem record006_parameters : Parameters record006 (rowOfCode 27) 8156813984512 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8156813984512 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch131.candidate13134 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8156813984512
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch131.candidate13134_checked

theorem record006_result : Result (27, 8156813984512) :=
  of_small 27 8156813984512 (by decide) ⟨record006, record006_core, record006_parameters, record006_coverage⟩
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

theorem record007_parameters : Parameters record007 (rowOfCode 27) 8173465501696 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8173465501696 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch068.candidate06836 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8173465501696
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch068.candidate06836_checked

theorem record007_result : Result (27, 8173465501696) :=
  of_small 27 8173465501696 (by decide) ⟨record007, record007_core, record007_parameters, record007_coverage⟩
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

theorem record008_parameters : Parameters record008 (rowOfCode 27) 8173859782656 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8173859782656 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch068.candidate06837 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8173859782656
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch068.candidate06837_checked

theorem record008_result : Result (27, 8173859782656) :=
  of_small 27 8173859782656 (by decide) ⟨record008, record008_core, record008_parameters, record008_coverage⟩
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

theorem record009_parameters : Parameters record009 (rowOfCode 27) 8186764525568 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8186764525568 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch068.candidate06856 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8186764525568
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch068.candidate06856_checked

theorem record009_result : Result (27, 8186764525568) :=
  of_small 27 8186764525568 (by decide) ⟨record009, record009_core, record009_parameters, record009_coverage⟩
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

theorem record010_parameters : Parameters record010 (rowOfCode 27) 8186770767872 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8186770767872 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch068.candidate06857 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8186770767872
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch068.candidate06857_checked

theorem record010_result : Result (27, 8186770767872) :=
  of_small 27 8186770767872 (by decide) ⟨record010, record010_core, record010_parameters, record010_coverage⟩
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

theorem record011_parameters : Parameters record011 (rowOfCode 27) 8195143632896 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record011_coverage : Coverage record011 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8195143632896 :=
  GraphCoverageDescriptions.coverage_of_checked record011 GraphCoverageDescriptions.GraphCoverageBatch068.candidate06862 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8195143632896
    (by rfl) record011_cells_exact
    (GraphCoverageDescriptions.small_allowed record011 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch068.candidate06862_checked

theorem record011_result : Result (27, 8195143632896) :=
  of_small 27 8195143632896 (by decide) ⟨record011, record011_core, record011_parameters, record011_coverage⟩
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

theorem record012_parameters : Parameters record012 (rowOfCode 27) 8246396260544 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record012_coverage : Coverage record012 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8246396260544 :=
  GraphCoverageDescriptions.coverage_of_checked record012 GraphCoverageDescriptions.GraphCoverageBatch131.candidate13135 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8246396260544
    (by rfl) record012_cells_exact
    (GraphCoverageDescriptions.small_allowed record012 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch131.candidate13135_checked

theorem record012_result : Result (27, 8246396260544) :=
  of_small 27 8246396260544 (by decide) ⟨record012, record012_core, record012_parameters, record012_coverage⟩
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

theorem record013_parameters : Parameters record013 (rowOfCode 27) 8246492989712 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record013_coverage : Coverage record013 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8246492989712 :=
  GraphCoverageDescriptions.coverage_of_checked record013 GraphCoverageDescriptions.GraphCoverageBatch131.candidate13136 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8246492989712
    (by rfl) record013_cells_exact
    (GraphCoverageDescriptions.small_allowed record013 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch131.candidate13136_checked

theorem record013_result : Result (27, 8246492989712) :=
  of_small 27 8246492989712 (by decide) ⟨record013, record013_core, record013_parameters, record013_coverage⟩
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

theorem record014_parameters : Parameters record014 (rowOfCode 27) 8247553722640 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record014_coverage : Coverage record014 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8247553722640 :=
  GraphCoverageDescriptions.coverage_of_checked record014 GraphCoverageDescriptions.GraphCoverageBatch131.candidate13137 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8247553722640
    (by rfl) record014_cells_exact
    (GraphCoverageDescriptions.small_allowed record014 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch131.candidate13137_checked

theorem record014_result : Result (27, 8247553722640) :=
  of_small 27 8247553722640 (by decide) ⟨record014, record014_core, record014_parameters, record014_coverage⟩
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

theorem record015_parameters : Parameters record015 (rowOfCode 27) 8324209278976 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record015_coverage : Coverage record015 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8324209278976 :=
  GraphCoverageDescriptions.coverage_of_checked record015 GraphCoverageDescriptions.GraphCoverageBatch068.candidate06872 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8324209278976
    (by rfl) record015_cells_exact
    (GraphCoverageDescriptions.small_allowed record015 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch068.candidate06872_checked

theorem record015_result : Result (27, 8324209278976) :=
  of_small 27 8324209278976 (by decide) ⟨record015, record015_core, record015_parameters, record015_coverage⟩
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

theorem record016_parameters : Parameters record016 (rowOfCode 27) 8569143427072 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record016_coverage : Coverage record016 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8569143427072 :=
  GraphCoverageDescriptions.coverage_of_checked record016 GraphCoverageDescriptions.GraphCoverageBatch068.candidate06886 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8569143427072
    (by rfl) record016_cells_exact
    (GraphCoverageDescriptions.small_allowed record016 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch068.candidate06886_checked

theorem record016_result : Result (27, 8569143427072) :=
  of_small 27 8569143427072 (by decide) ⟨record016, record016_core, record016_parameters, record016_coverage⟩
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

theorem record017_parameters : Parameters record017 (rowOfCode 27) 8637992927232 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record017_coverage : Coverage record017 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8637992927232 :=
  GraphCoverageDescriptions.coverage_of_checked record017 GraphCoverageDescriptions.GraphCoverageBatch068.candidate06888 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8637992927232
    (by rfl) record017_cells_exact
    (GraphCoverageDescriptions.small_allowed record017 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch068.candidate06888_checked

theorem record017_result : Result (27, 8637992927232) :=
  of_small 27 8637992927232 (by decide) ⟨record017, record017_core, record017_parameters, record017_coverage⟩
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

theorem record018_parameters : Parameters record018 (rowOfCode 27) 8654635925504 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record018_coverage : Coverage record018 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8654635925504 :=
  GraphCoverageDescriptions.coverage_of_checked record018 GraphCoverageDescriptions.GraphCoverageBatch068.candidate06890 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8654635925504
    (by rfl) record018_cells_exact
    (GraphCoverageDescriptions.small_allowed record018 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch068.candidate06890_checked

theorem record018_result : Result (27, 8654635925504) :=
  of_small 27 8654635925504 (by decide) ⟨record018, record018_core, record018_parameters, record018_coverage⟩
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

theorem record019_parameters : Parameters record019 (rowOfCode 27) 8732226420736 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record019_coverage : Coverage record019 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8732226420736 :=
  GraphCoverageDescriptions.coverage_of_checked record019 GraphCoverageDescriptions.GraphCoverageBatch068.candidate06899 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8732226420736
    (by rfl) record019_cells_exact
    (GraphCoverageDescriptions.small_allowed record019 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch068.candidate06899_checked

theorem record019_result : Result (27, 8732226420736) :=
  of_small 27 8732226420736 (by decide) ⟨record019, record019_core, record019_parameters, record019_coverage⟩
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

theorem record020_parameters : Parameters record020 (rowOfCode 27) 8732234743808 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record020_coverage : Coverage record020 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8732234743808 :=
  GraphCoverageDescriptions.coverage_of_checked record020 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06900 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8732234743808
    (by rfl) record020_cells_exact
    (GraphCoverageDescriptions.small_allowed record020 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch069.candidate06900_checked

theorem record020_result : Result (27, 8732234743808) :=
  of_small 27 8732234743808 (by decide) ⟨record020, record020_core, record020_parameters, record020_coverage⟩
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

theorem record021_parameters : Parameters record021 (rowOfCode 27) 8744830371840 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record021_coverage : Coverage record021 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8744830371840 :=
  GraphCoverageDescriptions.coverage_of_checked record021 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06906 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8744830371840
    (by rfl) record021_cells_exact
    (GraphCoverageDescriptions.small_allowed record021 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch069.candidate06906_checked

theorem record021_result : Result (27, 8744830371840) :=
  of_small 27 8744830371840 (by decide) ⟨record021, record021_core, record021_parameters, record021_coverage⟩
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

theorem record022_parameters : Parameters record022 (rowOfCode 27) 8745113354240 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record022_coverage : Coverage record022 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8745113354240 :=
  GraphCoverageDescriptions.coverage_of_checked record022 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06908 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8745113354240
    (by rfl) record022_cells_exact
    (GraphCoverageDescriptions.small_allowed record022 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch069.candidate06908_checked

theorem record022_result : Result (27, 8745113354240) :=
  of_small 27 8745113354240 (by decide) ⟨record022, record022_core, record022_parameters, record022_coverage⟩
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

theorem record023_parameters : Parameters record023 (rowOfCode 27) 8746839375872 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record023_coverage : Coverage record023 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8746839375872 :=
  GraphCoverageDescriptions.coverage_of_checked record023 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06910 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8746839375872
    (by rfl) record023_cells_exact
    (GraphCoverageDescriptions.small_allowed record023 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch069.candidate06910_checked

theorem record023_result : Result (27, 8746839375872) :=
  of_small 27 8746839375872 (by decide) ⟨record023, record023_core, record023_parameters, record023_coverage⟩
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

theorem record024_parameters : Parameters record024 (rowOfCode 27) 8747111940096 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record024_coverage : Coverage record024 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8747111940096 :=
  GraphCoverageDescriptions.coverage_of_checked record024 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06911 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8747111940096
    (by rfl) record024_cells_exact
    (GraphCoverageDescriptions.small_allowed record024 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch069.candidate06911_checked

theorem record024_result : Result (27, 8747111940096) :=
  of_small 27 8747111940096 (by decide) ⟨record024, record024_core, record024_parameters, record024_coverage⟩
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

theorem record025_parameters : Parameters record025 (rowOfCode 27) 8757975318528 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record025_coverage : Coverage record025 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8757975318528 :=
  GraphCoverageDescriptions.coverage_of_checked record025 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06914 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8757975318528
    (by rfl) record025_cells_exact
    (GraphCoverageDescriptions.small_allowed record025 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch069.candidate06914_checked

theorem record025_result : Result (27, 8757975318528) :=
  of_small 27 8757975318528 (by decide) ⟨record025, record025_core, record025_parameters, record025_coverage⟩
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

theorem record026_parameters : Parameters record026 (rowOfCode 27) 8766305140736 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record026_coverage : Coverage record026 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8766305140736 :=
  GraphCoverageDescriptions.coverage_of_checked record026 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06915 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8766305140736
    (by rfl) record026_cells_exact
    (GraphCoverageDescriptions.small_allowed record026 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch069.candidate06915_checked

theorem record026_result : Result (27, 8766305140736) :=
  of_small 27 8766305140736 (by decide) ⟨record026, record026_core, record026_parameters, record026_coverage⟩
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

theorem record027_parameters : Parameters record027 (rowOfCode 27) 8775163445248 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record027_coverage : Coverage record027 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8775163445248 :=
  GraphCoverageDescriptions.coverage_of_checked record027 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06916 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8775163445248
    (by rfl) record027_cells_exact
    (GraphCoverageDescriptions.small_allowed record027 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch069.candidate06916_checked

theorem record027_result : Result (27, 8775163445248) :=
  of_small 27 8775163445248 (by decide) ⟨record027, record027_core, record027_parameters, record027_coverage⟩
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

theorem record028_parameters : Parameters record028 (rowOfCode 27) 8783484944384 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record028_coverage : Coverage record028 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8783484944384 :=
  GraphCoverageDescriptions.coverage_of_checked record028 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06917 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8783484944384
    (by rfl) record028_cells_exact
    (GraphCoverageDescriptions.small_allowed record028 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch069.candidate06917_checked

theorem record028_result : Result (27, 8783484944384) :=
  of_small 27 8783484944384 (by decide) ⟨record028, record028_core, record028_parameters, record028_coverage⟩
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

theorem record029_parameters : Parameters record029 (rowOfCode 27) 8911862169600 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record029_coverage : Coverage record029 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8911862169600 :=
  GraphCoverageDescriptions.coverage_of_checked record029 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06920 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8911862169600
    (by rfl) record029_cells_exact
    (GraphCoverageDescriptions.small_allowed record029 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch069.candidate06920_checked

theorem record029_result : Result (27, 8911862169600) :=
  of_small 27 8911862169600 (by decide) ⟨record029, record029_core, record029_parameters, record029_coverage⟩
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

theorem record030_parameters : Parameters record030 (rowOfCode 27) 8980447428608 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record030_coverage : Coverage record030 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8980447428608 :=
  GraphCoverageDescriptions.coverage_of_checked record030 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12620 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8980447428608
    (by rfl) record030_cells_exact
    (GraphCoverageDescriptions.small_allowed record030 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch126.candidate12620_checked

theorem record030_result : Result (27, 8980447428608) :=
  of_small 27 8980447428608 (by decide) ⟨record030, record030_core, record030_parameters, record030_coverage⟩
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

theorem record031_parameters : Parameters record031 (rowOfCode 27) 8988768927744 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record031_coverage : Coverage record031 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8988768927744 :=
  GraphCoverageDescriptions.coverage_of_checked record031 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06921 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8988768927744
    (by rfl) record031_cells_exact
    (GraphCoverageDescriptions.small_allowed record031 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch069.candidate06921_checked

theorem record031_result : Result (27, 8988768927744) :=
  of_small 27 8988768927744 (by decide) ⟨record031, record031_core, record031_parameters, record031_coverage⟩
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

theorem record032_parameters : Parameters record032 (rowOfCode 27) 9064601879808 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record032_coverage : Coverage record032 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 9064601879808 :=
  GraphCoverageDescriptions.coverage_of_checked record032 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06923 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 9064601879808
    (by rfl) record032_cells_exact
    (GraphCoverageDescriptions.small_allowed record032 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch069.candidate06923_checked

theorem record032_result : Result (27, 9064601879808) :=
  of_small 27 9064601879808 (by decide) ⟨record032, record032_core, record032_parameters, record032_coverage⟩
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

theorem record033_parameters : Parameters record033 (rowOfCode 27) 9202573541504 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record033_coverage : Coverage record033 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 9202573541504 :=
  GraphCoverageDescriptions.coverage_of_checked record033 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06927 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 9202573541504
    (by rfl) record033_cells_exact
    (GraphCoverageDescriptions.small_allowed record033 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch069.candidate06927_checked

theorem record033_result : Result (27, 9202573541504) :=
  of_small 27 9202573541504 (by decide) ⟨record033, record033_core, record033_parameters, record033_coverage⟩
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

theorem record034_parameters : Parameters record034 (rowOfCode 27) 9202841976832 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record034_coverage : Coverage record034 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 9202841976832 :=
  GraphCoverageDescriptions.coverage_of_checked record034 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06928 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 9202841976832
    (by rfl) record034_cells_exact
    (GraphCoverageDescriptions.small_allowed record034 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch069.candidate06928_checked

theorem record034_result : Result (27, 9202841976832) :=
  of_small 27 9202841976832 (by decide) ⟨record034, record034_core, record034_parameters, record034_coverage⟩
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

theorem record035_parameters : Parameters record035 (rowOfCode 27) 9202846138368 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record035_coverage : Coverage record035 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 9202846138368 :=
  GraphCoverageDescriptions.coverage_of_checked record035 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06929 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 9202846138368
    (by rfl) record035_cells_exact
    (GraphCoverageDescriptions.small_allowed record035 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch069.candidate06929_checked

theorem record035_result : Result (27, 9202846138368) :=
  of_small 27 9202846138368 (by decide) ⟨record035, record035_core, record035_parameters, record035_coverage⟩
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

theorem record036_parameters : Parameters record036 (rowOfCode 27) 9270898753536 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record036_coverage : Coverage record036 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 9270898753536 :=
  GraphCoverageDescriptions.coverage_of_checked record036 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06933 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 9270898753536
    (by rfl) record036_cells_exact
    (GraphCoverageDescriptions.small_allowed record036 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch069.candidate06933_checked

theorem record036_result : Result (27, 9270898753536) :=
  of_small 27 9270898753536 (by decide) ⟨record036, record036_core, record036_parameters, record036_coverage⟩
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

theorem record037_parameters : Parameters record037 (rowOfCode 27) 9530142359553 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record037_coverage : Coverage record037 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 9530142359553 :=
  GraphCoverageDescriptions.coverage_of_checked record037 GraphCoverageDescriptions.GraphCoverageBatch131.candidate13138 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 9530142359553
    (by rfl) record037_cells_exact
    (GraphCoverageDescriptions.small_allowed record037 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch131.candidate13138_checked

theorem record037_result : Result (27, 9530142359553) :=
  of_small 27 9530142359553 (by decide) ⟨record037, record037_core, record037_parameters, record037_coverage⟩
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

theorem record038_parameters : Parameters record038 (rowOfCode 27) 9544564475136 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record038_coverage : Coverage record038 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 9544564475136 :=
  GraphCoverageDescriptions.coverage_of_checked record038 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12628 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 9544564475136
    (by rfl) record038_cells_exact
    (GraphCoverageDescriptions.small_allowed record038 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch126.candidate12628_checked

theorem record038_result : Result (27, 9544564475136) :=
  of_small 27 9544564475136 (by decide) ⟨record038, record038_core, record038_parameters, record038_coverage⟩
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

theorem record039_parameters : Parameters record039 (rowOfCode 27) 9682808733696 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record039_coverage : Coverage record039 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 9682808733696 :=
  GraphCoverageDescriptions.coverage_of_checked record039 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06949 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 9682808733696
    (by rfl) record039_cells_exact
    (GraphCoverageDescriptions.small_allowed record039 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch069.candidate06949_checked

theorem record039_result : Result (27, 9682808733696) :=
  of_small 27 9682808733696 (by decide) ⟨record039, record039_core, record039_parameters, record039_coverage⟩
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

theorem record040_parameters : Parameters record040 (rowOfCode 27) 9820985885696 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record040_coverage : Coverage record040 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 9820985885696 :=
  GraphCoverageDescriptions.coverage_of_checked record040 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06960 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 9820985885696
    (by rfl) record040_cells_exact
    (GraphCoverageDescriptions.small_allowed record040 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch069.candidate06960_checked

theorem record040_result : Result (27, 9820985885696) :=
  of_small 27 9820985885696 (by decide) ⟨record040, record040_core, record040_parameters, record040_coverage⟩
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

theorem record041_parameters : Parameters record041 (rowOfCode 27) 9898998972800 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record041_coverage : Coverage record041 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 9898998972800 :=
  GraphCoverageDescriptions.coverage_of_checked record041 GraphCoverageDescriptions.GraphCoverageBatch131.candidate13139 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 9898998972800
    (by rfl) record041_cells_exact
    (GraphCoverageDescriptions.small_allowed record041 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch131.candidate13139_checked

theorem record041_result : Result (27, 9898998972800) :=
  of_small 27 9898998972800 (by decide) ⟨record041, record041_core, record041_parameters, record041_coverage⟩
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

theorem record042_parameters : Parameters record042 (rowOfCode 27) 10000103735304 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record042_coverage : Coverage record042 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10000103735304 :=
  GraphCoverageDescriptions.coverage_of_checked record042 GraphCoverageDescriptions.GraphCoverageBatch131.candidate13140 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10000103735304
    (by rfl) record042_cells_exact
    (GraphCoverageDescriptions.small_allowed record042 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch131.candidate13140_checked

theorem record042_result : Result (27, 10000103735304) :=
  of_small 27 10000103735304 (by decide) ⟨record042, record042_core, record042_parameters, record042_coverage⟩
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

theorem record043_parameters : Parameters record043 (rowOfCode 27) 10041203687424 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record043_coverage : Coverage record043 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10041203687424 :=
  GraphCoverageDescriptions.coverage_of_checked record043 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06964 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10041203687424
    (by rfl) record043_cells_exact
    (GraphCoverageDescriptions.small_allowed record043 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch069.candidate06964_checked

theorem record043_result : Result (27, 10041203687424) :=
  of_small 27 10041203687424 (by decide) ⟨record043, record043_core, record043_parameters, record043_coverage⟩
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

theorem record044_parameters : Parameters record044 (rowOfCode 27) 10088931753984 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record044_coverage : Coverage record044 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10088931753984 :=
  GraphCoverageDescriptions.coverage_of_checked record044 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12631 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10088931753984
    (by rfl) record044_cells_exact
    (GraphCoverageDescriptions.small_allowed record044 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch126.candidate12631_checked

theorem record044_result : Result (27, 10088931753984) :=
  of_small 27 10088931753984 (by decide) ⟨record044, record044_core, record044_parameters, record044_coverage⟩
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

theorem record045_parameters : Parameters record045 (rowOfCode 27) 10090025321728 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record045_coverage : Coverage record045 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10090025321728 :=
  GraphCoverageDescriptions.coverage_of_checked record045 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12632 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10090025321728
    (by rfl) record045_cells_exact
    (GraphCoverageDescriptions.small_allowed record045 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch126.candidate12632_checked

theorem record045_result : Result (27, 10090025321728) :=
  of_small 27 10090025321728 (by decide) ⟨record045, record045_core, record045_parameters, record045_coverage⟩
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

theorem record046_parameters : Parameters record046 (rowOfCode 27) 10090165829633 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record046_coverage : Coverage record046 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10090165829633 :=
  GraphCoverageDescriptions.coverage_of_checked record046 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12633 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10090165829633
    (by rfl) record046_cells_exact
    (GraphCoverageDescriptions.small_allowed record046 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch126.candidate12633_checked

theorem record046_result : Result (27, 10090165829633) :=
  of_small 27 10090165829633 (by decide) ⟨record046, record046_core, record046_parameters, record046_coverage⟩
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

theorem record047_parameters : Parameters record047 (rowOfCode 27) 10136217288712 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record047_coverage : Coverage record047 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10136217288712 :=
  GraphCoverageDescriptions.coverage_of_checked record047 GraphCoverageDescriptions.GraphCoverageBatch131.candidate13141 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10136217288712
    (by rfl) record047_cells_exact
    (GraphCoverageDescriptions.small_allowed record047 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch131.candidate13141_checked

theorem record047_result : Result (27, 10136217288712) :=
  of_small 27 10136217288712 (by decide) ⟨record047, record047_core, record047_parameters, record047_coverage⟩
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

theorem record048_parameters : Parameters record048 (rowOfCode 27) 10153378365448 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record048_coverage : Coverage record048 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10153378365448 :=
  GraphCoverageDescriptions.coverage_of_checked record048 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12636 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10153378365448
    (by rfl) record048_cells_exact
    (GraphCoverageDescriptions.small_allowed record048 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch126.candidate12636_checked

theorem record048_result : Result (27, 10153378365448) :=
  of_small 27 10153378365448 (by decide) ⟨record048, record048_core, record048_parameters, record048_coverage⟩
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

theorem record049_parameters : Parameters record049 (rowOfCode 27) 10164723777536 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record049_coverage : Coverage record049 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10164723777536 :=
  GraphCoverageDescriptions.coverage_of_checked record049 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06968 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10164723777536
    (by rfl) record049_cells_exact
    (GraphCoverageDescriptions.small_allowed record049 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch069.candidate06968_checked

theorem record049_result : Result (27, 10164723777536) :=
  of_small 27 10164723777536 (by decide) ⟨record049, record049_core, record049_parameters, record049_coverage⟩
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

theorem record050_parameters : Parameters record050 (rowOfCode 27) 10226185043968 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record050_coverage : Coverage record050 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10226185043968 :=
  GraphCoverageDescriptions.coverage_of_checked record050 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06978 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10226185043968
    (by rfl) record050_cells_exact
    (GraphCoverageDescriptions.small_allowed record050 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch069.candidate06978_checked

theorem record050_result : Result (27, 10226185043968) :=
  of_small 27 10226185043968 (by decide) ⟨record050, record050_core, record050_parameters, record050_coverage⟩
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

theorem record051_parameters : Parameters record051 (rowOfCode 27) 10226189205504 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record051_coverage : Coverage record051 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10226189205504 :=
  GraphCoverageDescriptions.coverage_of_checked record051 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06979 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10226189205504
    (by rfl) record051_cells_exact
    (GraphCoverageDescriptions.small_allowed record051 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch069.candidate06979_checked

theorem record051_result : Result (27, 10226189205504) :=
  of_small 27 10226189205504 (by decide) ⟨record051, record051_core, record051_parameters, record051_coverage⟩
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

theorem record052_parameters : Parameters record052 (rowOfCode 27) 10228265418752 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record052_coverage : Coverage record052 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10228265418752 :=
  GraphCoverageDescriptions.coverage_of_checked record052 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06980 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10228265418752
    (by rfl) record052_cells_exact
    (GraphCoverageDescriptions.small_allowed record052 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch069.candidate06980_checked

theorem record052_result : Result (27, 10228265418752) :=
  of_small 27 10228265418752 (by decide) ⟨record052, record052_core, record052_parameters, record052_coverage⟩
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

theorem record053_parameters : Parameters record053 (rowOfCode 27) 10228269580288 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record053_coverage : Coverage record053 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10228269580288 :=
  GraphCoverageDescriptions.coverage_of_checked record053 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06981 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10228269580288
    (by rfl) record053_cells_exact
    (GraphCoverageDescriptions.small_allowed record053 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch069.candidate06981_checked

theorem record053_result : Result (27, 10228269580288) :=
  of_small 27 10228269580288 (by decide) ⟨record053, record053_core, record053_parameters, record053_coverage⟩
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

theorem record054_parameters : Parameters record054 (rowOfCode 27) 10232426168320 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record054_coverage : Coverage record054 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10232426168320 :=
  GraphCoverageDescriptions.coverage_of_checked record054 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06983 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10232426168320
    (by rfl) record054_cells_exact
    (GraphCoverageDescriptions.small_allowed record054 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch069.candidate06983_checked

theorem record054_result : Result (27, 10232426168320) :=
  of_small 27 10232426168320 (by decide) ⟨record054, record054_core, record054_parameters, record054_coverage⟩
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

theorem record055_parameters : Parameters record055 (rowOfCode 27) 10232430329856 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record055_coverage : Coverage record055 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10232430329856 :=
  GraphCoverageDescriptions.coverage_of_checked record055 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06984 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10232430329856
    (by rfl) record055_cells_exact
    (GraphCoverageDescriptions.small_allowed record055 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch069.candidate06984_checked

theorem record055_result : Result (27, 10232430329856) :=
  of_small 27 10232430329856 (by decide) ⟨record055, record055_core, record055_parameters, record055_coverage⟩
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

theorem record056_parameters : Parameters record056 (rowOfCode 27) 10301621829632 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record056_coverage : Coverage record056 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10301621829632 :=
  GraphCoverageDescriptions.coverage_of_checked record056 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06990 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10301621829632
    (by rfl) record056_cells_exact
    (GraphCoverageDescriptions.small_allowed record056 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch069.candidate06990_checked

theorem record056_result : Result (27, 10301621829632) :=
  of_small 27 10301621829632 (by decide) ⟨record056, record056_core, record056_parameters, record056_coverage⟩
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

theorem record057_parameters : Parameters record057 (rowOfCode 27) 10302016077952 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record057_coverage : Coverage record057 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10302016077952 :=
  GraphCoverageDescriptions.coverage_of_checked record057 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06994 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10302016077952
    (by rfl) record057_cells_exact
    (GraphCoverageDescriptions.small_allowed record057 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch069.candidate06994_checked

theorem record057_result : Result (27, 10302016077952) :=
  of_small 27 10302016077952 (by decide) ⟨record057, record057_core, record057_parameters, record057_coverage⟩
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

theorem record058_parameters : Parameters record058 (rowOfCode 27) 10302022222848 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record058_coverage : Coverage record058 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10302022222848 :=
  GraphCoverageDescriptions.coverage_of_checked record058 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06995 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10302022222848
    (by rfl) record058_cells_exact
    (GraphCoverageDescriptions.small_allowed record058 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch069.candidate06995_checked

theorem record058_result : Result (27, 10302022222848) :=
  of_small 27 10302022222848 (by decide) ⟨record058, record058_core, record058_parameters, record058_coverage⟩
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

theorem record059_parameters : Parameters record059 (rowOfCode 27) 10372692049920 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record059_coverage : Coverage record059 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10372692049920 :=
  GraphCoverageDescriptions.coverage_of_checked record059 GraphCoverageDescriptions.GraphCoverageBatch070.candidate07002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10372692049920
    (by rfl) record059_cells_exact
    (GraphCoverageDescriptions.small_allowed record059 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch070.candidate07002_checked

theorem record059_result : Result (27, 10372692049920) :=
  of_small 27 10372692049920 (by decide) ⟨record059, record059_core, record059_parameters, record059_coverage⟩
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

theorem record060_parameters : Parameters record060 (rowOfCode 27) 10446522892672 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record060_coverage : Coverage record060 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10446522892672 :=
  GraphCoverageDescriptions.coverage_of_checked record060 GraphCoverageDescriptions.GraphCoverageBatch131.candidate13142 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10446522892672
    (by rfl) record060_cells_exact
    (GraphCoverageDescriptions.small_allowed record060 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch131.candidate13142_checked

theorem record060_result : Result (27, 10446522892672) :=
  of_small 27 10446522892672 (by decide) ⟨record060, record060_core, record060_parameters, record060_coverage⟩
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

theorem record061_parameters : Parameters record061 (rowOfCode 27) 10448066351424 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record061_coverage : Coverage record061 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10448066351424 :=
  GraphCoverageDescriptions.coverage_of_checked record061 GraphCoverageDescriptions.GraphCoverageBatch131.candidate13143 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10448066351424
    (by rfl) record061_cells_exact
    (GraphCoverageDescriptions.small_allowed record061 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch131.candidate13143_checked

theorem record061_result : Result (27, 10448066351424) :=
  of_small 27 10448066351424 (by decide) ⟨record061, record061_core, record061_parameters, record061_coverage⟩
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

theorem record062_parameters : Parameters record062 (rowOfCode 27) 10484292159760 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record062_coverage : Coverage record062 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10484292159760 :=
  GraphCoverageDescriptions.coverage_of_checked record062 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12645 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10484292159760
    (by rfl) record062_cells_exact
    (GraphCoverageDescriptions.small_allowed record062 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch126.candidate12645_checked

theorem record062_result : Result (27, 10484292159760) :=
  of_small 27 10484292159760 (by decide) ⟨record062, record062_core, record062_parameters, record062_coverage⟩
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

theorem record063_parameters : Parameters record063 (rowOfCode 27) 10639451881473 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record063_coverage : Coverage record063 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10639451881473 :=
  GraphCoverageDescriptions.coverage_of_checked record063 GraphCoverageDescriptions.GraphCoverageBatch131.candidate13144 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10639451881473
    (by rfl) record063_cells_exact
    (GraphCoverageDescriptions.small_allowed record063 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch131.candidate13144_checked

theorem record063_result : Result (27, 10639451881473) :=
  of_small 27 10639451881473 (by decide) ⟨record063, record063_core, record063_parameters, record063_coverage⟩
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

theorem record064_parameters : Parameters record064 (rowOfCode 27) 10708171358208 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record064_coverage : Coverage record064 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10708171358208 :=
  GraphCoverageDescriptions.coverage_of_checked record064 GraphCoverageDescriptions.GraphCoverageBatch070.candidate07008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10708171358208
    (by rfl) record064_cells_exact
    (GraphCoverageDescriptions.small_allowed record064 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch070.candidate07008_checked

theorem record064_result : Result (27, 10708171358208) :=
  of_small 27 10708171358208 (by decide) ⟨record064, record064_core, record064_parameters, record064_coverage⟩
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

theorem record065_parameters : Parameters record065 (rowOfCode 27) 10716757098496 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record065_coverage : Coverage record065 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10716757098496 :=
  GraphCoverageDescriptions.coverage_of_checked record065 GraphCoverageDescriptions.GraphCoverageBatch070.candidate07009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10716757098496
    (by rfl) record065_cells_exact
    (GraphCoverageDescriptions.small_allowed record065 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch070.candidate07009_checked

theorem record065_result : Result (27, 10716757098496) :=
  of_small 27 10716757098496 (by decide) ⟨record065, record065_core, record065_parameters, record065_coverage⟩
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

theorem record066_parameters : Parameters record066 (rowOfCode 27) 10741484617728 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record066_coverage : Coverage record066 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10741484617728 :=
  GraphCoverageDescriptions.coverage_of_checked record066 GraphCoverageDescriptions.GraphCoverageBatch070.candidate07011 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10741484617728
    (by rfl) record066_cells_exact
    (GraphCoverageDescriptions.small_allowed record066 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch070.candidate07011_checked

theorem record066_result : Result (27, 10741484617728) :=
  of_small 27 10741484617728 (by decide) ⟨record066, record066_core, record066_parameters, record066_coverage⟩
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

theorem record067_parameters : Parameters record067 (rowOfCode 27) 10781588456448 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record067_coverage : Coverage record067 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10781588456448 :=
  GraphCoverageDescriptions.coverage_of_checked record067 GraphCoverageDescriptions.GraphCoverageBatch070.candidate07016 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10781588456448
    (by rfl) record067_cells_exact
    (GraphCoverageDescriptions.small_allowed record067 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch070.candidate07016_checked

theorem record067_result : Result (27, 10781588456448) :=
  of_small 27 10781588456448 (by decide) ⟨record067, record067_core, record067_parameters, record067_coverage⟩
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

theorem record068_parameters : Parameters record068 (rowOfCode 27) 10781720577024 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record068_coverage : Coverage record068 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10781720577024 :=
  GraphCoverageDescriptions.coverage_of_checked record068 GraphCoverageDescriptions.GraphCoverageBatch070.candidate07017 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10781720577024
    (by rfl) record068_cells_exact
    (GraphCoverageDescriptions.small_allowed record068 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch070.candidate07017_checked

theorem record068_result : Result (27, 10781720577024) :=
  of_small 27 10781720577024 (by decide) ⟨record068, record068_core, record068_parameters, record068_coverage⟩
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

theorem record069_parameters : Parameters record069 (rowOfCode 27) 10781984818176 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record069_coverage : Coverage record069 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10781984818176 :=
  GraphCoverageDescriptions.coverage_of_checked record069 GraphCoverageDescriptions.GraphCoverageBatch070.candidate07020 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10781984818176
    (by rfl) record069_cells_exact
    (GraphCoverageDescriptions.small_allowed record069 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch070.candidate07020_checked

theorem record069_result : Result (27, 10781984818176) :=
  of_small 27 10781984818176 (by decide) ⟨record069, record069_core, record069_parameters, record069_coverage⟩
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

theorem record070_parameters : Parameters record070 (rowOfCode 27) 10782112744064 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record070_coverage : Coverage record070 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10782112744064 :=
  GraphCoverageDescriptions.coverage_of_checked record070 GraphCoverageDescriptions.GraphCoverageBatch070.candidate07021 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10782112744064
    (by rfl) record070_cells_exact
    (GraphCoverageDescriptions.small_allowed record070 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch070.candidate07021_checked

theorem record070_result : Result (27, 10782112744064) :=
  of_small 27 10782112744064 (by decide) ⟨record070, record070_core, record070_parameters, record070_coverage⟩
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

theorem record071_parameters : Parameters record071 (rowOfCode 27) 10857729016064 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record071_coverage : Coverage record071 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10857729016064 :=
  GraphCoverageDescriptions.coverage_of_checked record071 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12646 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10857729016064
    (by rfl) record071_cells_exact
    (GraphCoverageDescriptions.small_allowed record071 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch126.candidate12646_checked

theorem record071_result : Result (27, 10857729016064) :=
  of_small 27 10857729016064 (by decide) ⟨record071, record071_core, record071_parameters, record071_coverage⟩
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

theorem record072_parameters : Parameters record072 (rowOfCode 27) 10884866899968 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record072_coverage : Coverage record072 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10884866899968 :=
  GraphCoverageDescriptions.coverage_of_checked record072 GraphCoverageDescriptions.GraphCoverageBatch070.candidate07027 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10884866899968
    (by rfl) record072_cells_exact
    (GraphCoverageDescriptions.small_allowed record072 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch070.candidate07027_checked

theorem record072_result : Result (27, 10884866899968) :=
  of_small 27 10884866899968 (by decide) ⟨record072, record072_core, record072_parameters, record072_coverage⟩
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

theorem record073_parameters : Parameters record073 (rowOfCode 27) 10892599410688 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record073_coverage : Coverage record073 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10892599410688 :=
  GraphCoverageDescriptions.coverage_of_checked record073 GraphCoverageDescriptions.GraphCoverageBatch070.candidate07035 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10892599410688
    (by rfl) record073_cells_exact
    (GraphCoverageDescriptions.small_allowed record073 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch070.candidate07035_checked

theorem record073_result : Result (27, 10892599410688) :=
  of_small 27 10892599410688 (by decide) ⟨record073, record073_core, record073_parameters, record073_coverage⟩
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

theorem record074_parameters : Parameters record074 (rowOfCode 27) 10909760095240 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record074_coverage : Coverage record074 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10909760095240 :=
  GraphCoverageDescriptions.coverage_of_checked record074 GraphCoverageDescriptions.GraphCoverageBatch070.candidate07045 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10909760095240
    (by rfl) record074_cells_exact
    (GraphCoverageDescriptions.small_allowed record074 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch070.candidate07045_checked

theorem record074_result : Result (27, 10909760095240) :=
  of_small 27 10909760095240 (by decide) ⟨record074, record074_core, record074_parameters, record074_coverage⟩
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

theorem record075_parameters : Parameters record075 (rowOfCode 27) 10956805505024 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record075_coverage : Coverage record075 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10956805505024 :=
  GraphCoverageDescriptions.coverage_of_checked record075 GraphCoverageDescriptions.GraphCoverageBatch070.candidate07048 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10956805505024
    (by rfl) record075_cells_exact
    (GraphCoverageDescriptions.small_allowed record075 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch070.candidate07048_checked

theorem record075_result : Result (27, 10956805505024) :=
  of_small 27 10956805505024 (by decide) ⟨record075, record075_core, record075_parameters, record075_coverage⟩
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

theorem record076_parameters : Parameters record076 (rowOfCode 27) 11180947014912 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record076_coverage : Coverage record076 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11180947014912 :=
  GraphCoverageDescriptions.coverage_of_checked record076 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12653 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11180947014912
    (by rfl) record076_cells_exact
    (GraphCoverageDescriptions.small_allowed record076 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch126.candidate12653_checked

theorem record076_result : Result (27, 11180947014912) :=
  of_small 27 11180947014912 (by decide) ⟨record076, record076_core, record076_parameters, record076_coverage⟩
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

theorem record077_parameters : Parameters record077 (rowOfCode 27) 11237945606144 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record077_coverage : Coverage record077 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11237945606144 :=
  GraphCoverageDescriptions.coverage_of_checked record077 GraphCoverageDescriptions.GraphCoverageBatch070.candidate07068 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11237945606144
    (by rfl) record077_cells_exact
    (GraphCoverageDescriptions.small_allowed record077 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch070.candidate07068_checked

theorem record077_result : Result (27, 11237945606144) :=
  of_small 27 11237945606144 (by decide) ⟨record077, record077_core, record077_parameters, record077_coverage⟩
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

theorem record078_parameters : Parameters record078 (rowOfCode 27) 11307984191488 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record078_coverage : Coverage record078 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11307984191488 :=
  GraphCoverageDescriptions.coverage_of_checked record078 GraphCoverageDescriptions.GraphCoverageBatch070.candidate07080 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11307984191488
    (by rfl) record078_cells_exact
    (GraphCoverageDescriptions.small_allowed record078 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch070.candidate07080_checked

theorem record078_result : Result (27, 11307984191488) :=
  of_small 27 11307984191488 (by decide) ⟨record078, record078_core, record078_parameters, record078_coverage⟩
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

theorem record079_parameters : Parameters record079 (rowOfCode 27) 11334591741952 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record079_coverage : Coverage record079 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11334591741952 :=
  GraphCoverageDescriptions.coverage_of_checked record079 GraphCoverageDescriptions.GraphCoverageBatch070.candidate07087 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11334591741952
    (by rfl) record079_cells_exact
    (GraphCoverageDescriptions.small_allowed record079 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch070.candidate07087_checked

theorem record079_result : Result (27, 11334591741952) :=
  of_small 27 11334591741952 (by decide) ⟨record079, record079_core, record079_parameters, record079_coverage⟩
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

theorem record080_parameters : Parameters record080 (rowOfCode 27) 11334721749120 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record080_coverage : Coverage record080 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11334721749120 :=
  GraphCoverageDescriptions.coverage_of_checked record080 GraphCoverageDescriptions.GraphCoverageBatch070.candidate07088 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11334721749120
    (by rfl) record080_cells_exact
    (GraphCoverageDescriptions.small_allowed record080 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch070.candidate07088_checked

theorem record080_result : Result (27, 11334721749120) :=
  of_small 27 11334721749120 (by decide) ⟨record080, record080_core, record080_parameters, record080_coverage⟩
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

theorem record081_parameters : Parameters record081 (rowOfCode 27) 11375512485888 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record081_coverage : Coverage record081 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11375512485888 :=
  GraphCoverageDescriptions.coverage_of_checked record081 GraphCoverageDescriptions.GraphCoverageBatch070.candidate07091 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11375512485888
    (by rfl) record081_cells_exact
    (GraphCoverageDescriptions.small_allowed record081 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch070.candidate07091_checked

theorem record081_result : Result (27, 11375512485888) :=
  of_small 27 11375512485888 (by decide) ⟨record081, record081_core, record081_parameters, record081_coverage⟩
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

theorem record082_parameters : Parameters record082 (rowOfCode 27) 11375636121728 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record082_coverage : Coverage record082 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11375636121728 :=
  GraphCoverageDescriptions.coverage_of_checked record082 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12656 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11375636121728
    (by rfl) record082_cells_exact
    (GraphCoverageDescriptions.small_allowed record082 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch126.candidate12656_checked

theorem record082_result : Result (27, 11375636121728) :=
  of_small 27 11375636121728 (by decide) ⟨record082, record082_core, record082_parameters, record082_coverage⟩
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

theorem record083_parameters : Parameters record083 (rowOfCode 27) 11384226054145 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record083_coverage : Coverage record083 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11384226054145 :=
  GraphCoverageDescriptions.coverage_of_checked record083 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12657 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11384226054145
    (by rfl) record083_cells_exact
    (GraphCoverageDescriptions.small_allowed record083 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch126.candidate12657_checked

theorem record083_result : Result (27, 11384226054145) :=
  of_small 27 11384226054145 (by decide) ⟨record083, record083_core, record083_parameters, record083_coverage⟩
#print axioms record083_result

theorem record084_core : Core record084 where
  matrix := record084_matrix_checked
  valid := record084_validity
  literal := record084_literal
  nodes := record084_raw_node_checks record084_validity
  leaf_nodup := record084_leaves_nodup
  frames := record084_frames_supported record084_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record084_certificates, record084_leaf_certificates_checked⟩

theorem record084_parameters : Parameters record084 (rowOfCode 27) 11401129263104 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record084_coverage : Coverage record084 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11401129263104 :=
  GraphCoverageDescriptions.coverage_of_checked record084 GraphCoverageDescriptions.GraphCoverageBatch070.candidate07092 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11401129263104
    (by rfl) record084_cells_exact
    (GraphCoverageDescriptions.small_allowed record084 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch070.candidate07092_checked

theorem record084_result : Result (27, 11401129263104) :=
  of_small 27 11401129263104 (by decide) ⟨record084, record084_core, record084_parameters, record084_coverage⟩
#print axioms record084_result

theorem record085_core : Core record085 where
  matrix := record085_matrix_checked
  valid := record085_validity
  literal := record085_literal
  nodes := record085_raw_node_checks record085_validity
  leaf_nodup := record085_leaves_nodup
  frames := record085_frames_supported record085_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record085_certificates, record085_leaf_certificates_checked⟩

theorem record085_parameters : Parameters record085 (rowOfCode 27) 11401265415168 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record085_coverage : Coverage record085 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11401265415168 :=
  GraphCoverageDescriptions.coverage_of_checked record085 GraphCoverageDescriptions.GraphCoverageBatch070.candidate07093 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11401265415168
    (by rfl) record085_cells_exact
    (GraphCoverageDescriptions.small_allowed record085 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch070.candidate07093_checked

theorem record085_result : Result (27, 11401265415168) :=
  of_small 27 11401265415168 (by decide) ⟨record085, record085_core, record085_parameters, record085_coverage⟩
#print axioms record085_result

theorem record086_core : Core record086 where
  matrix := record086_matrix_checked
  valid := record086_validity
  literal := record086_literal
  nodes := record086_raw_node_checks record086_validity
  leaf_nodup := record086_leaves_nodup
  frames := record086_frames_supported record086_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record086_certificates, record086_leaf_certificates_checked⟩

theorem record086_parameters : Parameters record086 (rowOfCode 27) 11401393341056 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record086_coverage : Coverage record086 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11401393341056 :=
  GraphCoverageDescriptions.coverage_of_checked record086 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12659 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11401393341056
    (by rfl) record086_cells_exact
    (GraphCoverageDescriptions.small_allowed record086 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch126.candidate12659_checked

theorem record086_result : Result (27, 11401393341056) :=
  of_small 27 11401393341056 (by decide) ⟨record086, record086_core, record086_parameters, record086_coverage⟩
#print axioms record086_result

theorem record087_core : Core record087 where
  matrix := record087_matrix_checked
  valid := record087_validity
  literal := record087_literal
  nodes := record087_raw_node_checks record087_validity
  leaf_nodup := record087_leaves_nodup
  frames := record087_frames_supported record087_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record087_certificates, record087_leaf_certificates_checked⟩

theorem record087_parameters : Parameters record087 (rowOfCode 27) 11413142716416 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record087_coverage : Coverage record087 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11413142716416 :=
  GraphCoverageDescriptions.coverage_of_checked record087 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07100 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11413142716416
    (by rfl) record087_cells_exact
    (GraphCoverageDescriptions.small_allowed record087 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch071.candidate07100_checked

theorem record087_result : Result (27, 11413142716416) :=
  of_small 27 11413142716416 (by decide) ⟨record087, record087_core, record087_parameters, record087_coverage⟩
#print axioms record087_result

theorem record088_core : Core record088 where
  matrix := record088_matrix_checked
  valid := record088_validity
  literal := record088_literal
  nodes := record088_raw_node_checks record088_validity
  leaf_nodup := record088_leaves_nodup
  frames := record088_frames_supported record088_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record088_certificates, record088_leaf_certificates_checked⟩

theorem record088_parameters : Parameters record088 (rowOfCode 27) 11431162445824 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record088_coverage : Coverage record088 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11431162445824 :=
  GraphCoverageDescriptions.coverage_of_checked record088 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07112 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11431162445824
    (by rfl) record088_cells_exact
    (GraphCoverageDescriptions.small_allowed record088 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch071.candidate07112_checked

theorem record088_result : Result (27, 11431162445824) :=
  of_small 27 11431162445824 (by decide) ⟨record088, record088_core, record088_parameters, record088_coverage⟩
#print axioms record088_result

theorem record089_core : Core record089 where
  matrix := record089_matrix_checked
  valid := record089_validity
  literal := record089_literal
  nodes := record089_raw_node_checks record089_validity
  leaf_nodup := record089_leaves_nodup
  frames := record089_frames_supported record089_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record089_certificates, record089_leaf_certificates_checked⟩

theorem record089_parameters : Parameters record089 (rowOfCode 27) 11431261536256 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record089_coverage : Coverage record089 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11431261536256 :=
  GraphCoverageDescriptions.coverage_of_checked record089 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07113 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11431261536256
    (by rfl) record089_cells_exact
    (GraphCoverageDescriptions.small_allowed record089 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch071.candidate07113_checked

theorem record089_result : Result (27, 11431261536256) :=
  of_small 27 11431261536256 (by decide) ⟨record089, record089_core, record089_parameters, record089_coverage⟩
#print axioms record089_result

theorem record090_core : Core record090 where
  matrix := record090_matrix_checked
  valid := record090_validity
  literal := record090_literal
  nodes := record090_raw_node_checks record090_validity
  leaf_nodup := record090_leaves_nodup
  frames := record090_frames_supported record090_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record090_certificates, record090_leaf_certificates_checked⟩

theorem record090_parameters : Parameters record090 (rowOfCode 27) 11431358513280 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record090_coverage : Coverage record090 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11431358513280 :=
  GraphCoverageDescriptions.coverage_of_checked record090 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12661 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11431358513280
    (by rfl) record090_cells_exact
    (GraphCoverageDescriptions.small_allowed record090 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch126.candidate12661_checked

theorem record090_result : Result (27, 11431358513280) :=
  of_small 27 11431358513280 (by decide) ⟨record090, record090_core, record090_parameters, record090_coverage⟩
#print axioms record090_result

theorem record091_core : Core record091 where
  matrix := record091_matrix_checked
  valid := record091_validity
  literal := record091_literal
  nodes := record091_raw_node_checks record091_validity
  leaf_nodup := record091_leaves_nodup
  frames := record091_frames_supported record091_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record091_certificates, record091_leaf_certificates_checked⟩

theorem record091_parameters : Parameters record091 (rowOfCode 27) 11444097744896 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record091_coverage : Coverage record091 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11444097744896 :=
  GraphCoverageDescriptions.coverage_of_checked record091 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07117 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11444097744896
    (by rfl) record091_cells_exact
    (GraphCoverageDescriptions.small_allowed record091 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch071.candidate07117_checked

theorem record091_result : Result (27, 11444097744896) :=
  of_small 27 11444097744896 (by decide) ⟨record091, record091_core, record091_parameters, record091_coverage⟩
#print axioms record091_result

theorem record092_core : Core record092 where
  matrix := record092_matrix_checked
  valid := record092_validity
  literal := record092_literal
  nodes := record092_raw_node_checks record092_validity
  leaf_nodup := record092_leaves_nodup
  frames := record092_frames_supported record092_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record092_certificates, record092_leaf_certificates_checked⟩

theorem record092_parameters : Parameters record092 (rowOfCode 27) 11444231946240 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record092_coverage : Coverage record092 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11444231946240 :=
  GraphCoverageDescriptions.coverage_of_checked record092 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07119 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11444231946240
    (by rfl) record092_cells_exact
    (GraphCoverageDescriptions.small_allowed record092 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch071.candidate07119_checked

theorem record092_result : Result (27, 11444231946240) :=
  of_small 27 11444231946240 (by decide) ⟨record092, record092_core, record092_parameters, record092_coverage⟩
#print axioms record092_result

theorem record093_core : Core record093 where
  matrix := record093_matrix_checked
  valid := record093_validity
  literal := record093_literal
  nodes := record093_raw_node_checks record093_validity
  leaf_nodup := record093_leaves_nodup
  frames := record093_frames_supported record093_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record093_certificates, record093_leaf_certificates_checked⟩

theorem record093_parameters : Parameters record093 (rowOfCode 27) 11444353501312 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record093_coverage : Coverage record093 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11444353501312 :=
  GraphCoverageDescriptions.coverage_of_checked record093 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12664 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11444353501312
    (by rfl) record093_cells_exact
    (GraphCoverageDescriptions.small_allowed record093 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch126.candidate12664_checked

theorem record093_result : Result (27, 11444353501312) :=
  of_small 27 11444353501312 (by decide) ⟨record093, record093_core, record093_parameters, record093_coverage⟩
#print axioms record093_result

theorem record094_core : Core record094 where
  matrix := record094_matrix_checked
  valid := record094_validity
  literal := record094_literal
  nodes := record094_raw_node_checks record094_validity
  leaf_nodup := record094_leaves_nodup
  frames := record094_frames_supported record094_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record094_certificates, record094_leaf_certificates_checked⟩

theorem record094_parameters : Parameters record094 (rowOfCode 27) 11444500348928 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record094_coverage : Coverage record094 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11444500348928 :=
  GraphCoverageDescriptions.coverage_of_checked record094 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07122 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11444500348928
    (by rfl) record094_cells_exact
    (GraphCoverageDescriptions.small_allowed record094 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch071.candidate07122_checked

theorem record094_result : Result (27, 11444500348928) :=
  of_small 27 11444500348928 (by decide) ⟨record094, record094_core, record094_parameters, record094_coverage⟩
#print axioms record094_result

theorem record095_core : Core record095 where
  matrix := record095_matrix_checked
  valid := record095_validity
  literal := record095_literal
  nodes := record095_raw_node_checks record095_validity
  leaf_nodup := record095_leaves_nodup
  frames := record095_frames_supported record095_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record095_certificates, record095_leaf_certificates_checked⟩

theorem record095_parameters : Parameters record095 (rowOfCode 27) 11446378381312 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record095_coverage : Coverage record095 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11446378381312 :=
  GraphCoverageDescriptions.coverage_of_checked record095 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07127 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11446378381312
    (by rfl) record095_cells_exact
    (GraphCoverageDescriptions.small_allowed record095 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch071.candidate07127_checked

theorem record095_result : Result (27, 11446378381312) :=
  of_small 27 11446378381312 (by decide) ⟨record095, record095_core, record095_parameters, record095_coverage⟩
#print axioms record095_result

theorem record096_core : Core record096 where
  matrix := record096_matrix_checked
  valid := record096_validity
  literal := record096_literal
  nodes := record096_raw_node_checks record096_validity
  leaf_nodup := record096_leaves_nodup
  frames := record096_frames_supported record096_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record096_certificates, record096_leaf_certificates_checked⟩

theorem record096_parameters : Parameters record096 (rowOfCode 27) 11452943433729 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record096_coverage : Coverage record096 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11452943433729 :=
  GraphCoverageDescriptions.coverage_of_checked record096 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12668 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11452943433729
    (by rfl) record096_cells_exact
    (GraphCoverageDescriptions.small_allowed record096 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch126.candidate12668_checked

theorem record096_result : Result (27, 11452943433729) :=
  of_small 27 11452943433729 (by decide) ⟨record096, record096_core, record096_parameters, record096_coverage⟩
#print axioms record096_result

theorem record097_core : Core record097 where
  matrix := record097_matrix_checked
  valid := record097_validity
  literal := record097_literal
  nodes := record097_raw_node_checks record097_validity
  leaf_nodup := record097_leaves_nodup
  frames := record097_frames_supported record097_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record097_certificates, record097_leaf_certificates_checked⟩

theorem record097_parameters : Parameters record097 (rowOfCode 27) 11471924904064 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record097_coverage : Coverage record097 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11471924904064 :=
  GraphCoverageDescriptions.coverage_of_checked record097 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07138 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11471924904064
    (by rfl) record097_cells_exact
    (GraphCoverageDescriptions.small_allowed record097 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch071.candidate07138_checked

theorem record097_result : Result (27, 11471924904064) :=
  of_small 27 11471924904064 (by decide) ⟨record097, record097_core, record097_parameters, record097_coverage⟩
#print axioms record097_result

theorem record098_core : Core record098 where
  matrix := record098_matrix_checked
  valid := record098_validity
  literal := record098_literal
  nodes := record098_raw_node_checks record098_validity
  leaf_nodup := record098_leaves_nodup
  frames := record098_frames_supported record098_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record098_certificates, record098_leaf_certificates_checked⟩

theorem record098_parameters : Parameters record098 (rowOfCode 27) 11471927017472 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record098_coverage : Coverage record098 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11471927017472 :=
  GraphCoverageDescriptions.coverage_of_checked record098 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07139 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11471927017472
    (by rfl) record098_cells_exact
    (GraphCoverageDescriptions.small_allowed record098 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch071.candidate07139_checked

theorem record098_result : Result (27, 11471927017472) :=
  of_small 27 11471927017472 (by decide) ⟨record098, record098_core, record098_parameters, record098_coverage⟩
#print axioms record098_result

theorem record099_core : Core record099 where
  matrix := record099_matrix_checked
  valid := record099_validity
  literal := record099_literal
  nodes := record099_raw_node_checks record099_validity
  leaf_nodup := record099_leaves_nodup
  frames := record099_frames_supported record099_cells_exact
  root_empty := by decide +kernel
  leaves_checked := ⟨record099_certificates, record099_leaf_certificates_checked⟩

theorem record099_parameters : Parameters record099 (rowOfCode 27) 11471931048960 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record099_coverage : Coverage record099 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11471931048960 :=
  GraphCoverageDescriptions.coverage_of_checked record099 GraphCoverageDescriptions.GraphCoverageBatch071.candidate07140 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11471931048960
    (by rfl) record099_cells_exact
    (GraphCoverageDescriptions.small_allowed record099 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch071.candidate07140_checked

theorem record099_result : Result (27, 11471931048960) :=
  of_small 27 11471931048960 (by decide) ⟨record099, record099_core, record099_parameters, record099_coverage⟩
#print axioms record099_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004
