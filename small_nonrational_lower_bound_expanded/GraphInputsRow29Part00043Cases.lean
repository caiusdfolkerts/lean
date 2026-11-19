module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00043Checked
public import GraphInputsRow29Part00043Metadata
public import GraphInputsRow29Part00043Frames
public import GraphInputsRow29Part00043Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch109
public import GraphCoverageBatch144
public import GraphInputsRow29Part00043Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00043
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 7611353432064 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10957 14

certified_graph_case record001 29 7614977179904 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10958 14

certified_graph_case record002 29 7615782322688 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10959 14

certified_graph_case record003 29 7619410460672 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14454 14

certified_graph_case record004 29 7620079386624 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10960 14

certified_graph_case record005 29 7623566950916 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10961 14

certified_graph_case record006 29 7623567082496 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10962 14

certified_graph_case record007 29 7623567147008 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14455 14

theorem record008_parameters : Parameters record008 (rowOfCode 29) 7623843774464 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 7623843774464 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10963 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 7623843774464
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch109.candidate10963_checked

theorem record008_result : Result (29, 7623843774464) :=
  of_direct_small 29 7623843774464 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00043.record008.direct_core, record008_parameters, record008_coverage⟩

theorem record009_parameters : Parameters record009 (rowOfCode 29) 7624103952384 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 7624103952384 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10964 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 7624103952384
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch109.candidate10964_checked

theorem record009_result : Result (29, 7624103952384) :=
  of_direct_small 29 7624103952384 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00043.record009.direct_core, record009_parameters, record009_coverage⟩

theorem record010_parameters : Parameters record010 (rowOfCode 29) 7699980910848 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 7699980910848 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10965 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 7699980910848
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch109.candidate10965_checked

theorem record010_result : Result (29, 7699980910848) :=
  of_direct_small 29 7699980910848 (by decide) ⟨record010, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00043.record010.direct_core, record010_parameters, record010_coverage⟩

certified_graph_case record011 29 7702127345920 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10966 14

certified_graph_case record012 29 7702523707648 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14456 14

certified_graph_case record013 29 7735412556032 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10967 14

certified_graph_case record014 29 7736985190656 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14457 14

certified_graph_case record015 29 7749876350976 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10968 14

certified_graph_case record016 29 7753087615232 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10969 14

certified_graph_case record017 29 7784168980480 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10970 14

certified_graph_case record018 29 7785299869952 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10971 14

certified_graph_case record019 29 7821945012224 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14458 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00043
