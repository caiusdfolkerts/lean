module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00048Checked
public import GraphInputsRow29Part00048Metadata
public import GraphInputsRow29Part00048Frames
public import GraphInputsRow29Part00048Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch110
public import GraphCoverageBatch144
public import GraphInputsRow29Part00048Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 8265171763200 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11004 14

certified_graph_case record001 29 8265262465280 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14472 14

certified_graph_case record002 29 8265274494976 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14473 14

certified_graph_case record003 29 8268617879808 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14474 14

certified_graph_case record004 29 8315350552832 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11005 14

certified_graph_case record005 29 8324192012304 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11006 14

certified_graph_case record006 29 8324209180673 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11007 14

certified_graph_case record007 29 8324209246208 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11008 14

theorem record008_parameters : Parameters record008 (rowOfCode 29) 8325265752065 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8325265752065 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8325265752065
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch110.candidate11009_checked

theorem record008_result : Result (29, 8325265752065) :=
  of_direct_small 29 8325265752065 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00048.record008.direct_core, record008_parameters, record008_coverage⟩
#print axioms record008_result

certified_graph_case record009 29 8325265817600 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14475 14

certified_graph_case record010 29 8332513511440 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11010 14

certified_graph_case record011 29 8332790759680 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14476 14

certified_graph_case record012 29 8332799148032 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11011 14

certified_graph_case record013 29 8332802789376 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14477 14

certified_graph_case record014 29 8334115603200 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14478 14

certified_graph_case record015 29 8334119862272 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11012 14

certified_graph_case record016 29 8334128185344 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11013 14

certified_graph_case record017 29 8340864303360 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14479 14

certified_graph_case record018 29 8341632385024 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14480 14

certified_graph_case record019 29 8402713444352 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11014 14

certified_graph_case record020 29 8402837241856 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11015 14

certified_graph_case record021 29 8406056894464 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14481 14

certified_graph_case record022 29 8409581682944 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14482 14

theorem record023_parameters : Parameters record023 (rowOfCode 29) 8474784169984 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record023_coverage : Coverage record023 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8474784169984 :=
  GraphCoverageDescriptions.coverage_of_checked record023 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11016 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8474784169984
    (by rfl) record023_cells_exact
    (GraphCoverageDescriptions.small_allowed record023 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch110.candidate11016_checked

theorem record023_result : Result (29, 8474784169984) :=
  of_direct_small 29 8474784169984 (by decide) ⟨record023, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00048.record023.direct_core, record023_parameters, record023_coverage⟩
#print axioms record023_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048
