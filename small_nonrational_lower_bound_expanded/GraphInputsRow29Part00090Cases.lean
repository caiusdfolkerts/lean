module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00090Checked
public import GraphInputsRow29Part00090Metadata
public import GraphInputsRow29Part00090Frames
public import GraphInputsRow29Part00090Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch113
public import GraphCoverageBatch147
public import GraphInputsRow29Part00090Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00090
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 15842005778688 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14736 14

theorem record001_parameters : Parameters record001 (rowOfCode 29) 15842282569728 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 15842282569728 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11381 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 15842282569728
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch113.candidate11381_checked

theorem record001_result : Result (29, 15842282569728) :=
  of_direct_small 29 15842282569728 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00090.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 29 15842389852160 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14737 14

theorem record003_parameters : Parameters record003 (rowOfCode 29) 15842542649344 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 15842542649344 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11382 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 15842542649344
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch113.candidate11382_checked

theorem record003_result : Result (29, 15842542649344) :=
  of_direct_small 29 15842542649344 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00090.record003.direct_core, record003_parameters, record003_coverage⟩

certified_graph_case record004 29 15842546810880 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11383 14

theorem record005_parameters : Parameters record005 (rowOfCode 29) 15842658254848 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 15842658254848 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11384 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 15842658254848
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch113.candidate11384_checked

theorem record005_result : Result (29, 15842658254848) :=
  of_direct_small 29 15842658254848 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00090.record005.direct_core, record005_parameters, record005_coverage⟩

theorem record006_parameters : Parameters record006 (rowOfCode 29) 15851247895040 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 15851247895040 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11385 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 15851247895040
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch113.candidate11385_checked

theorem record006_result : Result (29, 15851247895040) :=
  of_direct_small 29 15851247895040 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00090.record006.direct_core, record006_parameters, record006_coverage⟩

certified_graph_case record007 29 15859166888064 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14738 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00090
