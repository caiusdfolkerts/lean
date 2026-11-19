module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00065Checked
public import GraphInputsRow29Part00065Metadata
public import GraphInputsRow29Part00065Frames
public import GraphInputsRow29Part00065Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch111
public import GraphInputsRow29Part00065Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00065
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 12000541605888 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11169 14

certified_graph_case record001 29 12000694403072 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11170 14

theorem record002_parameters : Parameters record002 (rowOfCode 29) 12000698564608 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12000698564608 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11171 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12000698564608
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch111.candidate11171_checked

theorem record002_result : Result (29, 12000698564608) :=
  of_direct_small 29 12000698564608 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00065.record002.direct_core, record002_parameters, record002_coverage⟩

certified_graph_case record003 29 12000810008576 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11172 14

certified_graph_case record004 29 12004433756416 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11173 14

theorem record005_parameters : Parameters record005 (rowOfCode 29) 12005238899200 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12005238899200 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11174 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12005238899200
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch111.candidate11174_checked

theorem record005_result : Result (29, 12005238899200) :=
  of_direct_small 29 12005238899200 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00065.record005.direct_core, record005_parameters, record005_coverage⟩

certified_graph_case record006 29 12008747466880 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11175 14

certified_graph_case record007 29 12009131507712 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11176 14

theorem record008_parameters : Parameters record008 (rowOfCode 29) 12013023690880 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12013023690880 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11177 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12013023690880
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch111.candidate11177_checked

theorem record008_result : Result (29, 12013023690880) :=
  of_direct_small 29 12013023690880 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00065.record008.direct_core, record008_parameters, record008_coverage⟩

certified_graph_case record009 29 12017318641792 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11178 14

theorem record010_parameters : Parameters record010 (rowOfCode 29) 12021613625344 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12021613625344 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11179 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12021613625344
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch111.candidate11179_checked

theorem record010_result : Result (29, 12021613625344) :=
  of_direct_small 29 12021613625344 (by decide) ⟨record010, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00065.record010.direct_core, record010_parameters, record010_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00065
