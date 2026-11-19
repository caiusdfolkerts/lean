module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00182Checked
public import GraphInputsRow29Part00182Metadata
public import GraphInputsRow29Part00182Frames
public import GraphInputsRow29Part00182Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch118
public import GraphCoverageBatch119
public import GraphCoverageBatch153
public import GraphInputsRow29Part00182Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00182
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 26466876137728 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15311 14

theorem record001_parameters : Parameters record001 (rowOfCode 29) 26467275653248 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 26467275653248 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11899 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 26467275653248
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch118.candidate11899_checked

theorem record001_result : Result (29, 26467275653248) :=
  of_direct_small 29 26467275653248 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00182.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 29 26467275685888 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11900 14

certified_graph_case record003 29 26467276693632 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15312 14

certified_graph_case record004 29 26467345899552 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11901 14

certified_graph_case record005 29 26468315840640 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15313 14

certified_graph_case record006 29 26468315873280 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15314 14

certified_graph_case record007 29 26468316881024 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15315 14

theorem record008_parameters : Parameters record008 (rowOfCode 29) 26468419637280 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 26468419637280 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11902 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 26468419637280
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch119.candidate11902_checked

theorem record008_result : Result (29, 26468419637280) :=
  of_direct_small 29 26468419637280 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00182.record008.direct_core, record008_parameters, record008_coverage⟩

certified_graph_case record009 29 26475667398688 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15316 14

certified_graph_case record010 29 26476741136416 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15317 14

certified_graph_case record011 29 26498346156160 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15318 14

certified_graph_case record012 29 26498618621953 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15319 14

certified_graph_case record013 29 26502779371521 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11903 14

certified_graph_case record014 29 26511100870657 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15320 14

certified_graph_case record015 29 26511291744384 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15321 14

certified_graph_case record016 29 26532370743552 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15322 14

certified_graph_case record017 29 26532370808832 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11904 14

certified_graph_case record018 29 26532741390464 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15323 14

certified_graph_case record019 29 26535726694656 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15324 14

certified_graph_case record020 29 26544312434944 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15325 14

theorem record021_parameters : Parameters record021 (rowOfCode 29) 26571228381184 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record021_coverage : Coverage record021 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 26571228381184 :=
  GraphCoverageDescriptions.coverage_of_checked record021 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15326 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 26571228381184
    (by rfl) record021_cells_exact
    (GraphCoverageDescriptions.small_allowed record021 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch153.candidate15326_checked

theorem record021_result : Result (29, 26571228381184) :=
  of_direct_small 29 26571228381184 (by decide) ⟨record021, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00182.record021.direct_core, record021_parameters, record021_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00182
