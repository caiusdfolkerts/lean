module
prelude
public meta import GraphCases
public import GraphInputsRow26Part00080Checked
public import GraphInputsRow26Part00080Metadata
public import GraphInputsRow26Part00080Frames
public import GraphInputsRow26Part00080Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch103
public import GraphCoverageBatch130
public import GraphInputsRow26Part00080Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 26 33687073718272 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10378 14

certified_graph_case record001 26 33742623145984 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10379 14

certified_graph_case record002 26 33742631469056 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10380 14

certified_graph_case record003 26 33742672691200 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10381 14

certified_graph_case record004 26 33750423707648 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10382 14

certified_graph_case record005 26 33750926893312 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10383 14

certified_graph_case record006 26 33751530734080 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10384 14

certified_graph_case record007 26 34086020743424 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10385 14

certified_graph_case record008 26 34086020808704 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10386 14

certified_graph_case record009 26 34086022824192 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10387 14

certified_graph_case record010 26 34086022889472 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10388 14

certified_graph_case record011 26 34086228336704 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10390 14

certified_graph_case record012 26 34086228353024 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10391 14

certified_graph_case record013 26 34086228856896 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13075 14

certified_graph_case record014 26 34087163662592 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10392 14

certified_graph_case record015 26 34087163727872 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10393 14

certified_graph_case record016 26 34087171526672 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13076 14

certified_graph_case record017 26 34087180177664 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10394 14

certified_graph_case record018 26 34087180242944 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10395 14

certified_graph_case record019 26 34087188301840 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13077 14

certified_graph_case record020 26 34087302074432 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10396 14

certified_graph_case record021 26 34087303647248 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13078 14

theorem record022_parameters : Parameters record022 (rowOfCode 26) 34087320422416 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record022_coverage : Coverage record022 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34087320422416 :=
  GraphCoverageDescriptions.coverage_of_checked record022 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13079 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34087320422416
    (by rfl) record022_cells_exact
    (GraphCoverageDescriptions.small_allowed record022 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch130.candidate13079_checked

theorem record022_result : Result (26, 34087320422416) :=
  of_direct_small 26 34087320422416 (by decide) ⟨record022, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00080.record022.direct_core, record022_parameters, record022_coverage⟩
#print axioms record022_result

certified_graph_case record023 26 34088253719040 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10397 14

theorem record024_parameters : Parameters record024 (rowOfCode 26) 34088262041601 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record024_coverage : Coverage record024 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34088262041601 :=
  GraphCoverageDescriptions.coverage_of_checked record024 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13080 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34088262041601
    (by rfl) record024_cells_exact
    (GraphCoverageDescriptions.small_allowed record024 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch130.candidate13080_checked

theorem record024_result : Result (26, 34088262041601) :=
  of_direct_small 26 34088262041601 (by decide) ⟨record024, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00080.record024.direct_core, record024_parameters, record024_coverage⟩
#print axioms record024_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080
