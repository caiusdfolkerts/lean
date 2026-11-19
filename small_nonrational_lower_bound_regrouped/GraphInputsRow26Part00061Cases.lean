module
prelude
public meta import GraphCases
public import GraphInputsRow26Part00061Checked
public import GraphInputsRow26Part00061Metadata
public import GraphInputsRow26Part00061Frames
public import GraphInputsRow26Part00061Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch098
public import GraphCoverageBatch129
public import GraphCoverageBatch130
public import GraphInputsRow26Part00061Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 26 29068423872640 GraphCoverageDescriptions.GraphCoverageBatch129.candidate12992 14

certified_graph_case record001 26 29138218483840 GraphCoverageDescriptions.GraphCoverageBatch129.candidate12993 14

certified_graph_case record002 26 29138220564608 GraphCoverageDescriptions.GraphCoverageBatch129.candidate12994 14

certified_graph_case record003 26 29138224726144 GraphCoverageDescriptions.GraphCoverageBatch129.candidate12995 14

certified_graph_case record004 26 29138426028160 GraphCoverageDescriptions.GraphCoverageBatch129.candidate12996 14

certified_graph_case record005 26 29138690818064 GraphCoverageDescriptions.GraphCoverageBatch129.candidate12997 14

certified_graph_case record006 26 29139361370368 GraphCoverageDescriptions.GraphCoverageBatch129.candidate12998 14

certified_graph_case record007 26 29139361403008 GraphCoverageDescriptions.GraphCoverageBatch129.candidate12999 14

theorem record008_parameters : Parameters record008 (rowOfCode 26) 29139361431568 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29139361431568 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29139361431568
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch130.candidate13000_checked

theorem record008_result : Result (26, 29139361431568) :=
  of_direct_small 26 29139361431568 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00061.record008.direct_core, record008_parameters, record008_coverage⟩
#print axioms record008_result

certified_graph_case record009 26 29139378178176 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13001 14

certified_graph_case record010 26 29139493490944 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13002 14

certified_graph_case record011 26 29139493523584 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13003 14

certified_graph_case record012 26 29139493552144 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13004 14

certified_graph_case record013 26 29139495632912 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13005 14

certified_graph_case record014 26 29139499794448 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13006 14

certified_graph_case record015 26 29139516309520 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13007 14

certified_graph_case record016 26 29145757433872 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13008 14

certified_graph_case record017 26 29145934876928 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13009 14

certified_graph_case record018 26 29145958735888 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13010 14

certified_graph_case record019 26 29147029061888 GraphCoverageDescriptions.GraphCoverageBatch098.candidate09806 14

certified_graph_case record020 26 29147063652608 GraphCoverageDescriptions.GraphCoverageBatch098.candidate09807 14

theorem record021_parameters : Parameters record021 (rowOfCode 26) 29171573424144 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record021_coverage : Coverage record021 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29171573424144 :=
  GraphCoverageDescriptions.coverage_of_checked record021 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13011 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29171573424144
    (by rfl) record021_cells_exact
    (GraphCoverageDescriptions.small_allowed record021 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch130.candidate13011_checked

theorem record021_result : Result (26, 29171573424144) :=
  of_direct_small 26 29171573424144 (by decide) ⟨record021, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00061.record021.direct_core, record021_parameters, record021_coverage⟩
#print axioms record021_result

certified_graph_case record022 26 29171707625488 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13012 14

certified_graph_case record023 26 29171711787024 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13013 14

certified_graph_case record024 26 29175985670160 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13014 14

certified_graph_case record025 26 29180146419728 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13015 14

certified_graph_case record026 26 29180297756928 GraphCoverageDescriptions.GraphCoverageBatch098.candidate09808 14

certified_graph_case record027 26 29180299317504 GraphCoverageDescriptions.GraphCoverageBatch098.candidate09809 14

certified_graph_case record028 26 29215783190528 GraphCoverageDescriptions.GraphCoverageBatch098.candidate09811 14

certified_graph_case record029 26 29274583433232 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13016 14

certified_graph_case record030 26 29274585514000 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13017 14

certified_graph_case record031 26 29274589675536 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13018 14

theorem record032_parameters : Parameters record032 (rowOfCode 26) 29274790977552 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record032_coverage : Coverage record032 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29274790977552 :=
  GraphCoverageDescriptions.coverage_of_checked record032 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13019 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29274790977552
    (by rfl) record032_cells_exact
    (GraphCoverageDescriptions.small_allowed record032 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch130.candidate13019_checked

theorem record032_result : Result (26, 29274790977552) :=
  of_direct_small 26 29274790977552 (by decide) ⟨record032, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00061.record032.direct_core, record032_parameters, record032_coverage⟩
#print axioms record032_result

certified_graph_case record033 26 29276783183888 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13020 14

certified_graph_case record034 26 29276936081664 GraphCoverageDescriptions.GraphCoverageBatch098.candidate09812 14

certified_graph_case record035 26 29283156428816 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13021 14

certified_graph_case record036 26 29284463821056 GraphCoverageDescriptions.GraphCoverageBatch098.candidate09814 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061
