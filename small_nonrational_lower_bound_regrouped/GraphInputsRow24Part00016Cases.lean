module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00016Checked
public import GraphInputsRow24Part00016Metadata
public import GraphInputsRow24Part00016Frames
public import GraphInputsRow24Part00016Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch069
public import GraphCoverageBatch070
public import GraphInputsRow24Part00016Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 10228265418752 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06980 14

certified_graph_case record001 24 10228269580288 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06981 14

certified_graph_case record002 24 10231897686016 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06982 14

certified_graph_case record003 24 10232426168320 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06983 14

certified_graph_case record004 24 10232430329856 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06984 14

certified_graph_case record005 24 10243039838336 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06985 14

certified_graph_case record006 24 10267222114560 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06986 14

certified_graph_case record007 24 10276275503232 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06987 14

certified_graph_case record008 24 10301613441280 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06988 14

certified_graph_case record009 24 10301617668096 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06989 14

certified_graph_case record010 24 10301621829632 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06990 14

certified_graph_case record011 24 10301625861120 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06991 14

certified_graph_case record012 24 10301757981696 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06992 14

certified_graph_case record013 24 10301881713408 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06993 14

certified_graph_case record014 24 10302016077952 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06994 14

theorem record015_parameters : Parameters record015 (rowOfCode 24) 10302022222848 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record015_coverage : Coverage record015 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10302022222848 :=
  GraphCoverageDescriptions.coverage_of_checked record015 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06995 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10302022222848
    (by rfl) record015_cells_exact
    (GraphCoverageDescriptions.small_allowed record015 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch069.candidate06995_checked

theorem record015_result : Result (24, 10302022222848) :=
  of_direct_small 24 10302022222848 (by decide) ⟨record015, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00016.record015.direct_core, record015_parameters, record015_coverage⟩
#print axioms record015_result

certified_graph_case record016 24 10331646624000 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06996 14

certified_graph_case record017 24 10347133042944 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06997 14

certified_graph_case record018 24 10349139001344 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06998 14

certified_graph_case record019 24 10355972522240 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06999 14

certified_graph_case record020 24 10370603352064 GraphCoverageDescriptions.GraphCoverageBatch070.candidate07000 14

certified_graph_case record021 24 10372683726848 GraphCoverageDescriptions.GraphCoverageBatch070.candidate07001 14

theorem record022_parameters : Parameters record022 (rowOfCode 24) 10372692049920 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record022_coverage : Coverage record022 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10372692049920 :=
  GraphCoverageDescriptions.coverage_of_checked record022 GraphCoverageDescriptions.GraphCoverageBatch070.candidate07002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10372692049920
    (by rfl) record022_cells_exact
    (GraphCoverageDescriptions.small_allowed record022 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch070.candidate07002_checked

theorem record022_result : Result (24, 10372692049920) :=
  of_direct_small 24 10372692049920 (by decide) ⟨record022, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00016.record022.direct_core, record022_parameters, record022_coverage⟩
#print axioms record022_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016
