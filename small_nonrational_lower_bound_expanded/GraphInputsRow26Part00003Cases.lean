module
prelude
public meta import GraphCases
public import GraphInputsRow26Part00003Checked
public import GraphInputsRow26Part00003Metadata
public import GraphInputsRow26Part00003Frames
public import GraphInputsRow26Part00003Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch062
public import GraphCoverageBatch124
public import GraphInputsRow26Part00003Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 26) 1507602891008 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 1507602891008 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06221 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 1507602891008
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch062.candidate06221_checked

theorem record000_result : Result (26, 1507602891008) :=
  of_direct_small 26 1507602891008 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00003.record000.direct_core, record000_parameters, record000_coverage⟩

theorem record001_parameters : Parameters record001 (rowOfCode 26) 1507602956288 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 1507602956288 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06222 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 1507602956288
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch062.candidate06222_checked

theorem record001_result : Result (26, 1507602956288) :=
  of_direct_small 26 1507602956288 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00003.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 26 1507747495936 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06224 14

certified_graph_case record003 26 1508148019200 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06225 14

certified_graph_case record004 26 1535621759232 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06226 14

certified_graph_case record005 26 1654813458816 GraphCoverageDescriptions.GraphCoverageBatch124.candidate12437 14

theorem record006_parameters : Parameters record006 (rowOfCode 26) 1654947660160 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 1654947660160 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch124.candidate12438 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 1654947660160
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch124.candidate12438_checked

theorem record006_result : Result (26, 1654947660160) :=
  of_direct_small 26 1654947660160 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00003.record006.direct_core, record006_parameters, record006_coverage⟩

certified_graph_case record007 26 1688098668928 GraphCoverageDescriptions.GraphCoverageBatch124.candidate12439 14

certified_graph_case record008 26 1688216355200 GraphCoverageDescriptions.GraphCoverageBatch124.candidate12440 14

certified_graph_case record009 26 1688484757888 GraphCoverageDescriptions.GraphCoverageBatch124.candidate12441 14

certified_graph_case record010 26 1722576085376 GraphCoverageDescriptions.GraphCoverageBatch124.candidate12442 14

certified_graph_case record011 26 1857114177544 GraphCoverageDescriptions.GraphCoverageBatch124.candidate12443 14

certified_graph_case record012 26 1874294046720 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06228 14

certified_graph_case record013 26 1876766491392 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06230 14

certified_graph_case record014 26 1876774879744 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06231 14

theorem record015_parameters : Parameters record015 (rowOfCode 26) 1912082531072 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record015_coverage : Coverage record015 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 1912082531072 :=
  GraphCoverageDescriptions.coverage_of_checked record015 GraphCoverageDescriptions.GraphCoverageBatch124.candidate12444 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 1912082531072
    (by rfl) record015_cells_exact
    (GraphCoverageDescriptions.small_allowed record015 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch124.candidate12444_checked

theorem record015_result : Result (26, 1912082531072) :=
  of_direct_small 26 1912082531072 (by decide) ⟨record015, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00003.record015.direct_core, record015_parameters, record015_coverage⟩

certified_graph_case record016 26 1912090919424 GraphCoverageDescriptions.GraphCoverageBatch124.candidate12445 14

certified_graph_case record017 26 1919858902272 GraphCoverageDescriptions.GraphCoverageBatch124.candidate12446 14

certified_graph_case record018 26 1919858967552 GraphCoverageDescriptions.GraphCoverageBatch124.candidate12447 14

certified_graph_case record019 26 1920395641348 GraphCoverageDescriptions.GraphCoverageBatch124.candidate12448 14

certified_graph_case record020 26 1972073758720 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06232 14

certified_graph_case record021 26 1981468966912 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06233 14

certified_graph_case record022 26 1981737369600 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06234 14

certified_graph_case record023 26 1981861101824 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06235 14

certified_graph_case record024 26 1981997449216 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06236 14

certified_graph_case record025 26 1982005772288 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06237 14

certified_graph_case record026 26 1986030239744 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06238 14

certified_graph_case record027 26 1994152574984 GraphCoverageDescriptions.GraphCoverageBatch124.candidate12449 14

certified_graph_case record028 26 1994229104896 GraphCoverageDescriptions.GraphCoverageBatch124.candidate12450 14

certified_graph_case record029 26 1994230145280 GraphCoverageDescriptions.GraphCoverageBatch124.candidate12451 14

certified_graph_case record030 26 1994284695560 GraphCoverageDescriptions.GraphCoverageBatch124.candidate12452 14

certified_graph_case record031 26 1994548936712 GraphCoverageDescriptions.GraphCoverageBatch124.candidate12453 14

certified_graph_case record032 26 2001632067592 GraphCoverageDescriptions.GraphCoverageBatch124.candidate12454 14

certified_graph_case record033 26 2001766268936 GraphCoverageDescriptions.GraphCoverageBatch124.candidate12455 14

certified_graph_case record034 26 2002010030336 GraphCoverageDescriptions.GraphCoverageBatch124.candidate12456 14

certified_graph_case record035 26 2002011590912 GraphCoverageDescriptions.GraphCoverageBatch124.candidate12457 14

certified_graph_case record036 26 2002034671624 GraphCoverageDescriptions.GraphCoverageBatch124.candidate12458 14

certified_graph_case record037 26 2003143065600 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06239 14

certified_graph_case record038 26 2011735015552 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06240 14

certified_graph_case record039 26 2016290078720 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06241 14

certified_graph_case record040 26 2016298401792 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06242 14

certified_graph_case record041 26 2018688204800 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06243 14

certified_graph_case record042 26 2018787229952 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06244 14

certified_graph_case record043 26 2018787295232 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06245 14

certified_graph_case record044 26 2019777741056 GraphCoverageDescriptions.GraphCoverageBatch124.candidate12459 14

certified_graph_case record045 26 2019777806336 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06246 14

certified_graph_case record046 26 2019781772544 GraphCoverageDescriptions.GraphCoverageBatch124.candidate12460 14

theorem record047_parameters : Parameters record047 (rowOfCode 26) 2019922280449 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record047_coverage : Coverage record047 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 2019922280449 :=
  GraphCoverageDescriptions.coverage_of_checked record047 GraphCoverageDescriptions.GraphCoverageBatch124.candidate12461 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 2019922280449
    (by rfl) record047_cells_exact
    (GraphCoverageDescriptions.small_allowed record047 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch124.candidate12461_checked

theorem record047_result : Result (26, 2019922280449) :=
  of_direct_small 26 2019922280449 (by decide) ⟨record047, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00003.record047.direct_core, record047_parameters, record047_coverage⟩

certified_graph_case record048 26 2020314480896 GraphCoverageDescriptions.GraphCoverageBatch062.candidate06247 14

certified_graph_case record049 26 2020318642177 GraphCoverageDescriptions.GraphCoverageBatch124.candidate12462 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003
