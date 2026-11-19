module
prelude
public meta import GraphCases
public import GraphInputsRow30Part00031Checked
public import GraphInputsRow30Part00031Metadata
public import GraphInputsRow30Part00031Frames
public import GraphInputsRow30Part00031Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch114
public import GraphCoverageBatch115
public import GraphCoverageBatch155
public import GraphInputsRow30Part00031Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 30 17060415672336 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11479 14

certified_graph_case record001 30 17061254267520 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11480 14

certified_graph_case record002 30 17061489148432 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11481 14

certified_graph_case record003 30 17068234146048 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11482 14

certified_graph_case record004 30 17069005869056 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11483 14

certified_graph_case record005 30 17081357631744 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11484 14

certified_graph_case record006 30 17112496144640 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11485 14

certified_graph_case record007 30 17121090273280 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11486 14

certified_graph_case record008 30 17121627078656 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11487 14

certified_graph_case record009 30 17136957325312 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11488 14

certified_graph_case record010 30 17137725341696 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11489 14

certified_graph_case record011 30 17154376269824 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11490 14

certified_graph_case record012 30 17179886358784 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15555 14

certified_graph_case record013 30 17180431486976 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11492 14

certified_graph_case record014 30 17188476485888 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11493 14

certified_graph_case record015 30 17189013356544 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11494 14

certified_graph_case record016 30 17189021679616 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11495 14

certified_graph_case record017 30 17190078251008 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11496 14

certified_graph_case record018 30 17190212337664 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11497 14

certified_graph_case record019 30 17197586057232 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11498 14

certified_graph_case record020 30 17197602701840 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11499 14

certified_graph_case record021 30 17197854625792 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11500 14

certified_graph_case record022 30 17198122959104 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11501 14

certified_graph_case record023 30 17198261272576 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11502 14

certified_graph_case record024 30 17198533836800 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11503 14

certified_graph_case record025 30 17198928101888 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11504 14

certified_graph_case record026 30 17201381834752 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11505 14

certified_graph_case record027 30 17202149851136 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11506 14

certified_graph_case record028 30 17205639123200 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11507 14

certified_graph_case record029 30 17218800779264 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11508 14

certified_graph_case record030 30 17227659083776 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11509 14

certified_graph_case record031 30 17235980582912 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11510 14

certified_graph_case record032 30 17292083593216 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11512 14

certified_graph_case record033 30 17317602004992 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11514 14

certified_graph_case record034 30 17326451720720 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11515 14

certified_graph_case record035 30 17480516895236 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11517 14

certified_graph_case record036 30 17523487604736 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11520 14

certified_graph_case record037 30 17532081668096 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11521 14

certified_graph_case record038 30 17532610150400 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11522 14

certified_graph_case record039 30 17549236502528 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11523 14

certified_graph_case record040 30 17595514306944 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15556 14

theorem record041_parameters : Parameters record041 (rowOfCode 30) 17595578286464 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record041_coverage : Coverage record041 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17595578286464 :=
  GraphCoverageDescriptions.coverage_of_checked record041 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15557 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17595578286464
    (by rfl) record041_cells_exact
    (GraphCoverageDescriptions.small_allowed record041 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch155.candidate15557_checked

theorem record041_result : Result (30, 17595578286464) :=
  of_direct_small 30 17595578286464 (by decide) ⟨record041, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00031.record041.direct_core, record041_parameters, record041_coverage⟩

theorem record042_parameters : Parameters record042 (rowOfCode 30) 17595580367232 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record042_coverage : Coverage record042 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17595580367232 :=
  GraphCoverageDescriptions.coverage_of_checked record042 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15558 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17595580367232
    (by rfl) record042_cells_exact
    (GraphCoverageDescriptions.small_allowed record042 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch155.candidate15558_checked

theorem record042_result : Result (30, 17595580367232) :=
  of_direct_small 30 17595580367232 (by decide) ⟨record042, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00031.record042.direct_core, record042_parameters, record042_coverage⟩

certified_graph_case record043 30 17595714584896 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11525 14

certified_graph_case record044 30 17595718746432 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11526 14

certified_graph_case record045 30 17631130755392 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11527 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031
