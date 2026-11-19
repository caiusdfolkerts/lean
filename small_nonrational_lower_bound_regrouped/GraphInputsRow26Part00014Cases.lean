module
prelude
public meta import GraphCases
public import GraphInputsRow26Part00014Checked
public import GraphInputsRow26Part00014Metadata
public import GraphInputsRow26Part00014Frames
public import GraphInputsRow26Part00014Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch068
public import GraphCoverageBatch069
public import GraphCoverageBatch126
public import GraphInputsRow26Part00014Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 26 8654635925504 GraphCoverageDescriptions.GraphCoverageBatch068.candidate06890 14

certified_graph_case record001 26 8729659506944 GraphCoverageDescriptions.GraphCoverageBatch068.candidate06897 14

certified_graph_case record002 26 8732226420736 GraphCoverageDescriptions.GraphCoverageBatch068.candidate06899 14

certified_graph_case record003 26 8732234743808 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06900 14

certified_graph_case record004 26 8734092886016 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06902 14

certified_graph_case record005 26 8734629691392 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06903 14

certified_graph_case record006 26 8744830371840 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06906 14

certified_graph_case record007 26 8744956395520 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06907 14

certified_graph_case record008 26 8745113354240 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06908 14

certified_graph_case record009 26 8746839375872 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06910 14

certified_graph_case record010 26 8747111940096 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06911 14

certified_graph_case record011 26 8757975318528 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06914 14

certified_graph_case record012 26 8766305140736 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06915 14

certified_graph_case record013 26 8775163445248 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06916 14

certified_graph_case record014 26 8783484944384 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06917 14

certified_graph_case record015 26 8836431839616 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12617 14

certified_graph_case record016 26 8870526288256 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12618 14

certified_graph_case record017 26 8910455095680 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12619 14

certified_graph_case record018 26 8911862169600 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06920 14

certified_graph_case record019 26 8980447428608 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12620 14

certified_graph_case record020 26 8988768927744 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06921 14

certified_graph_case record021 26 9056555122816 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06922 14

theorem record022_parameters : Parameters record022 (rowOfCode 26) 9064601879808 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record022_coverage : Coverage record022 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 9064601879808 :=
  GraphCoverageDescriptions.coverage_of_checked record022 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06923 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 9064601879808
    (by rfl) record022_cells_exact
    (GraphCoverageDescriptions.small_allowed record022 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch069.candidate06923_checked

theorem record022_result : Result (26, 9064601879808) :=
  of_direct_small 26 9064601879808 (by decide) ⟨record022, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00014.record022.direct_core, record022_parameters, record022_coverage⟩
#print axioms record022_result

certified_graph_case record023 26 9065134588160 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06924 14

certified_graph_case record024 26 9185404141696 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06925 14

certified_graph_case record025 26 9202305106176 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06926 14

certified_graph_case record026 26 9202573541504 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06927 14

certified_graph_case record027 26 9202841976832 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06928 14

certified_graph_case record028 26 9202846138368 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06929 14

certified_graph_case record029 26 9245007331584 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12621 14

certified_graph_case record030 26 9249828651136 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06930 14

certified_graph_case record031 26 9254121521280 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06931 14

certified_graph_case record032 26 9256267956352 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06932 14

certified_graph_case record033 26 9270898753536 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06933 14

certified_graph_case record034 26 9288480211072 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06934 14

certified_graph_case record035 26 9424575988608 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12622 14

certified_graph_case record036 26 9495742840832 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06935 14

certified_graph_case record037 26 9518811545856 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12623 14

certified_graph_case record038 26 9529597296896 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12624 14

certified_graph_case record039 26 9529601523712 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12625 14

certified_graph_case record040 26 9529605489920 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12626 14

certified_graph_case record041 26 9530004127744 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12627 14

theorem record042_parameters : Parameters record042 (rowOfCode 26) 9544564475136 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record042_coverage : Coverage record042 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 9544564475136 :=
  GraphCoverageDescriptions.coverage_of_checked record042 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12628 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 9544564475136
    (by rfl) record042_cells_exact
    (GraphCoverageDescriptions.small_allowed record042 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch126.candidate12628_checked

theorem record042_result : Result (26, 9544564475136) :=
  of_direct_small 26 9544564475136 (by decide) ⟨record042, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00014.record042.direct_core, record042_parameters, record042_coverage⟩
#print axioms record042_result

certified_graph_case record043 26 9545097183488 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06939 14

certified_graph_case record044 26 9565710065920 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06940 14

certified_graph_case record045 26 9666406924416 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06943 14

certified_graph_case record046 26 9675902844928 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06944 14

certified_graph_case record047 26 9676295012480 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06945 14

certified_graph_case record048 26 9682267701504 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06946 14

certified_graph_case record049 26 9682804572160 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06948 14

certified_graph_case record050 26 9682808733696 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06949 14

certified_graph_case record051 26 9786185777408 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06952 14

certified_graph_case record052 26 9792613826816 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12629 14

certified_graph_case record053 26 9795239166080 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06953 14

certified_graph_case record054 26 9810264211584 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06955 14

certified_graph_case record055 26 9820585492480 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06956 14

certified_graph_case record056 26 9820979740800 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06959 14

certified_graph_case record057 26 9820985885696 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06960 14

certified_graph_case record058 26 10025600812288 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06962 14

certified_graph_case record059 26 10037498552704 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12630 14

certified_graph_case record060 26 10041203687424 GraphCoverageDescriptions.GraphCoverageBatch069.candidate06964 14

theorem record061_parameters : Parameters record061 (rowOfCode 26) 10088931753984 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record061_coverage : Coverage record061 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10088931753984 :=
  GraphCoverageDescriptions.coverage_of_checked record061 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12631 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10088931753984
    (by rfl) record061_cells_exact
    (GraphCoverageDescriptions.small_allowed record061 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch126.candidate12631_checked

theorem record061_result : Result (26, 10088931753984) :=
  of_direct_small 26 10088931753984 (by decide) ⟨record061, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00014.record061.direct_core, record061_parameters, record061_coverage⟩
#print axioms record061_result

certified_graph_case record062 26 10090025321728 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12632 14

certified_graph_case record063 26 10090165829633 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12633 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014
