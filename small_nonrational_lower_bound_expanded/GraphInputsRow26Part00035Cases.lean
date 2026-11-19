module
prelude
public meta import GraphCases
public import GraphInputsRow26Part00035Checked
public import GraphInputsRow26Part00035Metadata
public import GraphInputsRow26Part00035Frames
public import GraphInputsRow26Part00035Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch081
public import GraphCoverageBatch082
public import GraphCoverageBatch128
public import GraphInputsRow26Part00035Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00035
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 26 19733898330880 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08162 14

certified_graph_case record001 26 19740015724544 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08164 14

certified_graph_case record002 26 19740279965696 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08166 14

certified_graph_case record003 26 19742622483008 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08168 14

certified_graph_case record004 26 19831349919872 GraphCoverageDescriptions.GraphCoverageBatch128.candidate12844 14

certified_graph_case record005 26 19835444609152 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08170 14

certified_graph_case record006 26 19869803298944 GraphCoverageDescriptions.GraphCoverageBatch128.candidate12845 14

certified_graph_case record007 26 19908861657088 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08173 14

certified_graph_case record008 26 19917042647296 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08174 14

certified_graph_case record009 26 19917051035648 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08175 14

certified_graph_case record010 26 19917183156224 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08178 14

certified_graph_case record011 26 19917249216512 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08179 14

certified_graph_case record012 26 19917443203200 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08180 14

certified_graph_case record013 26 19917643464832 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08181 14

certified_graph_case record014 26 19921343905792 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08182 14

certified_graph_case record015 26 19938725150752 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08183 14

certified_graph_case record016 26 19947106418816 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08184 14

certified_graph_case record017 26 19985768415232 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08186 14

certified_graph_case record018 26 20017980669952 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08188 14

certified_graph_case record019 26 20034556528768 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08190 14

certified_graph_case record020 26 20036636903552 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08191 14

certified_graph_case record021 26 20047435202560 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08193 14

certified_graph_case record022 26 20047443525632 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08194 14

certified_graph_case record023 26 20047707766784 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08195 14

certified_graph_case record024 26 20049119152256 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08196 14

certified_graph_case record025 26 20106027499648 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08198 14

certified_graph_case record026 26 20123198980224 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08199 14

certified_graph_case record027 26 20123203174400 GraphCoverageDescriptions.GraphCoverageBatch082.candidate08200 14

theorem record028_parameters : Parameters record028 (rowOfCode 26) 20130682667008 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record028_coverage : Coverage record028 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 20130682667008 :=
  GraphCoverageDescriptions.coverage_of_checked record028 GraphCoverageDescriptions.GraphCoverageBatch082.candidate08201 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 20130682667008
    (by rfl) record028_cells_exact
    (GraphCoverageDescriptions.small_allowed record028 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch082.candidate08201_checked

theorem record028_result : Result (26, 20130682667008) :=
  of_direct_small 26 20130682667008 (by decide) ⟨record028, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00035.record028.direct_core, record028_parameters, record028_coverage⟩

certified_graph_case record029 26 20138239754368 GraphCoverageDescriptions.GraphCoverageBatch082.candidate08203 14

certified_graph_case record030 26 20140386189440 GraphCoverageDescriptions.GraphCoverageBatch128.candidate12846 14

certified_graph_case record031 26 20141459406976 GraphCoverageDescriptions.GraphCoverageBatch082.candidate08205 14

certified_graph_case record032 26 20144674865408 GraphCoverageDescriptions.GraphCoverageBatch082.candidate08206 14

certified_graph_case record033 26 20149950251008 GraphCoverageDescriptions.GraphCoverageBatch082.candidate08207 14

certified_graph_case record034 26 20150016311296 GraphCoverageDescriptions.GraphCoverageBatch082.candidate08208 14

certified_graph_case record035 26 20158531797120 GraphCoverageDescriptions.GraphCoverageBatch082.candidate08209 14

theorem record036_parameters : Parameters record036 (rowOfCode 26) 20158535991296 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record036_coverage : Coverage record036 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 20158535991296 :=
  GraphCoverageDescriptions.coverage_of_checked record036 GraphCoverageDescriptions.GraphCoverageBatch082.candidate08210 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 20158535991296
    (by rfl) record036_cells_exact
    (GraphCoverageDescriptions.small_allowed record036 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch082.candidate08210_checked

theorem record036_result : Result (26, 20158535991296) :=
  of_direct_small 26 20158535991296 (by decide) ⟨record036, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00035.record036.direct_core, record036_parameters, record036_coverage⟩

certified_graph_case record037 26 20158602051584 GraphCoverageDescriptions.GraphCoverageBatch082.candidate08211 14

certified_graph_case record038 26 20158635081728 GraphCoverageDescriptions.GraphCoverageBatch082.candidate08212 14

certified_graph_case record039 26 20158732058752 GraphCoverageDescriptions.GraphCoverageBatch082.candidate08213 14

certified_graph_case record040 26 20161854734336 GraphCoverageDescriptions.GraphCoverageBatch082.candidate08214 14

certified_graph_case record041 26 20162894921728 GraphCoverageDescriptions.GraphCoverageBatch082.candidate08215 14

certified_graph_case record042 26 20171471225088 GraphCoverageDescriptions.GraphCoverageBatch082.candidate08216 14

certified_graph_case record043 26 20171475419264 GraphCoverageDescriptions.GraphCoverageBatch082.candidate08217 14

certified_graph_case record044 26 20171727046784 GraphCoverageDescriptions.GraphCoverageBatch082.candidate08218 14

certified_graph_case record045 26 20173621854336 GraphCoverageDescriptions.GraphCoverageBatch128.candidate12847 14

certified_graph_case record046 26 20173675300992 GraphCoverageDescriptions.GraphCoverageBatch128.candidate12848 14

certified_graph_case record047 26 20173749780736 GraphCoverageDescriptions.GraphCoverageBatch082.candidate08219 14

certified_graph_case record048 26 20173807421568 GraphCoverageDescriptions.GraphCoverageBatch082.candidate08220 14

theorem record049_parameters : Parameters record049 (rowOfCode 26) 20173873481856 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record049_coverage : Coverage record049 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 20173873481856 :=
  GraphCoverageDescriptions.coverage_of_checked record049 GraphCoverageDescriptions.GraphCoverageBatch128.candidate12849 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 20173873481856
    (by rfl) record049_cells_exact
    (GraphCoverageDescriptions.small_allowed record049 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch128.candidate12849_checked

theorem record049_result : Result (26, 20173873481856) :=
  of_direct_small 26 20173873481856 (by decide) ⟨record049, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00035.record049.direct_core, record049_parameters, record049_coverage⟩

certified_graph_case record050 26 20174018216064 GraphCoverageDescriptions.GraphCoverageBatch082.candidate08221 14

certified_graph_case record051 26 20180312850432 GraphCoverageDescriptions.GraphCoverageBatch082.candidate08223 14

certified_graph_case record052 26 20186553911424 GraphCoverageDescriptions.GraphCoverageBatch082.candidate08224 14

certified_graph_case record053 26 20192923123840 GraphCoverageDescriptions.GraphCoverageBatch082.candidate08225 14

certified_graph_case record054 26 20192927318016 GraphCoverageDescriptions.GraphCoverageBatch082.candidate08226 14

certified_graph_case record055 26 20193063470080 GraphCoverageDescriptions.GraphCoverageBatch082.candidate08227 14

certified_graph_case record056 26 20193191395968 GraphCoverageDescriptions.GraphCoverageBatch082.candidate08228 14

certified_graph_case record057 26 20197220188160 GraphCoverageDescriptions.GraphCoverageBatch128.candidate12850 14

certified_graph_case record058 26 20199300562944 GraphCoverageDescriptions.GraphCoverageBatch082.candidate08229 14

certified_graph_case record059 26 20199432520320 GraphCoverageDescriptions.GraphCoverageBatch082.candidate08230 14

certified_graph_case record060 26 20227319431168 GraphCoverageDescriptions.GraphCoverageBatch082.candidate08231 14

certified_graph_case record061 26 20274604935296 GraphCoverageDescriptions.GraphCoverageBatch082.candidate08233 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00035
