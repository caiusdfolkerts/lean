module
prelude
public meta import GraphCases
public import GraphInputsRow19Part00034Checked
public import GraphInputsRow19Part00034Metadata
public import GraphInputsRow19Part00034Frames
public import GraphInputsRow19Part00034Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch020
public import GraphCoverageBatch037
public import GraphCoverageBatch038
public import GraphInputsRow19Part00034Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 19 32522629029888 GraphCoverageDescriptions.GraphCoverageBatch037.candidate03792 14

certified_graph_case record001 19 32522860240896 GraphCoverageDescriptions.GraphCoverageBatch020.candidate02034 14

certified_graph_case record002 19 32523124482048 GraphCoverageDescriptions.GraphCoverageBatch020.candidate02035 14

theorem record003_parameters : Parameters record003 (rowOfCode 19) 32530141552640 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32530141552640 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch020.candidate02036 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32530141552640
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch020.candidate02036_checked

theorem record003_result : Result (19, 32530141552640) :=
  of_direct_small 19 32530141552640 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00034.record003.direct_core, record003_parameters, record003_coverage⟩

certified_graph_case record004 19 32531189735680 GraphCoverageDescriptions.GraphCoverageBatch037.candidate03793 14

certified_graph_case record005 19 32531198124032 GraphCoverageDescriptions.GraphCoverageBatch020.candidate02037 14

certified_graph_case record006 19 32531726467616 GraphCoverageDescriptions.GraphCoverageBatch037.candidate03794 14

certified_graph_case record007 19 32641803157760 GraphCoverageDescriptions.GraphCoverageBatch037.candidate03795 14

certified_graph_case record008 19 32641810440448 GraphCoverageDescriptions.GraphCoverageBatch037.candidate03796 14

certified_graph_case record009 19 32641810505728 GraphCoverageDescriptions.GraphCoverageBatch037.candidate03797 14

certified_graph_case record010 19 32642306672896 GraphCoverageDescriptions.GraphCoverageBatch037.candidate03798 14

certified_graph_case record011 19 32642313752608 GraphCoverageDescriptions.GraphCoverageBatch037.candidate03799 14

certified_graph_case record012 19 32642313760768 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03800 14

certified_graph_case record013 19 32642314012704 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03801 14

certified_graph_case record014 19 32642331314184 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03802 14

certified_graph_case record015 19 32642900822272 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03803 14

certified_graph_case record016 19 32642900887552 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03804 14

certified_graph_case record017 19 32642917532160 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03805 14

certified_graph_case record018 19 32643371500552 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03806 14

certified_graph_case record019 19 32643388276737 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03807 14

theorem record020_parameters : Parameters record020 (rowOfCode 19) 32658973394976 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record020_coverage : Coverage record020 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32658973394976 :=
  GraphCoverageDescriptions.coverage_of_checked record020 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03808 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32658973394976
    (by rfl) record020_cells_exact
    (GraphCoverageDescriptions.small_allowed record020 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch038.candidate03808_checked

theorem record020_result : Result (19, 32658973394976) :=
  of_direct_small 19 32658973394976 (by decide) ⟨record020, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00034.record020.direct_core, record020_parameters, record020_coverage⟩

certified_graph_case record021 19 32659469763592 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03809 14

certified_graph_case record022 19 32710626451472 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03810 14

certified_graph_case record023 19 32711700390144 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03811 14

certified_graph_case record024 19 32712757020688 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03812 14

certified_graph_case record025 19 32712761182224 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03813 14

certified_graph_case record026 19 32713794945280 GraphCoverageDescriptions.GraphCoverageBatch020.candidate02038 14

certified_graph_case record027 19 32715076798496 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03814 14

certified_graph_case record028 19 32723415080960 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03815 14

certified_graph_case record029 19 32724471652352 GraphCoverageDescriptions.GraphCoverageBatch020.candidate02039 14

certified_graph_case record030 19 32724999995936 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03816 14

certified_graph_case record031 19 32745990422784 GraphCoverageDescriptions.GraphCoverageBatch020.candidate02040 14

certified_graph_case record032 19 32779242078464 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03817 14

certified_graph_case record033 19 32779242143744 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03818 14

certified_graph_case record034 19 32779245199616 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03819 14

certified_graph_case record035 19 32779245264896 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03820 14

certified_graph_case record036 19 32779477190912 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03821 14

certified_graph_case record037 19 32779484270624 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03822 14

certified_graph_case record038 19 32779484278784 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03823 14

certified_graph_case record039 19 32779501832200 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03824 14

certified_graph_case record040 19 32780335581440 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03825 14

certified_graph_case record041 19 32780335646720 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03826 14

certified_graph_case record042 19 32780352291328 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03827 14

certified_graph_case record043 19 32780541102112 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03828 14

certified_graph_case record044 19 32780542018568 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03829 14

certified_graph_case record045 19 32780558794753 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03830 14

certified_graph_case record046 19 32787815074048 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03831 14

certified_graph_case record047 19 32787822413856 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03832 14

theorem record048_parameters : Parameters record048 (rowOfCode 19) 32788318782472 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record048_coverage : Coverage record048 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32788318782472 :=
  GraphCoverageDescriptions.coverage_of_checked record048 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03833 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32788318782472
    (by rfl) record048_cells_exact
    (GraphCoverageDescriptions.small_allowed record048 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch038.candidate03833_checked

theorem record048_result : Result (19, 32788318782472) :=
  of_direct_small 19 32788318782472 (by decide) ⟨record048, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00034.record048.direct_core, record048_parameters, record048_coverage⟩

certified_graph_case record049 19 32788335558657 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03834 14

certified_graph_case record050 19 32804977119264 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03835 14

certified_graph_case record051 19 32804977647616 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03836 14

certified_graph_case record052 19 32804978557952 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03837 14

theorem record053_parameters : Parameters record053 (rowOfCode 19) 32805010539040 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record053_coverage : Coverage record053 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32805010539040 :=
  GraphCoverageDescriptions.coverage_of_checked record053 GraphCoverageDescriptions.GraphCoverageBatch038.candidate03838 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32805010539040
    (by rfl) record053_cells_exact
    (GraphCoverageDescriptions.small_allowed record053 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch038.candidate03838_checked

theorem record053_result : Result (19, 32805010539040) :=
  of_direct_small 19 32805010539040 (by decide) ⟨record053, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00034.record053.direct_core, record053_parameters, record053_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034
