module
prelude
public meta import GraphCases
public import GraphInputsRow23Part00009Checked
public import GraphInputsRow23Part00009Metadata
public import GraphInputsRow23Part00009Frames
public import GraphInputsRow23Part00009Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch047
public import GraphCoverageBatch048
public import GraphInputsRow23Part00009Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 23 16776699056128 GraphCoverageDescriptions.GraphCoverageBatch047.candidate04788 6

certified_graph_case record001 23 16778692984832 GraphCoverageDescriptions.GraphCoverageBatch047.candidate04789 6

certified_graph_case record002 23 16815208005632 GraphCoverageDescriptions.GraphCoverageBatch047.candidate04790 6

certified_graph_case record003 23 16906134257920 GraphCoverageDescriptions.GraphCoverageBatch047.candidate04791 6

certified_graph_case record004 23 16908350980096 GraphCoverageDescriptions.GraphCoverageBatch047.candidate04792 6

certified_graph_case record005 23 16908623544320 GraphCoverageDescriptions.GraphCoverageBatch047.candidate04793 6

certified_graph_case record006 23 16909019906048 GraphCoverageDescriptions.GraphCoverageBatch047.candidate04794 6

certified_graph_case record007 23 16914724225024 GraphCoverageDescriptions.GraphCoverageBatch047.candidate04795 6

certified_graph_case record008 23 16915261030400 GraphCoverageDescriptions.GraphCoverageBatch047.candidate04796 6

certified_graph_case record009 23 16930795700224 GraphCoverageDescriptions.GraphCoverageBatch047.candidate04797 6

certified_graph_case record010 23 16931904028672 GraphCoverageDescriptions.GraphCoverageBatch047.candidate04798 6

certified_graph_case record011 23 16932036149248 GraphCoverageDescriptions.GraphCoverageBatch047.candidate04799 6

certified_graph_case record012 23 16943667019776 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04800 6

certified_graph_case record013 23 16943939584000 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04801 6

certified_graph_case record014 23 16944451551232 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04802 6

certified_graph_case record015 23 16947959889920 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04803 6

certified_graph_case record016 23 16948496695296 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04804 6

certified_graph_case record017 23 16948612300800 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04805 6

certified_graph_case record018 23 16952236113920 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04806 6

certified_graph_case record019 23 16969415917568 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04807 6

certified_graph_case record020 23 16975996715008 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04808 6

certified_graph_case record021 23 16980430028800 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04809 6

certified_graph_case record022 23 16980958511104 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04810 6

certified_graph_case record023 23 16985119260672 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04811 6

certified_graph_case record024 23 16986671153152 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04812 6

certified_graph_case record025 23 17003842633728 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04813 6

certified_graph_case record026 23 17043798163456 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04814 6

certified_graph_case record027 23 17044066566144 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04815 6

certified_graph_case record028 23 17044070207488 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04816 6

certified_graph_case record029 23 17051582730240 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04817 6

certified_graph_case record030 23 17052404350976 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04818 6

certified_graph_case record031 23 17052639301632 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04819 6

certified_graph_case record032 23 17052668592128 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04820 6

certified_graph_case record033 23 17052676915200 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04821 6

certified_graph_case record034 23 17052899803136 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04822 6

certified_graph_case record035 23 17059912356096 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04823 6

certified_graph_case record036 23 17060180791424 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04824 6

certified_graph_case record037 23 17060415672336 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04825 6

certified_graph_case record038 23 17069005869056 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04826 6

certified_graph_case record039 23 17081357631744 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04827 6

certified_graph_case record040 23 17121090273280 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04828 6

certified_graph_case record041 23 17121627078656 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04829 6

certified_graph_case record042 23 17136957325312 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04830 6

certified_graph_case record043 23 17137725341696 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04831 6

certified_graph_case record044 23 17154376269824 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04832 6

theorem record045_parameters : Parameters record045 (rowOfCode 23) 17171556073472 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record045_coverage : Coverage record045 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17171556073472 :=
  GraphCoverageDescriptions.coverage_of_checked record045 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04833 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 17171556073472
    (by rfl) record045_cells_exact
    (GraphCoverageDescriptions.small_allowed record045 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch048.candidate04833_checked

theorem record045_result : Result (23, 17171556073472) :=
  of_direct_small 23 17171556073472 (by decide) ⟨record045, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00009.record045.direct_core, record045_parameters, record045_coverage⟩

certified_graph_case record046 23 17172084555776 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04834 6

certified_graph_case record047 23 17180431486976 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04835 6

certified_graph_case record048 23 17181081403648 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04836 6

certified_graph_case record049 23 17189013356544 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04837 6

certified_graph_case record050 23 17189021679616 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04838 6

certified_graph_case record051 23 17190078251008 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04839 6

certified_graph_case record052 23 17190212337664 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04840 6

certified_graph_case record053 23 17192796094464 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04841 6

certified_graph_case record054 23 17197586057232 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04842 6

certified_graph_case record055 23 17197854625792 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04843 6

certified_graph_case record056 23 17198261272576 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04844 6

certified_graph_case record057 23 17198533836800 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04845 6

certified_graph_case record058 23 17198928101888 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04846 6

certified_graph_case record059 23 17201381834752 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04847 6

certified_graph_case record060 23 17202149851136 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04848 6

certified_graph_case record061 23 17218800779264 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04849 6

certified_graph_case record062 23 17227659083776 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04850 6

certified_graph_case record063 23 17235980582912 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04851 6

certified_graph_case record064 23 17236509065216 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04852 6

certified_graph_case record065 23 17274358661120 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04853 6

certified_graph_case record066 23 17292083593216 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04854 6

certified_graph_case record067 23 17309255073792 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04855 6

certified_graph_case record068 23 17317602004992 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04856 6

certified_graph_case record069 23 17326183874560 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04857 6

certified_graph_case record070 23 17326451720720 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04858 6

theorem record071_parameters : Parameters record071 (rowOfCode 23) 17457033052160 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record071_coverage : Coverage record071 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17457033052160 :=
  GraphCoverageDescriptions.coverage_of_checked record071 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04859 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 17457033052160
    (by rfl) record071_cells_exact
    (GraphCoverageDescriptions.small_allowed record071 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch048.candidate04859_checked

theorem record071_result : Result (23, 17457033052160) :=
  of_direct_small 23 17457033052160 (by decide) ⟨record071, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00009.record071.direct_core, record071_parameters, record071_coverage⟩

theorem record072_parameters : Parameters record072 (rowOfCode 23) 17493678620672 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record072_coverage : Coverage record072 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17493678620672 :=
  GraphCoverageDescriptions.coverage_of_checked record072 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04860 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 17493678620672
    (by rfl) record072_cells_exact
    (GraphCoverageDescriptions.small_allowed record072 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch048.candidate04860_checked

theorem record072_result : Result (23, 17493678620672) :=
  of_direct_small 23 17493678620672 (by decide) ⟨record072, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00009.record072.direct_core, record072_parameters, record072_coverage⟩

theorem record073_parameters : Parameters record073 (rowOfCode 23) 17502528602112 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record073_coverage : Coverage record073 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17502528602112 :=
  GraphCoverageDescriptions.coverage_of_checked record073 GraphCoverageDescriptions.GraphCoverageBatch048.candidate04861 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 17502528602112
    (by rfl) record073_cells_exact
    (GraphCoverageDescriptions.small_allowed record073 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch048.candidate04861_checked

theorem record073_result : Result (23, 17502528602112) :=
  of_direct_small 23 17502528602112 (by decide) ⟨record073, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00009.record073.direct_core, record073_parameters, record073_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009
