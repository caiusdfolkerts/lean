module
prelude
public meta import GraphCases
public import GraphInputsRow23Part00011Checked
public import GraphInputsRow23Part00011Metadata
public import GraphInputsRow23Part00011Frames
public import GraphInputsRow23Part00011Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch049
public import GraphCoverageBatch050
public import GraphInputsRow23Part00011Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 23 19093952397312 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04962 6

certified_graph_case record001 23 19244853002496 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04963 6

certified_graph_case record002 23 19246999437568 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04964 6

certified_graph_case record003 23 19280284647680 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04965 6

certified_graph_case record004 23 19281857282304 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04966 6

certified_graph_case record005 23 19294748442624 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04967 6

certified_graph_case record006 23 19297959706880 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04968 6

certified_graph_case record007 23 19329041072128 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04969 6

certified_graph_case record008 23 19330171961600 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04970 6

certified_graph_case record009 23 19366280233216 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04971 6

certified_graph_case record010 23 19366817103872 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04972 6

certified_graph_case record011 23 19366825426944 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04973 6

certified_graph_case record012 23 19426816622592 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04974 6

certified_graph_case record013 23 19434865492224 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04975 6

certified_graph_case record014 23 19435402362880 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04976 6

certified_graph_case record015 23 19435410685952 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04977 6

certified_graph_case record016 23 19435534483456 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04978 6

certified_graph_case record017 23 19469762101248 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04979 6

certified_graph_case record018 23 19503723380736 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04980 6

certified_graph_case record019 23 19504260186112 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04981 6

certified_graph_case record020 23 19512581685248 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04982 6

certified_graph_case record021 23 19534796849152 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04983 6

certified_graph_case record022 23 19564251381760 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04984 6

certified_graph_case record023 23 19564259704832 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04985 6

certified_graph_case record024 23 19572837057152 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04986 6

theorem record025_parameters : Parameters record025 (rowOfCode 23) 19573914992640 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record025_coverage : Coverage record025 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19573914992640 :=
  GraphCoverageDescriptions.coverage_of_checked record025 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04987 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 19573914992640
    (by rfl) record025_cells_exact
    (GraphCoverageDescriptions.small_allowed record025 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch049.candidate04987_checked

theorem record025_result : Result (23, 19573914992640) :=
  of_direct_small 23 19573914992640 (by decide) ⟨record025, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00011.record025.direct_core, record025_parameters, record025_coverage⟩

certified_graph_case record026 23 19586326233344 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04988 6

certified_graph_case record027 23 19588947443712 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04989 6

certified_graph_case record028 23 19592068005888 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04990 6

certified_graph_case record029 23 19610889912576 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04991 6

certified_graph_case record030 23 19611627044864 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04992 6

certified_graph_case record031 23 19619561898240 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04993 6

certified_graph_case record032 23 19619574188032 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04994 6

certified_graph_case record033 23 19623978270976 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04995 6

certified_graph_case record034 23 19623982532608 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04996 6

certified_graph_case record035 23 19624263483392 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04997 6

certified_graph_case record036 23 19632572399616 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04998 6

certified_graph_case record037 23 19633109204992 GraphCoverageDescriptions.GraphCoverageBatch049.candidate04999 6

certified_graph_case record038 23 19637261860864 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05000 6

certified_graph_case record039 23 19645318889472 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05001 6

certified_graph_case record040 23 19645987815424 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05002 6

certified_graph_case record041 23 19649752203264 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05003 6

certified_graph_case record042 23 19650280685568 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05004 6

certified_graph_case record043 23 19701694464000 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05005 6

certified_graph_case record044 23 19709743398912 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05006 6

certified_graph_case record045 23 19710412324864 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05007 6

certified_graph_case record046 23 19718337462272 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05008 6

theorem record047_parameters : Parameters record047 (rowOfCode 23) 19718865944576 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record047_coverage : Coverage record047 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19718865944576 :=
  GraphCoverageDescriptions.coverage_of_checked record047 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 19718865944576
    (by rfl) record047_cells_exact
    (GraphCoverageDescriptions.small_allowed record047 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch050.candidate05009_checked

theorem record047_result : Result (23, 19718865944576) :=
  of_direct_small 23 19718865944576 (by decide) ⟨record047, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00011.record047.direct_core, record047_parameters, record047_coverage⟩

certified_graph_case record048 23 19724775784704 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05010 6

certified_graph_case record049 23 19729209163776 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05011 6

certified_graph_case record050 23 19729745969152 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05012 6

certified_graph_case record051 23 19733369913344 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05013 6

certified_graph_case record052 23 19733906718720 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05014 6

certified_graph_case record053 23 19741955653632 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05015 6

certified_graph_case record054 23 19742228217856 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05016 6

certified_graph_case record055 23 19742624579584 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05017 6

certified_graph_case record056 23 19748328898560 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05018 6

certified_graph_case record057 23 19878595534976 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05019 6

certified_graph_case record058 23 19901406281984 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05020 6

certified_graph_case record059 23 19901414670336 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05021 6

certified_graph_case record060 23 19905707540480 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05022 6

certified_graph_case record061 23 19907787915264 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05023 6

certified_graph_case record062 23 20038845267968 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05024 6

certified_graph_case record063 23 20175747318016 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05025 6

certified_graph_case record064 23 20176015785984 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05026 6

certified_graph_case record065 23 20176284188672 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05027 6

certified_graph_case record066 23 20192927186944 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05028 6

certified_graph_case record067 23 20193195589632 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05029 6

certified_graph_case record068 23 20199436713984 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05030 6

certified_graph_case record069 23 20278893674496 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05031 6

certified_graph_case record070 23 20346675663104 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05032 6

certified_graph_case record071 23 20381100474624 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05033 6

certified_graph_case record072 23 20381368877312 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05034 6

certified_graph_case record073 23 20381377265664 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05035 6

certified_graph_case record074 23 20385670135808 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05036 6

certified_graph_case record075 23 20388881400064 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05037 6

certified_graph_case record076 23 20393991634944 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05038 6

certified_graph_case record077 23 20412123582720 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05039 6

certified_graph_case record078 23 20415661506816 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05040 6

certified_graph_case record079 23 20415669895168 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05041 6

certified_graph_case record080 23 20419962765312 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05042 6

certified_graph_case record081 23 20423174029568 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05043 6

certified_graph_case record082 23 20428143755520 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05044 6

certified_graph_case record083 23 20428152143872 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05045 6

certified_graph_case record084 23 20428284264448 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05046 6

certified_graph_case record085 23 20428350324736 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05047 6

certified_graph_case record086 23 20428544311424 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05048 6

certified_graph_case record087 23 20429683589248 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05049 6

certified_graph_case record088 23 20496869523456 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05050 6

certified_graph_case record089 23 20525787185408 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05051 6

certified_graph_case record090 23 20526059814912 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05052 6

certified_graph_case record091 23 20526456176640 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05053 6

certified_graph_case record092 23 20622688682240 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05054 6

certified_graph_case record093 23 20634304282624 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05055 6

certified_graph_case record094 23 20687922168064 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05056 6

theorem record095_parameters : Parameters record095 (rowOfCode 23) 20688190636032 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record095_coverage : Coverage record095 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 20688190636032 :=
  GraphCoverageDescriptions.coverage_of_checked record095 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05057 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 20688190636032
    (by rfl) record095_cells_exact
    (GraphCoverageDescriptions.small_allowed record095 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch050.candidate05057_checked

theorem record095_result : Result (23, 20688190636032) :=
  of_direct_small 23 20688190636032 (by decide) ⟨record095, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00011.record095.direct_core, record095_parameters, record095_coverage⟩

theorem record096_parameters : Parameters record096 (rowOfCode 23) 20688198959104 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record096_coverage : Coverage record096 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 20688198959104 :=
  GraphCoverageDescriptions.coverage_of_checked record096 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05058 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 20688198959104
    (by rfl) record096_cells_exact
    (GraphCoverageDescriptions.small_allowed record096 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch050.candidate05058_checked

theorem record096_result : Result (23, 20688198959104) :=
  of_direct_small 23 20688198959104 (by decide) ⟨record096, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00011.record096.direct_core, record096_parameters, record096_coverage⟩

certified_graph_case record097 23 20688459038720 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05059 6

certified_graph_case record098 23 20688591159296 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05060 6

certified_graph_case record099 23 20690271010816 GraphCoverageDescriptions.GraphCoverageBatch050.candidate05061 6
end Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011
