module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow16Part00008Data
public import GraphInputsRow16Part00008Frames
public import GraphInputsRow16Part00008Leaves
public import GraphInputsRow16Part00008Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00008.record037
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record037
def vertexColumn : Fields := ⟨10, hexnat% "2f34acaa6a2ea662d8ae1b91e2785e0fb49ca6692e6652d4ad1b51d2745d0f743c8ea398f1364cb3c2e4b52e2b4acab1ac9b16c3b91cc789c6745c570dd0f23d1a298961382e07919294951342d0770390e2328d1324d0b12c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db4924936db492492492492492492492492449249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1c01c0907ff8000000", hexnat% "400400010000000000", 4829055069192192, hexnat% "200202008000000000", hexnat% "820820400000000000", 3384296790294528]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [5066519381803008, 3940658263883776, 279223176896970752, hexnat% "3e0000000000000000", hexnat% "800800000400000000", hexnat% "400400000100000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ee0c80494768000000", 243194380146442240, hexnat% "100000003080000000", 457396837154816, 7335975940259840, 1133046732423168]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fe0fe0481078000000", 23622320128, 422487342972928, 7318392344150016, 1134146244050944, 52913997086720]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5c05e1cbf0f8000000", hexnat% "820800000000000000", hexnat% "200202000100000000", 6812574045700096, 60129542144, 1125899906842624]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "760361fff5f8000000", hexnat% "80480000000000000", hexnat% "800800000000000000", 7318392344150016, 1125899906842624]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "54017bbff8d8000000", 468374361246531584, hexnat% "2a0000000000000000", hexnat% "800800400420000000", 1125912791744512]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400021a860d0000000", 270215977642229760, hexnat% "3e0000000000000000", hexnat% "800800400428000000", 7335975940259840, 288231488548241408, 1133115451899904]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record037_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record037_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record037_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record037_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record037_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record037_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record037_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record037_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record037_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00008.record037

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00008.record043
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record043
def vertexColumn : Fields := ⟨10, hexnat% "1f0da1eb261d98e4b8ae1b91e2785e0fb49ca66936479c94756352d2b46d4745d0f743c8e5334c7362d4b32d2b2ac6b46c9b16c3bc1d8789d2729c6745c570dd0f23c4f0bc1f2726225a611a499164954348d0b41dc0e4388c6324c5341c8709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db4db6926d249249249b6da693492492493489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨67, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1970324836974592, 5764678991290040320, hexnat% "80000006006c00000", 2305983746702049280, 67243081728, 285978576338026496, 1342177280]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record043_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record043_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record043_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record043_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record043_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record043_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record043_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record043_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record043_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00008.record043

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00008.record024
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3a87ab1b162da4e338ae4783e3a479b17152d64d334ad4743dd0ec398f134ccb31ce4b32cab46c5ba1d8791cc729e1725c3783d0f23c4f0bce21a83ac1916078e11a439c15150770390cc328c6344c3312c2b06e0741c8705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "49a6db49269b6d2492492492492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record024 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record024 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record024.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 30), (facetIndex 34), (facetIndex 38), (facetIndex 48), (facetIndex 58), (facetIndex 68)]))
 (.leaf ([(facetIndex 27), (facetIndex 40), (facetIndex 42), (facetIndex 45), (facetIndex 60), (facetIndex 70)])))
 (.branch 3
 (.leaf ([(facetIndex 43), (facetIndex 49), (facetIndex 61), (facetIndex 71)]))
 (.leaf ([(facetIndex 32), (facetIndex 35), (facetIndex 52), (facetIndex 62)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 33), (facetIndex 41), (facetIndex 46), (facetIndex 47)]))
 (.leaf ([(facetIndex 37), (facetIndex 44), (facetIndex 50), (facetIndex 51)])))
 (.branch 7
 (.leaf ([(facetIndex 28), (facetIndex 29), (facetIndex 31), (facetIndex 36), (facetIndex 39)]))
 (.leaf ([(facetIndex 53), (facetIndex 63)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "440000ed100003bb5090d461c2e623c362z14;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 54), (facetIndex 57)]))
 (.leaf ([(facetIndex 64), (facetIndex 67)])))
 (.branch 3
 (.leaf ([(facetIndex 55), (facetIndex 56), (facetIndex 59)]))
 (.leaf ([(facetIndex 65), (facetIndex 66), (facetIndex 69)]))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨2, sparse_nat% "c7d00828z1b;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 4
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [4]
def grouped2_0007 : List Nat := [4, 5]
def grouped2_0008 : List Nat := [4, 5, 6, 7]
def grouped2_0009 : List Nat := [5]
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7]
def grouped2_0012 : List Nat := [7]
def grouped3_0013 : List Nat := [0]
def grouped3_0014 : List Nat := [0, 1]
def grouped3_0016 : List Nat := [1]
def grouped3_0017 : List Nat := [2]
def grouped3_0018 : List Nat := [2, 3]
def grouped3_0019 : List Nat := [3]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record024 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record024_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00008.record024" "{\"atoms\":[{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00008.record024" 36

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00008.record024" "{\"ridges\":[[29,133],[36,134],[37,577],[44,577],[50,577],[50,578],[51,577],[51,578],[69,708]],\"owners\":[[29,133,[57,59],[2,33,35,36,38,39,54,55]],[36,134,[64,67],[2,29,33,35,38,39,65,69]],[37,577,[],[13,44,49,50,51,56,59]],[44,577,[59],[13,37,49,50,51,56]],[50,577,[56],[13,37,44,49,51,59]],[51,577,[56,59],[13,37,44,49,50]],[50,578,[66],[13,37,44,49,51,69]],[51,578,[66,69],[13,37,44,49,50]],[69,708,[59],[]]],\"edges\":[],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00008.record024" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00008.record024\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-8,-3],[-8,-7],[-9,-8],[-10,-1],[-10,-6],[-11,-3],[-11,-6],[-11,-7],[-11,-9],[-12,-1],[-12,-3],[-14,-1],[-14,-4],[-14,-6],[-14,-10],[-15,-2],[-20,-2],[-2,13,14],[-4,16,18],[-5],[-8,14],[-10,12],[-11,12,14],[-10,17],[-11,17,19],[-19,14],[-21,7,9,15,20],[-22,5,8,10,11],[-23,1,2,3,4,6],[-24,21],[-25,24],[-26,22],[-27,23],[-28,26],[-28,27],[-29,25],[-29,28],[29],[-13,30],[-16,31],[-18,31],[-12,32],[-17,33],[-31,34],[-30,34],[-32,-33,35],[-34,-35,36],[-36]],\"atoms\":[{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":44,\"b\":31},{\"tag\":\"incompatible\",\"a\":44,\"b\":43},{\"tag\":\"incompatible\",\"a\":49,\"b\":44},{\"tag\":\"incompatible\",\"a\":50,\"b\":28},{\"tag\":\"incompatible\",\"a\":50,\"b\":39},{\"tag\":\"incompatible\",\"a\":51,\"b\":31},{\"tag\":\"incompatible\",\"a\":51,\"b\":39},{\"tag\":\"incompatible\",\"a\":51,\"b\":43},{\"tag\":\"incompatible\",\"a\":51,\"b\":49},{\"tag\":\"incompatible\",\"a\":56,\"b\":28},{\"tag\":\"incompatible\",\"a\":56,\"b\":31},{\"tag\":\"incompatible\",\"a\":59,\"b\":28},{\"tag\":\"incompatible\",\"a\":59,\"b\":36},{\"tag\":\"incompatible\",\"a\":59,\"b\":39},{\"tag\":\"incompatible\",\"a\":59,\"b\":50},{\"tag\":\"incompatible\",\"a\":61,\"b\":29},{\"tag\":\"incompatible\",\"a\":71,\"b\":29},{\"tag\":\"mate\",\"ridge\":133,\"a\":29,\"owners\":[57,59]},{\"tag\":\"mate\",\"ridge\":134,\"a\":36,\"owners\":[64,67]},{\"tag\":\"mate\",\"ridge\":577,\"a\":37,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":577,\"a\":44,\"owners\":[59]},{\"tag\":\"mate\",\"ridge\":577,\"a\":50,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":577,\"a\":51,\"owners\":[56,59]},{\"tag\":\"mate\",\"ridge\":578,\"a\":50,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":578,\"a\":51,\"owners\":[66,69]},{\"tag\":\"mate\",\"ridge\":708,\"a\":69,\"owners\":[59]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[43,49,61,71],\"full_literals\":[-21,7,9,15,20]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[37,44,50,51],\"full_literals\":[-22,5,8,10,11]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[28,29,31,36,39],\"full_literals\":[-23,1,2,3,4,6]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-24,21,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-25,false,24],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-26,false,22],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-27,23,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-28,26,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-28,false,27],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-29,25,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-29,false,28],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":57,\"full_literals\":[-13,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":64,\"full_literals\":[-16,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":67,\"full_literals\":[-18,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":56,\"full_literals\":[-12,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":66,\"full_literals\":[-17,33]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-31,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-30,false,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-32,-33,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-34,-35,36],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true}]}"
  "p cnf 36 48\n-8 -3 0\n-8 -7 0\n-9 -8 0\n-10 -1 0\n-10 -6 0\n-11 -3 0\n-11 -6 0\n-11 -7 0\n-11 -9 0\n-12 -1 0\n-12 -3 0\n-14 -1 0\n-14 -4 0\n-14 -6 0\n-14 -10 0\n-15 -2 0\n-20 -2 0\n-2 13 14 0\n-4 16 18 0\n-5 0\n-8 14 0\n-10 12 0\n-11 12 14 0\n-10 17 0\n-11 17 19 0\n-19 14 0\n-21 7 9 15 20 0\n-22 5 8 10 11 0\n-23 1 2 3 4 6 0\n-24 21 0\n-25 24 0\n-26 22 0\n-27 23 0\n-28 26 0\n-28 27 0\n-29 25 0\n-29 28 0\n29 0\n-13 30 0\n-16 31 0\n-18 31 0\n-12 32 0\n-17 33 0\n-31 34 0\n-30 34 0\n-32 -33 35 0\n-34 -35 36 0\n-36 0\n"
  "49 -22 8 10 11 0 20 28 0\n50 25 0 38 36 0\n51 28 0 38 37 0\n52 24 0 50 31 0\n53 26 0 51 34 0\n54 27 0 51 35 0\n55 21 0 52 30 0\n56 22 0 53 32 0\n57 23 0 54 33 0\n58 -8 6 1 4 0 57 55 1 2 3 29 16 17 27 0\n59 -14 4 0 56 57 55 12 14 15 58 49 6 8 9 29 16 17 27 0\n60 -11 34 0 57 45 39 44 40 41 19 59 18 6 7 23 29 10 0\n61 34 0 56 57 44 45 40 41 39 19 59 21 18 60 49 4 5 22 29 11 0\n62 -35 0 61 48 47 0\n63 -10 0 62 22 24 42 43 46 0\n64 14 0 56 63 62 21 26 49 23 25 42 43 46 0\n65 -4 0 64 13 0\n66 0 64 65 59 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record024.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record024.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record024.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record024.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record024 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record024.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record024.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record024.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record024.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record024 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record024_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record024_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record024_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record024_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record024_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record024_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record024_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record024 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record024_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record024_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record024_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00008.record024

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00008.record047
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "d88ea969a6c58762b86e2785ed84e9965a5c54752b46d2745dd0f2368e6358ce3c4c7392ccb2ac6b86c9bc1d8719e1745c9715c3743c4f0be52169262988e07a51165252948d0770390d2328c6384c5322c4b06d0721c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6d26d349b49b4d2492492492492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record047 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record047 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record047.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record047.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record047.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 31), (facetIndex 39), (facetIndex 43), (facetIndex 44), (facetIndex 59), (facetIndex 69)]))
 (.leaf ([(facetIndex 27), (facetIndex 30), (facetIndex 35), (facetIndex 36), (facetIndex 49), (facetIndex 58), (facetIndex 68)])))
 (.branch 3
 (.leaf ([(facetIndex 28), (facetIndex 29), (facetIndex 32), (facetIndex 38), (facetIndex 53), (facetIndex 63)]))
 (.leaf ([(facetIndex 52), (facetIndex 62)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 40), (facetIndex 41), (facetIndex 55), (facetIndex 65)]))
 (.leaf ([(facetIndex 33), (facetIndex 34), (facetIndex 37), (facetIndex 45)])))
 (.branch 7
 (.leaf ([(facetIndex 42), (facetIndex 46), (facetIndex 48)]))
 (.leaf ([(facetIndex 47), (facetIndex 50), (facetIndex 51)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "10204c0040813fcefa81a40a936a0522z14;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 57)]))
 (.leaf ([(facetIndex 61)])))
 (.branch 3
 (.leaf ([(facetIndex 67)]))
 (.leaf ([(facetIndex 71)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 54), (facetIndex 56)]))
 (.leaf ([(facetIndex 60), (facetIndex 64)])))
 (.branch 7
 (.leaf ([(facetIndex 66)]))
 (.leaf ([(facetIndex 70)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "7c058500d0041z29;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4, 5]
def grouped2_0003 : List Nat := [4, 5, 6, 7]
def grouped2_0004 : List Nat := [6]
def grouped2_0005 : List Nat := [6, 7]
def grouped2_0006 : List Nat := [7]
def grouped3_0007 : List Nat := [0]
def grouped3_0008 : List Nat := [0, 1]
def grouped3_0009 : List Nat := [0, 1, 2, 3]
def grouped3_0011 : List Nat := [1]
def grouped3_0012 : List Nat := [2]
def grouped3_0013 : List Nat := [2, 3]
def grouped3_0014 : List Nat := [3]
def grouped3_0015 : List Nat := [4]
def grouped3_0016 : List Nat := [4, 5]
def grouped3_0017 : List Nat := [4, 5, 6, 7]
def grouped3_0018 : List Nat := [5]
def grouped3_0019 : List Nat := [6]
def grouped3_0020 : List Nat := [6, 7]
def grouped3_0021 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record047 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record047_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00008.record047" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0005\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00008.record047" 43

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00008.record047" "{\"ridges\":[[10,98],[14,769],[14,770],[35,98],[37,769],[37,770],[40,98],[44,98],[45,769],[45,770],[46,98],[47,98],[48,98],[50,769],[50,770],[51,769],[51,770],[56,116],[57,788],[60,232],[61,864],[66,116],[67,788],[70,232],[71,864]],\"owners\":[[10,98,[64,66,70,71],[35,40,44,46,47,48]],[35,98,[70,71],[10,40,44,46,47,48,64,66]],[40,98,[66,71],[10,35,44,46,47,48,64,70]],[44,98,[64,70,71],[10,35,40,46,47,48,66]],[46,98,[64,66,71],[10,35,40,44,47,48,70]],[47,98,[64,66,70],[10,35,40,44,46,48,71]],[48,98,[64,66,70],[10,35,40,44,46,47,71]],[14,769,[57,61],[37,45,50,51]],[37,769,[61],[14,45,50,51,57]],[45,769,[61],[14,37,50,51,57]],[50,769,[57],[14,37,45,51,61]],[51,769,[57],[14,37,45,50,61]],[14,770,[67,71],[37,45,50,51]],[37,770,[71],[14,45,50,51,67]],[45,770,[71],[14,37,50,51,67]],[50,770,[67],[14,37,45,51,71]],[51,770,[67],[14,37,45,50,71]],[56,116,[66],[]],[66,116,[56],[]],[57,788,[67],[]],[67,788,[57],[]],[60,232,[70],[]],[70,232,[60],[]],[61,864,[71],[]],[71,864,[61],[]]],\"edges\":[[35,[10,35,40,44,46,47,48,54,56,60,61,64,66,70,71]],[44,[14,37,45,50,51,57,61,67,71]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00008.record047" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00008.record047\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-22,-11],[-22,-12],[-1,18,19,21,22],[-3,21,22],[-5,19,22],[-6,18,21,22],[-8,18,19,22],[-9,18,19,21],[-10,18,19,21],[-2,15,17],[-4,17],[-7,17],[-11,15],[-12,15],[-2,20,22],[-4,22],[-7,22],[-11,20],[-12,20],[-14,19],[-19,14],[-15,20],[-20,15],[-16,21],[-21,16],[-17,22],[-22,17],[-23,9,11,12],[-24,23],[-25,24],[-26,25],[26],[-15,27],[-17,28],[-20,29],[-22,30],[-13,31],[-14,31],[-16,32],[-18,32],[-33,19],[-19,33],[-34,21],[-21,34],[-28,35],[-27,35],[-30,36],[-29,36],[-36,37],[-35,37],[-35,-36,38],[-32,39],[-31,39],[-40,33,34],[-34,40],[-33,40],[-39,41],[-39,-40,42],[-37,-42,43],[-38,-41,43],[-43],[1,3,5,6,8,9,10,13,14,16,17,18,19,21,22],[2,4,7,11,12,15,17,20,22]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":71,\"b\":50},{\"tag\":\"incompatible\",\"a\":71,\"b\":51},{\"tag\":\"mate\",\"ridge\":98,\"a\":10,\"owners\":[64,66,70,71]},{\"tag\":\"mate\",\"ridge\":98,\"a\":35,\"owners\":[70,71]},{\"tag\":\"mate\",\"ridge\":98,\"a\":40,\"owners\":[66,71]},{\"tag\":\"mate\",\"ridge\":98,\"a\":44,\"owners\":[64,70,71]},{\"tag\":\"mate\",\"ridge\":98,\"a\":46,\"owners\":[64,66,71]},{\"tag\":\"mate\",\"ridge\":98,\"a\":47,\"owners\":[64,66,70]},{\"tag\":\"mate\",\"ridge\":98,\"a\":48,\"owners\":[64,66,70]},{\"tag\":\"mate\",\"ridge\":769,\"a\":14,\"owners\":[57,61]},{\"tag\":\"mate\",\"ridge\":769,\"a\":37,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":769,\"a\":45,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":769,\"a\":50,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":769,\"a\":51,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":770,\"a\":14,\"owners\":[67,71]},{\"tag\":\"mate\",\"ridge\":770,\"a\":37,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":770,\"a\":45,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":770,\"a\":50,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":770,\"a\":51,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":116,\"a\":56,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":116,\"a\":66,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":788,\"a\":57,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":788,\"a\":67,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":232,\"a\":60,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":232,\"a\":70,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":864,\"a\":61,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":864,\"a\":71,\"owners\":[61]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[47,50,51],\"full_literals\":[-23,9,11,12]},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0004\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0005\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-24,false,23],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-25,false,24],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0003\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-26,false,25],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":57,\"full_literals\":[-15,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":61,\"full_literals\":[-17,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":67,\"full_literals\":[-20,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":71,\"full_literals\":[-22,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":54,\"full_literals\":[-13,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":56,\"full_literals\":[-14,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":60,\"full_literals\":[-16,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":64,\"full_literals\":[-18,32]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[66],\"full_literals\":[-33,19]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":66,\"full_literals\":[-19,33]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[70],\"full_literals\":[-34,21]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":70,\"full_literals\":[-21,34]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-28,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-27,false,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-30,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-29,false,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-36,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-35,false,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-35,-36,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-32,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-31,false,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-40,33,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-34,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-33,false,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-39,false,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-39,-40,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-37,-42,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-38,-41,43],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":35,\"owners\":[10,35,40,44,46,47,48,54,56,60,61,64,66,70,71]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[14,37,45,50,51,57,61,67,71]}]}"
  "p cnf 43 63\n-22 -11 0\n-22 -12 0\n-1 18 19 21 22 0\n-3 21 22 0\n-5 19 22 0\n-6 18 21 22 0\n-8 18 19 22 0\n-9 18 19 21 0\n-10 18 19 21 0\n-2 15 17 0\n-4 17 0\n-7 17 0\n-11 15 0\n-12 15 0\n-2 20 22 0\n-4 22 0\n-7 22 0\n-11 20 0\n-12 20 0\n-14 19 0\n-19 14 0\n-15 20 0\n-20 15 0\n-16 21 0\n-21 16 0\n-17 22 0\n-22 17 0\n-23 9 11 12 0\n-24 23 0\n-25 24 0\n-26 25 0\n26 0\n-15 27 0\n-17 28 0\n-20 29 0\n-22 30 0\n-13 31 0\n-14 31 0\n-16 32 0\n-18 32 0\n-33 19 0\n-19 33 0\n-34 21 0\n-21 34 0\n-28 35 0\n-27 35 0\n-30 36 0\n-29 36 0\n-36 37 0\n-35 37 0\n-35 -36 38 0\n-32 39 0\n-31 39 0\n-40 33 34 0\n-34 40 0\n-33 40 0\n-39 41 0\n-39 -40 42 0\n-37 -42 43 0\n-38 -41 43 0\n-43 0\n1 3 5 6 8 9 10 13 14 16 17 18 19 21 22 0\n2 4 7 11 12 15 17 20 22 0\n"
  "64 25 0 32 31 0\n65 24 0 64 30 0\n66 23 0 65 29 0\n67 37 0 49 50 47 48 45 46 36 35 34 33 16 17 15 18 19 63 0\n68 -42 0 67 61 59 0\n69 -40 0 68 58 52 53 39 38 25 21 43 41 54 0\n70 -34 0 69 55 0\n71 -33 0 69 56 0\n72 -21 0 70 44 0\n73 -19 0 71 42 0\n74 -16 0 72 24 0\n75 -14 0 73 20 0\n76 36 0 47 48 36 35 16 17 26 15 18 19 22 63 0\n77 35 0 45 46 34 33 11 12 27 10 13 14 23 63 0\n78 38 0 77 76 51 0\n79 -41 0 78 61 60 0\n80 -39 0 79 57 0\n81 -32 0 80 52 0\n82 -31 0 80 53 0\n83 -18 0 81 40 0\n84 -13 0 82 37 0\n85 -9 0 83 73 72 8 0\n86 -10 0 83 73 72 9 0\n87 22 0 72 73 83 74 75 84 86 85 26 4 5 6 3 7 62 0\n88 -11 0 87 1 0\n89 -12 0 87 2 0\n90 0 88 89 66 85 28 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record047.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record047.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record047.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record047.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record047 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record047.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record047.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record047.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record047.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record047 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record047_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record047_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record047_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record047_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record047_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record047_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record047_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record047 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record047_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record047_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record047_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00008.record047
