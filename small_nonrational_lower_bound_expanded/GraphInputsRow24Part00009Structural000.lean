module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00009Data
public import GraphInputsRow24Part00009Frames
public import GraphInputsRow24Part00009Leaves
public import GraphInputsRow24Part00009Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00009.record020
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record020
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 4611687186658492416, 4398063288320, 220177203462144, 17592186044416]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 3), 219902325555200, 54043204118380544, 4400193994752, 144678138029277184]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 4), 5769112222173233152, 198158385751785472, 8640266240, 57244397862912, 562949953421312]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2641511007075172352, 92427696209920, 739153288842182656, (certNat% 5), 1225014283016863744, (certNat% 6)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), 326510981574295552, (certNat% 5), 1099712954368, 2305984021579956224, 79169132167168]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [12441996902096961536, (certNat% 8), 39652211818496, (certNat% 9), 234187182770749440, 285212672]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [5850795286728802304, (certNat% 10), 83567178678272, 198158385751785472, 2594214122853761024, 578712560707043328]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [5774456206491910144, 234187182770749440, (certNat% 10), 4503600432676864, 2305845208236949504, 902971725287784448]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), (certNat% 12), 219906620522496, 9223374236012249088]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), 90071995768635392, 30786325577728, (certNat% 14), 4445962240, 1157425104234217472]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), 18014400673742848, 101155069755392, 35184372088832]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), 630503956421804032, 11529217245091725312, 4445962240, 2147483648, 219902325555200]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [340862156557778944, 576460752840294400, (certNat% 17), 234187182770749440, (certNat% 9), 268435456]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), (certNat% 19), 83562883710976, 1090519040, 900719934064033792, 140738025226240]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), 70368878395392, 144115190491774976, 57175678386176, (certNat% 21), 72057594037927936]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), 213305255788544, 756604737398243328, 939524096, 2594073385365405696, (certNat% 23)]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [16428160887291904, 900719925474099200, 1225014283016863744, 2305985945725304832, (certNat% 24), 162129588732821504, 956301312]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c21 c18
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c22 c17
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c23 c16
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c24 c15
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c25 c12
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c26 c9
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c27 c8
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c28 c7
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c29 c6
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c30 c5
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c31 c4
  c32
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record020_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record020_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record020_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record020_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record020_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record020_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record020_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record020_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record020_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00009.record020

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00009.record023
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "32cc72aa568daa98e655a2e4783ef078972729c655936745b1725a94e5c570d8b52d8751d0f6a338d5334e8b52ccb8ad1b26c5b0ee8751cc789ca719d170de0f43c2f07ea8550aa15aa154709a26292a519c154589515154c328c5322c2b06c4709c17"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "da6db4db69a49a69349369a492692493492493691249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record023 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record023 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record023.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record023.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record023.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 59), (facetIndex 67)]))
 (.branch 2
 (.leaf ([(facetIndex 36), (facetIndex 56)]))
 (.leaf ([(facetIndex 43), (facetIndex 61), (facetIndex 65)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 72), (facetIndex 73)]))
 (.leaf ([(facetIndex 74), (facetIndex 75)])))
 (.branch 6
 (.leaf ([(facetIndex 27), (facetIndex 28), (facetIndex 49), (facetIndex 51), (facetIndex 52)]))
 (.leaf ([(facetIndex 68), (facetIndex 69), (facetIndex 70), (facetIndex 77), (facetIndex 78)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b091b1b6010010001005a28000400001000005az14;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0003 : List Nat := [1]
def grouped3_0004 : List Nat := [1, 2]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [3]
def grouped3_0007 : List Nat := [3, 4]
def grouped3_0008 : List Nat := [3, 4, 5, 6]
def grouped3_0009 : List Nat := [4]
def grouped3_0010 : List Nat := [5]
def grouped3_0011 : List Nat := [5, 6]
def grouped3_0012 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record023 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record023_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00009.record023" "{\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00009.record023" 34

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00009.record023" "{\"ridges\":[[8,193],[8,194],[13,772],[18,776],[34,193],[34,194],[42,193],[42,194],[45,193],[45,194],[47,193],[47,194],[54,772],[55,772],[56,228],[58,772],[59,708],[60,772],[61,216],[63,776],[64,776],[65,456],[66,776],[67,960],[72,228],[74,216]],\"owners\":[[8,193,[56,59,61,65,67],[34,42,45,47]],[34,193,[61,65,67],[8,42,45,47,56,59]],[42,193,[56,59,67],[8,34,45,47,61,65]],[45,193,[56,59,65,67],[8,34,42,47,61]],[47,193,[59,61,65,67],[8,34,42,45,56]],[8,194,[72,74],[34,42,45,47]],[34,194,[74],[8,42,45,47,72]],[42,194,[72],[8,34,45,47,74]],[45,194,[72],[8,34,42,47,74]],[47,194,[74],[8,34,42,45,72]],[13,772,[77,78],[54,55,58,60]],[54,772,[],[13,55,58,60,77,78]],[55,772,[78],[13,54,58,60,77]],[58,772,[77],[13,54,55,60,78]],[60,772,[77,78],[13,54,55,58]],[18,776,[77,78],[54,63,64,66]],[63,776,[78],[18,54,64,66,77]],[64,776,[77],[18,54,63,66,78]],[66,776,[77,78],[18,54,63,64]],[56,228,[72],[]],[72,228,[56],[]],[59,708,[],[]],[61,216,[74],[]],[74,216,[61],[]],[65,456,[],[]],[67,960,[],[]]],\"edges\":[[39,[8,34,42,45,47,56,59,61,65,67,72,74]],[44,[13,18,54,55,58,60,63,64,66,67,77,78]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00009.record023" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00009.record023\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,10,12,14,17,19],[-4,14,17,19],[-5,10,12,19],[-6,10,12,17,19],[-7,12,14,17,19],[-1,20,21],[-4,21],[-5,20],[-6,20],[-7,21],[-2,22,23],[-8],[-9,23],[-11,22],[-13,22,23],[-3,22,23],[-15,23],[-16,22],[-18,22,23],[-10,20],[-20,10],[-12],[-14,21],[-21,14],[-17],[-19],[-10,24],[-14,25],[-20,26],[-21,27],[-22,28],[-23,28],[-25,29],[-24,29],[-29,30],[-27,31],[-26,31],[-28,32],[-31,-32,33],[-30,-33,34],[-34],[1,4,5,6,7,10,12,14,17,19,20,21],[2,3,8,9,11,13,15,16,18,19,22,23]],\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":193,\"a\":8,\"owners\":[56,59,61,65,67]},{\"tag\":\"mate\",\"ridge\":193,\"a\":34,\"owners\":[61,65,67]},{\"tag\":\"mate\",\"ridge\":193,\"a\":42,\"owners\":[56,59,67]},{\"tag\":\"mate\",\"ridge\":193,\"a\":45,\"owners\":[56,59,65,67]},{\"tag\":\"mate\",\"ridge\":193,\"a\":47,\"owners\":[59,61,65,67]},{\"tag\":\"mate\",\"ridge\":194,\"a\":8,\"owners\":[72,74]},{\"tag\":\"mate\",\"ridge\":194,\"a\":34,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":194,\"a\":42,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":194,\"a\":45,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":194,\"a\":47,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":772,\"a\":13,\"owners\":[77,78]},{\"tag\":\"mate\",\"ridge\":772,\"a\":54,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":772,\"a\":55,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":772,\"a\":58,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":772,\"a\":60,\"owners\":[77,78]},{\"tag\":\"mate\",\"ridge\":776,\"a\":18,\"owners\":[77,78]},{\"tag\":\"mate\",\"ridge\":776,\"a\":63,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":776,\"a\":64,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":776,\"a\":66,\"owners\":[77,78]},{\"tag\":\"mate\",\"ridge\":228,\"a\":56,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":228,\"a\":72,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":708,\"a\":59,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":216,\"a\":61,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":216,\"a\":74,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":456,\"a\":65,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":960,\"a\":67,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":56,\"full_literals\":[-10,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":61,\"full_literals\":[-14,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":72,\"full_literals\":[-20,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":74,\"full_literals\":[-21,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":77,\"full_literals\":[-22,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":78,\"full_literals\":[-23,28]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-25,29],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-24,false,29],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-29,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-27,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-26,false,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-28,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-31,-32,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-30,-33,34],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":39,\"owners\":[8,34,42,45,47,56,59,61,65,67,72,74]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[13,18,54,55,58,60,63,64,66,67,77,78]}]}"
  "44 1 4 5 6 7 10 14 20 21 0 22 25 26 42 0\n45 2 3 9 11 13 15 16 18 22 23 0 12 26 43 0\n46 29 0 26 25 22 33 34 28 27 2 5 24 1 3 4 21 44 0\n47 30 0 46 35 0\n48 -33 0 47 41 40 0\n49 31 0 36 37 30 29 7 10 23 6 8 9 20 44 0\n50 -32 0 49 48 39 0\n51 -28 0 50 38 0\n52 -22 0 51 31 0\n53 -23 0 51 32 0\n54 -2 0 52 53 11 0\n55 -11 0 52 14 0\n56 -13 0 52 53 15 0\n57 -3 0 52 53 16 0\n58 -16 0 52 18 0\n59 -18 0 52 53 19 0\n60 -9 0 53 13 0\n61 -15 0 53 17 0\n62 0 60 57 54 55 56 61 58 59 52 53 45 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record023.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record023.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record023.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record023.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record023 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record023.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record023.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record023.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record023.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record023 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record023_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record023_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record023_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record023_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record023_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record023_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record023_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record023 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record023_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record023_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record023_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00009.record023
