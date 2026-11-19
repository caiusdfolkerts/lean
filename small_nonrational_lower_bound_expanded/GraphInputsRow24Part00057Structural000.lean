module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00057Data
public import GraphInputsRow24Part00057Frames
public import GraphInputsRow24Part00057Leaves
public import GraphInputsRow24Part00057Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00057.record013
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record013
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), (certNat% 7), (certNat% 8), (certNat% 9), 4508004116332544]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 11), 164381386399023104, (certNat% 12), 18691697672192]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 14), 56075629887488, (certNat% 15), (certNat% 16), 139586437120]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), (certNat% 18), (certNat% 19), (certNat% 20), 20266267042643968, 10737418240]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), 81064814767505408, (certNat% 19), (certNat% 20), 130841883705344]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), (certNat% 7), (certNat% 8), (certNat% 9), 36099191532945408]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c8 c0
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1152358336415399936, (certNat% 23), (certNat% 24), (certNat% 25), (certNat% 26), 10737418240]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), (certNat% 28), (certNat% 29), (certNat% 30), 1009228666971881472, (certNat% 11)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1152883971156082688, (certNat% 31), (certNat% 32), 6917529029788565504, (certNat% 33), (certNat% 20)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), 8070450532247928832, (certNat% 35), (certNat% 36), 85572790966550528, 1027242927505539072]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), (certNat% 38), (certNat% 35), (certNat% 39), 117163959055810560, 1027242927505539072]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [143974243892199424, 1008947191458299904, (certNat% 40), (certNat% 41), (certNat% 24), (certNat% 25)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [413304009256861696, (certNat% 32), 739012551353827328, (certNat% 42), (certNat% 26), (certNat% 25), 4402341478400]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c17 c14
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c18 c13
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c19 c12
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c20 c11
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c21 c10
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c22 c10
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c23 c9
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c24 c7
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c25 c6
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c26 c5
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c27 c2
  c28
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record013_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record013_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00057.record013

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00057.record015
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2e41f1d21eaa63999635876a398e8b86e4785e0fae1747891e6c5a96653959535475a358d1b61d4745d0f5c3a8ce364d5334c73a2d8b8ad2b1ac5b0ee8761e2729d1725c3783d0f23c4f8b11a318661582e07a294668531625194558342d0758330c6344c5342c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db4d26d24936da49349349249a492692492492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record015 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record015 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record015.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record015.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record015.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 69)]))
 (.leaf ([(facetIndex 85)])))
 (.branch 3
 (.leaf ([(facetIndex 87)]))
 (.leaf ([(facetIndex 64), (facetIndex 71)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 53), (facetIndex 72)]))
 (.leaf ([(facetIndex 82), (facetIndex 86)])))
 (.branch 7
 (.leaf ([(facetIndex 84), (facetIndex 88)]))
 (.branch 8
 (.leaf ([(facetIndex 47), (facetIndex 60), (facetIndex 70)]))
 (.leaf ([(facetIndex 78), (facetIndex 79)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "625160500880000043700000300070000004000007z2f;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0, 1]
def grouped3_0001 : List Nat := [0, 1, 2, 3]
def grouped3_0003 : List Nat := [2]
def grouped3_0004 : List Nat := [2, 3]
def grouped3_0005 : List Nat := [3]
def grouped3_0006 : List Nat := [4]
def grouped3_0007 : List Nat := [4, 5]
def grouped3_0008 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0009 : List Nat := [5]
def grouped3_0010 : List Nat := [6]
def grouped3_0011 : List Nat := [6, 7, 8]
def grouped3_0012 : List Nat := [7]
def grouped3_0013 : List Nat := [7, 8]
def grouped3_0014 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record015 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record015_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00057.record015" "{\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00057.record015" 37

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00057.record015" "{\"ridges\":[[12,385],[20,641],[39,385],[40,641],[46,385],[47,650],[51,385],[54,385],[60,396],[61,641],[64,404],[67,641],[68,641],[70,904],[71,464],[78,396],[79,650],[82,404],[84,674],[86,464],[88,736]],\"owners\":[[12,385,[60,64,70,71],[39,46,51,54]],[39,385,[70,71],[12,46,51,54,60,64]],[46,385,[64,71],[12,39,51,54,60,70]],[51,385,[60,70],[12,39,46,54,64,71]],[54,385,[60,64,70],[12,39,46,51,71]],[20,641,[47,53,70,72],[40,61,67,68]],[40,641,[70,72],[20,47,53,61,67,68]],[61,641,[53,72],[20,40,47,67,68,70]],[67,641,[47,70],[20,40,53,61,68,72]],[68,641,[47,53,70],[20,40,61,67,72]],[47,650,[79],[]],[79,650,[47],[]],[84,674,[53],[]],[60,396,[78],[]],[78,396,[60],[]],[64,404,[82],[]],[82,404,[64],[]],[70,904,[],[]],[71,464,[86],[]],[86,464,[71],[]],[88,736,[72],[]]],\"edges\":[[42,[12,39,46,51,54,60,64,70,71,78,82,86]],[43,[20,40,47,53,61,67,68,70,72,79,84,88]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00057.record015" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00057.record015\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-9,-6],[-10,-6],[-18,-6],[-1,10,12,15,16],[-3,15,16],[-5,12,16],[-7,10,15],[-9,10,12,15],[-2,6,8,15,17],[-4,15,17],[-11,8,17],[-13,6,15],[-14,6,8,15],[-6,19],[-19,6],[-21,8],[-10,18],[-18,10],[-12,20],[-20,12],[-15],[-16,22],[-22,16],[-23,17],[-24,12,16],[-12,24],[-16,24],[-8,25],[-17,25],[-20,26],[-22,26],[-6,27],[-10,27],[-28,18,19],[-18,28],[-19,28],[-24,29],[-29,30],[-25,31],[-25,-26,32],[-27,-28,33],[-33,34],[-34,35],[-31,-34,36],[-32,35],[-36,37],[-30,-35,37],[-37],[1,3,5,7,9,10,12,15,16,18,20,22],[2,4,6,8,11,13,14,15,17,19,21,23]],\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":54,\"b\":47},{\"tag\":\"incompatible\",\"a\":60,\"b\":47},{\"tag\":\"incompatible\",\"a\":78,\"b\":47},{\"tag\":\"mate\",\"ridge\":385,\"a\":12,\"owners\":[60,64,70,71]},{\"tag\":\"mate\",\"ridge\":385,\"a\":39,\"owners\":[70,71]},{\"tag\":\"mate\",\"ridge\":385,\"a\":46,\"owners\":[64,71]},{\"tag\":\"mate\",\"ridge\":385,\"a\":51,\"owners\":[60,70]},{\"tag\":\"mate\",\"ridge\":385,\"a\":54,\"owners\":[60,64,70]},{\"tag\":\"mate\",\"ridge\":641,\"a\":20,\"owners\":[47,53,70,72]},{\"tag\":\"mate\",\"ridge\":641,\"a\":40,\"owners\":[70,72]},{\"tag\":\"mate\",\"ridge\":641,\"a\":61,\"owners\":[53,72]},{\"tag\":\"mate\",\"ridge\":641,\"a\":67,\"owners\":[47,70]},{\"tag\":\"mate\",\"ridge\":641,\"a\":68,\"owners\":[47,53,70]},{\"tag\":\"mate\",\"ridge\":650,\"a\":47,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":650,\"a\":79,\"owners\":[47]},{\"tag\":\"mate\",\"ridge\":674,\"a\":84,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":396,\"a\":60,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":396,\"a\":78,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":404,\"a\":64,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":404,\"a\":82,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":904,\"a\":70,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":464,\"a\":71,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":464,\"a\":86,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":736,\"a\":88,\"owners\":[72]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[64,71],\"full_literals\":[-24,12,16]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":64,\"full_literals\":[-12,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":71,\"full_literals\":[-16,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":53,\"full_literals\":[-8,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":72,\"full_literals\":[-17,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":82,\"full_literals\":[-20,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":86,\"full_literals\":[-22,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":47,\"full_literals\":[-6,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":60,\"full_literals\":[-10,27]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[78,79],\"full_literals\":[-28,18,19]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":78,\"full_literals\":[-18,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":79,\"full_literals\":[-19,28]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-24,29],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-29,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-25,false,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-25,-26,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-27,-28,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-33,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-34,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-31,-34,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-32,false,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-36,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-30,-35,37],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":42,\"owners\":[12,39,46,51,54,60,64,70,71,78,82,86]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[20,40,47,53,61,67,68,70,72,79,84,88]}]}"
  "51 -36 0 48 46 0\n52 1 3 5 7 9 10 12 16 18 20 22 0 21 49 0\n53 2 4 6 8 11 13 14 17 19 21 23 0 21 50 0\n54 6 25 0 21 28 29 11 24 10 16 12 15 9 13 53 0\n55 -6 24 0 21 26 27 6 23 5 20 1 2 3 4 7 52 0\n56 -10 33 0 17 33 35 41 0\n57 24 0 51 21 26 27 20 5 23 6 55 54 39 44 42 56 4 7 8 18 52 0\n58 29 0 57 37 0\n59 30 0 58 38 0\n60 -35 0 59 48 47 0\n61 -34 0 60 43 0\n62 -32 0 60 45 0\n63 -33 0 61 42 0\n64 -10 0 63 56 0\n65 -18 0 64 18 0\n66 -28 0 63 65 41 34 32 15 0\n67 -19 0 66 36 0\n68 -6 0 67 14 0\n69 25 0 68 54 0\n70 -26 0 69 62 40 0\n71 -20 0 70 30 0\n72 -22 0 70 31 0\n73 -12 0 71 19 0\n74 -16 0 72 22 0\n75 0 74 73 57 25 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record015.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record015.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record015.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record015.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record015 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record015.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record015.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record015.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record015.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record015 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record015_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record015_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record015_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record015_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record015_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record015_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record015_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record015 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record015_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record015_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record015_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00057.record015

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00057.record016
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1f2e274b8a1eaa63999635876a398e8b86e4785e0fae1747891e6a53959535475a358d8b46d4745d0f783b0dc3a8e6338d9354cd31cf0ba2d8b4ac6b86c5b0ee8761e2729d1725c3783d0f23c4f8a91a318661582e07a29464c5194550b41da0d8330e2318d1314e0b42c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6d349b4924db6d349b492492492492492492492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record016 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record016 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record016.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record016.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record016.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 32), (facetIndex 36), (facetIndex 41), (facetIndex 42), (facetIndex 43), (facetIndex 61), (facetIndex 77)]))
 (.leaf ([(facetIndex 33), (facetIndex 38), (facetIndex 44), (facetIndex 45), (facetIndex 63), (facetIndex 79)])))
 (.branch 3
 (.leaf ([(facetIndex 30), (facetIndex 60), (facetIndex 62), (facetIndex 66), (facetIndex 67), (facetIndex 69)]))
 (.leaf ([(facetIndex 76), (facetIndex 78), (facetIndex 82), (facetIndex 83), (facetIndex 85)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 35), (facetIndex 50), (facetIndex 51), (facetIndex 52), (facetIndex 56)]))
 (.leaf ([(facetIndex 37), (facetIndex 53), (facetIndex 54), (facetIndex 55), (facetIndex 57)])))
 (.branch 7
 (.leaf ([(facetIndex 31), (facetIndex 46), (facetIndex 47), (facetIndex 48), (facetIndex 58)]))
 (.branch 8
 (.leaf ([(facetIndex 34), (facetIndex 49), (facetIndex 59), (facetIndex 75)]))
 (.leaf ([(facetIndex 39), (facetIndex 40)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "30330013037000002022001202765455544476661100088150471062z1e;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 71)]))
 (.leaf ([(facetIndex 87)])))
 (.branch 3
 (.leaf ([(facetIndex 91)]))
 (.leaf ([(facetIndex 68), (facetIndex 73)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 70), (facetIndex 74)]))
 (.leaf ([(facetIndex 84), (facetIndex 89)])))
 (.branch 7
 (.leaf ([(facetIndex 86), (facetIndex 90)]))
 (.branch 8
 (.leaf ([(facetIndex 64), (facetIndex 65), (facetIndex 72)]))
 (.leaf ([(facetIndex 80), (facetIndex 81), (facetIndex 88)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "2658160500880000043704030077z40;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2, 3]
def grouped2_0006 : List Nat := [4, 5]
def grouped2_0007 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0008 : List Nat := [6]
def grouped2_0009 : List Nat := [6, 7, 8]
def grouped2_0010 : List Nat := [7]
def grouped2_0011 : List Nat := [7, 8]
def grouped2_0012 : List Nat := [8]
def grouped3_0013 : List Nat := [0, 1]
def grouped3_0014 : List Nat := [0, 1, 2, 3]
def grouped3_0016 : List Nat := [2]
def grouped3_0017 : List Nat := [2, 3]
def grouped3_0018 : List Nat := [3]
def grouped3_0019 : List Nat := [4]
def grouped3_0020 : List Nat := [4, 5]
def grouped3_0021 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0022 : List Nat := [5]
def grouped3_0023 : List Nat := [6]
def grouped3_0024 : List Nat := [6, 7, 8]
def grouped3_0025 : List Nat := [7]
def grouped3_0026 : List Nat := [7, 8]
def grouped3_0027 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record016 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record016_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00057.record016" "{\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00057.record016" 59

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00057.record016" "{\"ridges\":[[14,386],[15,641],[39,385],[40,641],[46,385],[47,641],[52,386],[55,642],[56,386],[57,641],[58,385],[58,386],[58,641],[58,642],[64,396],[65,652],[68,404],[72,385],[72,641],[72,904],[73,464],[80,396],[81,652],[84,404],[86,676],[88,904],[89,464],[90,736]],\"owners\":[[39,385,[72,73],[14,46,52,56,58,64,68]],[46,385,[68,73],[14,39,52,56,58,64,72]],[58,385,[64,68,73],[14,39,46,52,56,72]],[72,385,[14,39,52,56,68,73],[46,58,64]],[14,386,[80,84,88,89],[39,46,52,56,58]],[52,386,[80,88],[14,39,46,56,58,84,89]],[56,386,[80,84,88],[14,39,46,52,58,89]],[58,386,[80,84,89],[14,39,46,52,56,88]],[15,641,[65,70,72,74],[40,47,55,57,58]],[40,641,[72,74],[15,47,55,57,58,65,70]],[47,641,[70,74],[15,40,55,57,58,65,72]],[57,641,[65,70,72],[15,40,47,55,58,74]],[58,641,[65,70,74],[15,40,47,55,57,72]],[72,641,[15,40,55,57,70,74],[47,58,65]],[55,642,[81,88],[15,40,47,57,58,86,90]],[58,642,[81,86,90],[15,40,47,55,57,88]],[64,396,[80],[]],[80,396,[64],[]],[65,652,[81],[]],[81,652,[65],[]],[68,404,[84],[]],[84,404,[68],[]],[86,676,[70],[]],[72,904,[88],[]],[88,904,[72],[]],[73,464,[89],[]],[89,464,[73],[]],[90,736,[74],[]]],\"edges\":[[42,[14,39,46,52,56,58,64,68,72,73,80,84,88,89]],[43,[15,40,47,55,57,58,65,70,72,74,81,86,88,90]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00057.record016" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00057.record016\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-6,-2],[-7,-1],[-7,-6],[-12,-4],[-12,-8],[-12,-9],[-13,-7],[-14,-6],[-14,-12],[-15,-7],[-16,-6],[-19,-3],[-20,-3],[-20,-5],[-20,-18],[-23,-3],[-23,-12],[-23,-17],[-26,-20],[-28,-19],[-6,23,24],[-10,21,24],[-17,19,21,24],[-23,1,6,13,15,21,24],[-1,27,29,31,32],[-13,27,31],[-15,27,29,31],[-17,27,29,32],[-2,20,22,23,25],[-7,23,25],[-11,22,25],[-16,20,22,23],[-17,20,22,25],[-23,2,7,14,16,22,25],[-14,28,31],[-17,28,30,33],[-19,27],[-27,19],[-20,28],[-28,20],[-21,29],[-29,21],[-30,22],[-23,31],[-31,23],[-24,32],[-32,24],[-33,25],[-34,4,5,8,9,18,26],[-35,3,10,11,12,17],[-36,6,7],[-37,34],[-38,37],[-39,36],[-40,35,39],[-41,39],[-42,40],[-43,41],[-44,38,43],[-44,42],[44],[-45,21,24],[-21,45],[-24,45],[-22,46],[-25,46],[-29,47],[-32,47],[-48,30,33],[-49,19,20,23],[-19,49],[-20,49],[-23,49],[-50,27,28,31],[-27,50],[-28,50],[-31,50],[-45,51],[-51,52],[-46,53],[-46,-47,54],[-55,49],[-49,-50,55],[-56,48,55],[-55,56],[-56,57],[-53,-56,58],[-54,57],[-58,59],[-52,-57,59],[-59],[1,6,10,13,15,17,19,21,23,24,27,29,31,32],[2,7,11,14,16,17,20,22,23,25,28,30,31,33]],\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":39,\"b\":15},{\"tag\":\"incompatible\",\"a\":40,\"b\":14},{\"tag\":\"incompatible\",\"a\":40,\"b\":39},{\"tag\":\"incompatible\",\"a\":48,\"b\":33},{\"tag\":\"incompatible\",\"a\":48,\"b\":44},{\"tag\":\"incompatible\",\"a\":48,\"b\":45},{\"tag\":\"incompatible\",\"a\":52,\"b\":40},{\"tag\":\"incompatible\",\"a\":55,\"b\":39},{\"tag\":\"incompatible\",\"a\":55,\"b\":48},{\"tag\":\"incompatible\",\"a\":56,\"b\":40},{\"tag\":\"incompatible\",\"a\":57,\"b\":39},{\"tag\":\"incompatible\",\"a\":64,\"b\":31},{\"tag\":\"incompatible\",\"a\":65,\"b\":31},{\"tag\":\"incompatible\",\"a\":65,\"b\":38},{\"tag\":\"incompatible\",\"a\":65,\"b\":63},{\"tag\":\"incompatible\",\"a\":72,\"b\":31},{\"tag\":\"incompatible\",\"a\":72,\"b\":48},{\"tag\":\"incompatible\",\"a\":72,\"b\":58},{\"tag\":\"incompatible\",\"a\":79,\"b\":65},{\"tag\":\"incompatible\",\"a\":81,\"b\":64},{\"tag\":\"mate\",\"ridge\":385,\"a\":39,\"owners\":[72,73]},{\"tag\":\"mate\",\"ridge\":385,\"a\":46,\"owners\":[68,73]},{\"tag\":\"mate\",\"ridge\":385,\"a\":58,\"owners\":[64,68,73]},{\"tag\":\"mate\",\"ridge\":385,\"a\":72,\"owners\":[14,39,52,56,68,73]},{\"tag\":\"mate\",\"ridge\":386,\"a\":14,\"owners\":[80,84,88,89]},{\"tag\":\"mate\",\"ridge\":386,\"a\":52,\"owners\":[80,88]},{\"tag\":\"mate\",\"ridge\":386,\"a\":56,\"owners\":[80,84,88]},{\"tag\":\"mate\",\"ridge\":386,\"a\":58,\"owners\":[80,84,89]},{\"tag\":\"mate\",\"ridge\":641,\"a\":15,\"owners\":[65,70,72,74]},{\"tag\":\"mate\",\"ridge\":641,\"a\":40,\"owners\":[72,74]},{\"tag\":\"mate\",\"ridge\":641,\"a\":47,\"owners\":[70,74]},{\"tag\":\"mate\",\"ridge\":641,\"a\":57,\"owners\":[65,70,72]},{\"tag\":\"mate\",\"ridge\":641,\"a\":58,\"owners\":[65,70,74]},{\"tag\":\"mate\",\"ridge\":641,\"a\":72,\"owners\":[15,40,55,57,70,74]},{\"tag\":\"mate\",\"ridge\":642,\"a\":55,\"owners\":[81,88]},{\"tag\":\"mate\",\"ridge\":642,\"a\":58,\"owners\":[81,86,90]},{\"tag\":\"mate\",\"ridge\":396,\"a\":64,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":396,\"a\":80,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":652,\"a\":65,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":652,\"a\":81,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":404,\"a\":68,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":404,\"a\":84,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":676,\"a\":86,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":904,\"a\":72,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":904,\"a\":88,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":464,\"a\":73,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":464,\"a\":89,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":736,\"a\":90,\"owners\":[74]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[33,38,44,45,63,79],\"full_literals\":[-34,4,5,8,9,18,26]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[31,46,47,48,58],\"full_literals\":[-35,3,10,11,12,17]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[39,40],\"full_literals\":[-36,6,7]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-37,false,34],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-38,37,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-39,false,36],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-40,35,39],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-41,false,39],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-42,false,40],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-43,false,41],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-44,38,43],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-44,false,42],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[68,73],\"full_literals\":[-45,21,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":68,\"full_literals\":[-21,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":73,\"full_literals\":[-24,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":70,\"full_literals\":[-22,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":74,\"full_literals\":[-25,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":84,\"full_literals\":[-29,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":89,\"full_literals\":[-32,47]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[86,90],\"full_literals\":[-48,30,33]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[64,65,72],\"full_literals\":[-49,19,20,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":64,\"full_literals\":[-19,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":65,\"full_literals\":[-20,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":72,\"full_literals\":[-23,49]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[80,81,88],\"full_literals\":[-50,27,28,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":80,\"full_literals\":[-27,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":81,\"full_literals\":[-28,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":88,\"full_literals\":[-31,50]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-45,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-51,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-46,-47,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-55,49,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-49,-50,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-56,48,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-55,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-56,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-53,-56,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-54,false,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-58,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-52,-57,59],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":42,\"owners\":[14,39,46,52,56,58,64,68,72,73,80,84,88,89]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[15,40,47,55,57,58,65,70,72,74,81,86,88,90]}]}"
  "94 42 0 61 60 0\n95 40 0 94 57 0\n96 -58 0 91 89 0\n97 7 -36 46 24 0 66 65 51 1 8 11 21 34 0\n98 -7 25 45 0 64 63 2 3 7 10 30 24 0\n99 -23 -35 11 10 0 16 17 18 50 0\n100 -3 23 -49 0 12 13 70 0\n101 20 14 17 23 7 25 22 0 45 48 43 31 29 40 32 93 0\n102 17 3 -34 -35 7 25 22 10 0 31 99 50 4 5 6 9 101 14 15 19 49 0\n103 -56 45 0 96 95 61 64 63 22 87 80 65 66 31 43 48 69 84 82 98 97 54 56 55 58 59 53 52 99 100 102 23 36 20 0\n104 -17 45 0 103 85 64 47 63 42 23 28 71 75 83 0\n105 27 23 45 0 45 64 21 104 47 63 42 22 25 37 26 27 92 0\n106 -27 55 0 38 75 71 83 0\n107 45 0 103 85 106 105 44 73 77 83 0\n108 51 0 107 78 0\n109 52 0 108 79 0\n110 -57 0 109 91 90 0\n111 -56 0 110 86 0\n112 -54 0 110 88 0\n113 -55 0 111 85 0\n114 -27 0 113 106 0\n115 -50 0 113 114 83 72 73 40 45 74 0\n116 -28 0 115 76 0\n117 -31 0 115 77 0\n118 -20 0 116 39 0\n119 -14 0 116 117 35 0\n120 -23 0 117 44 0\n121 46 17 0 119 118 120 65 66 30 101 0\n122 47 0 107 67 68 41 46 62 0\n123 -46 0 122 112 81 0\n124 -22 0 123 65 0\n125 -25 0 123 66 0\n126 17 0 123 121 0\n127 0 124 125 118 126 33 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record016.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record016.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record016.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record016.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record016 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record016.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record016.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record016.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record016.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record016 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record016_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record016_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record016_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record016_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record016_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record016_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record016_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record016 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record016_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record016_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record016_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00057.record016

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00057.record019
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ab0ec670dc1f07ae1876a398e33a2e1b91e1783eb85d1aa4e9664d91e785a94e5654d51d68d634cd8b4ad1b51d2745d0f783b0dc398d531ce8b62ccb8ad1b0ef07a1d8731d2719e1715c3783d0f23c4f1a85a899160b81e3246916685616254548d0b41d88c6344c5312c2b06e0741c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db69b6da4926da6924d36924924936d24da49249a492492249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record019 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record019 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record019.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record019.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record019.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 64), (facetIndex 71), (facetIndex 74)]))
 (.leaf ([(facetIndex 66), (facetIndex 73), (facetIndex 75)])))
 (.branch 3
 (.leaf ([(facetIndex 45), (facetIndex 89)]))
 (.leaf ([(facetIndex 46), (facetIndex 91)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 37), (facetIndex 63), (facetIndex 88), (facetIndex 90)]))
 (.leaf ([(facetIndex 81), (facetIndex 84)])))
 (.branch 7
 (.leaf ([(facetIndex 87)]))
 (.branch 8
 (.leaf ([(facetIndex 50), (facetIndex 51), (facetIndex 52), (facetIndex 82), (facetIndex 83)]))
 (.leaf ([(facetIndex 85)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "3424608577500000101000000100400000000007770003200000004z25;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0002 : List Nat := [0, 1, 2, 3]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [2, 3]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [4]
def grouped3_0009 : List Nat := [4, 5]
def grouped3_0010 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7, 8]
def grouped3_0014 : List Nat := [7]
def grouped3_0015 : List Nat := [7, 8]
def grouped3_0016 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record019 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record019_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00057.record019" "{\"atoms\":[{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00057.record019" 57

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00057.record019" "{\"ridges\":[[17,385],[17,388],[18,644],[21,200],[37,198],[38,385],[38,388],[39,641],[44,193],[44,200],[50,450],[51,706],[60,200],[61,385],[64,212],[65,385],[66,228],[68,641],[68,644],[70,200],[72,200],[74,464],[75,736],[81,198],[82,394],[83,650],[84,116],[88,212],[89,408],[90,228]],\"owners\":[[17,385,[45,50,52,71,74],[38,61,65,68]],[38,385,[71,74],[17,45,50,52,61,65,68]],[61,385,[50,52,74],[17,38,45,65,68,71]],[65,385,[45,50,52],[17,38,61,68,71,74]],[17,388,[82,85,89],[38,61,65,68]],[38,388,[89],[17,61,65,68,82,85]],[39,641,[73,75],[18,46,51,52,62,67,68]],[68,641,[46,51,73,75],[18,39,52,62,67]],[18,644,[83,85,91],[39,62,67,68]],[68,644,[83,91],[18,39,62,67,85]],[44,193,[64,66,74,75],[21,37,50,51,60,70,72]],[21,200,[81,88,90],[44,60,70,72]],[44,200,[88,90],[21,60,70,72,81]],[60,200,[],[21,44,70,72,81,88,90]],[70,200,[81,90],[21,44,60,72,88]],[72,200,[81,88],[21,44,60,70,90]],[37,198,[81],[]],[81,198,[37],[]],[82,394,[45],[]],[83,650,[46],[]],[50,450,[],[]],[51,706,[],[]],[84,116,[63,87],[]],[64,212,[88],[]],[88,212,[64],[]],[66,228,[90],[]],[90,228,[66],[]],[89,408,[71],[]],[74,464,[],[]],[75,736,[],[]]],\"edges\":[[39,[21,37,44,50,51,60,64,66,70,72,74,75,81,88,90]],[42,[17,38,45,50,52,61,65,68,71,74,82,85,89]],[43,[18,39,46,51,52,62,67,68,73,75,83,85,91]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00057.record019" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00057.record019\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-17,-14],[-19,-15],[-21,-17],[-21,-19],[-28,-5],[-28,-8],[-28,-9],[-28,-12],[-29,-28],[-32,-28],[-34,-18],[-34,-23],[-35,-34],[-36,-20],[-36,-25],[-37,-36],[-1,8,10,12,23,26],[-5,23,26],[-14,10,12,26],[-18,8,10,12],[-1,29,32,35],[-5,35],[-6,25,27],[-21,9,11,25,27],[-2,30,32,37],[-21,30,37],[-7,17,19,26,27],[-3,28,34,36],[-7,34,36],[-13],[-22,28,36],[-24,28,34],[-4,28],[-28,4],[-29,8],[-30,9],[-10],[-11],[-31,16,33],[-17,34],[-34,17],[-19,36],[-36,19],[-35,23],[-26],[-27],[-17,38],[-23,38],[-19,39],[-25,39],[-8,40],[-35,40],[-9,41],[-37,41],[-4,42],[-16,42],[-34,42],[-36,42],[-43,28,31],[-28,43],[-33,44],[-12,45],[-29,45],[-30,45],[-32,46],[-39,47],[-38,47],[-41,48],[-40,48],[-48,49],[-47,49],[-47,-48,50],[-43,51],[-42,51],[-42,-43,52],[-46,53],[-45,53],[-53,54],[-44,54],[-51,55],[-51,-54,56],[-52,56],[-49,-56,57],[-50,-55,57],[-57],[3,4,7,10,11,13,17,19,22,24,26,27,28,34,36],[1,5,8,10,12,14,18,21,23,26,29,32,35],[2,6,9,11,12,15,20,21,25,27,30,32,37]],\"atoms\":[{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":64,\"b\":61},{\"tag\":\"incompatible\",\"a\":66,\"b\":62},{\"tag\":\"incompatible\",\"a\":68,\"b\":64},{\"tag\":\"incompatible\",\"a\":68,\"b\":66},{\"tag\":\"incompatible\",\"a\":81,\"b\":38},{\"tag\":\"incompatible\",\"a\":81,\"b\":45},{\"tag\":\"incompatible\",\"a\":81,\"b\":46},{\"tag\":\"incompatible\",\"a\":81,\"b\":52},{\"tag\":\"incompatible\",\"a\":82,\"b\":81},{\"tag\":\"incompatible\",\"a\":85,\"b\":81},{\"tag\":\"incompatible\",\"a\":88,\"b\":65},{\"tag\":\"incompatible\",\"a\":88,\"b\":71},{\"tag\":\"incompatible\",\"a\":89,\"b\":88},{\"tag\":\"incompatible\",\"a\":90,\"b\":67},{\"tag\":\"incompatible\",\"a\":90,\"b\":73},{\"tag\":\"incompatible\",\"a\":91,\"b\":90},{\"tag\":\"mate\",\"ridge\":385,\"a\":17,\"owners\":[45,50,52,71,74]},{\"tag\":\"mate\",\"ridge\":385,\"a\":38,\"owners\":[71,74]},{\"tag\":\"mate\",\"ridge\":385,\"a\":61,\"owners\":[50,52,74]},{\"tag\":\"mate\",\"ridge\":385,\"a\":65,\"owners\":[45,50,52]},{\"tag\":\"mate\",\"ridge\":388,\"a\":17,\"owners\":[82,85,89]},{\"tag\":\"mate\",\"ridge\":388,\"a\":38,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":641,\"a\":39,\"owners\":[73,75]},{\"tag\":\"mate\",\"ridge\":641,\"a\":68,\"owners\":[46,51,73,75]},{\"tag\":\"mate\",\"ridge\":644,\"a\":18,\"owners\":[83,85,91]},{\"tag\":\"mate\",\"ridge\":644,\"a\":68,\"owners\":[83,91]},{\"tag\":\"mate\",\"ridge\":193,\"a\":44,\"owners\":[64,66,74,75]},{\"tag\":\"mate\",\"ridge\":200,\"a\":21,\"owners\":[81,88,90]},{\"tag\":\"mate\",\"ridge\":200,\"a\":44,\"owners\":[88,90]},{\"tag\":\"mate\",\"ridge\":200,\"a\":60,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":200,\"a\":70,\"owners\":[81,90]},{\"tag\":\"mate\",\"ridge\":200,\"a\":72,\"owners\":[81,88]},{\"tag\":\"mate\",\"ridge\":198,\"a\":37,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":198,\"a\":81,\"owners\":[37]},{\"tag\":\"mate\",\"ridge\":394,\"a\":82,\"owners\":[45]},{\"tag\":\"mate\",\"ridge\":650,\"a\":83,\"owners\":[46]},{\"tag\":\"mate\",\"ridge\":450,\"a\":50,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":706,\"a\":51,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":116,\"a\":84,\"owners\":[63,87]},{\"tag\":\"mate\",\"ridge\":212,\"a\":64,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":212,\"a\":88,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":228,\"a\":66,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":228,\"a\":90,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":408,\"a\":89,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":464,\"a\":74,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":736,\"a\":75,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":64,\"full_literals\":[-17,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":71,\"full_literals\":[-23,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":66,\"full_literals\":[-19,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":73,\"full_literals\":[-25,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":45,\"full_literals\":[-8,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":89,\"full_literals\":[-35,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":46,\"full_literals\":[-9,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":91,\"full_literals\":[-37,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":37,\"full_literals\":[-4,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":63,\"full_literals\":[-16,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":88,\"full_literals\":[-34,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":90,\"full_literals\":[-36,42]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[81,84],\"full_literals\":[-43,28,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":81,\"full_literals\":[-28,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":87,\"full_literals\":[-33,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":52,\"full_literals\":[-12,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":82,\"full_literals\":[-29,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":83,\"full_literals\":[-30,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":85,\"full_literals\":[-32,46]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-39,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-48,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-47,false,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-47,-48,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-42,-43,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-46,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-45,false,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-53,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-51,false,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-51,-54,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-52,false,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-49,-56,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-50,-55,57],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":39,\"owners\":[21,37,44,50,51,60,64,66,70,72,74,75,81,88,90]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[17,38,45,50,52,61,65,68,71,74,82,85,89]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[18,39,46,51,52,62,67,68,73,75,83,85,91]}]}"
  "89 3 4 7 17 19 22 24 28 34 36 0 37 38 30 45 46 86 0\n90 1 5 8 12 14 18 21 23 29 32 35 0 37 45 87 0\n91 2 6 9 12 15 20 21 25 30 32 37 0 38 46 88 0\n92 28 47 0 45 46 67 47 41 66 49 27 43 33 31 28 32 89 0\n93 49 0 45 37 70 71 68 69 67 53 54 51 52 48 36 26 35 22 92 8 10 19 20 17 90 0\n94 -56 0 93 85 83 0\n95 -52 0 94 82 0\n96 47 0 46 38 45 37 66 67 92 50 48 5 6 7 8 9 10 24 44 19 20 17 90 0\n97 -43 0 95 94 73 75 81 55 56 79 34 61 59 39 0\n98 -28 0 97 60 0\n99 -4 0 98 33 0\n100 34 36 0 98 99 31 42 29 40 28 32 89 0\n101 -34 0 45 94 85 96 11 12 13 41 57 18 1 3 74 80 81 84 78 72 76 77 69 65 62 63 51 21 90 0\n102 36 0 101 100 0\n103 -20 0 102 14 0\n104 -25 0 102 15 0\n105 -37 0 102 16 0\n106 19 0 102 43 0\n107 42 0 102 58 0\n108 -6 0 104 46 23 0\n109 -15 0 106 2 0\n110 -21 0 106 4 0\n111 51 0 107 74 0\n112 55 0 111 80 0\n113 -54 0 111 94 81 0\n114 -50 0 112 85 84 0\n115 -53 0 113 78 0\n116 -48 0 114 96 72 0\n117 -46 0 115 76 0\n118 -45 0 115 77 0\n119 -41 0 116 68 0\n120 -32 0 117 65 0\n121 -12 0 118 62 0\n122 -30 0 118 64 0\n123 -9 0 119 53 0\n124 -2 0 120 122 105 25 0\n125 0 120 124 108 110 123 109 121 104 122 103 105 91 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record019.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record019.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record019.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record019.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record019 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record019.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record019.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record019.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record019.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record019 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record019_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record019_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record019_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record019_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record019_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record019_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record019_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record019 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record019_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record019_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record019_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00057.record019

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00057.record020
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1f2e2e2a9a6687a71996358768b92e1b91e1783eb8789a65991e5c5654d51d62d4b46d4745d0f783b0dc3a8e6338e9364c73c2e8b62d2b1ae1b46c9b16c3b61d4731e2749d1725c3783c4f34a2a198564382e078d18a4651550d0b41da0d8330e2318c9314e0b42c2b06d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6d249249b6db692492492492492492492492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record020 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record020 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record020.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record020.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record020.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 33), (facetIndex 37), (facetIndex 39), (facetIndex 66), (facetIndex 81)]))
 (.leaf ([(facetIndex 59), (facetIndex 61), (facetIndex 62), (facetIndex 63), (facetIndex 64)])))
 (.branch 3
 (.leaf ([(facetIndex 74), (facetIndex 76), (facetIndex 77), (facetIndex 78), (facetIndex 79)]))
 (.leaf ([(facetIndex 35), (facetIndex 36), (facetIndex 45), (facetIndex 46), (facetIndex 54)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 30), (facetIndex 32), (facetIndex 38), (facetIndex 50), (facetIndex 65), (facetIndex 80)]))
 (.leaf ([(facetIndex 51), (facetIndex 52), (facetIndex 53), (facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 58)])))
 (.branch 7
 (.leaf ([(facetIndex 31), (facetIndex 40), (facetIndex 42), (facetIndex 43), (facetIndex 44), (facetIndex 47), (facetIndex 48), (facetIndex 49)]))
 (.leaf ([(facetIndex 34), (facetIndex 41), (facetIndex 60), (facetIndex 75)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "4492e8000002124f36daedb36cdedbe1037c4dz17;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 69)]))
 (.leaf ([(facetIndex 73)])))
 (.branch 3
 (.leaf ([(facetIndex 84)]))
 (.leaf ([(facetIndex 88)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 89)]))
 (.leaf ([(facetIndex 67), (facetIndex 68)])))
 (.branch 7
 (.leaf ([(facetIndex 82), (facetIndex 83)]))
 (.branch 8
 (.leaf ([(facetIndex 70), (facetIndex 71), (facetIndex 72)]))
 (.leaf ([(facetIndex 85), (facetIndex 86), (facetIndex 87)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "43888266000000001777055z43;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4]
def grouped2_0003 : List Nat := [4, 5]
def grouped2_0004 : List Nat := [4, 5, 6, 7]
def grouped2_0005 : List Nat := [5]
def grouped2_0006 : List Nat := [6, 7]
def grouped3_0007 : List Nat := [0]
def grouped3_0008 : List Nat := [0, 1]
def grouped3_0009 : List Nat := [0, 1, 2, 3]
def grouped3_0011 : List Nat := [1]
def grouped3_0012 : List Nat := [2]
def grouped3_0013 : List Nat := [2, 3]
def grouped3_0014 : List Nat := [3]
def grouped3_0015 : List Nat := [4]
def grouped3_0016 : List Nat := [4, 5]
def grouped3_0017 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0018 : List Nat := [5]
def grouped3_0019 : List Nat := [6]
def grouped3_0020 : List Nat := [6, 7, 8]
def grouped3_0021 : List Nat := [7]
def grouped3_0022 : List Nat := [7, 8]
def grouped3_0023 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record020 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record020_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00057.record020" "{\"atoms\":[{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00057.record020" 57

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00057.record020" "{\"ridges\":[[13,131],[14,131],[14,385],[15,131],[15,641],[15,642],[22,193],[29,194],[39,131],[39,385],[47,385],[48,642],[51,385],[52,642],[53,131],[55,131],[55,641],[55,642],[56,385],[57,641],[58,385],[58,641],[66,193],[67,404],[68,452],[70,385],[70,408],[71,641],[71,664],[72,385],[72,641],[72,904],[81,194],[82,404],[83,452],[85,386],[85,408],[86,642],[86,664],[87,386],[87,642],[87,904]],\"owners\":[[22,193,[13,37,53,56,57,68,73],[66]],[66,193,[13,53,56,57,73],[22,37,68]],[29,194,[13,37,53,56,57,83,88],[81]],[81,194,[13,53,56,57,88],[29,37,83]],[14,385,[67,68,70,72],[39,47,51,56,58]],[39,385,[70,72],[14,47,51,56,58,67,68]],[47,385,[67,68],[14,39,51,56,58,70,72]],[51,385,[68,72],[14,39,47,56,58,67,70]],[56,385,[67,70,72],[14,39,47,51,58,68]],[58,385,[67,68,70],[14,39,47,51,56,72]],[70,385,[14,39,56,58,68],[47,51,67,72]],[72,385,[14,39,51,56,67,68],[47,58,70]],[85,386,[14,39,56,58,83],[47,51,82,87]],[87,386,[14,39,51,56,82,83],[47,58,85]],[15,641,[71,72,73],[48,52,55,57,58]],[55,641,[71,72],[15,48,52,57,58,73]],[57,641,[71,72],[15,48,52,55,58,73]],[58,641,[71,73],[15,48,52,55,57,72]],[71,641,[15,55,57,58,73],[48,52,72]],[72,641,[15,52,55,57,73],[48,58,71]],[15,642,[86,87,88],[48,52,55,57,58]],[48,642,[88],[15,52,55,57,58,86,87]],[52,642,[87,88],[15,48,55,57,58,86]],[55,642,[86,87],[15,48,52,57,58,88]],[86,642,[15,55,57,58,88],[48,52,87]],[87,642,[15,52,55,57,88],[48,58,86]],[67,404,[82],[]],[82,404,[67],[]],[68,452,[83],[]],[83,452,[68],[]],[70,408,[85],[]],[85,408,[70],[]],[71,664,[86],[]],[86,664,[71],[]],[72,904,[87],[]],[87,904,[72],[]]],\"edges\":[[39,[13,22,29,37,53,56,57,66,68,73,81,83,88]],[42,[14,39,47,51,56,58,67,68,70,72,82,83,85,87]],[43,[15,48,52,55,57,58,71,72,73,86,87,88]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00057.record020" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00057.record020\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-8,-6],[-8,-7],[-9,-8],[-13,-8],[-14,-1],[-14,-8],[-15,-1],[-15,-8],[-16,-1],[-16,-8],[-16,-14],[-16,-15],[-17,-14],[-17,-16],[-18,-3],[-18,-15],[-18,-17],[-19,-1],[-19,-2],[-19,-10],[-19,-14],[-19,-17],[-19,-18],[-20,-1],[-20,-8],[-20,-16],[-20,-17],[-20,-18],[-20,-19],[-21,-8],[-29,-8],[-34,-25],[-34,-33],[-1,-2,-17],[-1,-10,-17],[-2,-3,-16],[-3,-10,-16],[-4,1,8,16,18,19,24,28],[-22,1,16,18,19,28],[-5,1,8,16,18,19,32,36],[-30,1,16,18,19,36],[-2,23,24,25,27],[-10,25,27],[-11,23,24],[-14,24,27],[-18,23,25,27],[-20,23,24,25],[-25,2,10,18,20,24],[-27,2,10,14,18,23,24],[-33,2,10,18,20,32],[-35,2,10,14,18,31,32],[-3,26,27,28],[-17,26,27],[-19,26,27],[-20,26,28],[-26,3,17,19,20,28],[-27,3,15,17,19,28],[-3,34,35,36],[-12,36],[-15,35,36],[-17,34,35],[-34,3,17,19,20,36],[-35,3,15,17,19,36],[-23,31],[-31,23],[-24,32],[-32,24],[-25,33],[-33,25],[-26,34],[-34,26],[-27,35],[-35,27],[-37,6,7,9,13,21,29],[-38,14,15,16,17,18,19,20],[-39,37],[-39,38],[-40,39],[-41,40],[41],[-28,42],[-36,43],[-44,23,24],[-23,44],[-24,44],[-31,45],[-32,45],[-46,25,26,27],[-25,46],[-26,46],[-27,46],[-33,47],[-34,47],[-35,47],[-42,48],[-43,49],[-49,50],[-48,50],[-44,51],[-46,-47,52],[-52,54],[-45,53],[-54,55],[-51,-53,55],[-51,-54,56],[-56,57],[-50,-55,57],[-57],[1,4,5,8,16,18,19,22,24,28,30,32,36],[2,10,11,14,18,20,23,24,25,27,31,32,33,35],[3,12,15,17,19,20,26,27,28,34,35,36]],\"atoms\":[{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":37,\"b\":30},{\"tag\":\"incompatible\",\"a\":37,\"b\":32},{\"tag\":\"incompatible\",\"a\":38,\"b\":37},{\"tag\":\"incompatible\",\"a\":50,\"b\":37},{\"tag\":\"incompatible\",\"a\":51,\"b\":13},{\"tag\":\"incompatible\",\"a\":51,\"b\":37},{\"tag\":\"incompatible\",\"a\":52,\"b\":13},{\"tag\":\"incompatible\",\"a\":52,\"b\":37},{\"tag\":\"incompatible\",\"a\":53,\"b\":13},{\"tag\":\"incompatible\",\"a\":53,\"b\":37},{\"tag\":\"incompatible\",\"a\":53,\"b\":51},{\"tag\":\"incompatible\",\"a\":53,\"b\":52},{\"tag\":\"incompatible\",\"a\":55,\"b\":51},{\"tag\":\"incompatible\",\"a\":55,\"b\":53},{\"tag\":\"incompatible\",\"a\":56,\"b\":15},{\"tag\":\"incompatible\",\"a\":56,\"b\":52},{\"tag\":\"incompatible\",\"a\":56,\"b\":55},{\"tag\":\"incompatible\",\"a\":57,\"b\":13},{\"tag\":\"incompatible\",\"a\":57,\"b\":14},{\"tag\":\"incompatible\",\"a\":57,\"b\":39},{\"tag\":\"incompatible\",\"a\":57,\"b\":51},{\"tag\":\"incompatible\",\"a\":57,\"b\":55},{\"tag\":\"incompatible\",\"a\":57,\"b\":56},{\"tag\":\"incompatible\",\"a\":58,\"b\":13},{\"tag\":\"incompatible\",\"a\":58,\"b\":37},{\"tag\":\"incompatible\",\"a\":58,\"b\":53},{\"tag\":\"incompatible\",\"a\":58,\"b\":55},{\"tag\":\"incompatible\",\"a\":58,\"b\":56},{\"tag\":\"incompatible\",\"a\":58,\"b\":57},{\"tag\":\"incompatible\",\"a\":65,\"b\":37},{\"tag\":\"incompatible\",\"a\":80,\"b\":37},{\"tag\":\"incompatible\",\"a\":86,\"b\":70},{\"tag\":\"incompatible\",\"a\":86,\"b\":85},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[13,14,55]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[13,39,55]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[14,15,53]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[15,39,53]},{\"tag\":\"mate\",\"ridge\":193,\"a\":22,\"owners\":[13,37,53,56,57,68,73]},{\"tag\":\"mate\",\"ridge\":193,\"a\":66,\"owners\":[13,53,56,57,73]},{\"tag\":\"mate\",\"ridge\":194,\"a\":29,\"owners\":[13,37,53,56,57,83,88]},{\"tag\":\"mate\",\"ridge\":194,\"a\":81,\"owners\":[13,53,56,57,88]},{\"tag\":\"mate\",\"ridge\":385,\"a\":14,\"owners\":[67,68,70,72]},{\"tag\":\"mate\",\"ridge\":385,\"a\":39,\"owners\":[70,72]},{\"tag\":\"mate\",\"ridge\":385,\"a\":47,\"owners\":[67,68]},{\"tag\":\"mate\",\"ridge\":385,\"a\":51,\"owners\":[68,72]},{\"tag\":\"mate\",\"ridge\":385,\"a\":56,\"owners\":[67,70,72]},{\"tag\":\"mate\",\"ridge\":385,\"a\":58,\"owners\":[67,68,70]},{\"tag\":\"mate\",\"ridge\":385,\"a\":70,\"owners\":[14,39,56,58,68]},{\"tag\":\"mate\",\"ridge\":385,\"a\":72,\"owners\":[14,39,51,56,67,68]},{\"tag\":\"mate\",\"ridge\":386,\"a\":85,\"owners\":[14,39,56,58,83]},{\"tag\":\"mate\",\"ridge\":386,\"a\":87,\"owners\":[14,39,51,56,82,83]},{\"tag\":\"mate\",\"ridge\":641,\"a\":15,\"owners\":[71,72,73]},{\"tag\":\"mate\",\"ridge\":641,\"a\":55,\"owners\":[71,72]},{\"tag\":\"mate\",\"ridge\":641,\"a\":57,\"owners\":[71,72]},{\"tag\":\"mate\",\"ridge\":641,\"a\":58,\"owners\":[71,73]},{\"tag\":\"mate\",\"ridge\":641,\"a\":71,\"owners\":[15,55,57,58,73]},{\"tag\":\"mate\",\"ridge\":641,\"a\":72,\"owners\":[15,52,55,57,73]},{\"tag\":\"mate\",\"ridge\":642,\"a\":15,\"owners\":[86,87,88]},{\"tag\":\"mate\",\"ridge\":642,\"a\":48,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":642,\"a\":52,\"owners\":[87,88]},{\"tag\":\"mate\",\"ridge\":642,\"a\":55,\"owners\":[86,87]},{\"tag\":\"mate\",\"ridge\":642,\"a\":86,\"owners\":[15,55,57,58,88]},{\"tag\":\"mate\",\"ridge\":642,\"a\":87,\"owners\":[15,52,55,57,88]},{\"tag\":\"mate\",\"ridge\":404,\"a\":67,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":404,\"a\":82,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":452,\"a\":68,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":452,\"a\":83,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":408,\"a\":70,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":408,\"a\":85,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":664,\"a\":71,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":664,\"a\":86,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":904,\"a\":72,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":904,\"a\":87,\"owners\":[72]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[30,32,38,50,65,80],\"full_literals\":[-37,6,7,9,13,21,29]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[51,52,53,55,56,57,58],\"full_literals\":[-38,14,15,16,17,18,19,20]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-39,37,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-39,false,38],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-40,39,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-41,false,40],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":73,\"full_literals\":[-28,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":88,\"full_literals\":[-36,43]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[67,68],\"full_literals\":[-44,23,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":67,\"full_literals\":[-23,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":68,\"full_literals\":[-24,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":82,\"full_literals\":[-31,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":83,\"full_literals\":[-32,45]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[70,71,72],\"full_literals\":[-46,25,26,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":70,\"full_literals\":[-25,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":71,\"full_literals\":[-26,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":72,\"full_literals\":[-27,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":85,\"full_literals\":[-33,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":86,\"full_literals\":[-34,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":87,\"full_literals\":[-35,47]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-42,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-49,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-48,false,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-44,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-46,-47,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-52,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-45,false,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-54,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-51,-53,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-51,-54,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-56,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-50,-55,57],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":39,\"owners\":[13,22,29,37,53,56,57,66,68,73,81,83,88]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[14,39,47,51,56,58,67,68,70,72,82,83,85,87]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[15,48,52,55,57,58,71,72,73,86,87,88]}]}"
  "112 40 0 80 79 0\n113 39 0 112 78 0\n114 37 0 113 76 0\n115 38 0 113 77 0\n116 -56 0 108 106 0\n117 -1 18 17 0 115 5 7 9 18 24 75 0\n118 16 19 1 18 8 24 50 0 67 98 95 81 97 96 82 40 39 41 38 109 0\n119 34 35 20 19 15 17 50 0 72 97 96 82 59 98 95 81 58 70 111 0\n120 35 20 14 19 15 18 17 44 50 0 85 67 84 65 44 72 119 32 33 43 42 110 0\n121 -35 -16 19 15 18 17 44 36 0 11 85 84 63 73 36 37 49 0\n122 19 15 18 8 17 44 50 0 117 85 97 96 82 118 11 121 26 120 0\n123 -19 18 44 0 85 67 84 65 44 19 20 21 29 48 50 49 51 110 0\n124 18 8 17 44 50 0 85 117 123 118 122 12 0\n125 -18 17 50 0 97 96 82 59 98 95 81 15 16 23 28 56 62 57 63 111 0\n126 17 44 50 0 115 125 123 124 6 8 10 25 75 0\n127 -8 0 114 1 2 3 4 30 31 74 0\n128 44 50 0 127 84 85 44 65 67 126 13 14 17 22 27 118 34 35 48 50 49 51 110 0\n129 35 -17 52 0 72 61 53 93 90 100 0\n130 -35 52 0 73 94 91 100 0\n131 26 50 0 116 128 99 105 101 130 129 72 97 96 82 60 59 98 95 81 52 54 55 71 111 0\n132 50 0 116 128 99 105 101 131 70 90 93 100 0\n133 -55 0 132 108 107 0\n134 -54 0 133 103 0\n135 -52 0 134 101 0\n136 -35 0 135 130 0\n137 -27 0 136 72 0\n138 -46 0 135 137 100 92 93 68 70 88 0\n139 -25 0 138 89 0\n140 -10 0 139 137 43 0\n141 -33 0 139 69 0\n142 44 18 20 0 136 137 141 140 139 84 85 44 65 67 42 45 110 0\n143 -44 0 133 99 104 102 86 87 64 66 83 0\n144 -23 0 143 84 0\n145 -24 0 143 85 0\n146 -18 0 144 139 137 46 0\n147 -20 0 144 145 139 47 0\n148 0 146 147 143 142 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record020.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record020.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record020.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record020.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record020 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record020.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record020.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record020.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record020.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record020 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record020_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record020_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record020_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record020_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record020_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record020_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record020_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record020 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record020_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record020_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record020_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00057.record020
