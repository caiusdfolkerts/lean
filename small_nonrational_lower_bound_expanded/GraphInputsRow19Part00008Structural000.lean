module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow19Part00008Data
public import GraphInputsRow19Part00008Frames
public import GraphInputsRow19Part00008Leaves
public import GraphInputsRow19Part00008Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00008.record084
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record084
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 2611340115968, 1152956688978935808, 571746314878976, 9223653511831486464]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 3), 9223372036854775808, (certNat% 4), (certNat% 5)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), 9223372243013206016, 571746319073280, 2474974904320, (certNat% 7)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), 79164874948608, 2680126701568, 844425198567424, 9223372036871553024]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c6 c7
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c6 c8
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c6 c9
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), 2474974904320, (certNat% 10), 8796097216512]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), 79164874948608, (certNat% 12), 2473901162496, 549890031616]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), 87960963776512, 571746319073280, 10376293541545508864, 893487415296, 2345589014528]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c17 c4
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c18 c3
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c19 c0
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record084_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record084_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record084_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record084_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record084_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record084_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record084_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record084_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record084_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00008.record084

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00008.record055
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "d88ea969a6c58762b86e2785ed84e9965a5c54752b46d2745dd0f2368e6358ce3c4c7392ccb2ac6b86c9bc1d8719e1745c9715c3743c4f0be52169262988e07a51165252948d0770390d2328c6384c5322c4b06d0721c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6d26d349b49b4d2492492492492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record055 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record055 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record055.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record055.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record055.data.quota

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
def grouped3_0015 : List Nat := [0, 1, 2, 3]
def grouped3_0017 : List Nat := [1]
def grouped3_0018 : List Nat := [2]
def grouped3_0019 : List Nat := [2, 3]
def grouped3_0020 : List Nat := [3]
def grouped3_0021 : List Nat := [4]
def grouped3_0022 : List Nat := [4, 5]
def grouped3_0023 : List Nat := [4, 5, 6, 7]
def grouped3_0024 : List Nat := [5]
def grouped3_0025 : List Nat := [6]
def grouped3_0026 : List Nat := [6, 7]
def grouped3_0027 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record055 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record055_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00008.record055" "{\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":4,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":4,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00008.record055" 54

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00008.record055" "{\"ridges\":[[14,770],[37,770],[45,770],[47,97],[50,770],[51,770],[56,116],[57,788],[60,232],[61,864],[64,108]],\"owners\":[[47,97,[54,56,60],[10,35,40,44,46,48,61]],[14,770,[67,71],[37,45,50,51]],[37,770,[71],[14,45,50,51,67]],[45,770,[71],[14,37,50,51,67]],[50,770,[67],[14,37,45,51,71]],[51,770,[67],[14,37,45,50,71]],[64,108,[54],[]],[56,116,[66],[]],[57,788,[67],[]],[60,232,[70],[]],[61,864,[71],[]]],\"edges\":[[44,[14,37,45,50,51,57,61,67,71]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00008.record055" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00008.record055\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-11,-10],[-12,-11],[-13,-11],[-15,-14],[-18,-2],[-18,-3],[-18,-4],[-18,-8],[-20,-12],[-20,-13],[-21,-15],[-24,-14],[-24,-21],[-25,-2],[-25,-3],[-26,-5],[-26,-6],[-26,-7],[-26,-9],[-26,-16],[-26,-23],[-27,-10],[-27,-12],[-27,-13],[-10,15,17,19],[-1,25,27],[-4,27],[-8,27],[-12,25],[-13,25],[-22,15],[-17,24],[-18,25],[-19,26],[-20,27],[-28,14,21],[-29,5,6,16,23],[-30,2,3,4,8],[-31,7,9,11],[-32,10,12,13],[-33,28],[-34,33],[-35,29],[-35,30],[-36,31],[-36,32],[-37,35,36],[-38,35],[-38,36],[-39,34,38],[-39,37],[39],[-40,18],[-41,20],[-42,25],[-25,42],[-43,27],[-27,43],[-44,15,17],[-45,19,22],[-46,24],[-47,26],[-48,40],[-48,41],[-49,42,43],[-43,49],[-42,49],[-50,48],[-51,44,45],[-52,46,47],[-53,51,52],[-54,50,53],[54],[1,4,8,12,13,18,20,25,27]],\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":48,\"b\":47},{\"tag\":\"incompatible\",\"a\":50,\"b\":48},{\"tag\":\"incompatible\",\"a\":51,\"b\":48},{\"tag\":\"incompatible\",\"a\":54,\"b\":52},{\"tag\":\"incompatible\",\"a\":57,\"b\":33},{\"tag\":\"incompatible\",\"a\":57,\"b\":34},{\"tag\":\"incompatible\",\"a\":57,\"b\":37},{\"tag\":\"incompatible\",\"a\":57,\"b\":45},{\"tag\":\"incompatible\",\"a\":61,\"b\":50},{\"tag\":\"incompatible\",\"a\":61,\"b\":51},{\"tag\":\"incompatible\",\"a\":62,\"b\":54},{\"tag\":\"incompatible\",\"a\":66,\"b\":52},{\"tag\":\"incompatible\",\"a\":66,\"b\":62},{\"tag\":\"incompatible\",\"a\":67,\"b\":33},{\"tag\":\"incompatible\",\"a\":67,\"b\":34},{\"tag\":\"incompatible\",\"a\":70,\"b\":40},{\"tag\":\"incompatible\",\"a\":70,\"b\":41},{\"tag\":\"incompatible\",\"a\":70,\"b\":42},{\"tag\":\"incompatible\",\"a\":70,\"b\":46},{\"tag\":\"incompatible\",\"a\":70,\"b\":55},{\"tag\":\"incompatible\",\"a\":70,\"b\":65},{\"tag\":\"incompatible\",\"a\":71,\"b\":47},{\"tag\":\"incompatible\",\"a\":71,\"b\":50},{\"tag\":\"incompatible\",\"a\":71,\"b\":51},{\"tag\":\"mate\",\"ridge\":97,\"a\":47,\"owners\":[54,56,60]},{\"tag\":\"mate\",\"ridge\":770,\"a\":14,\"owners\":[67,71]},{\"tag\":\"mate\",\"ridge\":770,\"a\":37,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":770,\"a\":45,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":770,\"a\":50,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":770,\"a\":51,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":108,\"a\":64,\"owners\":[54]},{\"tag\":\"mate\",\"ridge\":116,\"a\":56,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":788,\"a\":57,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":232,\"a\":60,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":864,\"a\":61,\"owners\":[71]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[52,62],\"full_literals\":[-28,14,21]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[40,41,55,65],\"full_literals\":[-29,5,6,16,23]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[33,34,37,45],\"full_literals\":[-30,2,3,4,8]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[42,46,48],\"full_literals\":[-31,7,9,11]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[47,50,51],\"full_literals\":[-32,10,12,13]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-33,false,28],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-34,false,33],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-35,29,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-35,false,30],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-36,31,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-36,false,32],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-37,35,36],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-38,35,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-38,false,36],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-39,34,38],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-39,false,37],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[57],\"full_literals\":[-40,18]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[61],\"full_literals\":[-41,20]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[67],\"full_literals\":[-42,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":67,\"full_literals\":[-25,42]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[71],\"full_literals\":[-43,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":71,\"full_literals\":[-27,43]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[54,56],\"full_literals\":[-44,15,17]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[60,64],\"full_literals\":[-45,19,22]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[66],\"full_literals\":[-46,24]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[70],\"full_literals\":[-47,26]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-48,40,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-48,false,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-49,42,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-50,48,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-51,44,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-52,46,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-53,51,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-54,50,53],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":4,\"grouped\":true},{\"tag\":\"edge\",\"edge\":44,\"owners\":[14,37,45,50,51,57,61,67,71]}]}"
  "75 37 0 52 51 0\n76 49 0 66 67 58 56 27 28 35 26 29 30 33 74 0\n77 -26 0 75 16 17 18 19 20 21 37 43 47 45 46 39 1 2 3 40 0\n78 -19 0 77 34 0\n79 -47 0 77 62 0\n80 43 -30 0 76 58 65 27 28 55 14 15 38 0\n81 -38 0 48 49 44 46 80 57 22 23 24 40 0\n82 34 0 81 52 50 0\n83 33 0 82 42 0\n84 28 0 83 41 0\n85 -24 0 84 12 13 36 0\n86 -17 0 85 32 0\n87 -46 0 85 61 0\n88 -52 0 87 79 70 0\n89 -15 0 84 4 11 36 0\n90 -10 0 86 89 78 25 0\n91 -22 0 89 31 0\n92 -44 0 89 86 59 0\n93 -45 0 91 78 60 0\n94 -51 0 93 92 69 0\n95 -53 0 94 88 71 0\n96 50 0 95 73 72 0\n97 48 0 96 68 0\n98 40 0 97 63 0\n99 41 0 97 64 0\n100 18 0 98 53 0\n101 20 0 99 54 0\n102 -2 0 100 5 0\n103 -3 0 100 6 0\n104 -4 0 100 7 0\n105 -8 0 100 8 0\n106 -12 0 101 9 0\n107 -13 0 101 10 0\n108 -30 0 103 104 102 105 38 0\n109 -32 0 107 90 106 40 0\n110 -35 0 108 44 0\n111 -36 0 109 46 0\n112 0 110 111 75 47 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record055.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record055.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record055.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record055.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record055 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record055.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record055.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record055.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record055.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record055 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record055_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record055_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record055_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record055_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record055_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record055_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record055_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record055 Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record055_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record055_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record055_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00008.record055
