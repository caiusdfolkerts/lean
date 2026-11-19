module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00092Data
public import GraphInputsRow24Part00092Frames
public import GraphInputsRow24Part00092Leaves
public import GraphInputsRow24Part00092Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record006
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨82, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨95, by decide⟩, ⟨102, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), 30786325577728, (certNat% 5), (certNat% 6)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 3), (certNat% 4), 57174604644352, (certNat% 5), (certNat% 6)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), (certNat% 9), 16140901064495857664, (certNat% 4), (certNat% 10), (certNat% 11)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), (certNat% 9), (certNat% 13), (certNat% 4), (certNat% 10), (certNat% 11)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 15), 70437463654400, (certNat% 16), 25769803776, 68169720922112]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), (certNat% 18), (certNat% 19), (certNat% 20), 25769803776, (certNat% 21)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), (certNat% 23), 121332826112, (certNat% 24)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 4), (certNat% 16), (certNat% 26), 65970697666560, 25769803776]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), (certNat% 28), (certNat% 3), 65970697666560, (certNat% 29), (certNat% 30)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 4), (certNat% 32), (certNat% 16), 25769803776, 68169720922112]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), (certNat% 21), (certNat% 34), 68169720922112, (certNat% 4), (certNat% 35), 25836912640]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c12 c9
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c13 c8
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c14 c5
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c15 c4
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c16 c3
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c17 c2
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c18 c1
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c19 c0
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record006_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record016
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record016
def vertexColumn : Fields := ⟨10, (certNat% 36)⟩
def kindColumn : Fields := ⟨3, (certNat% 37)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), (certNat% 39), 11259033428164608, (certNat% 40), (certNat% 41)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), (certNat% 43), (certNat% 44), 18014673387388928, 2814788421812224, (certNat% 45)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), (certNat% 47), (certNat% 41), (certNat% 48), 18084767253659648]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c4 c5
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 49), (certNat% 50), (certNat% 51), (certNat% 52)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 53), (certNat% 47), 18225504742014976, (certNat% 54), (certNat% 41)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 55), 18014742106865664, (certNat% 56), (certNat% 57), 211109453758464, (certNat% 58)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c12 c2
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 59), (certNat% 60), (certNat% 61), 21042453532377088, (certNat% 40), (certNat% 62), 316753838080]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c15 c1
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c16 c0
  c17
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record016_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record016_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record016_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record016_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record016_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record016_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record016_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record016_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record016_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record016

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record008
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "5b29c9723c1f1725aa9a1e966a58d62d876a394e4b86e8789e1783e5c569a66598e47959695954d58d4b51d68d9354d8b52d1b61d2745d0f563a4d5334d332cc73a2d4b4ac6b86c9ba1d8731ca719e1725c570de0f43c8f07c5a0e9464984e0ba91864590e685515258344d0b54348c9314c3312c2b06d0721c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6db49b6da49b49b49249b6da49249a492492692492493492491249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record008 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record008 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record008.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 53), (facetIndex 70), (facetIndex 75)]))
 (.leaf ([(facetIndex 30), (facetIndex 32), (facetIndex 59), (facetIndex 61), (facetIndex 63), (facetIndex 64)])))
 (.branch 3
 (.leaf ([(facetIndex 29), (facetIndex 42), (facetIndex 43), (facetIndex 72), (facetIndex 73), (facetIndex 74)]))
 (.leaf ([(facetIndex 48), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 52)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 31), (facetIndex 37), (facetIndex 45), (facetIndex 46), (facetIndex 60), (facetIndex 62), (facetIndex 83), (facetIndex 84)]))
 (.leaf ([(facetIndex 44), (facetIndex 54), (facetIndex 71), (facetIndex 82), (facetIndex 90), (facetIndex 91)])))
 (.branch 7
 (.leaf ([(facetIndex 33), (facetIndex 34), (facetIndex 35), (facetIndex 55), (facetIndex 56), (facetIndex 58), (facetIndex 78), (facetIndex 79)]))
 (.leaf ([(facetIndex 38), (facetIndex 39), (facetIndex 40), (facetIndex 41)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "b40004940d80092a0000130c386d436db1254bffe0db185z16;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 65), (facetIndex 76), (facetIndex 77)]))
 (.leaf ([(facetIndex 86), (facetIndex 93), (facetIndex 94)])))
 (.branch 3
 (.leaf ([(facetIndex 95), (facetIndex 99)]))
 (.leaf ([(facetIndex 36), (facetIndex 47), (facetIndex 57)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 80), (facetIndex 81), (facetIndex 85)]))
 (.leaf ([(facetIndex 89), (facetIndex 92), (facetIndex 98)])))
 (.branch 7
 (.leaf ([(facetIndex 66), (facetIndex 67), (facetIndex 68), (facetIndex 69)]))
 (.leaf ([(facetIndex 87), (facetIndex 88), (facetIndex 96), (facetIndex 97)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "57f44d02fe60024000000036d80000018000000600000003z1b;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2, 3]
def grouped2_0006 : List Nat := [4, 5]
def grouped2_0007 : List Nat := [4, 5, 6, 7]
def grouped2_0008 : List Nat := [6]
def grouped2_0009 : List Nat := [6, 7]
def grouped2_0010 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record008 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record008_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record008" "{\"atoms\":[{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":5}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record008" 22

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record008" "{\"ridges\":[[35,146],[53,656],[58,536],[70,656],[75,656]],\"owners\":[[35,146,[92],[10,42,49,51,53,80,87,88,89]],[58,536,[92],[21,43,73,74,75,81,96,97,98]],[53,656,[98],[22,70,75,89,92]],[70,656,[92],[22,53,75,89,98]],[75,656,[89],[22,53,70,92,98]]],\"edges\":[],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record008" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record008\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-8,-1],[-8,-2],[-8,-3],[-8,-5],[-8,-6],[-8,-7],[-10,-8],[-11,-8],[-12,-1],[-12,-2],[-12,-5],[-12,-6],[-12,-10],[-12,-11],[-13,-9],[-14,-1],[-14,-2],[-14,-3],[-14,-5],[-14,-6],[-14,-7],[-14,-10],[-14,-11],[-3,13],[-7,13],[-4,14],[-8,13],[-9,12],[-15,4,8,9],[-16,1,2,3,5,6,7,10,11],[-17,15],[-18,17],[-19,16],[-20,19],[-21,18],[-21,20],[21],[-22,12,13,14],[-12,22],[-13,22],[-14,22]],\"atoms\":[{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":70,\"b\":33},{\"tag\":\"incompatible\",\"a\":70,\"b\":34},{\"tag\":\"incompatible\",\"a\":70,\"b\":35},{\"tag\":\"incompatible\",\"a\":70,\"b\":55},{\"tag\":\"incompatible\",\"a\":70,\"b\":56},{\"tag\":\"incompatible\",\"a\":70,\"b\":58},{\"tag\":\"incompatible\",\"a\":78,\"b\":70},{\"tag\":\"incompatible\",\"a\":79,\"b\":70},{\"tag\":\"incompatible\",\"a\":89,\"b\":33},{\"tag\":\"incompatible\",\"a\":89,\"b\":34},{\"tag\":\"incompatible\",\"a\":89,\"b\":55},{\"tag\":\"incompatible\",\"a\":89,\"b\":56},{\"tag\":\"incompatible\",\"a\":89,\"b\":78},{\"tag\":\"incompatible\",\"a\":89,\"b\":79},{\"tag\":\"incompatible\",\"a\":92,\"b\":75},{\"tag\":\"incompatible\",\"a\":98,\"b\":33},{\"tag\":\"incompatible\",\"a\":98,\"b\":34},{\"tag\":\"incompatible\",\"a\":98,\"b\":35},{\"tag\":\"incompatible\",\"a\":98,\"b\":55},{\"tag\":\"incompatible\",\"a\":98,\"b\":56},{\"tag\":\"incompatible\",\"a\":98,\"b\":58},{\"tag\":\"incompatible\",\"a\":98,\"b\":78},{\"tag\":\"incompatible\",\"a\":98,\"b\":79},{\"tag\":\"mate\",\"ridge\":146,\"a\":35,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":536,\"a\":58,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":656,\"a\":53,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":656,\"a\":70,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":656,\"a\":75,\"owners\":[89]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[53,70,75],\"full_literals\":[-15,4,8,9]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[33,34,35,55,56,58,78,79],\"full_literals\":[-16,1,2,3,5,6,7,10,11]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-17,15,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-18,17,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-19,16,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-20,false,19],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-21,18,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-21,false,20],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[89,92,98],\"full_literals\":[-22,12,13,14]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":89,\"full_literals\":[-12,22]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":92,\"full_literals\":[-13,22]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":98,\"full_literals\":[-14,22]}]}"
  "42 18 0 37 35 0\n43 20 0 37 36 0\n44 17 0 42 32 0\n45 19 0 43 34 0\n46 15 0 44 31 0\n47 16 0 45 33 0\n48 22 0 46 39 40 41 28 27 26 29 0\n49 13 14 0 48 47 24 25 38 9 10 11 12 13 14 30 0\n50 -8 0 47 1 2 3 4 5 6 7 8 30 0\n51 14 0 50 46 26 49 29 15 0\n52 -1 0 51 16 0\n53 -2 0 51 17 0\n54 -3 0 51 18 0\n55 -5 0 51 19 0\n56 -6 0 51 20 0\n57 -7 0 51 21 0\n58 -10 0 51 22 0\n59 -11 0 51 23 0\n60 0 55 56 47 52 53 54 57 58 59 30 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record008.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record008.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record008.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record008.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record008 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record008.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record008.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record008.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record008.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record008 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record008_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record008 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record008_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record008_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record009
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "5b29c5aa9a8e966a59362da8e5392e1ba1e2785e5a6998e565a55352d68d5352d1b61d2745d58e334ccb3a2e4b52e2b4ac6b26c5ba1d8731ca719e1745c5783d0f23c3ca4a1a0e946498960d84e0b81ea46190e545494950d44d0b41da0d4348e1324c3382c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b69249349249a4924d2492492492492492492491249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record009 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record009 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record009.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record009.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record009.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 48), (facetIndex 49), (facetIndex 52), (facetIndex 58), (facetIndex 71), (facetIndex 85)]))
 (.leaf ([(facetIndex 38), (facetIndex 39), (facetIndex 50), (facetIndex 51), (facetIndex 53), (facetIndex 54)])))
 (.branch 3
 (.leaf ([(facetIndex 41), (facetIndex 43), (facetIndex 44), (facetIndex 57), (facetIndex 68), (facetIndex 82)]))
 (.branch 4
 (.leaf ([(facetIndex 42), (facetIndex 47), (facetIndex 62), (facetIndex 69), (facetIndex 76), (facetIndex 83)]))
 (.leaf ([(facetIndex 37), (facetIndex 55), (facetIndex 61), (facetIndex 72), (facetIndex 75), (facetIndex 86)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 46), (facetIndex 59), (facetIndex 70), (facetIndex 84)]))
 (.leaf ([(facetIndex 40), (facetIndex 45), (facetIndex 65), (facetIndex 79)])))
 (.branch 8
 (.leaf ([(facetIndex 56), (facetIndex 67), (facetIndex 81)]))
 (.branch 9
 (.leaf ([(facetIndex 74), (facetIndex 77), (facetIndex 78)]))
 (.leaf ([(facetIndex 60), (facetIndex 63), (facetIndex 64)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "40532706883480405327069934950274110110035622326114z25;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 66)]))
 (.branch 2
 (.leaf ([(facetIndex 73)]))
 (.leaf ([(facetIndex 80)]))))
 (.branch 4
 (.leaf ([(facetIndex 87)]))
 (.branch 5
 (.leaf ([(facetIndex 88)]))
 (.leaf ([(facetIndex 89)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "2c600002000008z36;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3, 4]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [3, 4]
def grouped2_0009 : List Nat := [4]
def grouped2_0010 : List Nat := [5]
def grouped2_0011 : List Nat := [5, 6]
def grouped2_0012 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0013 : List Nat := [6]
def grouped2_0014 : List Nat := [7]
def grouped2_0015 : List Nat := [7, 8, 9]
def grouped2_0016 : List Nat := [8]
def grouped2_0017 : List Nat := [8, 9]
def grouped2_0018 : List Nat := [9]
def grouped3_0019 : List Nat := [0]
def grouped3_0020 : List Nat := [0, 1, 2]
def grouped3_0022 : List Nat := [1]
def grouped3_0023 : List Nat := [1, 2]
def grouped3_0024 : List Nat := [2]
def grouped3_0025 : List Nat := [3]
def grouped3_0026 : List Nat := [3, 4, 5]
def grouped3_0027 : List Nat := [4]
def grouped3_0028 : List Nat := [4, 5]
def grouped3_0029 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record009 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record009_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record009" "{\"atoms\":[{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0017\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0017\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record009" 110

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record009" "{\"ridges\":[[8,73],[8,74],[10,35],[13,259],[14,67],[14,259],[18,13],[18,76],[20,133],[21,289],[22,321],[28,14],[28,76],[29,38],[30,134],[31,262],[32,70],[32,262],[33,42],[45,67],[45,70],[46,259],[46,262],[48,73],[48,74],[50,73],[50,74],[54,67],[54,73],[54,74],[56,35],[57,259],[58,35],[60,73],[60,76],[63,76],[64,13],[66,13],[66,652],[68,289],[69,133],[73,73],[73,360],[74,70],[74,74],[74,76],[77,76],[78,14],[80,14],[80,652],[82,262],[83,134],[87,74],[88,652],[89,360]],\"owners\":[[10,35,[2,7,13,43,44,50,52,59],[56,58]],[56,35,[2,7,13,43,50,52,59],[10,44,58]],[58,35,[2,7,13,43,44,50,59],[10,52,56]],[29,38,[2,27,31,43,44,77,84],[81]],[54,67,[3,14,40,43,45,59],[8,48,50]],[74,70,[3,32,43,45,84],[28,40,77]],[20,133,[4,37,44,45,46,47,66],[61,67,69]],[69,133,[4,37,44,45,46],[20,47,61,66,67]],[30,134,[4,37,44,45,46,47,80],[75,81,83]],[83,134,[4,37,44,45,46],[30,47,75,80,81]],[13,259,[5,14,38,41,46,53],[51,57]],[57,259,[5,14,38,46,53],[13,41,51]],[31,262,[5,32,38,41,46,79],[78,82]],[82,262,[5,32,38,46,79],[31,41,78]],[33,42,[7,27,50,51,52,77,78,87],[85]],[8,73,[18,60,63,65,73],[48,50,53,54]],[48,73,[18,63,65,73],[8,50,53,54,60]],[50,73,[18,60,65],[8,48,53,54,63,73]],[54,73,[18,60,63,65,73],[8,48,50,53]],[8,74,[28,74,77,79,87],[48,50,53,54]],[48,74,[28,77,79,87],[8,50,53,54,74]],[50,74,[28,74,79],[8,48,53,54,77,87]],[54,74,[28,74,77,79,87],[8,48,50,53]],[21,289,[13,51,57,59,73],[64,68,70]],[68,289,[13,51,59,73],[21,57,64,70]],[22,321,[14,53,59,73],[65,70]],[18,76,[28,74,77,79,89],[60,63,65]],[28,76,[18,60,63,65,89],[74,77,79]],[60,76,[28,77,79,89],[18,63,65,74]],[63,76,[28,74,79],[18,60,65,77,89]],[74,76,[18,63,65,89],[28,60,77,79]],[77,76,[18,60,65],[28,63,74,79,89]],[66,652,[80,88],[]],[80,652,[66,88],[]],[88,652,[66,80],[]],[73,360,[87,89],[]],[89,360,[73,87],[]]],\"edges\":[[7,[5,13,14,21,22,38,41,46,51,53,57,59,64,65,68,70,73]],[12,[2,7,10,13,27,29,31,33,43,44,50,51,52,56,57,58,59,77,78,81,82,84,85,87]],[15,[5,13,14,31,32,38,41,46,51,53,57,59,78,79,82,84,87]],[21,[4,20,30,37,44,45,46,47,61,66,67,69,75,80,81,83,88]],[26,[8,18,28,48,50,53,54,60,63,65,73,74,77,79,87,89]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record009" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record009\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-24,-3],[-24,-21],[-28,-24],[-29,-4],[-29,-23],[-29,-25],[-30,-1],[-30,-2],[-30,-21],[-30,-22],[-30,-23],[-30,-24],[-30,-25],[-30,-26],[-30,-27],[-30,-28],[-30,-29],[-31,-24],[-31,-30],[-37,-5],[-37,-35],[-42,-30],[-43,-21],[-43,-23],[-44,-24],[-44,-43],[-45,-43],[-46,-21],[-46,-44],[-46,-45],[-47,-36],[-48,-47],[-49,-21],[-49,-26],[-49,-31],[-49,-38],[-49,-43],[-49,-44],[-49,-45],[-49,-46],[-50,-24],[-50,-43],[-52,-49],[-54,-49],[-55,-22],[-55,-33],[-55,-34],[-55,-36],[-55,-42],[-55,-46],[-55,-47],[-55,-48],[-55,-53],[-56,-14],[-56,-23],[-56,-24],[-56,-43],[-57,-24],[-57,-49],[-58,-49],[-59,-55],[-60,-36],[-60,-47],[-60,-48],[-60,-55],[-61,-47],[-61,-55],[-61,-60],[-62,-56],[-62,-59],[-63,-24],[-63,-56],[-64,-63],[-65,-49],[-66,-30],[-66,-55],[-67,-56],[-68,-49],[-70,-21],[-70,-26],[-70,-31],[-70,-38],[-70,-44],[-70,-45],[-70,-52],[-70,-54],[-70,-57],[-70,-58],[-70,-65],[-70,-68],[-71,-22],[-71,-27],[-71,-33],[-71,-34],[-71,-36],[-71,-42],[-71,-46],[-71,-47],[-71,-48],[-71,-53],[-71,-59],[-71,-60],[-71,-61],[-71,-66],[-10,-47,-49],[-15,-60,-62],[-7,1,5,8,27,28,33,35,42],[-39,1,5,8,27,33,35,42],[-41,1,5,8,27,28,33,42],[-16,1,14,18,27,28,59,66],[-37,2,9,24,27,29,42],[-9,-29,-37],[-56,2,19,27,29,66],[-19,-29,-56],[-11,3,21,28,29,30,31,49],[-52,3,21,28,29,30],[-17,3,21,28,29,30,31,62],[-65,3,21,28,29,30],[-8,4,9,22,25,30,36],[-40,4,9,22,30,36],[-8,-9,-30],[-9,-30,-40],[-18,4,19,22,25,30,61],[-64,4,19,22,30,61],[-18,-19,-30],[-19,-30,-64],[-20,5,14,33,34,35,59,60,69],[-6,10,43,46,48,55],[-32,10,46,48,55],[-33,10,43,48],[-37,10,43,46,48,55],[-37,-43,-55],[-6,15,56,59,61,69],[-32,15,59,61,69],[-33,15,56,61],[-37,15,56,59,61,69],[-37,-56,-69],[-12,8,34,40,42,55],[-51,8,34,42,55],[-13,9,36,42,55],[-10,15,56,59,61,71],[-15,10,43,46,48,71],[-43,15,59,61,71],[-46,15,56,61],[-56,10,46,48,71],[-59,10,43,48],[-49,62,70],[-62,49,70],[-70,49,62],[-55,69,71],[-71,55,69],[-72,22,23,33,34,36,37],[-73,25,27,28,40,51,64],[-74,26,31,45,52,58,65],[-75,21,38,44,54,57,68],[-76,30,42,53,66],[-30,76],[-77,24,29,48,61],[-24,77],[-29,77],[-78,39,50,63],[-79,56,59,60],[-80,43,46,47],[-81,72],[-82,74,75],[-83,74],[-85,73],[-84,82],[-85,83],[-87,81],[-86,84],[-87,85],[-88,76,77],[-89,76],[-89,77],[-76,-77,89],[-90,79,80],[-91,79],[-91,80],[-92,78,91],[-92,90],[-93,91],[-94,88,93],[-94,89,92],[-95,89,93],[-96,89],[-96,93],[-97,86,96],[-97,87,95],[-97,94],[97],[-98,49],[-49,98],[-99,55],[-55,99],[-100,62],[-62,100],[-69,101],[-102,70],[-70,102],[-103,71],[-71,103],[-104,99,100],[-100,104],[-99,104],[-105,98,104],[-104,105],[-98,105],[-106,102,103],[-102,106],[-102,-103,107],[-107,108],[-108,106],[-101,-106,108],[-109,105,108],[-105,-108,110],[109],[-110],[4,8,9,12,13,22,25,30,34,36,40,42,47,48,51,53,55],[1,5,7,8,14,16,18,20,27,28,33,34,35,39,40,41,42,59,60,63,64,66,67,69],[4,8,9,18,19,22,25,30,34,36,40,42,60,61,64,66,69],[3,11,17,21,28,29,30,31,44,49,50,52,57,62,63,65,70],[6,10,15,32,33,36,37,43,46,48,55,56,59,61,69,71]],\"atoms\":[{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":40,\"b\":4},{\"tag\":\"incompatible\",\"a\":40,\"b\":37},{\"tag\":\"incompatible\",\"a\":44,\"b\":40},{\"tag\":\"incompatible\",\"a\":45,\"b\":5},{\"tag\":\"incompatible\",\"a\":45,\"b\":39},{\"tag\":\"incompatible\",\"a\":45,\"b\":41},{\"tag\":\"incompatible\",\"a\":46,\"b\":2},{\"tag\":\"incompatible\",\"a\":46,\"b\":3},{\"tag\":\"incompatible\",\"a\":46,\"b\":37},{\"tag\":\"incompatible\",\"a\":46,\"b\":38},{\"tag\":\"incompatible\",\"a\":46,\"b\":39},{\"tag\":\"incompatible\",\"a\":46,\"b\":40},{\"tag\":\"incompatible\",\"a\":46,\"b\":41},{\"tag\":\"incompatible\",\"a\":46,\"b\":42},{\"tag\":\"incompatible\",\"a\":46,\"b\":43},{\"tag\":\"incompatible\",\"a\":46,\"b\":44},{\"tag\":\"incompatible\",\"a\":46,\"b\":45},{\"tag\":\"incompatible\",\"a\":47,\"b\":40},{\"tag\":\"incompatible\",\"a\":47,\"b\":46},{\"tag\":\"incompatible\",\"a\":54,\"b\":7},{\"tag\":\"incompatible\",\"a\":54,\"b\":52},{\"tag\":\"incompatible\",\"a\":59,\"b\":46},{\"tag\":\"incompatible\",\"a\":60,\"b\":37},{\"tag\":\"incompatible\",\"a\":60,\"b\":39},{\"tag\":\"incompatible\",\"a\":61,\"b\":40},{\"tag\":\"incompatible\",\"a\":61,\"b\":60},{\"tag\":\"incompatible\",\"a\":62,\"b\":60},{\"tag\":\"incompatible\",\"a\":63,\"b\":37},{\"tag\":\"incompatible\",\"a\":63,\"b\":61},{\"tag\":\"incompatible\",\"a\":63,\"b\":62},{\"tag\":\"incompatible\",\"a\":64,\"b\":53},{\"tag\":\"incompatible\",\"a\":65,\"b\":64},{\"tag\":\"incompatible\",\"a\":66,\"b\":37},{\"tag\":\"incompatible\",\"a\":66,\"b\":42},{\"tag\":\"incompatible\",\"a\":66,\"b\":47},{\"tag\":\"incompatible\",\"a\":66,\"b\":55},{\"tag\":\"incompatible\",\"a\":66,\"b\":60},{\"tag\":\"incompatible\",\"a\":66,\"b\":61},{\"tag\":\"incompatible\",\"a\":66,\"b\":62},{\"tag\":\"incompatible\",\"a\":66,\"b\":63},{\"tag\":\"incompatible\",\"a\":67,\"b\":40},{\"tag\":\"incompatible\",\"a\":67,\"b\":60},{\"tag\":\"incompatible\",\"a\":69,\"b\":66},{\"tag\":\"incompatible\",\"a\":72,\"b\":66},{\"tag\":\"incompatible\",\"a\":73,\"b\":38},{\"tag\":\"incompatible\",\"a\":73,\"b\":50},{\"tag\":\"incompatible\",\"a\":73,\"b\":51},{\"tag\":\"incompatible\",\"a\":73,\"b\":53},{\"tag\":\"incompatible\",\"a\":73,\"b\":59},{\"tag\":\"incompatible\",\"a\":73,\"b\":63},{\"tag\":\"incompatible\",\"a\":73,\"b\":64},{\"tag\":\"incompatible\",\"a\":73,\"b\":65},{\"tag\":\"incompatible\",\"a\":73,\"b\":70},{\"tag\":\"incompatible\",\"a\":74,\"b\":27},{\"tag\":\"incompatible\",\"a\":74,\"b\":39},{\"tag\":\"incompatible\",\"a\":74,\"b\":40},{\"tag\":\"incompatible\",\"a\":74,\"b\":60},{\"tag\":\"incompatible\",\"a\":75,\"b\":40},{\"tag\":\"incompatible\",\"a\":75,\"b\":66},{\"tag\":\"incompatible\",\"a\":76,\"b\":66},{\"tag\":\"incompatible\",\"a\":77,\"b\":73},{\"tag\":\"incompatible\",\"a\":78,\"b\":53},{\"tag\":\"incompatible\",\"a\":78,\"b\":64},{\"tag\":\"incompatible\",\"a\":78,\"b\":65},{\"tag\":\"incompatible\",\"a\":78,\"b\":73},{\"tag\":\"incompatible\",\"a\":79,\"b\":64},{\"tag\":\"incompatible\",\"a\":79,\"b\":73},{\"tag\":\"incompatible\",\"a\":79,\"b\":78},{\"tag\":\"incompatible\",\"a\":80,\"b\":74},{\"tag\":\"incompatible\",\"a\":80,\"b\":77},{\"tag\":\"incompatible\",\"a\":81,\"b\":40},{\"tag\":\"incompatible\",\"a\":81,\"b\":74},{\"tag\":\"incompatible\",\"a\":82,\"b\":81},{\"tag\":\"incompatible\",\"a\":83,\"b\":66},{\"tag\":\"incompatible\",\"a\":84,\"b\":46},{\"tag\":\"incompatible\",\"a\":84,\"b\":73},{\"tag\":\"incompatible\",\"a\":85,\"b\":74},{\"tag\":\"incompatible\",\"a\":86,\"b\":66},{\"tag\":\"incompatible\",\"a\":88,\"b\":37},{\"tag\":\"incompatible\",\"a\":88,\"b\":42},{\"tag\":\"incompatible\",\"a\":88,\"b\":47},{\"tag\":\"incompatible\",\"a\":88,\"b\":55},{\"tag\":\"incompatible\",\"a\":88,\"b\":61},{\"tag\":\"incompatible\",\"a\":88,\"b\":62},{\"tag\":\"incompatible\",\"a\":88,\"b\":69},{\"tag\":\"incompatible\",\"a\":88,\"b\":72},{\"tag\":\"incompatible\",\"a\":88,\"b\":75},{\"tag\":\"incompatible\",\"a\":88,\"b\":76},{\"tag\":\"incompatible\",\"a\":88,\"b\":83},{\"tag\":\"incompatible\",\"a\":88,\"b\":86},{\"tag\":\"incompatible\",\"a\":89,\"b\":38},{\"tag\":\"incompatible\",\"a\":89,\"b\":43},{\"tag\":\"incompatible\",\"a\":89,\"b\":50},{\"tag\":\"incompatible\",\"a\":89,\"b\":51},{\"tag\":\"incompatible\",\"a\":89,\"b\":53},{\"tag\":\"incompatible\",\"a\":89,\"b\":59},{\"tag\":\"incompatible\",\"a\":89,\"b\":63},{\"tag\":\"incompatible\",\"a\":89,\"b\":64},{\"tag\":\"incompatible\",\"a\":89,\"b\":65},{\"tag\":\"incompatible\",\"a\":89,\"b\":70},{\"tag\":\"incompatible\",\"a\":89,\"b\":77},{\"tag\":\"incompatible\",\"a\":89,\"b\":78},{\"tag\":\"incompatible\",\"a\":89,\"b\":79},{\"tag\":\"incompatible\",\"a\":89,\"b\":84},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[18,64,66]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[28,78,80]},{\"tag\":\"mate\",\"ridge\":35,\"a\":10,\"owners\":[2,7,13,43,44,50,52,59]},{\"tag\":\"mate\",\"ridge\":35,\"a\":56,\"owners\":[2,7,13,43,50,52,59]},{\"tag\":\"mate\",\"ridge\":35,\"a\":58,\"owners\":[2,7,13,43,44,50,59]},{\"tag\":\"mate\",\"ridge\":38,\"a\":29,\"owners\":[2,27,31,43,44,77,84]},{\"tag\":\"mate\",\"ridge\":67,\"a\":54,\"owners\":[3,14,40,43,45,59]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[14,45,54]},{\"tag\":\"mate\",\"ridge\":70,\"a\":74,\"owners\":[3,32,43,45,84]},{\"tag\":\"three\",\"ridge\":70,\"vertices\":[32,45,74]},{\"tag\":\"mate\",\"ridge\":133,\"a\":20,\"owners\":[4,37,44,45,46,47,66]},{\"tag\":\"mate\",\"ridge\":133,\"a\":69,\"owners\":[4,37,44,45,46]},{\"tag\":\"mate\",\"ridge\":134,\"a\":30,\"owners\":[4,37,44,45,46,47,80]},{\"tag\":\"mate\",\"ridge\":134,\"a\":83,\"owners\":[4,37,44,45,46]},{\"tag\":\"mate\",\"ridge\":259,\"a\":13,\"owners\":[5,14,38,41,46,53]},{\"tag\":\"mate\",\"ridge\":259,\"a\":57,\"owners\":[5,14,38,46,53]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[13,14,46]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[14,46,57]},{\"tag\":\"mate\",\"ridge\":262,\"a\":31,\"owners\":[5,32,38,41,46,79]},{\"tag\":\"mate\",\"ridge\":262,\"a\":82,\"owners\":[5,32,38,46,79]},{\"tag\":\"three\",\"ridge\":262,\"vertices\":[31,32,46]},{\"tag\":\"three\",\"ridge\":262,\"vertices\":[32,46,82]},{\"tag\":\"mate\",\"ridge\":42,\"a\":33,\"owners\":[7,27,50,51,52,77,78,87]},{\"tag\":\"mate\",\"ridge\":73,\"a\":8,\"owners\":[18,60,63,65,73]},{\"tag\":\"mate\",\"ridge\":73,\"a\":48,\"owners\":[18,63,65,73]},{\"tag\":\"mate\",\"ridge\":73,\"a\":50,\"owners\":[18,60,65]},{\"tag\":\"mate\",\"ridge\":73,\"a\":54,\"owners\":[18,60,63,65,73]},{\"tag\":\"three\",\"ridge\":73,\"vertices\":[54,60,73]},{\"tag\":\"mate\",\"ridge\":74,\"a\":8,\"owners\":[28,74,77,79,87]},{\"tag\":\"mate\",\"ridge\":74,\"a\":48,\"owners\":[28,77,79,87]},{\"tag\":\"mate\",\"ridge\":74,\"a\":50,\"owners\":[28,74,79]},{\"tag\":\"mate\",\"ridge\":74,\"a\":54,\"owners\":[28,74,77,79,87]},{\"tag\":\"three\",\"ridge\":74,\"vertices\":[54,74,87]},{\"tag\":\"mate\",\"ridge\":289,\"a\":21,\"owners\":[13,51,57,59,73]},{\"tag\":\"mate\",\"ridge\":289,\"a\":68,\"owners\":[13,51,59,73]},{\"tag\":\"mate\",\"ridge\":321,\"a\":22,\"owners\":[14,53,59,73]},{\"tag\":\"mate\",\"ridge\":76,\"a\":18,\"owners\":[28,74,77,79,89]},{\"tag\":\"mate\",\"ridge\":76,\"a\":28,\"owners\":[18,60,63,65,89]},{\"tag\":\"mate\",\"ridge\":76,\"a\":60,\"owners\":[28,77,79,89]},{\"tag\":\"mate\",\"ridge\":76,\"a\":63,\"owners\":[28,74,79]},{\"tag\":\"mate\",\"ridge\":76,\"a\":74,\"owners\":[18,63,65,89]},{\"tag\":\"mate\",\"ridge\":76,\"a\":77,\"owners\":[18,60,65]},{\"tag\":\"mate\",\"ridge\":652,\"a\":66,\"owners\":[80,88]},{\"tag\":\"mate\",\"ridge\":652,\"a\":80,\"owners\":[66,88]},{\"tag\":\"mate\",\"ridge\":652,\"a\":88,\"owners\":[66,80]},{\"tag\":\"mate\",\"ridge\":360,\"a\":73,\"owners\":[87,89]},{\"tag\":\"mate\",\"ridge\":360,\"a\":89,\"owners\":[73,87]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[38,39,50,51,53,54],\"full_literals\":[-72,22,23,33,34,36,37]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[41,43,44,57,68,82],\"full_literals\":[-73,25,27,28,40,51,64]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[42,47,62,69,76,83],\"full_literals\":[-74,26,31,45,52,58,65]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[37,55,61,72,75,86],\"full_literals\":[-75,21,38,44,54,57,68]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[46,59,70,84],\"full_literals\":[-76,30,42,53,66]},{\"tag\":\"group_take\",\"kind\":2,\"index\":5,\"member\":46,\"full_literals\":[-30,76]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[40,45,65,79],\"full_literals\":[-77,24,29,48,61]},{\"tag\":\"group_take\",\"kind\":2,\"index\":6,\"member\":40,\"full_literals\":[-24,77]},{\"tag\":\"group_take\",\"kind\":2,\"index\":6,\"member\":45,\"full_literals\":[-29,77]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[56,67,81],\"full_literals\":[-78,39,50,63]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[74,77,78],\"full_literals\":[-79,56,59,60]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[60,63,64],\"full_literals\":[-80,43,46,47]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-81,false,72],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0008\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-82,74,75],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0008\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-83,74,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-85,73,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-84,false,82],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-85,false,83],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-87,81,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-86,false,84],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-87,false,85],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-88,76,77],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-89,76,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-89,false,77],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-76,-77,89],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0018\",\"joined_name\":\"grouped2_0017\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-90,79,80],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0018\",\"joined_name\":\"grouped2_0017\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-91,79,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0018\",\"joined_name\":\"grouped2_0017\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-91,false,80],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-92,78,91],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-92,false,90],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-93,false,91],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-94,88,93],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-94,89,92],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-95,89,93],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-96,89,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-96,false,93],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-97,86,96],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-97,87,95],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-97,false,94],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[66],\"full_literals\":[-98,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":66,\"full_literals\":[-49,98]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[73],\"full_literals\":[-99,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":73,\"full_literals\":[-55,99]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[80],\"full_literals\":[-100,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":80,\"full_literals\":[-62,100]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":87,\"full_literals\":[-69,101]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[88],\"full_literals\":[-102,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":88,\"full_literals\":[-70,102]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[89],\"full_literals\":[-103,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":89,\"full_literals\":[-71,103]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-104,99,100],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-100,104],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-99,false,104],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-105,98,104],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-104,105],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-98,false,105],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-106,102,103],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-102,false,106],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-102,-103,107],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-107,108],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-108,false,106],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-101,-106,108],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-109,105,108],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-105,-108,110],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":7,\"owners\":[5,13,14,21,22,38,41,46,51,53,57,59,64,65,68,70,73]},{\"tag\":\"edge\",\"edge\":12,\"owners\":[2,7,10,13,27,29,31,33,43,44,50,51,52,56,57,58,59,77,78,81,82,84,85,87]},{\"tag\":\"edge\",\"edge\":15,\"owners\":[5,13,14,31,32,38,41,46,51,53,57,59,78,79,82,84,87]},{\"tag\":\"edge\",\"edge\":21,\"owners\":[4,20,30,37,44,45,46,47,61,66,67,69,75,80,81,83,88]},{\"tag\":\"edge\",\"edge\":26,\"owners\":[8,18,28,48,50,53,54,60,63,65,73,74,77,79,87,89]}]}"
  "224 94 0 191 190 0\n225 -89 -71 0 104 103 100 99 96 174 175 156 12 17 158 0\n226 29 -77 -108 0 218 213 216 208 193 207 204 197 149 199 209 201 225 176 157 103 99 158 1 2 3 18 25 41 58 71 115 117 116 118 222 0\n227 -91 -71 0 102 101 98 97 178 179 162 163 57 0\n228 -77 -108 0 218 191 213 216 208 193 207 204 197 149 199 209 201 225 227 182 185 189 170 164 100 99 98 96 95 94 93 91 205 195 176 157 226 4 5 6 152 112 119 120 140 138 139 219 0\n229 -108 0 218 191 224 213 216 207 208 204 205 193 197 195 149 199 209 201 91 92 93 94 95 96 97 98 100 101 102 104 151 225 184 181 227 182 180 185 189 170 172 164 167 228 183 159 160 173 156 7 8 11 13 16 152 20 21 111 137 121 122 162 108 139 153 177 73 163 161 42 0\n230 -107 0 229 212 0\n231 105 0 229 217 215 0\n232 49 70 99 0 231 192 148 206 196 203 0\n233 -70 38 -30 -82 0 19 14 9 83 84 85 86 87 88 89 90 154 155 165 0\n234 -49 -30 -82 0 19 14 9 36 38 39 43 44 59 60 74 78 154 155 165 0\n235 -70 -30 -82 0 82 233 0\n236 -37 -30 47 77 0 224 191 175 186 188 171 168 234 235 232 194 65 61 50 47 46 75 22 16 15 8 7 184 181 160 159 20 21 111 132 121 122 163 107 108 109 177 162 54 72 77 113 137 125 126 127 110 220 0\n237 -30 47 77 0 191 175 186 188 171 168 10 11 234 235 232 194 46 47 48 50 61 65 236 152 164 170 189 185 182 178 179 162 163 57 0\n238 -55 47 77 0 224 237 49 50 53 61 65 76 156 173 183 182 178 179 162 163 57 0\n239 -43 99 -82 0 23 26 27 37 232 80 81 82 85 86 87 88 89 90 154 155 165 0\n240 -46 99 -82 0 28 29 30 40 232 80 81 82 85 86 87 88 89 90 154 155 165 0\n241 -70 -74 0 80 81 84 85 88 89 154 0\n242 47 77 0 191 175 186 188 171 168 238 194 239 240 163 179 182 185 189 172 169 166 241 232 34 35 39 43 60 74 154 0\n243 -49 -82 0 33 34 35 36 38 39 43 44 59 60 74 78 154 155 165 0\n244 77 0 191 175 186 188 171 168 242 51 194 243 232 79 82 83 86 87 90 241 155 165 0\n245 -62 -70 0 229 230 191 241 86 87 83 82 79 90 155 165 168 171 188 187 182 178 200 211 202 210 214 198 150 69 70 162 62 64 68 106 133 141 134 143 135 144 136 223 0\n246 -70 0 230 229 191 79 82 83 86 87 90 200 241 155 210 211 165 214 202 168 198 171 150 188 187 182 179 245 149 37 40 163 31 32 66 105 128 129 146 131 130 145 142 223 0\n247 -49 0 246 191 37 40 147 243 69 70 168 171 188 187 182 178 179 162 163 63 0\n248 99 0 247 246 232 0\n249 55 0 248 194 0\n250 -22 0 249 45 0\n251 -33 0 249 46 0\n252 -34 0 249 47 0\n253 -36 0 249 48 0\n254 -42 0 249 49 0\n255 -46 0 249 50 0\n256 -47 0 249 51 0\n257 -48 0 249 52 0\n258 -53 0 249 53 0\n259 -59 0 249 61 0\n260 -60 0 249 65 0\n261 -61 0 249 67 0\n262 -66 0 249 76 0\n263 -56 93 0 257 244 258 191 251 262 260 261 254 253 252 250 55 56 158 4 6 17 114 156 124 123 174 185 189 170 164 152 112 137 119 120 221 0\n264 -30 0 257 244 261 12 17 158 0\n265 -76 0 264 254 262 258 156 0\n266 -89 0 265 174 0\n267 92 0 266 224 184 0\n268 90 0 267 181 0\n269 79 0 268 255 256 249 266 252 253 250 251 191 177 178 163 182 24 132 185 152 189 164 170 0\n270 56 0 269 260 259 162 0\n271 -43 0 270 57 0\n272 93 0 270 263 0\n273 -80 0 271 256 255 163 0\n274 91 0 272 182 0\n275 0 274 273 179 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record009.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record009.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record009.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record009.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record009 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record009.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record009.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record009.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record009.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record009 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record009_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record009 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record009_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record009_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record009

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record011
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2aca70f25aa9a66a96558b61da8e538ae1ba1e4789e3c6a95a719a6599a9695955552d475a354d8b4ad1b61d4749d58ce3a4d9334cb31ce8b62d4b4ac6b86d1b26e8751ca785d1725c3783d0f23c4f07d522a8661582ea4551a24a9196151560d0b54328c6344c9314d0b22c2b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db4d36936da6d36926934926d249249249a4d2492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record011 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record011 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record011.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record011.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record011.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 60), (facetIndex 71)]))
 (.leaf ([(facetIndex 63), (facetIndex 73)])))
 (.branch 3
 (.leaf ([(facetIndex 79), (facetIndex 87)]))
 (.leaf ([(facetIndex 82), (facetIndex 88)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 38), (facetIndex 54), (facetIndex 67)]))
 (.leaf ([(facetIndex 74), (facetIndex 80), (facetIndex 90)])))
 (.branch 7
 (.leaf ([(facetIndex 41), (facetIndex 55), (facetIndex 68), (facetIndex 70), (facetIndex 89)]))
 (.branch 8
 (.leaf ([(facetIndex 75), (facetIndex 76), (facetIndex 85)]))
 (.leaf ([(facetIndex 84), (facetIndex 86)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "56328780305200775100606400010000000640000000000006004z26;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record011 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record011_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record011" "{\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record011" 68

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record011" "{\"ridges\":[[6,265],[6,266],[8,146],[16,532],[19,648],[21,656],[30,265],[30,266],[33,146],[35,532],[39,146],[40,266],[43,265],[43,266],[44,265],[44,266],[45,265],[45,266],[46,648],[48,146],[49,146],[50,146],[51,146],[51,656],[55,284],[56,532],[61,648],[65,532],[66,656],[68,408],[69,648],[69,656],[70,792],[72,648],[84,646],[86,538],[89,156]],\"owners\":[[6,265,[55,60,68,70,71],[30,40,43,44,45]],[30,265,[68,70,71],[6,40,43,44,45,55,60]],[43,265,[55,60,68,70],[6,30,40,44,45,71]],[44,265,[55,68,70],[6,30,40,43,45,60,71]],[45,265,[55,60,70,71],[6,30,40,43,44,68]],[6,266,[75,79,85,87],[30,40,43,44,45]],[30,266,[85,87],[6,40,43,44,45,75,79]],[40,266,[79,87],[6,30,43,44,45,75,85]],[43,266,[75,79,85],[6,30,40,44,45,87]],[44,266,[75,85],[6,30,40,43,45,79,87]],[45,266,[75,79,87],[6,30,40,43,44,85]],[8,146,[74,82,84,85,86,88],[33,39,48,49,50,51]],[33,146,[85,86,88],[8,39,48,49,50,51,74,82,84]],[39,146,[82,84,88],[8,33,48,49,50,51,74,85,86]],[48,146,[74,84,85,86],[8,33,39,49,50,51,82,88]],[49,146,[74,82,84,85,86],[8,33,39,48,50,51,88]],[50,146,[74,82,84,86,88],[8,33,39,48,49,51,85]],[51,146,[74,82,85,88],[8,33,39,48,49,50,84,86]],[16,532,[76,84,89],[35,56,65,66]],[35,532,[89],[16,56,65,66,76,84]],[56,532,[84],[16,35,65,66,76,89]],[65,532,[76,84,89],[16,35,56,66]],[19,648,[80,86,89,90],[46,61,69,72]],[46,648,[89,90],[19,61,69,72,80,86]],[61,648,[86],[19,46,69,72,80,89,90]],[69,648,[80,90],[19,46,61,72,86,89]],[72,648,[80,86,89],[19,46,61,69,90]],[21,656,[84,86,89],[51,66,69]],[51,656,[89],[21,66,69,84,86]],[66,656,[86],[21,51,69,84,89]],[69,656,[84],[21,51,66,86,89]],[84,646,[38,80],[]],[86,538,[41,76],[]],[89,156,[54,74],[]],[55,284,[75],[]],[68,408,[85],[]],[70,792,[],[]]],\"edges\":[[28,[6,30,40,43,44,45,55,60,68,70,71,75,79,85,87]],[32,[8,21,33,39,48,49,50,51,54,63,66,68,69,73,74,82,84,85,86,88,89]],[34,[16,21,35,41,51,56,65,66,69,70,76,84,86,89]],[43,[19,21,38,46,51,61,66,67,69,72,80,84,86,89,90]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record011" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record011\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-22,-21],[-30,-21],[-37,-21],[-37,-36],[-43,-12],[-43,-21],[-43,-38],[-44,-22],[-44,-30],[-44,-37],[-44,-43],[-47,-37],[-47,-43],[-1,22,24,30,32,33],[-6,30,32,33],[-13,22,24,30,32],[-14,22,30,32],[-15,22,24,32,33],[-1,37,39,43,45],[-6,43,45],[-11,39,45],[-13,37,39,43],[-14,37,43],[-15,37,39,45],[-2,36,41,42,43,44,46],[-7,43,44,46],[-10,41,42,46],[-17,36,42,43,44],[-18,36,41,42,43,44],[-19,36,41,42,44,46],[-20,36,41,43,46],[-3,38,42,47],[-8,47],[-23,42],[-27,38,42,47],[-4,40,44,47,48],[-16,47,48],[-25,44],[-31,40,48],[-34,40,44,47],[-5,42,44,47],[-20,47],[-28,44],[-31,42],[-42,9,40],[-44,12,38],[-47,21,36],[-22,37],[-30,43],[-32],[-24,49],[-33,49],[-26,50],[-35,50],[-39,51],[-45,51],[-41,52],[-46,52],[-9,53],[-21,53],[-29,53],[-36,54],[-40,54],[-48,54],[-12,55],[-47,55],[-37,56],[-38,56],[-43,56],[-42,57],[-44,57],[-50,58],[-49,58],[-52,59],[-51,59],[-59,60],[-58,60],[-54,61],[-53,61],[-57,62],[-56,62],[-56,-57,63],[-62,64],[-63,65],[-55,64],[-55,-62,65],[-65,66],[-61,-64,66],[-61,-65,67],[-67,68],[-60,-66,68],[-68],[1,6,11,13,14,15,22,24,30,32,33,37,39,43,45],[2,5,7,10,17,18,19,20,21,26,28,30,31,35,36,41,42,43,44,46,47],[3,5,8,12,20,23,27,28,31,32,38,42,44,47],[4,5,9,16,20,25,28,29,31,34,40,42,44,47,48]],\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":55,\"b\":54},{\"tag\":\"incompatible\",\"a\":68,\"b\":54},{\"tag\":\"incompatible\",\"a\":75,\"b\":54},{\"tag\":\"incompatible\",\"a\":75,\"b\":74},{\"tag\":\"incompatible\",\"a\":85,\"b\":41},{\"tag\":\"incompatible\",\"a\":85,\"b\":54},{\"tag\":\"incompatible\",\"a\":85,\"b\":76},{\"tag\":\"incompatible\",\"a\":86,\"b\":55},{\"tag\":\"incompatible\",\"a\":86,\"b\":68},{\"tag\":\"incompatible\",\"a\":86,\"b\":75},{\"tag\":\"incompatible\",\"a\":86,\"b\":85},{\"tag\":\"incompatible\",\"a\":89,\"b\":75},{\"tag\":\"incompatible\",\"a\":89,\"b\":85},{\"tag\":\"mate\",\"ridge\":265,\"a\":6,\"owners\":[55,60,68,70,71]},{\"tag\":\"mate\",\"ridge\":265,\"a\":30,\"owners\":[68,70,71]},{\"tag\":\"mate\",\"ridge\":265,\"a\":43,\"owners\":[55,60,68,70]},{\"tag\":\"mate\",\"ridge\":265,\"a\":44,\"owners\":[55,68,70]},{\"tag\":\"mate\",\"ridge\":265,\"a\":45,\"owners\":[55,60,70,71]},{\"tag\":\"mate\",\"ridge\":266,\"a\":6,\"owners\":[75,79,85,87]},{\"tag\":\"mate\",\"ridge\":266,\"a\":30,\"owners\":[85,87]},{\"tag\":\"mate\",\"ridge\":266,\"a\":40,\"owners\":[79,87]},{\"tag\":\"mate\",\"ridge\":266,\"a\":43,\"owners\":[75,79,85]},{\"tag\":\"mate\",\"ridge\":266,\"a\":44,\"owners\":[75,85]},{\"tag\":\"mate\",\"ridge\":266,\"a\":45,\"owners\":[75,79,87]},{\"tag\":\"mate\",\"ridge\":146,\"a\":8,\"owners\":[74,82,84,85,86,88]},{\"tag\":\"mate\",\"ridge\":146,\"a\":33,\"owners\":[85,86,88]},{\"tag\":\"mate\",\"ridge\":146,\"a\":39,\"owners\":[82,84,88]},{\"tag\":\"mate\",\"ridge\":146,\"a\":48,\"owners\":[74,84,85,86]},{\"tag\":\"mate\",\"ridge\":146,\"a\":49,\"owners\":[74,82,84,85,86]},{\"tag\":\"mate\",\"ridge\":146,\"a\":50,\"owners\":[74,82,84,86,88]},{\"tag\":\"mate\",\"ridge\":146,\"a\":51,\"owners\":[74,82,85,88]},{\"tag\":\"mate\",\"ridge\":532,\"a\":16,\"owners\":[76,84,89]},{\"tag\":\"mate\",\"ridge\":532,\"a\":35,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":532,\"a\":56,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":532,\"a\":65,\"owners\":[76,84,89]},{\"tag\":\"mate\",\"ridge\":648,\"a\":19,\"owners\":[80,86,89,90]},{\"tag\":\"mate\",\"ridge\":648,\"a\":46,\"owners\":[89,90]},{\"tag\":\"mate\",\"ridge\":648,\"a\":61,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":648,\"a\":69,\"owners\":[80,90]},{\"tag\":\"mate\",\"ridge\":648,\"a\":72,\"owners\":[80,86,89]},{\"tag\":\"mate\",\"ridge\":656,\"a\":21,\"owners\":[84,86,89]},{\"tag\":\"mate\",\"ridge\":656,\"a\":51,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":656,\"a\":66,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":656,\"a\":69,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":646,\"a\":84,\"owners\":[38,80]},{\"tag\":\"mate\",\"ridge\":538,\"a\":86,\"owners\":[41,76]},{\"tag\":\"mate\",\"ridge\":156,\"a\":89,\"owners\":[54,74]},{\"tag\":\"mate\",\"ridge\":284,\"a\":55,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":408,\"a\":68,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":792,\"a\":70,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":60,\"full_literals\":[-24,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":71,\"full_literals\":[-33,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":63,\"full_literals\":[-26,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":73,\"full_literals\":[-35,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":79,\"full_literals\":[-39,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":87,\"full_literals\":[-45,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":82,\"full_literals\":[-41,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":88,\"full_literals\":[-46,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":38,\"full_literals\":[-9,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":54,\"full_literals\":[-21,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":67,\"full_literals\":[-29,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":74,\"full_literals\":[-36,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":80,\"full_literals\":[-40,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":90,\"full_literals\":[-48,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":41,\"full_literals\":[-12,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":89,\"full_literals\":[-47,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":75,\"full_literals\":[-37,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":76,\"full_literals\":[-38,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":85,\"full_literals\":[-43,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":84,\"full_literals\":[-42,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":86,\"full_literals\":[-44,57]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-50,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-49,false,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-52,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-51,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-59,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-58,false,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-54,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-57,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-56,false,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-56,-57,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-62,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-63,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-55,false,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-55,-62,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-65,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-61,-64,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-61,-65,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-67,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-60,-66,68],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":28,\"owners\":[6,30,40,43,44,45,55,60,68,70,71,75,79,85,87]},{\"tag\":\"edge\",\"edge\":32,\"owners\":[8,21,33,39,48,49,50,51,54,63,66,68,69,73,74,82,84,85,86,88,89]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[16,21,35,41,51,56,65,66,69,70,76,84,86,89]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[19,21,38,46,51,61,66,67,69,72,80,84,86,89,90]}]}"
  "97 -67 0 92 90 0\n98 1 6 11 13 14 15 22 24 30 33 37 39 43 45 0 50 93 0\n99 3 5 8 12 20 23 27 28 31 38 42 44 47 0 50 95 0\n100 -44 60 0 50 76 75 55 56 21 77 73 52 51 8 9 10 11 18 14 15 16 17 98 0\n101 61 44 0 43 38 78 79 62 63 64 59 60 61 39 45 47 37 42 41 36 40 96 0\n102 -21 60 0 50 76 75 55 56 21 77 73 52 51 1 2 3 6 18 14 15 16 17 98 0\n103 37 43 60 0 49 76 75 56 20 55 21 77 73 52 51 48 24 19 22 23 98 0\n104 43 42 60 0 76 74 58 57 27 44 102 100 43 77 72 54 53 26 49 103 4 12 30 25 28 29 31 41 94 0\n105 42 60 0 100 43 34 44 104 5 7 13 32 35 33 42 41 99 0\n106 60 0 97 100 101 89 84 105 70 82 67 69 103 0\n107 -66 0 106 92 91 0\n108 -65 0 107 87 0\n109 -63 0 108 84 0\n110 44 0 107 43 101 88 83 85 80 81 65 66 70 68 33 42 41 34 44 32 35 99 0\n111 57 0 110 71 0\n112 62 0 111 80 0\n113 -56 0 111 109 82 0\n114 -55 0 112 108 86 0\n115 -38 0 113 68 0\n116 -12 0 114 65 0\n117 0 115 116 110 46 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record011.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record011.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record011.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record011.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record011 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record011.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record011.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record011.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record011.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record011 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record011_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record011 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record011_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record011_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record011

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record012
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "f4a72aa5ab1aa6a96558b61da8e538ae1ba1e4789e3c6a95a719a659939695554d52d475a354d1b61d4749da8d63c4e9394cb31cf0ba2d4b8ad2b2ac6b86d1b26e8751ca785d1725c3783d0f23c4f07cac548661582ea4551a24a929465254552342d50c6384d1314e0b42c2b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db4d36936da6d34924934da6924d24924926d2492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record012 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record012 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record012.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record012.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record012.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 60), (facetIndex 71)]))
 (.leaf ([(facetIndex 50), (facetIndex 73)])))
 (.branch 3
 (.leaf ([(facetIndex 79), (facetIndex 87)]))
 (.leaf ([(facetIndex 82), (facetIndex 90)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 38), (facetIndex 39), (facetIndex 55)]))
 (.leaf ([(facetIndex 74), (facetIndex 80), (facetIndex 88)])))
 (.branch 7
 (.leaf ([(facetIndex 57), (facetIndex 58), (facetIndex 68), (facetIndex 70), (facetIndex 85)]))
 (.branch 8
 (.leaf ([(facetIndex 75), (facetIndex 76), (facetIndex 86)]))
 (.leaf ([(facetIndex 84), (facetIndex 89)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "38527680305200775100606000000000660400001000000000044z26;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record012 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record012_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record012" "{\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record012" 63

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record012" "{\"ridges\":[[5,265],[9,530],[15,148],[21,656],[30,265],[33,148],[35,530],[40,266],[41,530],[44,265],[46,265],[48,265],[51,530],[52,656],[53,530],[56,148],[57,284],[58,540],[63,148],[64,148],[66,148],[66,656],[68,408],[69,648],[69,656],[70,792],[75,284],[76,540],[84,646],[85,154],[86,792],[89,540]],\"owners\":[[5,265,[57,60,68,70,71],[30,40,44,46,48]],[30,265,[68,70,71],[5,40,44,46,48,57,60]],[44,265,[57,60,68,70],[5,30,40,46,48,71]],[46,265,[57,68,70],[5,30,40,44,48,60,71]],[48,265,[57,60,68,71],[5,30,40,44,46,70]],[40,266,[79,87],[5,30,44,46,48,75,86]],[9,530,[76,84,85,86],[35,41,51,52,53]],[35,530,[85,86],[9,41,51,52,53,76,84]],[41,530,[84],[9,35,51,52,53,76,85,86]],[51,530,[76,84,85,86],[9,35,41,52,53]],[53,530,[76,84,85],[9,35,41,51,52,86]],[15,148,[74,82,84,89,90],[33,56,63,64,66]],[33,148,[89,90],[15,56,63,64,66,74,82,84]],[56,148,[82,84,90],[15,33,63,64,66,74,89]],[63,148,[74,84,89],[15,33,56,64,66,82,90]],[64,148,[74,82,84,89],[15,33,56,63,66,90]],[66,148,[74,82,90],[15,33,56,63,64,84,89]],[69,648,[80,88],[19,47,61,72,85,89]],[21,656,[84,85,89],[52,66,69]],[52,656,[89],[21,66,69,84,85]],[66,656,[85],[21,52,69,84,89]],[69,656,[84],[21,52,66,85,89]],[84,646,[38,80],[]],[85,154,[39,74],[]],[57,284,[75],[]],[75,284,[57],[]],[58,540,[76,89],[]],[76,540,[58,89],[]],[89,540,[58,76],[]],[68,408,[],[]],[70,792,[86],[]],[86,792,[70],[]]],\"edges\":[[28,[5,30,40,44,46,48,57,60,68,70,71,75,79,86,87]],[32,[15,21,33,39,50,52,56,63,64,66,68,69,73,74,82,84,85,89,90]],[34,[9,21,35,41,51,52,53,58,66,69,70,76,84,85,86,89]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record012" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record012\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-42,-20],[-42,-28],[-42,-32],[-42,-39],[-1,20,22,26,28,29],[-5,26,28,29],[-12,20,22,26,28],[-13,20,26,28],[-14,20,22,26,29],[-10,34,40],[-2,33,37,38,39],[-7,38,39],[-11,37],[-16,33,37,38,39],[-18,33,37,38],[-3,31,36,37,42,43],[-6,42,43],[-19,36,37,43],[-23,31,37,42],[-24,31,36,37,42],[-25,31,36,43],[-27,35,41],[-4,37,38,42],[-17,42],[-25,38],[-27,37],[-37,8,35],[-38,9,31],[-20,32],[-32,20],[-21,33,42],[-33,21,42],[-42,21,33],[-26],[-28,39],[-39,28],[-22,44],[-29,44],[-15,45],[-30,45],[-34,46],[-40,46],[-36,47],[-43,47],[-8,48],[-9,48],[-31,49],[-35,49],[-41,49],[-50,20,21,26,28,38],[-20,50],[-21,50],[-28,50],[-38,50],[-51,32,33,39],[-32,51],[-33,51],[-39,51],[-52,37,42],[-37,52],[-42,52],[-45,53],[-44,53],[-47,54],[-46,54],[-54,55],[-53,55],[-49,56],[-48,56],[-57,51,52],[-52,57],[-51,57],[-51,-52,58],[-59,50,57],[-57,59],[-58,60],[-50,59],[-50,-57,60],[-60,61],[-56,-59,61],[-56,-60,62],[-62,63],[-55,-61,63],[-63],[1,5,10,12,13,14,20,22,26,28,29,32,34,39,40],[3,4,6,9,15,17,19,23,24,25,26,27,30,31,36,37,38,42,43],[2,4,7,11,16,17,18,21,25,27,28,33,37,38,39,42]],\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":89,\"b\":57},{\"tag\":\"incompatible\",\"a\":89,\"b\":70},{\"tag\":\"incompatible\",\"a\":89,\"b\":75},{\"tag\":\"incompatible\",\"a\":89,\"b\":86},{\"tag\":\"mate\",\"ridge\":265,\"a\":5,\"owners\":[57,60,68,70,71]},{\"tag\":\"mate\",\"ridge\":265,\"a\":30,\"owners\":[68,70,71]},{\"tag\":\"mate\",\"ridge\":265,\"a\":44,\"owners\":[57,60,68,70]},{\"tag\":\"mate\",\"ridge\":265,\"a\":46,\"owners\":[57,68,70]},{\"tag\":\"mate\",\"ridge\":265,\"a\":48,\"owners\":[57,60,68,71]},{\"tag\":\"mate\",\"ridge\":266,\"a\":40,\"owners\":[79,87]},{\"tag\":\"mate\",\"ridge\":530,\"a\":9,\"owners\":[76,84,85,86]},{\"tag\":\"mate\",\"ridge\":530,\"a\":35,\"owners\":[85,86]},{\"tag\":\"mate\",\"ridge\":530,\"a\":41,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":530,\"a\":51,\"owners\":[76,84,85,86]},{\"tag\":\"mate\",\"ridge\":530,\"a\":53,\"owners\":[76,84,85]},{\"tag\":\"mate\",\"ridge\":148,\"a\":15,\"owners\":[74,82,84,89,90]},{\"tag\":\"mate\",\"ridge\":148,\"a\":33,\"owners\":[89,90]},{\"tag\":\"mate\",\"ridge\":148,\"a\":56,\"owners\":[82,84,90]},{\"tag\":\"mate\",\"ridge\":148,\"a\":63,\"owners\":[74,84,89]},{\"tag\":\"mate\",\"ridge\":148,\"a\":64,\"owners\":[74,82,84,89]},{\"tag\":\"mate\",\"ridge\":148,\"a\":66,\"owners\":[74,82,90]},{\"tag\":\"mate\",\"ridge\":648,\"a\":69,\"owners\":[80,88]},{\"tag\":\"mate\",\"ridge\":656,\"a\":21,\"owners\":[84,85,89]},{\"tag\":\"mate\",\"ridge\":656,\"a\":52,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":656,\"a\":66,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":656,\"a\":69,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":646,\"a\":84,\"owners\":[38,80]},{\"tag\":\"mate\",\"ridge\":154,\"a\":85,\"owners\":[39,74]},{\"tag\":\"mate\",\"ridge\":284,\"a\":57,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":284,\"a\":75,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":540,\"a\":58,\"owners\":[76,89]},{\"tag\":\"mate\",\"ridge\":540,\"a\":76,\"owners\":[58,89]},{\"tag\":\"mate\",\"ridge\":540,\"a\":89,\"owners\":[58,76]},{\"tag\":\"mate\",\"ridge\":408,\"a\":68,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":792,\"a\":70,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":792,\"a\":86,\"owners\":[70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":60,\"full_literals\":[-22,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":71,\"full_literals\":[-29,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":50,\"full_literals\":[-15,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":73,\"full_literals\":[-30,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":79,\"full_literals\":[-34,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":87,\"full_literals\":[-40,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":82,\"full_literals\":[-36,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":90,\"full_literals\":[-43,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":38,\"full_literals\":[-8,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":39,\"full_literals\":[-9,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":74,\"full_literals\":[-31,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":80,\"full_literals\":[-35,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":88,\"full_literals\":[-41,49]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[57,58,68,70,85],\"full_literals\":[-50,20,21,26,28,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":57,\"full_literals\":[-20,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":58,\"full_literals\":[-21,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":70,\"full_literals\":[-28,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":85,\"full_literals\":[-38,50]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[75,76,86],\"full_literals\":[-51,32,33,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":75,\"full_literals\":[-32,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":76,\"full_literals\":[-33,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":86,\"full_literals\":[-39,51]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[84,89],\"full_literals\":[-52,37,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":84,\"full_literals\":[-37,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":89,\"full_literals\":[-42,52]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-45,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-47,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-54,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-49,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-48,false,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-57,51,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-52,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-51,false,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-51,-52,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-59,50,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-57,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-58,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-50,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-50,-57,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-60,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-56,-59,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-56,-60,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-62,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-55,-61,63],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":28,\"owners\":[5,30,40,44,46,48,57,60,68,70,71,75,79,86,87]},{\"tag\":\"edge\",\"edge\":32,\"owners\":[15,21,33,39,50,52,56,63,64,66,68,69,73,74,82,84,85,89,90]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[9,21,35,41,51,52,53,58,66,69,70,76,84,85,86,89]}]}"
  "88 -50 20 21 28 38 0 34 50 0\n89 -62 0 84 82 0\n90 1 5 10 12 13 14 20 22 28 29 32 34 39 40 0 34 85 0\n91 3 4 6 9 15 17 19 23 24 25 27 30 31 36 37 38 42 43 0 34 86 0\n92 -42 55 0 34 66 65 41 42 10 67 63 38 37 1 2 3 4 8 9 6 7 5 90 0\n93 56 55 0 92 24 66 64 44 17 67 62 40 39 43 68 69 47 48 49 45 46 21 28 22 27 18 23 19 20 16 91 0\n94 20 28 55 0 34 36 67 63 38 6 66 65 41 42 10 37 8 9 30 7 5 90 0\n95 -20 60 0 29 51 56 78 72 0\n96 55 0 89 93 81 95 94 35 53 58 78 72 0\n97 -61 0 96 84 83 0\n98 -60 0 97 79 0\n99 -58 0 98 76 0\n100 -20 0 98 95 0\n101 -32 0 100 30 0\n102 -28 0 98 35 53 58 78 72 0\n103 -39 0 102 36 0\n104 59 0 103 102 75 77 71 72 52 54 60 61 57 25 12 13 26 23 15 11 14 24 87 0\n105 -56 0 104 97 80 0\n106 -49 0 105 68 0\n107 -48 0 105 69 0\n108 -31 0 106 47 0\n109 -35 0 106 48 0\n110 -8 0 107 45 0\n111 -9 0 107 46 0\n112 -38 0 108 111 28 0\n113 -37 0 109 110 27 0\n114 51 50 0 104 113 74 52 57 70 33 59 0\n115 50 0 99 103 101 52 114 73 55 61 32 0\n116 -57 0 115 98 78 0\n117 21 0 115 102 100 112 88 0\n118 -52 0 116 71 0\n119 -51 0 116 72 0\n120 -42 0 118 61 0\n121 -33 0 119 57 0\n122 0 121 120 117 31 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record012.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record012.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record012.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record012.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record012 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record012.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record012.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record012.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record012.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record012 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record012_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record012 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record012_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record012_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record012

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record014
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2aca72aaa6a5aa9966c5a96558b61da8e53a2e2b86e8789e178f13a69936565a5595554b51d68d5346d8749d17563a4cb31ce8b52cab86c9b16e8751d2729c6785c9715c3783d0f23c4f07e94a30ac5486a859168382e544a91a4a5454952342d50c6344c5312c2b41c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "936db49369a4936d36d249a69a69b4d26d3492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record014 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record014 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record014.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record014.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record014.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 44), (facetIndex 54), (facetIndex 65)]))
 (.leaf ([(facetIndex 52), (facetIndex 56), (facetIndex 85), (facetIndex 86)])))
 (.branch 3
 (.leaf ([(facetIndex 28), (facetIndex 33), (facetIndex 36), (facetIndex 39), (facetIndex 41), (facetIndex 45), (facetIndex 47), (facetIndex 50)]))
 (.leaf ([(facetIndex 35), (facetIndex 69), (facetIndex 78), (facetIndex 79)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 34), (facetIndex 58), (facetIndex 60), (facetIndex 61)]))
 (.leaf ([(facetIndex 59), (facetIndex 70), (facetIndex 77)])))
 (.branch 7
 (.leaf ([(facetIndex 27), (facetIndex 29), (facetIndex 30), (facetIndex 32), (facetIndex 37), (facetIndex 38)]))
 (.leaf ([(facetIndex 31), (facetIndex 71), (facetIndex 72), (facetIndex 74)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "480006e81c7f58000024b010010804100105b2716fb2cz14;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 48), (facetIndex 57), (facetIndex 66)]))
 (.leaf ([(facetIndex 51), (facetIndex 55), (facetIndex 62), (facetIndex 75)])))
 (.branch 3
 (.leaf ([(facetIndex 67), (facetIndex 73), (facetIndex 80)]))
 (.leaf ([(facetIndex 40), (facetIndex 42), (facetIndex 76), (facetIndex 81)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 46), (facetIndex 68), (facetIndex 84)]))
 (.leaf ([(facetIndex 43), (facetIndex 63), (facetIndex 82), (facetIndex 83)])))
 (.branch 7
 (.leaf ([(facetIndex 49), (facetIndex 53)]))
 (.leaf ([(facetIndex 64)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "4b5a003210004407a40000230230100ac3z1e;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [4]
def grouped2_0009 : List Nat := [4, 5]
def grouped2_0010 : List Nat := [4, 5, 6, 7]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7]
def grouped2_0014 : List Nat := [7]
def grouped3_0015 : List Nat := [0]
def grouped3_0016 : List Nat := [0, 1]
def grouped3_0017 : List Nat := [0, 1, 2, 3]
def grouped3_0019 : List Nat := [1]
def grouped3_0020 : List Nat := [2]
def grouped3_0021 : List Nat := [2, 3]
def grouped3_0022 : List Nat := [3]
def grouped3_0023 : List Nat := [4]
def grouped3_0024 : List Nat := [4, 5]
def grouped3_0025 : List Nat := [4, 5, 6, 7]
def grouped3_0026 : List Nat := [5]
def grouped3_0027 : List Nat := [6]
def grouped3_0028 : List Nat := [6, 7]
def grouped3_0029 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record014 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record014_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record014" "{\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record014" 88

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record014" "{\"ridges\":[[14,164],[16,137],[26,656],[34,145],[35,530],[42,137],[46,137],[49,643],[52,137],[56,137],[58,145],[60,145],[61,145],[61,656],[63,216],[65,97],[65,137],[66,240],[69,530],[72,522],[74,648],[78,656],[79,532],[82,600],[83,154],[85,656],[86,644]],\"owners\":[[65,97,[8,36,47,50,57,62],[15,54,66]],[34,145,[63,64,66],[12,42,48,49,52,58,60,61]],[58,145,[42,49,63,64],[12,34,48,52,60,61,66]],[60,145,[42,48,49,63,64,66],[12,34,52,58,61]],[61,145,[42,48,63,66],[12,34,49,52,58,60,64]],[14,164,[24,71,76,81,86],[37,58]],[72,522,[43,46,82,83],[19,31,69,74,84]],[35,530,[82,83],[21,43,49,69,78,79]],[69,530,[49],[21,35,43,78,79,82,83]],[79,532,[26,53,61,85],[21,35,69]],[86,644,[26,40,61,78],[25,56,74,81]],[74,648,[64],[25,46,56,83,84,85,86]],[26,656,[49,64,83],[61,78,85]],[61,656,[83],[26,49,64,78,85]],[78,656,[64],[26,49,61,83,85]],[85,656,[49],[26,61,64,78,83]],[49,643,[40,46],[]],[83,154,[42,68],[]],[63,216,[],[]],[66,240,[],[]],[82,600,[],[]]],\"edges\":[[36,[14,16,24,37,44,48,58,65,66,71,76,81,84,86]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record014" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record014\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-10,-9],[-11,-10],[-17,-10],[-17,-15],[-18,-17],[-24,-1],[-25,-7],[-28,-8],[-28,-10],[-28,-12],[-28,-14],[-28,-16],[-28,-22],[-28,-23],[-29,-17],[-31,-19],[-31,-30],[-33,-4],[-33,-28],[-33,-31],[-35,-26],[-35,-33],[-36,-32],[-37,-36],[-41,-10],[-41,-30],[-41,-33],[-47,-28],[-48,-6],[-48,-9],[-48,-45],[-48,-46],[-53,-11],[-53,-51],[-56,-6],[-56,-8],[-56,-16],[-56,-23],[-56,-27],[-56,-30],[-56,-47],[-56,-50],[-56,-54],[-57,-56],[-58,-20],[-58,-41],[-58,-56],[-59,-47],[-59,-48],[-59,-49],[-42,1,15,26,29,34,39],[-3,-21,-33],[-21,-33,-42],[-25,-30,-42],[-13,40,41,43],[-35,21,28,40,41],[-37,21,27,28,40,41,43],[-38,21,27,40,43],[-2,4,47,50,54,59],[-48,22,25,55,56],[-14,55,56],[-45,28],[-53,5,31,38,58],[-59,5,19,38,52],[-49,41],[-5,28,41,56],[-38,56],[-52,41],[-58,28],[-28,19,25],[-56,21,44],[-40],[-43],[-55],[-60,23,32,42],[-61,30,33,58,59],[-62,7,12,15,18,20,24,26,29],[-63,14,45,52,53],[-64,13,35,37,38],[-65,36,46,51],[-66,6,8,9,11,16,17],[-67,10,47,48,49],[-68,60],[-68,61],[-69,62],[-69,63],[-70,68],[-70,69],[-71,64],[-71,65],[-72,66],[-72,67],[-73,71],[-73,72],[-74,70],[-74,73],[74],[-27,75],[-34,75],[-39,76],[-19,77],[-21,77],[-25,78],[-44,78],[-56,79],[-28,80],[-76,81],[-75,81],[-77,82],[-82,83],[-81,83],[-78,84],[-78,-79,85],[-80,86],[-84,-86,87],[-85,87],[-83,-87,88],[-88],[2,3,4,16,23,27,35,42,43,47,50,54,57,59]],\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":31,\"b\":30},{\"tag\":\"incompatible\",\"a\":32,\"b\":31},{\"tag\":\"incompatible\",\"a\":38,\"b\":31},{\"tag\":\"incompatible\",\"a\":38,\"b\":36},{\"tag\":\"incompatible\",\"a\":39,\"b\":38},{\"tag\":\"incompatible\",\"a\":45,\"b\":8},{\"tag\":\"incompatible\",\"a\":46,\"b\":28},{\"tag\":\"incompatible\",\"a\":49,\"b\":29},{\"tag\":\"incompatible\",\"a\":49,\"b\":31},{\"tag\":\"incompatible\",\"a\":49,\"b\":33},{\"tag\":\"incompatible\",\"a\":49,\"b\":35},{\"tag\":\"incompatible\",\"a\":49,\"b\":37},{\"tag\":\"incompatible\",\"a\":49,\"b\":43},{\"tag\":\"incompatible\",\"a\":49,\"b\":44},{\"tag\":\"incompatible\",\"a\":50,\"b\":38},{\"tag\":\"incompatible\",\"a\":53,\"b\":40},{\"tag\":\"incompatible\",\"a\":53,\"b\":52},{\"tag\":\"incompatible\",\"a\":56,\"b\":24},{\"tag\":\"incompatible\",\"a\":56,\"b\":49},{\"tag\":\"incompatible\",\"a\":56,\"b\":53},{\"tag\":\"incompatible\",\"a\":58,\"b\":47},{\"tag\":\"incompatible\",\"a\":58,\"b\":56},{\"tag\":\"incompatible\",\"a\":59,\"b\":54},{\"tag\":\"incompatible\",\"a\":60,\"b\":59},{\"tag\":\"incompatible\",\"a\":64,\"b\":31},{\"tag\":\"incompatible\",\"a\":64,\"b\":52},{\"tag\":\"incompatible\",\"a\":64,\"b\":56},{\"tag\":\"incompatible\",\"a\":71,\"b\":49},{\"tag\":\"incompatible\",\"a\":72,\"b\":27},{\"tag\":\"incompatible\",\"a\":72,\"b\":30},{\"tag\":\"incompatible\",\"a\":72,\"b\":69},{\"tag\":\"incompatible\",\"a\":72,\"b\":70},{\"tag\":\"incompatible\",\"a\":79,\"b\":32},{\"tag\":\"incompatible\",\"a\":79,\"b\":77},{\"tag\":\"incompatible\",\"a\":83,\"b\":27},{\"tag\":\"incompatible\",\"a\":83,\"b\":29},{\"tag\":\"incompatible\",\"a\":83,\"b\":37},{\"tag\":\"incompatible\",\"a\":83,\"b\":44},{\"tag\":\"incompatible\",\"a\":83,\"b\":48},{\"tag\":\"incompatible\",\"a\":83,\"b\":52},{\"tag\":\"incompatible\",\"a\":83,\"b\":71},{\"tag\":\"incompatible\",\"a\":83,\"b\":76},{\"tag\":\"incompatible\",\"a\":83,\"b\":81},{\"tag\":\"incompatible\",\"a\":84,\"b\":83},{\"tag\":\"incompatible\",\"a\":85,\"b\":41},{\"tag\":\"incompatible\",\"a\":85,\"b\":64},{\"tag\":\"incompatible\",\"a\":85,\"b\":83},{\"tag\":\"incompatible\",\"a\":86,\"b\":71},{\"tag\":\"incompatible\",\"a\":86,\"b\":72},{\"tag\":\"incompatible\",\"a\":86,\"b\":74},{\"tag\":\"mate\",\"ridge\":97,\"a\":65,\"owners\":[8,36,47,50,57,62]},{\"tag\":\"three\",\"ridge\":137,\"vertices\":[16,42,56]},{\"tag\":\"three\",\"ridge\":137,\"vertices\":[42,56,65]},{\"tag\":\"three\",\"ridge\":137,\"vertices\":[46,52,65]},{\"tag\":\"mate\",\"ridge\":145,\"a\":34,\"owners\":[63,64,66]},{\"tag\":\"mate\",\"ridge\":145,\"a\":58,\"owners\":[42,49,63,64]},{\"tag\":\"mate\",\"ridge\":145,\"a\":60,\"owners\":[42,48,49,63,64,66]},{\"tag\":\"mate\",\"ridge\":145,\"a\":61,\"owners\":[42,48,63,66]},{\"tag\":\"mate\",\"ridge\":164,\"a\":14,\"owners\":[24,71,76,81,86]},{\"tag\":\"mate\",\"ridge\":522,\"a\":72,\"owners\":[43,46,82,83]},{\"tag\":\"mate\",\"ridge\":530,\"a\":35,\"owners\":[82,83]},{\"tag\":\"mate\",\"ridge\":530,\"a\":69,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":532,\"a\":79,\"owners\":[26,53,61,85]},{\"tag\":\"mate\",\"ridge\":644,\"a\":86,\"owners\":[26,40,61,78]},{\"tag\":\"mate\",\"ridge\":648,\"a\":74,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":656,\"a\":26,\"owners\":[49,64,83]},{\"tag\":\"mate\",\"ridge\":656,\"a\":61,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":656,\"a\":78,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":656,\"a\":85,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":643,\"a\":49,\"owners\":[40,46]},{\"tag\":\"mate\",\"ridge\":154,\"a\":83,\"owners\":[42,68]},{\"tag\":\"mate\",\"ridge\":216,\"a\":63,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":240,\"a\":66,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":600,\"a\":82,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[44,54,65],\"full_literals\":[-60,23,32,42]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[52,56,85,86],\"full_literals\":[-61,30,33,58,59]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[28,33,36,39,41,45,47,50],\"full_literals\":[-62,7,12,15,18,20,24,26,29]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[35,69,78,79],\"full_literals\":[-63,14,45,52,53]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[34,58,60,61],\"full_literals\":[-64,13,35,37,38]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[59,70,77],\"full_literals\":[-65,36,46,51]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[27,29,30,32,37,38],\"full_literals\":[-66,6,8,9,11,16,17]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[31,71,72,74],\"full_literals\":[-67,10,47,48,49]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-68,60,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-68,false,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-69,62,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-69,false,63],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-70,68,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-70,false,69],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-71,64,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-71,false,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-72,66,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-72,false,67],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-73,71,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-73,false,72],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-74,70,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-74,false,73],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":48,\"full_literals\":[-27,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":57,\"full_literals\":[-34,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":62,\"full_literals\":[-39,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":40,\"full_literals\":[-19,77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":42,\"full_literals\":[-21,77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":46,\"full_literals\":[-25,78]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":68,\"full_literals\":[-44,78]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":83,\"full_literals\":[-56,79]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":49,\"full_literals\":[-28,80]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-76,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-75,false,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-77,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-82,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-81,false,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-78,false,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-78,-79,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-80,false,86],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-84,-86,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-85,false,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-83,-87,88],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":36,\"owners\":[14,16,24,37,44,48,58,65,66,71,76,81,84,86]}]}"
  "120 70 0 97 95 0\n121 73 0 97 96 0\n122 68 0 120 87 0\n123 69 0 120 88 0\n124 71 0 121 93 0\n125 72 0 121 94 0\n126 60 0 122 83 0\n127 61 0 122 84 0\n128 62 0 123 85 0\n129 63 0 123 86 0\n130 64 0 124 89 0\n131 65 0 124 90 0\n132 66 0 125 91 0\n133 67 0 125 92 0\n134 2 3 4 16 23 27 35 42 47 50 54 57 59 0 73 119 0\n135 -41 0 127 133 25 26 27 46 76 48 49 50 82 0\n136 -49 0 135 65 0\n137 -52 0 135 68 0\n138 -13 0 135 72 73 55 0\n139 28 83 0 73 72 135 138 130 110 109 102 111 108 98 58 56 57 79 0\n140 83 0 73 72 136 133 137 129 132 131 126 138 130 127 128 110 111 109 107 108 101 102 100 98 99 58 139 8 9 10 11 12 14 19 28 70 82 7 29 30 31 32 49 78 33 34 81 80 4 5 15 23 24 75 79 54 21 76 51 45 6 77 0\n141 -87 0 140 118 117 0\n142 -85 0 141 116 0\n143 -28 56 0 136 133 74 141 9 13 28 106 82 114 60 115 103 112 0\n144 5 -53 58 38 0 127 137 63 16 17 20 64 76 0\n145 56 0 74 135 137 129 67 61 143 62 69 66 78 144 0\n146 -6 0 145 35 0\n147 -8 0 145 36 0\n148 -16 0 145 37 0\n149 -23 0 145 38 0\n150 -27 0 145 39 0\n151 -30 0 145 40 0\n152 -47 0 145 41 0\n153 -50 0 145 42 0\n154 -54 0 145 43 0\n155 -57 0 145 44 0\n156 -58 0 145 47 0\n157 79 0 145 105 0\n158 -78 0 157 142 113 0\n159 -44 0 158 104 0\n160 21 0 159 145 71 0\n161 59 0 151 156 127 160 155 154 153 152 150 149 148 76 18 22 53 52 59 134 0\n162 -48 0 161 49 0\n163 10 0 162 133 136 152 82 0\n164 -9 0 163 1 0\n165 -11 0 163 2 0\n166 -17 0 163 3 0\n167 0 166 164 132 148 165 146 147 81 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record014.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record014.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record014.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record014.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record014 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record014.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record014.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record014.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record014.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record014 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record014_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record014_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record014_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record014_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record014_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record014_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record014_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record014 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record014_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record014_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record014_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record014

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record015
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2aca70f23aa9a36966a59562d876a394e2b86e8789e178f1aa4e9a6659366a559715a55552d475a354d8b4ad1b61d2745d58ce3a4d9334cb31ce8b52ccb86c9b16e8751d2729c6785c9715c3783d0f23c4f07d522a86a4582ea4551a24a91a6154560d0b54328c6344c9314c8b12c2b41c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36d36da6db49b6d24db6926d34926d2492492693492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record015 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record015 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record015.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record015.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record015.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 78), (facetIndex 79), (facetIndex 89)]))
 (.leaf ([(facetIndex 35), (facetIndex 56), (facetIndex 65), (facetIndex 66)])))
 (.branch 3
 (.leaf ([(facetIndex 28), (facetIndex 33), (facetIndex 36), (facetIndex 39), (facetIndex 57), (facetIndex 64), (facetIndex 84)]))
 (.leaf ([(facetIndex 46), (facetIndex 61), (facetIndex 71), (facetIndex 73)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 58), (facetIndex 59), (facetIndex 72)]))
 (.leaf ([(facetIndex 41), (facetIndex 44), (facetIndex 45), (facetIndex 47), (facetIndex 49), (facetIndex 52), (facetIndex 53)])))
 (.branch 7
 (.leaf ([(facetIndex 27), (facetIndex 29), (facetIndex 30), (facetIndex 31), (facetIndex 32), (facetIndex 38)]))
 (.branch 8
 (.leaf ([(facetIndex 34), (facetIndex 42), (facetIndex 48), (facetIndex 50), (facetIndex 51)]))
 (.leaf ([(facetIndex 37)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "2000000000034300001120030442100557757535507502682172666626z1b;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 54), (facetIndex 60), (facetIndex 62), (facetIndex 67)]))
 (.leaf ([(facetIndex 63), (facetIndex 74), (facetIndex 82)])))
 (.branch 3
 (.leaf ([(facetIndex 75), (facetIndex 80), (facetIndex 86)]))
 (.leaf ([(facetIndex 69), (facetIndex 90)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 40), (facetIndex 55), (facetIndex 68), (facetIndex 83)]))
 (.leaf ([(facetIndex 76), (facetIndex 81), (facetIndex 92)])))
 (.branch 7
 (.leaf ([(facetIndex 43), (facetIndex 70), (facetIndex 87), (facetIndex 91)]))
 (.branch 8
 (.leaf ([(facetIndex 77), (facetIndex 85)]))
 (.leaf ([(facetIndex 88)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "56308627041520075210006340000100000004000000000006004z28;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [4]
def grouped2_0009 : List Nat := [4, 5]
def grouped2_0010 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7, 8]
def grouped2_0014 : List Nat := [7]
def grouped2_0015 : List Nat := [7, 8]
def grouped2_0016 : List Nat := [8]
def grouped3_0017 : List Nat := [0]
def grouped3_0018 : List Nat := [0, 1]
def grouped3_0019 : List Nat := [0, 1, 2, 3]
def grouped3_0021 : List Nat := [1]
def grouped3_0022 : List Nat := [2]
def grouped3_0023 : List Nat := [2, 3]
def grouped3_0024 : List Nat := [3]
def grouped3_0025 : List Nat := [4]
def grouped3_0026 : List Nat := [4, 5]
def grouped3_0027 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0028 : List Nat := [5]
def grouped3_0029 : List Nat := [6]
def grouped3_0030 : List Nat := [6, 7, 8]
def grouped3_0031 : List Nat := [7]
def grouped3_0032 : List Nat := [7, 8]
def grouped3_0033 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record015 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record015_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record015" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0032\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0030\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0027\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record015" 77

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record015" "{\"ridges\":[[10,98],[11,162],[17,104],[18,168],[31,524],[36,98],[46,648],[47,98],[48,162],[52,98],[52,162],[53,98],[59,44],[68,676],[71,648],[71,656],[78,44],[78,98],[78,104],[79,44],[83,180],[89,98],[89,104],[91,156],[92,676]],\"owners\":[[10,98,[24,78,82,86,89,90],[36,47,52,53]],[36,98,[24,89,90],[10,47,52,53,78,82,86]],[47,98,[24,78,86,89],[10,36,52,53,82,90]],[52,98,[24,78,82,86],[10,36,47,53,89,90]],[53,98,[24,78,82,89,90],[10,36,47,52,86]],[78,98,[10,47,52,53,90],[24,36,82,86,89]],[89,98,[10,36,47,53,82,86],[24,52,78,90]],[11,162,[25,79,83,89,90],[37,48,52]],[48,162,[25,79,89],[11,37,52,83,90]],[52,162,[25,79,83],[11,37,48,89,90]],[59,44,[22,78,79],[13,57,58,92]],[78,44,[13,58,59,92],[22,57,79]],[79,44,[13,57,59],[22,58,78,92]],[31,524,[91,92],[14,56,59,61,77,81]],[17,104,[24,78,89],[57,72]],[78,104,[17,72],[24,57,89]],[89,104,[17,57],[24,72,78]],[18,168,[25,79,89,92],[58,72,73]],[46,648,[91,92],[19,61,71,73,81,88]],[71,648,[81,92],[19,46,61,73,88,91]],[71,656,[85],[21,51,65,88,91]],[91,156,[55,76],[]],[83,180,[63],[]],[68,676,[92],[]],[92,676,[68],[]]],\"edges\":[[35,[10,17,24,36,47,52,53,57,62,67,72,74,78,82,86,89,90]],[36,[11,18,25,37,48,52,58,63,68,72,73,74,79,83,89,90,92]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record015" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record015\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-15,-1],[-15,-9],[-15,-10],[-15,-11],[-15,-13],[-15,-14],[-16,-15],[-18,-15],[-20,-15],[-21,-15],[-24,-4],[-24,-23],[-25,-22],[-25,-23],[-26,-25],[-32,-3],[-32,-17],[-32,-23],[-32,-24],[-32,-25],[-33,-24],[-33,-25],[-33,-32],[-36,-8],[-37,-7],[-37,-15],[-37,-24],[-37,-36],[-43,-6],[-43,-32],[-43,-36],[-43,-37],[-45,-15],[-46,-15],[-46,-25],[-46,-26],[-46,-41],[-1,7,36,39,42,43,44],[-14,7,43,44],[-18,7,36,42,43],[-20,7,36,39,42],[-21,7,36,39,43,44],[-36,1,18,20,21,44],[-43,1,14,18,21,39,42],[-2,8,37,40,43,44],[-19,8,37,43],[-20,8,37,40],[-25,6,36,37],[-36,3,24,25,46],[-37,3,23,25],[-12,45,46],[-4,7,36,43],[-36,4,32],[-43,4,23],[-5,8,37,43,46],[-17,45,46],[-31,38,46],[-31,41],[-45,22,35],[-40,28],[-30,46],[-46,30],[-47,36,37,43],[-48,17,26,31,33],[-49,24,25,32],[-50,9,10,11,12,13,16],[-51,15],[-52,47],[-53,48],[-54,52],[-54,53],[-55,49],[-56,51],[-57,50],[-57,56],[-58,55,57],[-59,57],[-60,54,59],[-60,58],[60],[-27,61],[-29,61],[-28,62],[-34,62],[-39,62],[-42,63],[-44,64],[-30,65],[-35,66],[-38,66],[-46,66],[-45,67],[-41,68],[-62,69],[-61,69],[-64,70],[-63,70],[-70,71],[-69,71],[-66,72],[-65,-66,73],[-68,74],[-74,75],[-67,75],[-72,-75,76],[-73,76],[-71,-76,77],[-77],[1,4,7,14,18,20,21,23,27,29,32,34,36,39,42,43,44],[2,5,8,15,19,20,24,28,30,32,33,34,37,40,43,44,46]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":37,\"b\":10},{\"tag\":\"incompatible\",\"a\":37,\"b\":27},{\"tag\":\"incompatible\",\"a\":37,\"b\":29},{\"tag\":\"incompatible\",\"a\":37,\"b\":30},{\"tag\":\"incompatible\",\"a\":37,\"b\":32},{\"tag\":\"incompatible\",\"a\":37,\"b\":36},{\"tag\":\"incompatible\",\"a\":38,\"b\":37},{\"tag\":\"incompatible\",\"a\":47,\"b\":37},{\"tag\":\"incompatible\",\"a\":52,\"b\":37},{\"tag\":\"incompatible\",\"a\":53,\"b\":37},{\"tag\":\"incompatible\",\"a\":58,\"b\":17},{\"tag\":\"incompatible\",\"a\":58,\"b\":57},{\"tag\":\"incompatible\",\"a\":59,\"b\":55},{\"tag\":\"incompatible\",\"a\":59,\"b\":57},{\"tag\":\"incompatible\",\"a\":61,\"b\":59},{\"tag\":\"incompatible\",\"a\":72,\"b\":13},{\"tag\":\"incompatible\",\"a\":72,\"b\":46},{\"tag\":\"incompatible\",\"a\":72,\"b\":57},{\"tag\":\"incompatible\",\"a\":72,\"b\":58},{\"tag\":\"incompatible\",\"a\":72,\"b\":59},{\"tag\":\"incompatible\",\"a\":73,\"b\":58},{\"tag\":\"incompatible\",\"a\":73,\"b\":59},{\"tag\":\"incompatible\",\"a\":73,\"b\":72},{\"tag\":\"incompatible\",\"a\":78,\"b\":25},{\"tag\":\"incompatible\",\"a\":79,\"b\":24},{\"tag\":\"incompatible\",\"a\":79,\"b\":37},{\"tag\":\"incompatible\",\"a\":79,\"b\":58},{\"tag\":\"incompatible\",\"a\":79,\"b\":78},{\"tag\":\"incompatible\",\"a\":89,\"b\":22},{\"tag\":\"incompatible\",\"a\":89,\"b\":72},{\"tag\":\"incompatible\",\"a\":89,\"b\":78},{\"tag\":\"incompatible\",\"a\":89,\"b\":79},{\"tag\":\"incompatible\",\"a\":91,\"b\":37},{\"tag\":\"incompatible\",\"a\":92,\"b\":37},{\"tag\":\"incompatible\",\"a\":92,\"b\":59},{\"tag\":\"incompatible\",\"a\":92,\"b\":61},{\"tag\":\"incompatible\",\"a\":92,\"b\":85},{\"tag\":\"mate\",\"ridge\":98,\"a\":10,\"owners\":[24,78,82,86,89,90]},{\"tag\":\"mate\",\"ridge\":98,\"a\":36,\"owners\":[24,89,90]},{\"tag\":\"mate\",\"ridge\":98,\"a\":47,\"owners\":[24,78,86,89]},{\"tag\":\"mate\",\"ridge\":98,\"a\":52,\"owners\":[24,78,82,86]},{\"tag\":\"mate\",\"ridge\":98,\"a\":53,\"owners\":[24,78,82,89,90]},{\"tag\":\"mate\",\"ridge\":98,\"a\":78,\"owners\":[10,47,52,53,90]},{\"tag\":\"mate\",\"ridge\":98,\"a\":89,\"owners\":[10,36,47,53,82,86]},{\"tag\":\"mate\",\"ridge\":162,\"a\":11,\"owners\":[25,79,83,89,90]},{\"tag\":\"mate\",\"ridge\":162,\"a\":48,\"owners\":[25,79,89]},{\"tag\":\"mate\",\"ridge\":162,\"a\":52,\"owners\":[25,79,83]},{\"tag\":\"mate\",\"ridge\":44,\"a\":59,\"owners\":[22,78,79]},{\"tag\":\"mate\",\"ridge\":44,\"a\":78,\"owners\":[13,58,59,92]},{\"tag\":\"mate\",\"ridge\":44,\"a\":79,\"owners\":[13,57,59]},{\"tag\":\"mate\",\"ridge\":524,\"a\":31,\"owners\":[91,92]},{\"tag\":\"mate\",\"ridge\":104,\"a\":17,\"owners\":[24,78,89]},{\"tag\":\"mate\",\"ridge\":104,\"a\":78,\"owners\":[17,72]},{\"tag\":\"mate\",\"ridge\":104,\"a\":89,\"owners\":[17,57]},{\"tag\":\"mate\",\"ridge\":168,\"a\":18,\"owners\":[25,79,89,92]},{\"tag\":\"mate\",\"ridge\":648,\"a\":46,\"owners\":[91,92]},{\"tag\":\"mate\",\"ridge\":648,\"a\":71,\"owners\":[81,92]},{\"tag\":\"mate\",\"ridge\":656,\"a\":71,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":156,\"a\":91,\"owners\":[55,76]},{\"tag\":\"mate\",\"ridge\":180,\"a\":83,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":676,\"a\":68,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":676,\"a\":92,\"owners\":[68]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[78,79,89],\"full_literals\":[-47,36,37,43]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[46,61,71,73],\"full_literals\":[-48,17,26,31,33]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[58,59,72],\"full_literals\":[-49,24,25,32]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[27,29,30,31,32,38],\"full_literals\":[-50,9,10,11,12,13,16]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[37],\"full_literals\":[-51,15]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-52,47,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-53,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-54,52,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-54,false,53],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-55,49,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-56,false,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-57,50,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-57,false,56],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-58,55,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-59,false,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-60,54,59],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-60,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":62,\"full_literals\":[-27,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":67,\"full_literals\":[-29,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":63,\"full_literals\":[-28,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":74,\"full_literals\":[-34,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":82,\"full_literals\":[-39,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":86,\"full_literals\":[-42,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":90,\"full_literals\":[-44,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":68,\"full_literals\":[-30,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":76,\"full_literals\":[-35,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":81,\"full_literals\":[-38,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":92,\"full_literals\":[-46,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":91,\"full_literals\":[-45,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":85,\"full_literals\":[-41,68]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-62,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-61,false,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-64,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-70,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-69,false,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-66,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-65,-66,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0031\",\"right_name\":\"grouped3_0033\",\"joined_name\":\"grouped3_0032\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-68,false,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0032\",\"joined_name\":\"grouped3_0030\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-74,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0032\",\"joined_name\":\"grouped3_0030\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-67,false,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0026\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0027\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-72,-75,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0026\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0027\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-73,false,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-71,-76,77],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":35,\"owners\":[10,17,24,36,47,52,53,57,62,67,72,74,78,82,86,89,90]},{\"tag\":\"edge\",\"edge\":36,\"owners\":[11,18,25,37,48,52,58,63,68,72,73,74,79,83,89,90,92]}]}"
  "111 58 0 80 79 0\n112 -57 9 12 0 74 75 73 67 3 4 5 7 66 0\n113 -15 -47 71 0 99 94 85 98 97 86 96 87 1 6 8 9 10 26 43 44 63 0\n114 -33 -49 0 21 22 23 65 0\n115 25 24 46 -49 -47 0 65 16 18 30 49 50 63 0\n116 37 43 24 46 -47 71 0 111 113 67 73 75 76 72 115 20 61 114 99 94 83 60 84 98 96 87 63 24 45 46 47 55 110 0\n117 43 24 46 -47 71 0 111 113 67 73 75 76 72 115 20 14 99 95 82 81 94 85 84 98 97 86 96 87 116 25 28 38 39 40 41 42 52 109 0\n118 24 46 -47 71 0 111 113 67 73 75 76 72 115 117 29 31 32 48 0\n119 -24 -47 0 11 12 19 27 53 54 63 0\n120 -47 71 0 80 111 113 67 73 75 77 76 78 72 71 69 114 119 118 35 36 37 65 58 17 64 0\n121 -57 0 75 73 67 2 33 34 112 51 0\n122 -59 0 121 77 0\n123 55 0 121 111 76 0\n124 54 0 122 80 78 0\n125 49 0 123 72 0\n126 52 0 124 70 0\n127 53 0 124 71 0\n128 -33 0 125 114 0\n129 47 0 126 68 0\n130 48 0 127 69 0\n131 71 0 129 120 0\n132 -24 0 129 119 0\n133 -76 0 131 108 107 0\n134 -73 0 133 106 0\n135 -45 22 0 133 59 92 89 104 100 105 0\n136 -31 46 0 133 57 58 90 93 100 102 105 103 0\n137 46 0 129 125 132 128 130 115 13 15 135 56 64 136 0\n138 30 0 137 62 0\n139 66 0 137 91 0\n140 65 0 138 88 0\n141 0 140 139 134 101 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record015.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record015.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record015.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record015.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record015 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record015.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record015.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record015.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record015.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record015 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record015_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record015_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record015_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record015_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record015_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record015_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record015_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record015 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record015_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record015_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record015_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record015
