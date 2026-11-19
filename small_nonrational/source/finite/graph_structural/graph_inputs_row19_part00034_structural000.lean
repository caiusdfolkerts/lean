module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow19Part00034Data
public import GraphInputsRow19Part00034Frames
public import GraphInputsRow19Part00034Leaves
public import GraphInputsRow19Part00034Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00034.record020
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record020
def vertexColumn : Fields := ⟨10, hexnat% "9e19c570dc9a99a568da1ea6665956359362d8766394e3391e2785e9c669666598e479995954d4b51d58d4749d1766364d332cc73c2e8b62e4b8ac6b46c9b16c3b61e4789d2729c6745c9715c3743c8f13c1f1d2629286646499454950d62382d0b22d0721c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6d36da6db69b6db6d36da49349a6db4924d26d349249a49b249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨57, by decide⟩, ⟨66, by decide⟩, ⟨72, by decide⟩, ⟨77, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40200c0e300dc0000", hexnat% "20000000101800000000", hexnat% "1000000000009000000", 8444249301319680, 637534208]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [148830869540044800, hexnat% "20000000101800000000", 3377699725770752, hexnat% "1000000000009000000", hexnat% "40002000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4021cc00326d80000", 580610875719680, 962072936448, hexnat% "1000000000008000000", hexnat% "20000000000800000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [148830869544239104, hexnat% "20000000101800000000", 3940649674997760, hexnat% "1040000000001000000", 134217728]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1078045966336, hexnat% "21000000100000000000", 148829893935759360, hexnat% "40002000001100000", 771751936, 3377699724722176]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨18, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨19, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c7 c0
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c8 c0
  c9
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record020_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record020_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record020_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record020_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record020_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record020_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record020_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record020_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record020_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00034.record020

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00034.record048
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record048
def vertexColumn : Fields := ⟨10, hexnat% "25c4f2725a8da4e8ba1ea96959366392e4789e1783e9c569964d92e479a56556364d4b61d2745d0f66358e9394cd38ccb31cd8b52ccb4acab1ac9b16c3bc1e8761e4749e1725c570dd0f23c4f0bc1f1e09c94872858964a4694348d90d2318e0741c87"⟩
def kindColumn : Fields := ⟨3, hexnat% "da6db4936da6da6da6d34d36934db4db4d36d24924da4db249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffffff7dffffdff0000", 35184405643264, 2251799813685248]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fbfeff7dffffdff0000", hexnat% "400000000000000000", 35184405643264, 1155173304420532224]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7f9feeff977ffaff0000", hexnat% "600000000001000000", 1152956688978935808, 79164904308736, 72058143793741824]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6fdeffff9ff7ffff0000", hexnat% "10000000800000000", hexnat% "10200000000000000000", 105553116266496]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6f9effff9fffffff0000", 105553116266496, hexnat% "410000000000000000", hexnat% "10200000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffeffd7fff7ddef0000", 571473920, 11258999068426240, hexnat% "10000000800000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6fffffd79ff7d9ef0000", hexnat% "10000000400000000000", 603979776, 11258999069474816, 35218765381632]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c12 c7
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fbfffd5fffffd7f0000", 2251799847239680, hexnat% "400000000000800000", 9570149208162304]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6f7fefd5df77fdef0000", hexnat% "10800000008000000000", 9570149208162304, 1152956723338674176, 2251799848288256]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffefd7fffffdff0000", 11258999068426240, 33554432, 1152921504606846976]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c1 c17
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffefd7dfffd5ff0000", 1152956688978935808, 11258999068426240, 704643072]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7f9fefd5ffffc4ff0000", 9570149208162304, 1155173304420532224, hexnat% "600000000001000000", 973078528]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c21 c18
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffeefd7dff5fdef0000", 11258999069474816, hexnat% "10000000a00000000", 35184405643264, 1152921504606846976]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffefd79ff5fdef0000", 11258999069474816, 105561706201088, 34393292800, 1152921504606846976]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6f9efffdf7ffc7ff0000", hexnat% "10200000080000000000", 939524096, hexnat% "10002000000000000", hexnat% "400000000000000000"]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6f9effddb77dc5ef0000", hexnat% "600000000000000000", 974127104, hexnat% "10000000488000000000", 9570149208162304, hexnat% "10000000200000000"]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c26 c25
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c27 c24
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c28 c23
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c29 c22
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c30 c16
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c31 c13
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨19, by decide⟩ c32 c6
  c33
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record048_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record048_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record048_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record048_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record048_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record048_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record048_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record048_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record048_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00034.record048

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00034.record003
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "dc9cb2a9a9361d98e9389e17a71ca6695a4d9594d54d4756364d534cd2745dc8e6394e334ccb31cf0ba2d8b92e2b4ac6b26c5b61e4749c6745c570de0f13c1f2590e23a611c649254554348d1362348c930ce0b42c8b41c8705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db69a69a6da69249249a4924924d34d3492489249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record003 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record003 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record003.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record003.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record003.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 46), (facetIndex 60), (facetIndex 62)]))
 (.leaf ([(facetIndex 22), (facetIndex 31), (facetIndex 64), (facetIndex 66)])))
 (.branch 3
 (.leaf ([(facetIndex 23), (facetIndex 48), (facetIndex 50), (facetIndex 51), (facetIndex 52), (facetIndex 53)]))
 (.leaf ([(facetIndex 26), (facetIndex 49), (facetIndex 56)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 24), (facetIndex 36), (facetIndex 37), (facetIndex 38), (facetIndex 39), (facetIndex 40)]))
 (.leaf ([(facetIndex 25), (facetIndex 33), (facetIndex 42)])))
 (.branch 7
 (.leaf ([(facetIndex 27), (facetIndex 29), (facetIndex 35), (facetIndex 43)]))
 (.branch 8
 (.leaf ([(facetIndex 41), (facetIndex 54)]))
 (.leaf ([(facetIndex 44), (facetIndex 47)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "101000000030722223280086574444460501060635421z16;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 32), (facetIndex 58)]))
 (.leaf ([(facetIndex 63), (facetIndex 72)])))
 (.branch 3
 (.leaf ([(facetIndex 28), (facetIndex 55), (facetIndex 57)]))
 (.leaf ([(facetIndex 34), (facetIndex 59), (facetIndex 61)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 67), (facetIndex 68)]))
 (.leaf ([(facetIndex 69), (facetIndex 70)])))
 (.branch 7
 (.leaf ([(facetIndex 30), (facetIndex 45)]))
 (.leaf ([(facetIndex 65), (facetIndex 71)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1f6c8382186104000000300000000c0182z15;"⟩
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
def grouped2_0007 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0008 : List Nat := [6]
def grouped2_0009 : List Nat := [6, 7, 8]
def grouped2_0010 : List Nat := [7]
def grouped2_0011 : List Nat := [7, 8]
def grouped2_0012 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record003 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record003_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00034.record003" "{\"atoms\":[{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":5}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00034.record003" 37

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00034.record003" "{\"ridges\":[[17,112],[18,608],[29,290],[41,112],[43,290],[44,546],[46,608],[47,289],[54,112],[57,356],[59,360],[60,584],[62,112],[62,608],[65,582],[67,102],[69,106],[71,594]],\"owners\":[[47,289,[55,57,59],[9,29,35,43,61]],[29,290,[70],[9,35,43,47,68]],[43,290,[70],[9,29,35,47,68]],[44,546,[69,70],[10,36,46,47,71]],[60,584,[65],[16,37,52,69]],[17,112,[67,71],[41,54,62]],[41,112,[],[17,54,62,67,71]],[54,112,[71],[17,41,62,67]],[62,112,[67],[17,41,54,71]],[18,608,[69,71],[46,60,62]],[46,608,[],[18,60,62,69,71]],[62,608,[69],[18,46,60,71]],[67,102,[28],[]],[65,582,[30],[]],[69,106,[34],[]],[71,594,[45],[]],[57,356,[],[]],[59,360,[],[]]],\"edges\":[[35,[17,18,28,34,41,46,54,57,59,60,62,67,69,71]]],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00034.record003" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00034.record003\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-11,-4],[-11,-7],[-14,-7],[-14,-8],[-15,-12],[-16,-3],[-19,-6],[-20,-4],[-20,-11],[-24,-14],[-25,-11],[-14,16,17,18],[-5,24],[-10,24],[-11,23,24],[-19,21],[-1,22,25],[-9],[-15,25],[-20,22],[-2,23,25],[-13],[-20,23],[-22,4],[-21,6],[-23,7],[-25,12],[-17],[-18],[-26,13,19,20],[-27,3,5,8,10],[-28,9,15],[-29,11,14],[-30,26],[-31,30],[-32,28,29],[-33,28],[-34,27,33],[-34,32],[-35,34],[-36,31,35],[36],[-37,23,24],[-23,37],[-24,37],[1,2,4,7,9,13,15,17,18,19,20,22,23,25]],\"atoms\":[{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":44,\"b\":28},{\"tag\":\"incompatible\",\"a\":44,\"b\":34},{\"tag\":\"incompatible\",\"a\":47,\"b\":34},{\"tag\":\"incompatible\",\"a\":47,\"b\":35},{\"tag\":\"incompatible\",\"a\":54,\"b\":45},{\"tag\":\"incompatible\",\"a\":55,\"b\":27},{\"tag\":\"incompatible\",\"a\":60,\"b\":30},{\"tag\":\"incompatible\",\"a\":62,\"b\":28},{\"tag\":\"incompatible\",\"a\":62,\"b\":44},{\"tag\":\"incompatible\",\"a\":70,\"b\":47},{\"tag\":\"incompatible\",\"a\":71,\"b\":44},{\"tag\":\"mate\",\"ridge\":289,\"a\":47,\"owners\":[55,57,59]},{\"tag\":\"mate\",\"ridge\":290,\"a\":29,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":290,\"a\":43,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":546,\"a\":44,\"owners\":[69,70]},{\"tag\":\"mate\",\"ridge\":584,\"a\":60,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":112,\"a\":17,\"owners\":[67,71]},{\"tag\":\"mate\",\"ridge\":112,\"a\":41,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":112,\"a\":54,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":112,\"a\":62,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":608,\"a\":18,\"owners\":[69,71]},{\"tag\":\"mate\",\"ridge\":608,\"a\":46,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":608,\"a\":62,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":102,\"a\":67,\"owners\":[28]},{\"tag\":\"mate\",\"ridge\":582,\"a\":65,\"owners\":[30]},{\"tag\":\"mate\",\"ridge\":106,\"a\":69,\"owners\":[34]},{\"tag\":\"mate\",\"ridge\":594,\"a\":71,\"owners\":[45]},{\"tag\":\"mate\",\"ridge\":356,\"a\":57,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":360,\"a\":59,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[46,60,62],\"full_literals\":[-26,13,19,20]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[27,29,35,43],\"full_literals\":[-27,3,5,8,10]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[41,54],\"full_literals\":[-28,9,15]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[44,47],\"full_literals\":[-29,11,14]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-30,26,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-31,30,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-32,28,29],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-33,28,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-34,27,33],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-34,false,32],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-35,false,34],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-36,31,35],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[69,70],\"full_literals\":[-37,23,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":69,\"full_literals\":[-23,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":70,\"full_literals\":[-24,37]},{\"tag\":\"edge\",\"edge\":35,\"owners\":[17,18,28,34,41,46,54,57,59,60,62,67,69,71]}]}"
  "p cnf 37 46\n-11 -4 0\n-11 -7 0\n-14 -7 0\n-14 -8 0\n-15 -12 0\n-16 -3 0\n-19 -6 0\n-20 -4 0\n-20 -11 0\n-24 -14 0\n-25 -11 0\n-14 16 17 18 0\n-5 24 0\n-10 24 0\n-11 23 24 0\n-19 21 0\n-1 22 25 0\n-9 0\n-15 25 0\n-20 22 0\n-2 23 25 0\n-13 0\n-20 23 0\n-22 4 0\n-21 6 0\n-23 7 0\n-25 12 0\n-17 0\n-18 0\n-26 13 19 20 0\n-27 3 5 8 10 0\n-28 9 15 0\n-29 11 14 0\n-30 26 0\n-31 30 0\n-32 28 29 0\n-33 28 0\n-34 27 33 0\n-34 32 0\n-35 34 0\n-36 31 35 0\n36 0\n-37 23 24 0\n-23 37 0\n-24 37 0\n1 2 4 7 9 13 15 17 18 19 20 22 23 25 0\n"
  "47 -26 19 20 0 22 30 0\n48 -28 15 0 18 32 0\n49 1 2 4 7 15 19 20 22 23 25 0 18 22 28 29 46 0\n50 -19 0 7 16 25 0\n51 37 28 0 50 42 29 28 37 44 45 23 13 14 15 47 34 35 41 40 39 38 36 33 4 12 31 6 0\n52 -14 -37 0 3 10 26 43 0\n53 -11 15 0 50 1 2 11 24 26 17 21 49 9 0\n54 -20 0 8 20 24 0\n55 -26 0 54 50 47 0\n56 -30 0 55 34 0\n57 -31 0 56 35 0\n58 35 0 57 42 41 0\n59 34 0 58 40 0\n60 32 0 59 39 0\n61 -15 0 5 19 27 0\n62 -28 0 61 48 0\n63 -11 0 61 53 0\n64 37 0 62 51 0\n65 29 0 62 60 36 0\n66 14 0 65 63 33 0\n67 0 66 64 52 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record003.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record003.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record003.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record003.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record003 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record003.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record003.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record003.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record003.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record003 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record003_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record003 Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record003_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record003_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00034.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00034.record053
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "5b0dc5a8da99966958d64d8b61db0ea398e9394e3392e1b89e17a65955352d475c368d6364d4b46d2745d98e534ccb31cf0ba2d8b92d2b1ac9b16f07a1d8791e2749ca719e1745c9715c3783d0f23c4f0bc1f1d24c1ca4a494950d60d4348d48c930ce0b42c8b"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6db4db4db6db6924924d36d249249a6db6d36da6924db249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record053 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record053 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record053.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 22), (facetIndex 43), (facetIndex 44), (facetIndex 45)]))
 (.leaf ([(facetIndex 29), (facetIndex 51), (facetIndex 58)])))
 (.branch 3
 (.leaf ([(facetIndex 20), (facetIndex 38), (facetIndex 40), (facetIndex 41), (facetIndex 42)]))
 (.leaf ([(facetIndex 24), (facetIndex 49), (facetIndex 57)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 39), (facetIndex 52), (facetIndex 56)]))
 (.leaf ([(facetIndex 19), (facetIndex 21), (facetIndex 67), (facetIndex 71)])))
 (.branch 7
 (.leaf ([(facetIndex 36)]))
 (.leaf ([(facetIndex 53), (facetIndex 54), (facetIndex 55)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "a00a0000005cffc21800009288600000800302aa00000000000000"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

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

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record053 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record053_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00034.record053" "{\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00034.record053" 48

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00034.record053" "{\"ridges\":[[24,133],[36,146],[38,265],[38,266],[39,521],[40,265],[42,265],[68,390],[72,166]],\"owners\":[[38,265,[7,53,55],[1,40,42,51]],[40,265,[7,51,55],[1,38,42,53]],[42,265,[7,51,53],[1,38,40,55]],[38,266,[66,68,70],[1,20,40,42,64,79]],[39,521,[8,54,55],[2,41,42,52]],[36,146,[72,74],[4,24,44,62,78]],[24,133,[6,53,54],[10,19,28,32,33,57]],[72,166,[28],[]],[68,390,[32],[]]],\"edges\":[],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00034.record053" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00034.record053\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-9,-4],[-9,-6],[-11,-4],[-11,-8],[-11,-10],[-14,-11],[-15,-11],[-16,-11],[-20,-3],[-20,-18],[-20,-19],[-21,-2],[-21,-5],[-21,-15],[-21,-18],[-21,-20],[-22,-1],[-22,-17],[-22,-18],[-22,-20],[-22,-21],[-25,-23],[-25,-24],[-27,-9],[-30,-9],[-32,-5],[-32,-6],[-32,-26],[-32,-27],[-32,-29],[-32,-30],[-12,2,20,22],[-14,2,18,22],[-16,2,18,20],[-12,26,28,29],[-13,3,21,22],[-11,31,32],[-7,1,20,21],[-31,8],[-28,10],[-33,9,18,25],[-34,5,12,14,15,16],[-35,7,17,24],[-36,13,19,23],[-37,4,6,27,30],[-38,11],[-39,20,21,22],[-40,33],[-41,34],[-41,35],[-42,40],[-42,41],[-43,36],[-43,37],[-44,38,39],[-45,38],[-46,43,45],[-47,43],[-46,44],[-47,45],[-48,42,47],[-48,46],[48]],\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":29,\"b\":19},{\"tag\":\"incompatible\",\"a\":29,\"b\":21},{\"tag\":\"incompatible\",\"a\":36,\"b\":19},{\"tag\":\"incompatible\",\"a\":36,\"b\":28},{\"tag\":\"incompatible\",\"a\":36,\"b\":32},{\"tag\":\"incompatible\",\"a\":40,\"b\":36},{\"tag\":\"incompatible\",\"a\":41,\"b\":36},{\"tag\":\"incompatible\",\"a\":42,\"b\":36},{\"tag\":\"incompatible\",\"a\":53,\"b\":8},{\"tag\":\"incompatible\",\"a\":53,\"b\":51},{\"tag\":\"incompatible\",\"a\":53,\"b\":52},{\"tag\":\"incompatible\",\"a\":54,\"b\":7},{\"tag\":\"incompatible\",\"a\":54,\"b\":20},{\"tag\":\"incompatible\",\"a\":54,\"b\":41},{\"tag\":\"incompatible\",\"a\":54,\"b\":51},{\"tag\":\"incompatible\",\"a\":54,\"b\":53},{\"tag\":\"incompatible\",\"a\":55,\"b\":6},{\"tag\":\"incompatible\",\"a\":55,\"b\":49},{\"tag\":\"incompatible\",\"a\":55,\"b\":51},{\"tag\":\"incompatible\",\"a\":55,\"b\":53},{\"tag\":\"incompatible\",\"a\":55,\"b\":54},{\"tag\":\"incompatible\",\"a\":58,\"b\":56},{\"tag\":\"incompatible\",\"a\":58,\"b\":57},{\"tag\":\"incompatible\",\"a\":67,\"b\":29},{\"tag\":\"incompatible\",\"a\":71,\"b\":29},{\"tag\":\"incompatible\",\"a\":74,\"b\":20},{\"tag\":\"incompatible\",\"a\":74,\"b\":21},{\"tag\":\"incompatible\",\"a\":74,\"b\":66},{\"tag\":\"incompatible\",\"a\":74,\"b\":67},{\"tag\":\"incompatible\",\"a\":74,\"b\":70},{\"tag\":\"incompatible\",\"a\":74,\"b\":71},{\"tag\":\"mate\",\"ridge\":265,\"a\":38,\"owners\":[7,53,55]},{\"tag\":\"mate\",\"ridge\":265,\"a\":40,\"owners\":[7,51,55]},{\"tag\":\"mate\",\"ridge\":265,\"a\":42,\"owners\":[7,51,53]},{\"tag\":\"mate\",\"ridge\":266,\"a\":38,\"owners\":[66,68,70]},{\"tag\":\"mate\",\"ridge\":521,\"a\":39,\"owners\":[8,54,55]},{\"tag\":\"mate\",\"ridge\":146,\"a\":36,\"owners\":[72,74]},{\"tag\":\"mate\",\"ridge\":133,\"a\":24,\"owners\":[6,53,54]},{\"tag\":\"mate\",\"ridge\":166,\"a\":72,\"owners\":[28]},{\"tag\":\"mate\",\"ridge\":390,\"a\":68,\"owners\":[32]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[29,51,58],\"full_literals\":[-33,9,18,25]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[20,38,40,41,42],\"full_literals\":[-34,5,12,14,15,16]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[24,49,57],\"full_literals\":[-35,7,17,24]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[39,52,56],\"full_literals\":[-36,13,19,23]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[19,21,67,71],\"full_literals\":[-37,4,6,27,30]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[36],\"full_literals\":[-38,11]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[53,54,55],\"full_literals\":[-39,20,21,22]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-40,false,33],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-41,34,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-41,false,35],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-42,40,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-42,false,41],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-43,36,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-43,false,37],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-44,38,39],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-45,38,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-46,43,45],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-47,43,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-46,false,44],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-47,false,45],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-48,42,47],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-48,false,46],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true}]}"
  "p cnf 48 63\n-9 -4 0\n-9 -6 0\n-11 -4 0\n-11 -8 0\n-11 -10 0\n-14 -11 0\n-15 -11 0\n-16 -11 0\n-20 -3 0\n-20 -18 0\n-20 -19 0\n-21 -2 0\n-21 -5 0\n-21 -15 0\n-21 -18 0\n-21 -20 0\n-22 -1 0\n-22 -17 0\n-22 -18 0\n-22 -20 0\n-22 -21 0\n-25 -23 0\n-25 -24 0\n-27 -9 0\n-30 -9 0\n-32 -5 0\n-32 -6 0\n-32 -26 0\n-32 -27 0\n-32 -29 0\n-32 -30 0\n-12 2 20 22 0\n-14 2 18 22 0\n-16 2 18 20 0\n-12 26 28 29 0\n-13 3 21 22 0\n-11 31 32 0\n-7 1 20 21 0\n-31 8 0\n-28 10 0\n-33 9 18 25 0\n-34 5 12 14 15 16 0\n-35 7 17 24 0\n-36 13 19 23 0\n-37 4 6 27 30 0\n-38 11 0\n-39 20 21 22 0\n-40 33 0\n-41 34 0\n-41 35 0\n-42 40 0\n-42 41 0\n-43 36 0\n-43 37 0\n-44 38 39 0\n-45 38 0\n-46 43 45 0\n-47 43 0\n-46 44 0\n-47 45 0\n-48 42 47 0\n-48 46 0\n48 0\n"
  "64 46 0 63 62 0\n65 44 0 64 59 0\n66 -18 -39 0 10 15 19 47 0\n67 21 22 23 38 0 65 64 56 57 53 55 47 9 11 36 44 0\n68 22 23 38 0 65 63 56 60 61 52 49 55 66 67 12 13 14 16 33 34 42 32 0\n69 -25 38 0 63 56 60 61 52 50 22 23 68 17 18 20 21 43 38 0\n70 38 0 65 64 63 55 56 66 60 57 61 54 51 48 69 41 1 2 24 25 45 0\n71 11 0 70 46 0\n72 -4 0 71 3 0\n73 -8 0 71 4 0\n74 -10 0 71 5 0\n75 -14 0 71 6 0\n76 -15 0 71 7 0\n77 -16 0 71 8 0\n78 -31 0 73 39 0\n79 -28 0 74 40 0\n80 32 0 78 71 37 0\n81 -5 0 80 26 0\n82 -6 0 80 27 0\n83 -26 0 80 28 0\n84 -27 0 80 29 0\n85 -29 0 80 30 0\n86 -30 0 80 31 0\n87 -12 0 85 79 83 35 0\n88 -37 0 86 82 72 84 45 0\n89 -34 0 87 76 81 75 77 42 0\n90 -43 0 88 54 0\n91 -41 0 89 49 0\n92 -47 0 90 58 0\n93 -42 0 91 52 0\n94 0 93 92 63 61 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record053.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record053.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record053.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record053.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record053 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record053.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record053.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record053.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record053.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record053 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record053_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record053_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record053_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record053_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record053_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record053_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record053_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record053 Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record053_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record053_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record053_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00034.record053
