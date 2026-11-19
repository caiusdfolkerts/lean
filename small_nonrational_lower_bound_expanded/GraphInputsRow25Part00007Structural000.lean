module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow25Part00007Data
public import GraphInputsRow25Part00007Frames
public import GraphInputsRow25Part00007Leaves
public import GraphInputsRow25Part00007Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00007.record064
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record064
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨67, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨76, by decide⟩, ⟨83, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), 9804371573157658624, (certNat% 5), 143623706378240, (certNat% 6)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), 9232379236109516800, 1170935907411296256, (certNat% 8), (certNat% 9), 288230377225453568, (certNat% 10)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), 1441151885187743744, (certNat% 12), (certNat% 13), 15762599769538560, (certNat% 3), 2305843009213693952]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), 20266198323167232, 297237576480194560, 1700807049216, (certNat% 15), (certNat% 16)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), 9804336388785569792, 20266198323167232, (certNat% 18), (certNat% 19), (certNat% 20), (certNat% 21)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), 143486267424768, (certNat% 23), (certNat% 3), (certNat% 9), 9813343588577181696, 1073741824]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), 143486267424768, (certNat% 25), (certNat% 3), (certNat% 9), 9813343588577181696, 1073741824]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), 1170935907444850688, (certNat% 27), (certNat% 28), 9813343588577181696, (certNat% 29), 2251800887427072, 2594073385365405696]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record064_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record064_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record064_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record064_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record064_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record064_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record064_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record064_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record064_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00007.record064

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00007.record070
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record070
def vertexColumn : Fields := ⟨10, (certNat% 30)⟩
def kindColumn : Fields := ⟨3, (certNat% 31)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨68, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨84, by decide⟩, ⟨88, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 32), (certNat% 33), 288232850187091968, 720575940379279360, (certNat% 34), (certNat% 35)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 36), 432345564361785344, 11287174053888, (certNat% 37), 576460754182471680, (certNat% 38), (certNat% 39)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), (certNat% 41), (certNat% 42), (certNat% 43), (certNat% 44), 3377699720527872, (certNat% 33)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 45), (certNat% 43), 1134713179734016, (certNat% 46), (certNat% 47), (certNat% 48), 68719476736]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 49), (certNat% 48), (certNat% 50), (certNat% 51), 540431955418677248, 1152921504606846976, (certNat% 52)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 53), (certNat% 54), (certNat% 55), (certNat% 56), 1407375420424192, (certNat% 57), 2305843009213693952]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 58), 360287970256748544, (certNat% 46), (certNat% 59), (certNat% 60), (certNat% 61), (certNat% 62)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 63), 1407375420424192, 720575940379279360, (certNat% 64), 11529215063248338944, (certNat% 65)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 66), 1134713179734016, (certNat% 43), 567416719409152, (certNat% 67), (certNat% 68)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 69), 567416719409152, 540431955351568384, (certNat% 70), (certNat% 59), (certNat% 67), 1125917623582720]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 71), (certNat% 72), 3729543441416192, (certNat% 73), (certNat% 51), 9223372054034644992, 536870912]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 74), (certNat% 75), 9223372054034644992, 576460752907403264, (certNat% 76), 540431955284459520, 68719476736]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 77), (certNat% 78), (certNat% 79), 828662331503280128, (certNat% 70), (certNat% 51), (certNat% 72), 1125917623582720]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c16 c13
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨94, by decide⟩ c17 c12
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c18 c7
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c19 c6
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c20 c5
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c21 c4
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c22 c3
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c23 c2
  c24
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record070_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record070_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record070_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record070_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record070_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record070_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record070_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record070_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record070_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00007.record070

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00007.record065
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3b0e6364cd1b49b31c6725c6ca6a3aa5a699964d8b62b86e2785ee8761e4731ac5b1e26a99a4e9c669966659d17256966559715656558d5352d70d6364d8b4ad1b61d4749d175a398ce364e538cd332ce4b32e2b2ac6b86c5b61d2729d1725c570dc8f0bc9a1984e07b2168661c45919261926525195151341d28c6324c8b12c1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db6db6db6da49249a6d349269249369b69b4924924db493492692492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record065 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record065 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record065.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record065.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record065.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 27), (facetIndex 38), (facetIndex 39), (facetIndex 55), (facetIndex 77), (facetIndex 88)]))
 (.leaf ([(facetIndex 49), (facetIndex 67), (facetIndex 68), (facetIndex 84)])))
 (.branch 3
 (.leaf ([(facetIndex 28), (facetIndex 36), (facetIndex 86), (facetIndex 87)]))
 (.branch 4
 (.leaf ([(facetIndex 41), (facetIndex 43), (facetIndex 48)]))
 (.leaf ([(facetIndex 34), (facetIndex 50), (facetIndex 69), (facetIndex 70), (facetIndex 85)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 37), (facetIndex 52), (facetIndex 53), (facetIndex 54), (facetIndex 73), (facetIndex 74), (facetIndex 75)]))
 (.leaf ([(facetIndex 29), (facetIndex 62), (facetIndex 80), (facetIndex 82)])))
 (.branch 8
 (.leaf ([(facetIndex 42), (facetIndex 51), (facetIndex 58), (facetIndex 72)]))
 (.branch 9
 (.leaf ([(facetIndex 32), (facetIndex 47), (facetIndex 65), (facetIndex 66), (facetIndex 83)]))
 (.leaf ([(facetIndex 30), (facetIndex 31), (facetIndex 33)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "224186060000555704411880060007000555741380003730005204989962z1c;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 40), (facetIndex 45), (facetIndex 46)]))
 (.branch 2
 (.leaf ([(facetIndex 64), (facetIndex 94)]))
 (.leaf ([(facetIndex 56), (facetIndex 57), (facetIndex 76), (facetIndex 78), (facetIndex 96)]))))
 (.branch 4
 (.leaf ([(facetIndex 79), (facetIndex 81)]))
 (.branch 5
 (.leaf ([(facetIndex 89), (facetIndex 95), (facetIndex 101)]))
 (.leaf ([(facetIndex 105), (facetIndex 106)])))))
 (.branch 9
 (.branch 7
 (.leaf ([(facetIndex 60), (facetIndex 63), (facetIndex 71), (facetIndex 98)]))
 (.branch 8
 (.leaf ([(facetIndex 100), (facetIndex 103), (facetIndex 104)]))
 (.leaf ([(facetIndex 35), (facetIndex 44), (facetIndex 61)]))))
 (.branch 11
 (.branch 10
 (.leaf ([(facetIndex 90), (facetIndex 91), (facetIndex 92)]))
 (.leaf ([(facetIndex 93), (facetIndex 97), (facetIndex 102)])))
 (.branch 12
 (.leaf ([(facetIndex 59)]))
 (.leaf ([(facetIndex 99)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "5577a47c6a241a999400000003032020000600000016086b022000000000008000000008z23;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 13
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2, 3, 4]
def grouped2_0006 : List Nat := [5, 6]
def grouped2_0007 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0008 : List Nat := [7]
def grouped2_0009 : List Nat := [7, 8, 9]
def grouped2_0010 : List Nat := [8, 9]
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1, 2]
def grouped3_0013 : List Nat := [0, 1, 2, 3, 4, 5]
def grouped3_0015 : List Nat := [1]
def grouped3_0016 : List Nat := [1, 2]
def grouped3_0017 : List Nat := [2]
def grouped3_0018 : List Nat := [3]
def grouped3_0019 : List Nat := [3, 4, 5]
def grouped3_0020 : List Nat := [4]
def grouped3_0021 : List Nat := [4, 5]
def grouped3_0022 : List Nat := [5]
def grouped3_0023 : List Nat := [6]
def grouped3_0024 : List Nat := [6, 7, 8]
def grouped3_0025 : List Nat := [6, 7, 8, 9, 10, 11, 12]
def grouped3_0026 : List Nat := [7]
def grouped3_0027 : List Nat := [7, 8]
def grouped3_0028 : List Nat := [8]
def grouped3_0029 : List Nat := [9]
def grouped3_0030 : List Nat := [9, 10]
def grouped3_0031 : List Nat := [9, 10, 11, 12]
def grouped3_0032 : List Nat := [10]
def grouped3_0033 : List Nat := [11]
def grouped3_0034 : List Nat := [11, 12]
def grouped3_0035 : List Nat := [12]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record065 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record065_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00007.record065" "{\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":9,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":10},{\"tag\":\"group\",\"kind\":3,\"index\":11},{\"tag\":\"group\",\"kind\":3,\"index\":12},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0027\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0030\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0034\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0031\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00007.record065" 101

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00007.record065" "{\"ridges\":[[12,276],[14,292],[16,536],[17,584],[19,784],[20,577],[20,608],[22,545],[34,292],[37,536],[40,554],[42,584],[45,562],[46,594],[49,577],[49,608],[54,536],[57,556],[58,584],[60,780],[62,292],[63,564],[64,596],[65,276],[66,784],[67,292],[68,608],[69,292],[70,545],[71,836],[72,584],[74,536],[75,536],[77,584],[77,608],[78,680],[82,800],[83,784],[84,608],[85,800],[94,594],[96,554],[98,596],[100,780],[101,556],[103,564],[104,836]],\"owners\":[[12,276,[91,92,99,100,102,103],[32,53,62,65,66]],[65,276,[91,100,103],[12,32,53,62,66,92,99,102]],[14,292,[91,93,102,103,104],[34,62,67,69,70]],[34,292,[102,103,104],[14,62,67,69,70,91,93]],[62,292,[93,104],[14,34,67,69,70,91,102,103]],[67,292,[91,93,102,103],[14,34,62,69,70,104]],[69,292,[91,103,104],[14,34,62,67,70,93,102]],[16,536,[94,98,100,105],[37,54,72,74,75]],[37,536,[98,100,105],[16,54,72,74,75,94]],[54,536,[94,105],[16,37,72,74,75,98,100]],[74,536,[94,98,100],[16,37,54,72,75,105]],[75,536,[94,98],[16,37,54,72,74,100,105]],[20,577,[17,42,46,58,64,71,72],[49,68,84]],[49,577,[17,58,64,71,72],[20,42,46,68,84]],[17,584,[94,96,98,101],[42,58,72,77]],[42,584,[98,101],[17,58,72,77,94,96]],[58,584,[94,96],[17,42,72,77,98,101]],[72,584,[96,101],[17,42,58,77,94,98]],[77,584,[94,98],[17,42,58,72,96,101]],[19,784,[100,103,105,106],[66,75,82,83]],[66,784,[105,106],[19,75,82,83,100,103]],[83,784,[100,103],[19,66,75,82,105,106]],[22,545,[20,40,45,49,57,63,68,77,78,81],[70,82,85]],[70,545,[20,40,45,49,77,78,81],[22,57,63,68,82,85]],[20,608,[96,101,104],[49,68,77,84]],[49,608,[101,104],[20,68,77,84,96]],[68,608,[96],[20,49,77,84,101,104]],[77,608,[104],[20,49,68,84,96,101]],[84,608,[96,101],[20,49,68,77,104]],[82,800,[104],[22,70,84,85,103,106]],[85,800,[103,104],[22,70,82,84,106]],[40,554,[96],[]],[96,554,[40],[]],[45,562,[],[]],[46,594,[94],[]],[94,594,[46],[]],[57,556,[101],[]],[101,556,[57],[]],[60,780,[100],[]],[100,780,[60],[]],[63,564,[103],[]],[103,564,[63],[]],[64,596,[98],[]],[98,596,[64],[]],[71,836,[104],[]],[104,836,[71],[]],[78,680,[],[]]],\"edges\":[[22,[12,14,32,34,35,53,59,60,62,65,66,67,69,70,71,91,92,93,99,100,102,103,104]],[29,[16,17,37,40,42,54,57,58,60,72,74,75,77,78,79,94,96,98,100,101,105]],[34,[16,19,37,45,46,54,63,64,66,72,74,75,81,82,83,94,98,100,103,105,106]],[41,[17,20,42,46,49,58,64,68,71,72,77,84,94,96,98,101,104]],[44,[19,22,60,66,70,71,75,79,82,83,84,85,100,103,104,105,106]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00007.record065" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00007.record065\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-19,-16],[-24,-20],[-30,-9],[-30,-21],[-33,-24],[-38,-15],[-38,-24],[-40,-18],[-47,-24],[-54,-12],[-54,-18],[-54,-53],[-55,-32],[-55,-36],[-57,-37],[-58,-8],[-58,-13],[-58,-14],[-58,-23],[-58,-25],[-58,-34],[-58,-49],[-61,-57],[-1,50,51,56,57,59,60],[-31,50,57,60],[-2,50,52,59,60,61],[-10,59,60,61],[-28,52,61],[-33,50,52,59,60],[-35,50,60,61],[-3,53,55,57,62],[-12,55,57,62],[-22,53,62],[-39,53,55,57],[-40,53,55],[-6,4,16,18,25,30,37,38],[-19,4,25,30,37,38],[-4,53,54,55,58],[-16,55,58],[-25,53,54],[-38,54,58],[-41,53,55],[-5,57,60,62,63],[-32,62,63],[-46,57,60],[-7,6,15,17,19,24,29,34,41,42,44],[-36,6,15,17,19,41,42,44],[-6,54,58,61],[-19,58,61],[-34,54],[-41,61],[-47,54,58],[-45,61],[-48,60,61],[-15,54],[-54,15],[-17],[-18,53],[-53,18],[-24,58],[-58,24],[-27,57],[-57,27],[-29,60],[-60,29],[-30,55],[-55,30],[-37,61],[-61,37],[-42],[-64,8,13,14,23,41,49],[-65,19,33,34,47],[-66,16,20,25,38],[-67,64,65],[-68,64],[-69,67],[-70,68],[-71,66],[-72,71],[-73,69],[-73,70,72],[73],[-15,74],[-18,74],[-30,75],[-53,75],[-24,76],[-54,76],[-43,77],[-44,77],[-58,78],[-62,79],[-63,79],[-27,80],[-29,80],[-37,80],[-55,80],[-81,57,60,61],[-57,81],[-60,81],[-61,81],[-11,82],[-50,83],[-51,83],[-52,84],[-59,84],[-26,85],[-56,86],[-76,87],[-75,87],[-87,88],[-74,88],[-74,-87,89],[-79,90],[-78,90],[-90,91],[-77,91],[-91,92],[-88,92],[-89,-91,93],[-82,94],[-81,94],[-80,95],[-80,-94,96],[-84,97],[-83,97],[-86,98],[-85,98],[-98,99],[-97,99],[-95,-99,100],[-96,100],[-92,-100,101],[-93,101],[-101],[1,2,9,10,11,21,26,27,28,31,32,33,35,36,37,50,51,52,56,57,59,60,61],[3,4,12,15,16,22,24,25,27,38,39,40,41,42,43,53,54,55,57,58,62],[3,5,12,17,18,22,29,30,32,38,39,40,44,45,46,53,55,57,60,62,63],[4,6,16,18,19,25,30,34,37,38,41,47,53,54,55,58,61],[5,7,27,32,36,37,40,43,45,46,47,48,57,60,61,62,63]],\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":10,\"kind\":3},{\"tag\":\"group\",\"index\":11,\"kind\":3},{\"tag\":\"group\",\"index\":12,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":49,\"b\":42},{\"tag\":\"incompatible\",\"a\":57,\"b\":51},{\"tag\":\"incompatible\",\"a\":64,\"b\":32},{\"tag\":\"incompatible\",\"a\":64,\"b\":53},{\"tag\":\"incompatible\",\"a\":67,\"b\":57},{\"tag\":\"incompatible\",\"a\":72,\"b\":40},{\"tag\":\"incompatible\",\"a\":72,\"b\":57},{\"tag\":\"incompatible\",\"a\":75,\"b\":46},{\"tag\":\"incompatible\",\"a\":84,\"b\":57},{\"tag\":\"incompatible\",\"a\":96,\"b\":37},{\"tag\":\"incompatible\",\"a\":96,\"b\":46},{\"tag\":\"incompatible\",\"a\":96,\"b\":94},{\"tag\":\"incompatible\",\"a\":98,\"b\":66},{\"tag\":\"incompatible\",\"a\":98,\"b\":70},{\"tag\":\"incompatible\",\"a\":100,\"b\":71},{\"tag\":\"incompatible\",\"a\":101,\"b\":27},{\"tag\":\"incompatible\",\"a\":101,\"b\":38},{\"tag\":\"incompatible\",\"a\":101,\"b\":39},{\"tag\":\"incompatible\",\"a\":101,\"b\":55},{\"tag\":\"incompatible\",\"a\":101,\"b\":58},{\"tag\":\"incompatible\",\"a\":101,\"b\":68},{\"tag\":\"incompatible\",\"a\":101,\"b\":88},{\"tag\":\"incompatible\",\"a\":104,\"b\":100},{\"tag\":\"mate\",\"ridge\":276,\"a\":12,\"owners\":[91,92,99,100,102,103]},{\"tag\":\"mate\",\"ridge\":276,\"a\":65,\"owners\":[91,100,103]},{\"tag\":\"mate\",\"ridge\":292,\"a\":14,\"owners\":[91,93,102,103,104]},{\"tag\":\"mate\",\"ridge\":292,\"a\":34,\"owners\":[102,103,104]},{\"tag\":\"mate\",\"ridge\":292,\"a\":62,\"owners\":[93,104]},{\"tag\":\"mate\",\"ridge\":292,\"a\":67,\"owners\":[91,93,102,103]},{\"tag\":\"mate\",\"ridge\":292,\"a\":69,\"owners\":[91,103,104]},{\"tag\":\"mate\",\"ridge\":536,\"a\":16,\"owners\":[94,98,100,105]},{\"tag\":\"mate\",\"ridge\":536,\"a\":37,\"owners\":[98,100,105]},{\"tag\":\"mate\",\"ridge\":536,\"a\":54,\"owners\":[94,105]},{\"tag\":\"mate\",\"ridge\":536,\"a\":74,\"owners\":[94,98,100]},{\"tag\":\"mate\",\"ridge\":536,\"a\":75,\"owners\":[94,98]},{\"tag\":\"mate\",\"ridge\":577,\"a\":20,\"owners\":[17,42,46,58,64,71,72]},{\"tag\":\"mate\",\"ridge\":577,\"a\":49,\"owners\":[17,58,64,71,72]},{\"tag\":\"mate\",\"ridge\":584,\"a\":17,\"owners\":[94,96,98,101]},{\"tag\":\"mate\",\"ridge\":584,\"a\":42,\"owners\":[98,101]},{\"tag\":\"mate\",\"ridge\":584,\"a\":58,\"owners\":[94,96]},{\"tag\":\"mate\",\"ridge\":584,\"a\":72,\"owners\":[96,101]},{\"tag\":\"mate\",\"ridge\":584,\"a\":77,\"owners\":[94,98]},{\"tag\":\"mate\",\"ridge\":784,\"a\":19,\"owners\":[100,103,105,106]},{\"tag\":\"mate\",\"ridge\":784,\"a\":66,\"owners\":[105,106]},{\"tag\":\"mate\",\"ridge\":784,\"a\":83,\"owners\":[100,103]},{\"tag\":\"mate\",\"ridge\":545,\"a\":22,\"owners\":[20,40,45,49,57,63,68,77,78,81]},{\"tag\":\"mate\",\"ridge\":545,\"a\":70,\"owners\":[20,40,45,49,77,78,81]},{\"tag\":\"mate\",\"ridge\":608,\"a\":20,\"owners\":[96,101,104]},{\"tag\":\"mate\",\"ridge\":608,\"a\":49,\"owners\":[101,104]},{\"tag\":\"mate\",\"ridge\":608,\"a\":68,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":608,\"a\":77,\"owners\":[104]},{\"tag\":\"mate\",\"ridge\":608,\"a\":84,\"owners\":[96,101]},{\"tag\":\"mate\",\"ridge\":800,\"a\":82,\"owners\":[104]},{\"tag\":\"mate\",\"ridge\":800,\"a\":85,\"owners\":[103,104]},{\"tag\":\"mate\",\"ridge\":554,\"a\":40,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":554,\"a\":96,\"owners\":[40]},{\"tag\":\"mate\",\"ridge\":562,\"a\":45,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":594,\"a\":46,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":594,\"a\":94,\"owners\":[46]},{\"tag\":\"mate\",\"ridge\":556,\"a\":57,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":556,\"a\":101,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":780,\"a\":60,\"owners\":[100]},{\"tag\":\"mate\",\"ridge\":780,\"a\":100,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":564,\"a\":63,\"owners\":[103]},{\"tag\":\"mate\",\"ridge\":564,\"a\":103,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":596,\"a\":64,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":596,\"a\":98,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":836,\"a\":71,\"owners\":[104]},{\"tag\":\"mate\",\"ridge\":836,\"a\":104,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":680,\"a\":78,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[27,38,39,55,77,88],\"full_literals\":[-64,8,13,14,23,41,49]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[49,67,68,84],\"full_literals\":[-65,19,33,34,47]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[42,51,58,72],\"full_literals\":[-66,16,20,25,38]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-67,64,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-68,64,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-69,67,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-70,68,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-71,66,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-72,false,71],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-73,69,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-73,70,72],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":9,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":40,\"full_literals\":[-15,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":46,\"full_literals\":[-18,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":64,\"full_literals\":[-30,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":94,\"full_literals\":[-53,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":57,\"full_literals\":[-24,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":96,\"full_literals\":[-54,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":79,\"full_literals\":[-43,77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":81,\"full_literals\":[-44,77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":101,\"full_literals\":[-58,78]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":105,\"full_literals\":[-62,79]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":106,\"full_literals\":[-63,79]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":60,\"full_literals\":[-27,80]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":63,\"full_literals\":[-29,80]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":71,\"full_literals\":[-37,80]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":98,\"full_literals\":[-55,80]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[100,103,104],\"full_literals\":[-81,57,60,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":100,\"full_literals\":[-57,81]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":103,\"full_literals\":[-60,81]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":104,\"full_literals\":[-61,81]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":35,\"full_literals\":[-11,82]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":91,\"full_literals\":[-50,83]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":92,\"full_literals\":[-51,83]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":93,\"full_literals\":[-52,84]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":102,\"full_literals\":[-59,84]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":59,\"full_literals\":[-26,85]},{\"tag\":\"group_take\",\"kind\":3,\"index\":12,\"member\":99,\"full_literals\":[-56,86]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-76,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-75,false,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-87,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-74,false,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-74,-87,89],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-79,90],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-78,false,90],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-90,91],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-77,false,91],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-91,92],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-88,false,92],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0013\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-89,-91,93],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0026\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0027\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-82,94],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0026\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0027\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-81,false,94],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-80,false,95],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-80,-94,96],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0032\",\"joined_name\":\"grouped3_0030\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-84,97],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0032\",\"joined_name\":\"grouped3_0030\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-83,false,97],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[11],\"right\":[12],\"left_name\":\"grouped3_0033\",\"right_name\":\"grouped3_0035\",\"joined_name\":\"grouped3_0034\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-86,98],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[11],\"right\":[12],\"left_name\":\"grouped3_0033\",\"right_name\":\"grouped3_0035\",\"joined_name\":\"grouped3_0034\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-85,false,98],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9,10],\"right\":[11,12],\"left_name\":\"grouped3_0030\",\"right_name\":\"grouped3_0034\",\"joined_name\":\"grouped3_0031\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-98,99],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9,10],\"right\":[11,12],\"left_name\":\"grouped3_0030\",\"right_name\":\"grouped3_0034\",\"joined_name\":\"grouped3_0031\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-97,false,99],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11,12],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-95,-99,100],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11,12],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0025\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-96,false,100],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11,12],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-92,-100,101],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11,12],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-93,false,101],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":22,\"owners\":[12,14,32,34,35,53,59,60,62,65,66,67,69,70,71,91,92,93,99,100,102,103,104]},{\"tag\":\"edge\",\"edge\":29,\"owners\":[16,17,37,40,42,54,57,58,60,72,74,75,77,78,79,94,96,98,100,101,105]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[16,19,37,45,46,54,63,64,66,72,74,75,81,82,83,94,98,100,103,105,106]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[17,20,42,46,49,58,64,68,71,72,77,84,94,96,98,101,104]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[19,22,60,66,70,71,75,79,82,83,84,85,100,103,104,105,106]}]}"
  "141 69 0 82 80 0\n142 67 0 141 76 0\n143 -93 0 135 134 0\n144 3 4 12 15 16 22 24 25 27 38 39 40 41 43 53 54 55 57 58 62 0 70 137 0\n145 3 5 12 18 22 29 30 32 38 39 40 44 45 46 53 55 57 60 62 63 0 57 138 0\n146 57 92 0 118 116 115 91 119 111 110 86 109 88 85 67 38 42 35 39 40 41 114 92 33 87 112 83 117 89 62 32 31 34 144 0\n147 92 0 118 119 116 111 112 115 109 110 84 91 88 85 86 41 52 50 67 40 39 42 38 146 15 23 37 36 139 0\n148 -100 0 147 135 133 0\n149 -96 0 148 132 0\n150 -81 0 149 122 124 94 95 96 63 65 69 98 0\n151 -57 0 150 99 0\n152 -60 0 150 100 0\n153 -61 0 150 101 0\n154 -46 0 151 152 45 0\n155 -27 0 151 62 0\n156 -48 0 152 153 54 0\n157 -29 0 152 64 0\n158 -41 0 153 51 0\n159 -45 0 153 53 0\n160 -37 0 153 68 0\n161 53 54 55 58 0 153 158 160 48 52 41 50 39 66 49 58 40 38 139 0\n162 54 55 58 0 143 157 70 158 57 159 153 152 151 156 154 155 160 49 60 50 55 52 48 161 59 86 8 84 110 113 120 116 117 114 89 90 92 93 46 47 44 43 140 0\n163 55 58 0 143 152 151 154 159 157 66 162 10 11 12 56 88 35 34 6 83 109 113 120 116 117 114 90 92 93 44 33 43 31 145 0\n164 -55 0 149 148 153 152 151 160 155 13 14 67 97 3 4 123 124 131 121 129 130 102 127 128 125 126 108 107 105 106 103 104 28 27 25 30 24 26 29 136 0\n165 58 0 164 163 0\n166 -8 0 165 16 0\n167 -13 0 165 17 0\n168 -14 0 165 18 0\n169 -23 0 165 19 0\n170 -25 0 165 20 0\n171 -34 0 165 21 0\n172 -49 0 165 22 0\n173 24 0 165 61 0\n174 -64 0 167 166 158 169 168 172 71 0\n175 -20 0 173 2 0\n176 -33 0 173 5 0\n177 -38 0 173 7 0\n178 -47 0 173 9 0\n179 65 0 174 142 74 0\n180 -68 0 174 75 0\n181 19 0 179 178 171 176 72 0\n182 -70 0 180 77 0\n183 -16 0 181 1 0\n184 72 0 182 82 81 0\n185 -66 0 183 177 170 175 73 0\n186 71 0 184 79 0\n187 0 186 185 78 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record065.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record065.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record065.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record065.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record065 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record065.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record065.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record065.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record065.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record065 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record065_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record065_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record065_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record065_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record065_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record065_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record065_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record065 Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record065_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record065_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record065_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00007.record065

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00007.record069
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ea278d51b46b25c6ca729aa5a8e87a699964d8b6338ae1783ee87516c671e2729aa5a99a6598e479d15a5c5595955554d4b5c358d934cd4b4ad8745d0f5a398d9394e334ccb31ce4b32e2b1ae1b16c3b61cc749ca745c970dc2f07f302a8562384ec85a1c46518c531926292a585454552344d28c530cc8b12c2b21c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6db6db6d24d249a4924da4924da49a69a6d2492493492692491249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record069 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record069 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record069.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record069.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record069.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 55), (facetIndex 61), (facetIndex 69)]))
 (.branch 2
 (.leaf ([(facetIndex 57), (facetIndex 77)]))
 (.leaf ([(facetIndex 96), (facetIndex 99)]))))
 (.branch 4
 (.leaf ([(facetIndex 97), (facetIndex 101)]))
 (.branch 5
 (.leaf ([(facetIndex 35), (facetIndex 50), (facetIndex 62)]))
 (.leaf ([(facetIndex 40), (facetIndex 51), (facetIndex 70)])))))
 (.branch 9
 (.branch 7
 (.leaf ([(facetIndex 86), (facetIndex 87), (facetIndex 88)]))
 (.branch 8
 (.leaf ([(facetIndex 90), (facetIndex 91), (facetIndex 93)]))
 (.leaf ([(facetIndex 92), (facetIndex 94), (facetIndex 100)]))))
 (.branch 10
 (.leaf ([(facetIndex 89), (facetIndex 95), (facetIndex 98)]))
 (.branch 11
 (.leaf ([(facetIndex 53)]))
 (.leaf ([(facetIndex 82)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "3829329878779666000b0000100000050000000400001000a054000000000500004z23;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 12
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0002 : List Nat := [0, 1, 2, 3, 4, 5]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [1, 2]
def grouped3_0006 : List Nat := [2]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [3, 4, 5]
def grouped3_0009 : List Nat := [4]
def grouped3_0010 : List Nat := [4, 5]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7, 8]
def grouped3_0014 : List Nat := [6, 7, 8, 9, 10, 11]
def grouped3_0015 : List Nat := [7]
def grouped3_0016 : List Nat := [7, 8]
def grouped3_0017 : List Nat := [8]
def grouped3_0018 : List Nat := [9]
def grouped3_0019 : List Nat := [9, 10, 11]
def grouped3_0020 : List Nat := [10, 11]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record069 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record069_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00007.record069" "{\"atoms\":[{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0005\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0005\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00007.record069" 78

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00007.record069" "{\"ridges\":[[13,276],[14,261],[14,388],[16,552],[17,584],[20,592],[33,276],[35,294],[37,261],[37,388],[40,538],[42,552],[44,584],[49,592],[51,610],[55,540],[57,300],[59,584],[60,388],[61,780],[63,276],[64,276],[65,592],[66,276],[67,276],[68,388],[69,836],[71,552],[72,584],[72,592],[73,552],[73,584],[75,552],[76,552],[77,904],[78,592],[80,592],[86,180],[87,294],[88,402],[89,294],[96,540],[97,300],[98,180],[99,836],[101,904]],\"owners\":[[14,261,[13,33,35,57,61,63,64,67,69],[37,60,68]],[37,261,[13,57,61,63,64,67,69],[14,33,35,60,68]],[13,276,[87,88,98,99],[33,63,64,66,67]],[33,276,[98,99],[13,63,64,66,67,87,88]],[63,276,[88,99],[13,33,64,66,67,87,98]],[64,276,[87,88,98],[13,33,63,66,67,99]],[66,276,[87,99],[13,33,63,64,67,88,98]],[67,276,[87,88,98],[13,33,63,64,66,99]],[14,388,[88,89,97,98],[37,60,66,68]],[37,388,[97,98],[14,60,66,68,88,89]],[60,388,[88,89,98],[14,37,66,68,97]],[68,388,[88],[14,37,60,66,89,97,98]],[16,552,[91,93,100,101],[42,71,73,75,76]],[42,552,[100,101],[16,71,73,75,76,91,93]],[71,552,[93,101],[16,42,73,75,76,91,100]],[73,552,[91,101],[16,42,71,75,76,93,100]],[75,552,[91,93,100],[16,42,71,73,76,101]],[76,552,[91,93,100],[16,42,71,73,75,101]],[17,584,[92,93,96,100],[44,59,72,73]],[44,584,[96,100],[17,59,72,73,92,93]],[59,584,[92,93,100],[17,44,72,73,96]],[72,584,[93],[17,44,59,73,92,96,100]],[73,584,[92,96],[17,44,59,72,93,100]],[20,592,[92,94,96,99,100],[49,65,72,78,80]],[49,592,[96,99,100],[20,65,72,78,80,92,94]],[65,592,[92,94,100],[20,49,72,78,80,96,99]],[72,592,[94,99],[20,49,65,78,80,92,96,100]],[78,592,[92,96,99],[20,49,65,72,80,94,100]],[80,592,[92,94,96,100],[20,49,65,72,78,99]],[35,294,[87,89],[]],[87,294,[35,89],[]],[89,294,[35,87],[]],[40,538,[91,92],[]],[88,402,[50,95],[]],[51,610,[93,94],[]],[55,540,[96],[]],[96,540,[55],[]],[57,300,[97],[]],[97,300,[57],[]],[61,780,[],[]],[86,180,[62,98],[]],[98,180,[62,86],[]],[69,836,[99],[]],[99,836,[69],[]],[77,904,[101],[]],[101,904,[77],[]]],\"edges\":[[22,[13,14,33,35,37,57,60,61,63,64,66,67,68,69,87,88,89,97,98,99]],[29,[16,17,40,42,44,55,59,61,71,72,73,75,76,77,91,92,93,96,100,101]],[41,[17,20,44,49,51,59,65,69,72,73,78,80,92,93,94,96,99,100]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00007.record069" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00007.record069\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-33,-16],[-48,-45],[-2,1,6,7,16,19,21,22,25,27],[-8,1,16,19,21,22,25,27],[-1,37,38,47,48],[-6,47,48],[-21,38,48],[-22,37,38,47],[-24,37,48],[-25,37,38,47],[-2,38,39,46,47],[-8,46,47],[-18,38,39,47],[-26,38],[-3,40,42,49,50],[-10,49,50],[-28,42,50],[-30,40,50],[-31,40,42,49],[-32,40,42,49],[-4,41,42,45,49],[-11,45,49],[-17,41,42,49],[-29,42],[-30,41,45],[-5,41,43,45,48,49],[-12,45,48,49],[-23,41,43,49],[-29,43,48],[-34,41,45,48],[-35,41,43,45,49],[-7,37,39],[-37,7,39],[-39,7,37],[-9,40,41],[-38,13,44],[-14,42,43],[-15,45],[-45,15],[-16,46],[-46,16],[-19],[-36,20,47],[-47,20,36],[-27,48],[-48,27],[-33,50],[-50,33],[-15,51],[-27,51],[-52,16,33],[-16,52],[-33,52],[-53,45,48],[-45,53],[-48,53],[-46,54],[-50,54],[-7,55],[-13,55],[-20,55],[-9,56],[-57,36,37,38],[-36,57],[-37,57],[-38,57],[-40,58],[-42,58],[-41,59],[-43,59],[-49,59],[-39,60],[-44,60],[-47,60],[-61,52,53],[-53,61],[-52,61],[-52,-53,62],[-61,63],[-62,64],[-51,63],[-51,-61,64],[-51,-62,65],[-56,66],[-55,66],[-66,67],[-54,67],[-67,68],[-63,68],[-63,-67,69],[-64,69],[-65,70],[-59,71],[-58,71],[-71,72],[-57,72],[-57,-71,73],[-60,74],[-74,75],[-72,75],[-72,-74,76],[-73,76],[-73,-74,77],[-77,78],[-68,-76,78],[-69,-75,78],[-70,78],[-78],[1,2,6,7,8,16,18,19,21,22,24,25,26,27,37,38,39,46,47,48],[3,4,9,10,11,15,17,19,28,29,30,31,32,33,40,41,42,45,49,50],[4,5,11,12,14,17,23,27,29,30,34,35,41,42,43,45,48,49]],\"atoms\":[{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":77,\"b\":57},{\"tag\":\"incompatible\",\"a\":99,\"b\":96},{\"tag\":\"mate\",\"ridge\":261,\"a\":14,\"owners\":[13,33,35,57,61,63,64,67,69]},{\"tag\":\"mate\",\"ridge\":261,\"a\":37,\"owners\":[13,57,61,63,64,67,69]},{\"tag\":\"mate\",\"ridge\":276,\"a\":13,\"owners\":[87,88,98,99]},{\"tag\":\"mate\",\"ridge\":276,\"a\":33,\"owners\":[98,99]},{\"tag\":\"mate\",\"ridge\":276,\"a\":63,\"owners\":[88,99]},{\"tag\":\"mate\",\"ridge\":276,\"a\":64,\"owners\":[87,88,98]},{\"tag\":\"mate\",\"ridge\":276,\"a\":66,\"owners\":[87,99]},{\"tag\":\"mate\",\"ridge\":276,\"a\":67,\"owners\":[87,88,98]},{\"tag\":\"mate\",\"ridge\":388,\"a\":14,\"owners\":[88,89,97,98]},{\"tag\":\"mate\",\"ridge\":388,\"a\":37,\"owners\":[97,98]},{\"tag\":\"mate\",\"ridge\":388,\"a\":60,\"owners\":[88,89,98]},{\"tag\":\"mate\",\"ridge\":388,\"a\":68,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":552,\"a\":16,\"owners\":[91,93,100,101]},{\"tag\":\"mate\",\"ridge\":552,\"a\":42,\"owners\":[100,101]},{\"tag\":\"mate\",\"ridge\":552,\"a\":71,\"owners\":[93,101]},{\"tag\":\"mate\",\"ridge\":552,\"a\":73,\"owners\":[91,101]},{\"tag\":\"mate\",\"ridge\":552,\"a\":75,\"owners\":[91,93,100]},{\"tag\":\"mate\",\"ridge\":552,\"a\":76,\"owners\":[91,93,100]},{\"tag\":\"mate\",\"ridge\":584,\"a\":17,\"owners\":[92,93,96,100]},{\"tag\":\"mate\",\"ridge\":584,\"a\":44,\"owners\":[96,100]},{\"tag\":\"mate\",\"ridge\":584,\"a\":59,\"owners\":[92,93,100]},{\"tag\":\"mate\",\"ridge\":584,\"a\":72,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":584,\"a\":73,\"owners\":[92,96]},{\"tag\":\"mate\",\"ridge\":592,\"a\":20,\"owners\":[92,94,96,99,100]},{\"tag\":\"mate\",\"ridge\":592,\"a\":49,\"owners\":[96,99,100]},{\"tag\":\"mate\",\"ridge\":592,\"a\":65,\"owners\":[92,94,100]},{\"tag\":\"mate\",\"ridge\":592,\"a\":72,\"owners\":[94,99]},{\"tag\":\"mate\",\"ridge\":592,\"a\":78,\"owners\":[92,96,99]},{\"tag\":\"mate\",\"ridge\":592,\"a\":80,\"owners\":[92,94,96,100]},{\"tag\":\"mate\",\"ridge\":294,\"a\":35,\"owners\":[87,89]},{\"tag\":\"mate\",\"ridge\":294,\"a\":87,\"owners\":[35,89]},{\"tag\":\"mate\",\"ridge\":294,\"a\":89,\"owners\":[35,87]},{\"tag\":\"mate\",\"ridge\":538,\"a\":40,\"owners\":[91,92]},{\"tag\":\"mate\",\"ridge\":402,\"a\":88,\"owners\":[50,95]},{\"tag\":\"mate\",\"ridge\":610,\"a\":51,\"owners\":[93,94]},{\"tag\":\"mate\",\"ridge\":540,\"a\":55,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":540,\"a\":96,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":300,\"a\":57,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":300,\"a\":97,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":780,\"a\":61,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":180,\"a\":86,\"owners\":[62,98]},{\"tag\":\"mate\",\"ridge\":180,\"a\":98,\"owners\":[62,86]},{\"tag\":\"mate\",\"ridge\":836,\"a\":69,\"owners\":[99]},{\"tag\":\"mate\",\"ridge\":836,\"a\":99,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":904,\"a\":77,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":904,\"a\":101,\"owners\":[77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":55,\"full_literals\":[-15,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":69,\"full_literals\":[-27,51]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[57,77],\"full_literals\":[-52,16,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":57,\"full_literals\":[-16,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":77,\"full_literals\":[-33,52]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[96,99],\"full_literals\":[-53,45,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":96,\"full_literals\":[-45,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":99,\"full_literals\":[-48,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":97,\"full_literals\":[-46,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":101,\"full_literals\":[-50,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":35,\"full_literals\":[-7,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":50,\"full_literals\":[-13,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":62,\"full_literals\":[-20,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":40,\"full_literals\":[-9,56]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[86,87,88],\"full_literals\":[-57,36,37,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":86,\"full_literals\":[-36,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":87,\"full_literals\":[-37,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":88,\"full_literals\":[-38,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":91,\"full_literals\":[-40,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":93,\"full_literals\":[-42,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":92,\"full_literals\":[-41,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":94,\"full_literals\":[-43,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":100,\"full_literals\":[-49,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":89,\"full_literals\":[-39,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":95,\"full_literals\":[-44,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":98,\"full_literals\":[-47,60]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-61,52,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-53,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-52,false,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-52,-53,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-61,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-62,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-51,false,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-51,-61,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-51,-62,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-56,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-55,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-66,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-54,false,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-67,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-63,-67,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-64,false,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-65,false,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-59,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-58,false,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-71,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-57,false,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-57,-71,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-60,false,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-74,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-72,false,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-72,-74,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-73,false,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-73,-74,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-77,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-68,-76,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-69,-75,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-70,false,78],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":22,\"owners\":[13,14,33,35,37,57,60,61,63,64,66,67,68,69,87,88,89,97,98,99]},{\"tag\":\"edge\",\"edge\":29,\"owners\":[16,17,40,42,44,55,59,61,71,72,73,75,76,77,91,92,93,96,100,101]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[17,20,44,49,51,59,65,69,72,73,78,80,92,93,94,96,99,100]}]}"
  "112 -77 0 108 104 0\n113 -70 0 108 107 0\n114 -65 0 113 92 0\n115 1 2 6 7 8 16 18 21 22 24 25 26 27 37 38 39 46 47 48 0 42 109 0\n116 3 4 9 10 11 15 17 28 29 30 31 32 33 40 41 42 45 49 50 0 42 110 0\n117 57 68 0 89 79 76 56 88 87 57 40 86 85 61 59 81 50 64 65 66 44 5 8 9 10 34 7 11 13 14 6 12 115 0\n118 71 68 0 89 79 76 56 55 88 87 58 47 86 84 62 81 49 93 94 69 70 71 67 68 21 25 29 16 22 15 19 23 20 17 116 0\n119 68 0 112 88 86 85 59 60 61 117 118 97 103 98 72 73 33 36 63 74 43 0\n120 -76 0 119 108 105 0\n121 -73 0 120 102 0\n122 45 50 71 0 94 68 17 67 18 93 71 15 16 47 24 69 35 20 23 19 38 21 22 116 0\n123 -45 64 0 39 55 49 76 82 0\n124 48 -57 0 108 121 97 93 71 96 100 106 91 123 22 69 25 94 68 21 70 31 37 24 28 23 45 30 26 27 111 0\n125 -57 0 121 108 96 97 100 106 91 80 123 122 124 48 56 53 78 0\n126 -37 0 125 65 0\n127 -38 0 125 66 0\n128 -26 0 127 14 0\n129 -48 45 0 114 108 46 56 50 76 83 82 78 91 53 106 48 100 122 95 0\n130 -61 33 69 53 0 75 79 51 90 40 87 57 0\n131 16 60 48 0 42 127 126 128 74 6 10 8 5 72 13 32 7 9 45 41 4 3 115 0\n132 -72 45 0 120 108 129 54 100 101 106 98 131 1 52 130 77 0\n133 41 42 49 45 0 132 95 93 70 37 24 129 27 22 45 21 25 23 30 31 28 26 111 0\n134 45 0 132 95 93 94 69 68 133 71 0\n135 -48 0 134 2 0\n136 15 0 134 39 0\n137 53 0 134 55 0\n138 64 0 134 123 0\n139 51 0 136 49 0\n140 69 0 138 91 0\n141 -62 0 139 114 83 0\n142 -75 0 140 108 106 0\n143 -52 0 141 137 78 0\n144 -74 0 142 99 0\n145 -16 0 143 52 0\n146 -60 0 144 98 0\n147 0 145 146 135 131 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record069.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record069.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record069.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record069.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record069 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record069.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record069.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record069.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record069.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record069 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record069_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record069_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record069_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record069_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record069_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record069_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record069_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record069 Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record069_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record069_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record069_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00007.record069
