module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow25Part00010Data
public import GraphInputsRow25Part00010Frames
public import GraphInputsRow25Part00010Leaves
public import GraphInputsRow25Part00010Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00010.record068
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record068
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨82, by decide⟩, ⟨84, by decide⟩, ⟨86, by decide⟩, ⟨89, by decide⟩, ⟨93, by decide⟩, ⟨95, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 90071992547409920, (certNat% 3), (certNat% 4), 6442450944, (certNat% 5), (certNat% 6)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), (certNat% 9), (certNat% 10), (certNat% 11), (certNat% 12), 16777216]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 4), (certNat% 14), (certNat% 15), (certNat% 11), (certNat% 16), (certNat% 17), 167772160]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record068_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record068_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record068_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record068_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record068_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record068_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record068_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record068_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record068_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00010.record068

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00010.record094
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record094
def vertexColumn : Fields := ⟨10, (certNat% 18)⟩
def kindColumn : Fields := ⟨3, (certNat% 19)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨89, by decide⟩, ⟨101, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), (certNat% 21), 377990676480, (certNat% 22), (certNat% 23)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), (certNat% 21), (certNat% 25), 2595200384783876096, (certNat% 26), (certNat% 27), (certNat% 28)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), (certNat% 30), (certNat% 31), (certNat% 32), (certNat% 33)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), (certNat% 35), 2305843009347911680, (certNat% 30), (certNat% 32)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 36), (certNat% 30), (certNat% 37), (certNat% 33), (certNat% 32), 134217728]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), (certNat% 39), (certNat% 40), (certNat% 41), (certNat% 32), (certNat% 42), 576460752437641216]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 43), (certNat% 39), (certNat% 44), (certNat% 45), (certNat% 46)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 47), (certNat% 48), (certNat% 25), (certNat% 49), (certNat% 50), (certNat% 51), (certNat% 46)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 52), (certNat% 53), (certNat% 21), (certNat% 31), (certNat% 54), (certNat% 55), (certNat% 56)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 57), 2882303761651335168, (certNat% 58), (certNat% 59), (certNat% 53), (certNat% 35)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 60), (certNat% 61), (certNat% 53), 4035225266258182144, (certNat% 30), (certNat% 62)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 63), 4035225266258182144, (certNat% 48), (certNat% 64), (certNat% 58), (certNat% 65), (certNat% 66)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c17 c14
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 67), (certNat% 58), (certNat% 39), (certNat% 66), (certNat% 68), (certNat% 46)]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 69), (certNat% 68), (certNat% 33), 1127042368143360, (certNat% 31), (certNat% 56), (certNat% 70)]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 71), (certNat% 30), (certNat% 68), (certNat% 61), (certNat% 33)]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 72), (certNat% 37), (certNat% 73), (certNat% 74), (certNat% 53), (certNat% 46), (certNat% 75)]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c23 c22
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 76), (certNat% 30), 343630938112, (certNat% 61), (certNat% 77), (certNat% 78), (certNat% 79)]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 80), (certNat% 79), (certNat% 81), (certNat% 82), (certNat% 83), (certNat% 84), (certNat% 85)]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 86), (certNat% 87), (certNat% 88), (certNat% 89), (certNat% 53), (certNat% 90), (certNat% 51)]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 91), (certNat% 92), (certNat% 93), (certNat% 53), (certNat% 94), (certNat% 54), 2594074484877033472, (certNat% 51)]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c28 c27
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c29 c26
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c30 c25
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c31 c24
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c32 c21
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c33 c18
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c34 c13
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c35 c12
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c36 c9
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c37 c2
  c38
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record094_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record094_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record094_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record094_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record094_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record094_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record094_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record094_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record094_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00010.record094

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00010.record079
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2f0da0f8d50f4730ec370bc1f362d4a72d2b2a9a96a2e87ad1b16959562d876538ae1b89e1783ed86e1d46d1ac6713c749727299a5693a4d92e479d15c53971595555354b51d58d534cd2b46d2745d0f723c4cb3c2e2b4acab26c3bc1ca785d1725c3723c2f07e703c0e83514c3323243a312c4a92550d2370388e130cd0b0ad0705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "269a4936da6db6db6db4db6db6d24db6d34db6db49a4934da49249a4d2492449249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record079 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record079 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record079.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record079.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record079.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 47), (facetIndex 48), (facetIndex 79), (facetIndex 99)]))
 (.leaf ([(facetIndex 68), (facetIndex 69), (facetIndex 92), (facetIndex 104)])))
 (.branch 3
 (.leaf ([(facetIndex 28), (facetIndex 29), (facetIndex 31), (facetIndex 39)]))
 (.leaf ([(facetIndex 35), (facetIndex 36), (facetIndex 37), (facetIndex 40)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 25), (facetIndex 27), (facetIndex 34), (facetIndex 38)]))
 (.leaf ([(facetIndex 46), (facetIndex 51), (facetIndex 61), (facetIndex 67)])))
 (.branch 7
 (.leaf ([(facetIndex 97), (facetIndex 98), (facetIndex 100), (facetIndex 102)]))
 (.branch 8
 (.leaf ([(facetIndex 43), (facetIndex 45), (facetIndex 50), (facetIndex 59)]))
 (.leaf ([(facetIndex 23), (facetIndex 24), (facetIndex 26), (facetIndex 32)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "1060606600001z16;11500000507000000057000570700324333408202248488z17;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 54), (facetIndex 82), (facetIndex 83)]))
 (.branch 2
 (.leaf ([(facetIndex 64), (facetIndex 88), (facetIndex 89)]))
 (.leaf ([(facetIndex 84), (facetIndex 85), (facetIndex 93)]))))
 (.branch 4
 (.leaf ([(facetIndex 90), (facetIndex 91), (facetIndex 94)]))
 (.branch 5
 (.leaf ([(facetIndex 52), (facetIndex 53), (facetIndex 101)]))
 (.leaf ([(facetIndex 62), (facetIndex 63), (facetIndex 103)])))))
 (.branch 9
 (.branch 7
 (.leaf ([(facetIndex 30), (facetIndex 41), (facetIndex 44), (facetIndex 77)]))
 (.branch 8
 (.leaf ([(facetIndex 49), (facetIndex 74), (facetIndex 78), (facetIndex 80)]))
 (.leaf ([(facetIndex 33), (facetIndex 81), (facetIndex 95)]))))
 (.branch 11
 (.branch 10
 (.leaf ([(facetIndex 42), (facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 66), (facetIndex 70), (facetIndex 71), (facetIndex 73)]))
 (.leaf ([(facetIndex 58), (facetIndex 65), (facetIndex 72)])))
 (.branch 12
 (.leaf ([(facetIndex 60), (facetIndex 75), (facetIndex 76), (facetIndex 96)]))
 (.leaf ([(facetIndex 86), (facetIndex 87)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "5040000b83203311cc220087076bb79a990009a1550b0a9990440070000609600000008006z1e;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 13
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0007 : List Nat := [0]
def grouped3_0008 : List Nat := [0, 1, 2]
def grouped3_0009 : List Nat := [0, 1, 2, 3, 4, 5]
def grouped3_0011 : List Nat := [1]
def grouped3_0012 : List Nat := [1, 2]
def grouped3_0013 : List Nat := [2]
def grouped3_0014 : List Nat := [3]
def grouped3_0015 : List Nat := [3, 4, 5]
def grouped3_0016 : List Nat := [4]
def grouped3_0017 : List Nat := [4, 5]
def grouped3_0018 : List Nat := [5]
def grouped3_0019 : List Nat := [6]
def grouped3_0020 : List Nat := [6, 7, 8]
def grouped3_0021 : List Nat := [6, 7, 8, 9, 10, 11, 12]
def grouped3_0022 : List Nat := [7]
def grouped3_0023 : List Nat := [7, 8]
def grouped3_0024 : List Nat := [8]
def grouped3_0025 : List Nat := [9]
def grouped3_0026 : List Nat := [9, 10]
def grouped3_0027 : List Nat := [9, 10, 11, 12]
def grouped3_0028 : List Nat := [10]
def grouped3_0029 : List Nat := [11]
def grouped3_0030 : List Nat := [11, 12]
def grouped3_0031 : List Nat := [12]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record079 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record079_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00010.record079" "{\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":9,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":10},{\"tag\":\"group\",\"kind\":3,\"index\":11},{\"tag\":\"group\",\"kind\":3,\"index\":12},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0030\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0027\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0027\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00010.record079" 81

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00010.record079" "{\"ridges\":[[8,769],[8,770],[22,608],[28,22],[29,22],[31,769],[31,770],[35,42],[36,42],[37,769],[37,770],[39,769],[39,770],[40,769],[40,770],[53,581],[57,581],[63,585],[64,808],[66,585],[68,608],[71,337],[73,353],[83,582],[85,582],[85,832],[89,586],[90,808],[91,586],[92,608],[93,338],[93,832],[94,354],[101,788],[103,832],[104,608]],\"owners\":[[28,22,[74,75,76,80,81,83],[1,23,26,27,29,82,84]],[29,22,[74,75,76,80,81,82],[1,23,26,27,28,83,84]],[35,42,[74,77,78,86,87,89],[3,24,32,34,36,88,90]],[36,42,[74,77,78,86,87,88],[3,24,32,34,35,89,90]],[8,769,[54,57,64,66,71,73],[31,37,39,40]],[31,769,[64,66,71,73],[8,37,39,40,54,57]],[37,769,[54,57,71,73],[8,31,39,40,64,66]],[39,769,[57,64,66,73],[8,31,37,40,54,71]],[40,769,[54,57,66,71],[8,31,37,39,64,73]],[8,770,[84,85,90,91,93,94],[31,37,39,40]],[31,770,[90,91,93,94],[8,37,39,40,84,85]],[37,770,[84,85,93,94],[8,31,39,40,90,91]],[39,770,[85,90,91,94],[8,31,37,40,84,93]],[40,770,[84,85,91,93],[8,31,37,39,90,94]],[22,608,[63,72,73,89,94,103],[68,92,104]],[68,608,[89,94,103],[22,63,72,73,92,104]],[92,608,[63,72,73,103],[22,68,89,94,104]],[104,608,[63,73,89,94,103],[22,68,72,92]],[71,337,[52],[]],[53,581,[57],[]],[57,581,[53],[]],[101,788,[54,84],[]],[85,832,[66,71,73,103],[57,91,93,94,101]],[93,832,[57,66,73,103],[71,85,91,94,101]],[103,832,[57,71,85,93,101],[66,73,91,94]],[73,353,[62],[]],[63,585,[66],[]],[66,585,[63],[]],[64,808,[90,103],[]],[90,808,[64,103],[]],[93,338,[82],[]],[83,582,[85],[]],[85,582,[83],[]],[94,354,[88],[]],[89,586,[91],[]],[91,586,[89],[]]],\"edges\":[[41,[22,53,57,63,66,68,70,71,72,73,83,85,89,91,92,93,94,101,103,104]],[44,[8,31,37,39,40,54,57,64,66,71,73,84,85,90,91,93,94,101,103]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00010.record079" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00010.record079\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-6,-5],[-9,-7],[-17,-6],[-17,-7],[-3,24,25,26,29,30,32],[-4,24,25,26,29,30,31],[-6,24,27,28,35,36,38],[-7,24,27,28,35,36,37],[-1,13,14,17,18,21,23],[-5,17,18,21,23],[-8,13,14,21,23],[-9,14,17,18,23],[-10,13,14,18,21],[-1,33,34,39,40,42,43],[-5,39,40,42,43],[-8,33,34,42,43],[-9,34,39,40,43],[-10,33,34,40,42],[-2,16,22,23,38,43,45],[-19,38,43,45],[-41,16,22,23,45],[-46,16,23,38,43,45],[-21,11],[-12,14],[-14,12],[-44,13,33],[-34,18,21,23,45],[-42,14,18,23,45],[-45,14,21,34,42,44],[-23,15],[-16,18],[-18,16],[-17,39,45],[-39,17,45],[-42,31],[-32,34],[-34,32],[-43,37],[-38,40],[-40,38],[-47,3,4,5,9],[-48,6,7,8,10],[-49,47],[-49,48],[-50,49],[-51,50],[51],[-13,52],[-31,52],[-32,52],[-17,53],[-37,53],[-38,53],[-33,54],[-34,54],[-42,54],[-39,55],[-40,55],[-43,55],[-11,56],[-12,56],[-44,56],[-15,57],[-16,57],[-45,57],[-27,58],[-24,59],[-28,59],[-29,59],[-30,60],[-14,61],[-18,61],[-20,61],[-21,61],[-23,61],[-22,62],[-25,63],[-26,63],[-35,64],[-36,64],[-54,65],[-53,65],[-65,66],[-52,66],[-52,-65,67],[-57,68],[-56,68],[-68,69],[-55,69],[-69,70],[-66,70],[-66,-69,71],[-67,71],[-67,-69,72],[-60,73],[-59,73],[-73,74],[-58,74],[-62,75],[-61,75],[-64,76],[-63,76],[-76,77],[-75,77],[-75,-76,78],[-77,79],[-78,80],[-74,79],[-74,-77,80],[-70,-80,81],[-71,-79,81],[-72,81],[-81],[2,12,14,16,18,19,20,21,22,23,32,34,38,40,41,42,43,44,45,46],[1,5,8,9,10,13,14,17,18,21,23,33,34,39,40,42,43,44,45]],\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":10,\"kind\":3},{\"tag\":\"group\",\"index\":11,\"kind\":3},{\"tag\":\"group\",\"index\":12,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":35,\"b\":31},{\"tag\":\"incompatible\",\"a\":39,\"b\":36},{\"tag\":\"incompatible\",\"a\":64,\"b\":35},{\"tag\":\"incompatible\",\"a\":64,\"b\":36},{\"tag\":\"mate\",\"ridge\":22,\"a\":28,\"owners\":[74,75,76,80,81,83]},{\"tag\":\"mate\",\"ridge\":22,\"a\":29,\"owners\":[74,75,76,80,81,82]},{\"tag\":\"mate\",\"ridge\":42,\"a\":35,\"owners\":[74,77,78,86,87,89]},{\"tag\":\"mate\",\"ridge\":42,\"a\":36,\"owners\":[74,77,78,86,87,88]},{\"tag\":\"mate\",\"ridge\":769,\"a\":8,\"owners\":[54,57,64,66,71,73]},{\"tag\":\"mate\",\"ridge\":769,\"a\":31,\"owners\":[64,66,71,73]},{\"tag\":\"mate\",\"ridge\":769,\"a\":37,\"owners\":[54,57,71,73]},{\"tag\":\"mate\",\"ridge\":769,\"a\":39,\"owners\":[57,64,66,73]},{\"tag\":\"mate\",\"ridge\":769,\"a\":40,\"owners\":[54,57,66,71]},{\"tag\":\"mate\",\"ridge\":770,\"a\":8,\"owners\":[84,85,90,91,93,94]},{\"tag\":\"mate\",\"ridge\":770,\"a\":31,\"owners\":[90,91,93,94]},{\"tag\":\"mate\",\"ridge\":770,\"a\":37,\"owners\":[84,85,93,94]},{\"tag\":\"mate\",\"ridge\":770,\"a\":39,\"owners\":[85,90,91,94]},{\"tag\":\"mate\",\"ridge\":770,\"a\":40,\"owners\":[84,85,91,93]},{\"tag\":\"mate\",\"ridge\":608,\"a\":22,\"owners\":[63,72,73,89,94,103]},{\"tag\":\"mate\",\"ridge\":608,\"a\":68,\"owners\":[89,94,103]},{\"tag\":\"mate\",\"ridge\":608,\"a\":92,\"owners\":[63,72,73,103]},{\"tag\":\"mate\",\"ridge\":608,\"a\":104,\"owners\":[63,73,89,94,103]},{\"tag\":\"mate\",\"ridge\":337,\"a\":71,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":581,\"a\":53,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":581,\"a\":57,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":788,\"a\":101,\"owners\":[54,84]},{\"tag\":\"mate\",\"ridge\":832,\"a\":85,\"owners\":[66,71,73,103]},{\"tag\":\"mate\",\"ridge\":832,\"a\":93,\"owners\":[57,66,73,103]},{\"tag\":\"mate\",\"ridge\":832,\"a\":103,\"owners\":[57,71,85,93,101]},{\"tag\":\"mate\",\"ridge\":353,\"a\":73,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":585,\"a\":63,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":585,\"a\":66,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":808,\"a\":64,\"owners\":[90,103]},{\"tag\":\"mate\",\"ridge\":808,\"a\":90,\"owners\":[64,103]},{\"tag\":\"mate\",\"ridge\":338,\"a\":93,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":582,\"a\":83,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":582,\"a\":85,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":354,\"a\":94,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":586,\"a\":89,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":586,\"a\":91,\"owners\":[89]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[28,29,31,39],\"full_literals\":[-47,3,4,5,9]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[35,36,37,40],\"full_literals\":[-48,6,7,8,10]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-49,47,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-49,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-50,false,49],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-51,50,false],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":9,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":54,\"full_literals\":[-13,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":82,\"full_literals\":[-31,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":83,\"full_literals\":[-32,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":64,\"full_literals\":[-17,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":88,\"full_literals\":[-37,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":89,\"full_literals\":[-38,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":84,\"full_literals\":[-33,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":85,\"full_literals\":[-34,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":93,\"full_literals\":[-42,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":90,\"full_literals\":[-39,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":91,\"full_literals\":[-40,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":94,\"full_literals\":[-43,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":52,\"full_literals\":[-11,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":53,\"full_literals\":[-12,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":101,\"full_literals\":[-44,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":62,\"full_literals\":[-15,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":63,\"full_literals\":[-16,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":103,\"full_literals\":[-45,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":77,\"full_literals\":[-27,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":74,\"full_literals\":[-24,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":78,\"full_literals\":[-28,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":80,\"full_literals\":[-29,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":81,\"full_literals\":[-30,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":57,\"full_literals\":[-14,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":66,\"full_literals\":[-18,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":70,\"full_literals\":[-20,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":71,\"full_literals\":[-21,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":73,\"full_literals\":[-23,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":72,\"full_literals\":[-22,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":75,\"full_literals\":[-25,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":76,\"full_literals\":[-26,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":12,\"member\":86,\"full_literals\":[-35,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":12,\"member\":87,\"full_literals\":[-36,64]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-54,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-65,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-52,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-52,-65,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-57,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-56,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-68,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-55,false,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-69,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-66,false,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-66,-69,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0009\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-67,false,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0009\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-67,-69,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-60,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-59,false,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-73,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-58,false,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-62,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-61,false,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[11],\"right\":[12],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0030\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-64,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[11],\"right\":[12],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0030\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9,10],\"right\":[11,12],\"left_name\":\"grouped3_0026\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0027\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-76,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9,10],\"right\":[11,12],\"left_name\":\"grouped3_0026\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0027\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-75,false,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9,10],\"right\":[11,12],\"left_name\":\"grouped3_0026\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0027\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-75,-76,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11,12],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-77,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11,12],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-78,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11,12],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-74,false,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11,12],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-74,-77,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11,12],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-70,-80,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11,12],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-71,-79,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11,12],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-72,false,81],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":41,\"owners\":[22,53,57,63,66,68,70,71,72,73,83,85,89,91,92,93,94,101,103,104]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[8,31,37,39,40,54,57,64,66,71,73,84,85,90,91,93,94,101,103]}]}"
  "116 50 0 47 46 0\n117 49 0 116 45 0\n118 47 0 117 43 0\n119 48 0 117 44 0\n120 -72 0 113 112 0\n121 70 0 90 91 88 89 83 84 86 87 57 58 59 81 48 63 64 65 60 61 62 33 54 55 56 30 32 23 25 10 14 18 17 16 115 0\n122 -80 0 121 113 110 0\n123 -78 0 122 107 0\n124 69 75 0 100 72 31 71 24 75 74 73 99 76 88 89 86 87 58 59 65 62 39 28 27 21 20 22 19 36 114 0\n125 75 71 0 100 71 72 74 75 124 92 83 84 81 82 48 54 55 56 51 52 53 26 9 11 13 29 10 34 12 38 40 115 0\n126 65 74 64 0 119 97 96 68 67 98 66 80 79 81 82 54 55 56 52 53 38 8 40 7 16 18 42 0\n127 74 71 0 123 118 125 105 102 78 77 101 93 97 95 96 70 67 69 126 83 85 92 49 50 89 35 6 37 5 57 58 59 17 15 41 0\n128 71 0 122 125 127 104 109 0\n129 -79 0 128 113 111 0\n130 -77 0 129 106 0\n131 -74 0 129 108 0\n132 -76 0 130 103 0\n133 -75 0 130 104 0\n134 -73 0 131 97 0\n135 -64 0 132 101 0\n136 -63 0 132 102 0\n137 -61 0 133 100 0\n138 69 0 133 124 0\n139 -60 0 134 95 0\n140 -59 0 134 96 0\n141 65 0 135 131 126 0\n142 -25 0 136 77 0\n143 -26 0 136 78 0\n144 -14 0 137 71 0\n145 -18 0 137 72 0\n146 -21 0 137 74 0\n147 -23 0 137 75 0\n148 -67 0 138 120 94 0\n149 -30 0 139 70 0\n150 -24 0 140 67 0\n151 -29 0 140 69 0\n152 -52 0 141 148 85 0\n153 -13 0 152 48 0\n154 -31 0 152 49 0\n155 -32 0 152 50 0\n156 -8 0 153 144 146 147 11 0\n157 -10 0 153 144 145 146 13 0\n158 -4 0 154 150 143 151 149 142 6 0\n159 -3 0 155 142 143 150 149 151 5 0\n160 -6 0 159 158 118 147 145 144 1 3 41 12 0\n161 7 0 160 119 157 156 42 0\n162 -9 0 161 2 0\n163 -17 0 161 4 0\n164 5 0 162 118 158 159 41 0\n165 0 164 163 145 146 147 10 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record079.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record079.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record079.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record079.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record079 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record079.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record079.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record079.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record079.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record079 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record079_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record079_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record079_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record079_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record079_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record079_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record079_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record079 Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record079_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record079_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record079_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00010.record079
