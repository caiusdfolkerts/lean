module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow19Part00035Data
public import GraphInputsRow19Part00035Frames
public import GraphInputsRow19Part00035Leaves
public import GraphInputsRow19Part00035Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00035.record063
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record063
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨22, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨46, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨68, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 7881299347898368, (certNat% 3), 68720001024, 788529152]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4972045332961296384, 1125968911532032, 6755399442104320, (certNat% 4), 4432540467200]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4972045401945014272, (certNat% 5), 4432540467200, 2251799818928128, 5629499534213120]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [360363747360636928, 4611686087146864640, 7881299347898368, (certNat% 4)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), 1125968626319360, 2322168557862912, 4503599627370496]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), 72061992084439040, (certNat% 8), 288300744895889408]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), 6755399441055744, (certNat% 10), 360287970189639680]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), 893353197568, 2322168557862912, 76565591711809536, 288230376151711744]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), 288300744895889408, 369098752, 4611686087146864640]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), 962072674304, 2322168557862912, 360287970189639680]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), 234881024, 687194767360, 6755399441055744]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), 234881024, 4611756387171565568, 1030792151040, 2251799813685248]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c16 c13
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c17 c12
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), 288300744895889408, 72062035034112000, 2251799852482560, 4503599761588224]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), 288300744895889408, 3377699720527872, (certNat% 3), 117440512]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), 360287978779574272, (certNat% 8), 2322168562057216, 962072674304]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 8), 288300744895889408, 1005022347264, 72057594037927936]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), 4611756387171565568, 8594128896, 360287970189639680, 996432412672]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), (certNat% 22), 288230651029618688, 4611686018427387904, 721554505728]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), 76561193665298432, (certNat% 3), 84934656, 1005022347264, 288230376151711744]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c26 c23
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c27 c22
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c28 c21
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c29 c20
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c30 c19
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c31 c18
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c32 c11
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨19, by decide⟩ c33 c2
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨18, by decide⟩ c34 c1
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c35 c0
  c36
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record063_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record063_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record063_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record063_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record063_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record063_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record063_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record063_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record063_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00035.record063

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00035.record019
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1d8ae2b4ab29c8f0bc749ca6695a368e6558d68b8ae27b19564d98e4b939655554d58d4b58b4ad8749d0f4e354cd352ccb8ad2b2ad1b26c5b51cc789ca719d1725c5783c8f0bc1f350aa318a65462986519896151554342c2b11c27"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db6db6da69a6934da4934d36d34d249b4924da6d3249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record019 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record019 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record019.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record019.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record019.data.quota

def groupMembers1 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 0)]))
 (.leaf ([(facetIndex 1)])))
 (.branch 3
 (.leaf ([(facetIndex 2)]))
 (.leaf ([(facetIndex 3)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 4)]))
 (.leaf ([(facetIndex 5)])))
 (.branch 7
 (.leaf ([(facetIndex 6)]))
 (.leaf ([(facetIndex 7)])))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ([(facetIndex 8)]))
 (.leaf ([(facetIndex 9)])))
 (.branch 11
 (.leaf ([(facetIndex 10)]))
 (.leaf ([(facetIndex 11)]))))
 (.branch 14
 (.branch 13
 (.leaf ([(facetIndex 12)]))
 (.leaf ([(facetIndex 13)])))
 (.branch 15
 (.leaf ([(facetIndex 14)]))
 (.leaf ([(facetIndex 15)]))))))
def groupColors1 : PackedGraphCertificate.Fields :=
  ⟨4, 18364758544493064720⟩
def grouping1 : FacetSat.Grouping data.count where
  count := 16
  members := fun g => groupMembers1.get g
  color := fun c => groupColors1.get c.val
def groupKind1 : List Nat := List.range grouping1.count

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 30), (facetIndex 53), (facetIndex 54)]))
 (.leaf ([(facetIndex 17), (facetIndex 31), (facetIndex 32), (facetIndex 33)])))
 (.branch 3
 (.leaf ([(facetIndex 41), (facetIndex 43), (facetIndex 45), (facetIndex 51)]))
 (.leaf ([(facetIndex 24), (facetIndex 56), (facetIndex 60)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 27), (facetIndex 35), (facetIndex 37)]))
 (.leaf ([(facetIndex 20), (facetIndex 46), (facetIndex 47), (facetIndex 48)])))
 (.branch 7
 (.leaf ([(facetIndex 23), (facetIndex 25)]))
 (.leaf ([(facetIndex 26), (facetIndex 58)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "31c3000405b504100208092009f3c05008000000000000"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 28), (facetIndex 63), (facetIndex 64)]))
 (.leaf ([(facetIndex 39), (facetIndex 68), (facetIndex 70)])))
 (.branch 3
 (.leaf ([(facetIndex 66), (facetIndex 69), (facetIndex 71)]))
 (.branch 4
 (.leaf ([(facetIndex 61), (facetIndex 65), (facetIndex 72)]))
 (.leaf ([(facetIndex 16), (facetIndex 18), (facetIndex 19), (facetIndex 67)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 21), (facetIndex 22), (facetIndex 55), (facetIndex 62)]))
 (.leaf ([(facetIndex 29), (facetIndex 34), (facetIndex 38), (facetIndex 40), (facetIndex 44)])))
 (.branch 8
 (.leaf ([(facetIndex 36), (facetIndex 42), (facetIndex 49), (facetIndex 50), (facetIndex 52)]))
 (.branch 9
 (.leaf ([(facetIndex 57)]))
 (.leaf ([(facetIndex 59)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "321214230053090805007077000060706160706000060000005504404z10;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped1_0000 : List Nat := [0, 1]
def grouped1_0001 : List Nat := [0, 1, 2, 3]
def grouped1_0002 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]
def grouped1_0004 : List Nat := [2]
def grouped1_0005 : List Nat := [2, 3]
def grouped1_0006 : List Nat := [3]
def grouped1_0007 : List Nat := [4, 5]
def grouped1_0008 : List Nat := [4, 5, 6, 7]
def grouped1_0009 : List Nat := [6]
def grouped1_0010 : List Nat := [6, 7]
def grouped1_0011 : List Nat := [7]
def grouped1_0012 : List Nat := [8]
def grouped1_0013 : List Nat := [8, 9]
def grouped1_0014 : List Nat := [8, 9, 10, 11]
def grouped1_0015 : List Nat := [8, 9, 10, 11, 12, 13, 14, 15]
def grouped1_0016 : List Nat := [9]
def grouped1_0017 : List Nat := [10]
def grouped1_0018 : List Nat := [10, 11]
def grouped1_0019 : List Nat := [11]
def grouped1_0020 : List Nat := [12]
def grouped1_0021 : List Nat := [12, 13]
def grouped1_0022 : List Nat := [12, 13, 14, 15]
def grouped1_0023 : List Nat := [13]
def grouped1_0024 : List Nat := [14]
def grouped1_0025 : List Nat := [14, 15]
def grouped1_0026 : List Nat := [15]
def grouped2_0027 : List Nat := [0]
def grouped2_0028 : List Nat := [0, 1]
def grouped2_0029 : List Nat := [0, 1, 2, 3]
def grouped2_0031 : List Nat := [1]
def grouped2_0032 : List Nat := [2]
def grouped2_0033 : List Nat := [2, 3]
def grouped2_0034 : List Nat := [3]
def grouped2_0035 : List Nat := [4]
def grouped2_0036 : List Nat := [4, 5]
def grouped2_0037 : List Nat := [4, 5, 6, 7]
def grouped2_0038 : List Nat := [5]
def grouped2_0039 : List Nat := [6]
def grouped2_0040 : List Nat := [6, 7]
def grouped2_0041 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record019 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record019_matrix_checked

def leafCount : Nat := 8
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaf0000 : List (Fin data.count) := [(facetIndex 3), (facetIndex 15), (facetIndex 25), (facetIndex 27), (facetIndex 31), (facetIndex 48), (facetIndex 51), (facetIndex 53), (facetIndex 60), (facetIndex 63), (facetIndex 65), (facetIndex 68), (facetIndex 69)]
theorem leaf0000_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0000 = true := by
  decide +kernel
theorem leaf0000_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0000 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0000_counts_checked
def leaf0001 : List (Fin data.count) := [(facetIndex 10), (facetIndex 14), (facetIndex 25), (facetIndex 27), (facetIndex 32), (facetIndex 41), (facetIndex 46), (facetIndex 53), (facetIndex 60), (facetIndex 63), (facetIndex 65), (facetIndex 70), (facetIndex 71)]
theorem leaf0001_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0001 = true := by
  decide +kernel
theorem leaf0001_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0001 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0001_counts_checked
def leaf0002 : List (Fin data.count) := [(facetIndex 14), (facetIndex 15), (facetIndex 25), (facetIndex 27), (facetIndex 32), (facetIndex 48), (facetIndex 51), (facetIndex 53), (facetIndex 60), (facetIndex 63), (facetIndex 65), (facetIndex 68), (facetIndex 69)]
theorem leaf0002_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0002 = true := by
  decide +kernel
theorem leaf0002_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0002 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0002_counts_checked
def leaf0003 : List (Fin data.count) := [(facetIndex 10), (facetIndex 15), (facetIndex 25), (facetIndex 26), (facetIndex 32), (facetIndex 37), (facetIndex 48), (facetIndex 54), (facetIndex 56), (facetIndex 64), (facetIndex 70), (facetIndex 71), (facetIndex 72)]
theorem leaf0003_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0003 = true := by
  decide +kernel
theorem leaf0003_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0003 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0003_counts_checked
def leaf0004 : List (Fin data.count) := [(facetIndex 10), (facetIndex 11), (facetIndex 25), (facetIndex 27), (facetIndex 32), (facetIndex 48), (facetIndex 54), (facetIndex 56), (facetIndex 58), (facetIndex 64), (facetIndex 70), (facetIndex 71), (facetIndex 72)]
theorem leaf0004_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0004 = true := by
  decide +kernel
theorem leaf0004_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0004 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0004_counts_checked
def leaf0005 : List (Fin data.count) := [(facetIndex 6), (facetIndex 14), (facetIndex 25), (facetIndex 27), (facetIndex 32), (facetIndex 46), (facetIndex 51), (facetIndex 53), (facetIndex 60), (facetIndex 63), (facetIndex 65), (facetIndex 68), (facetIndex 69)]
theorem leaf0005_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0005 = true := by
  decide +kernel
theorem leaf0005_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0005 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0005_counts_checked
def leaf0006 : List (Fin data.count) := [(facetIndex 11), (facetIndex 15), (facetIndex 25), (facetIndex 27), (facetIndex 30), (facetIndex 31), (facetIndex 48), (facetIndex 51), (facetIndex 60), (facetIndex 64), (facetIndex 68), (facetIndex 69), (facetIndex 72)]
theorem leaf0006_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0006 = true := by
  decide +kernel
theorem leaf0006_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0006 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0006_counts_checked
def leaf0007 : List (Fin data.count) := [(facetIndex 11), (facetIndex 14), (facetIndex 24), (facetIndex 27), (facetIndex 32), (facetIndex 43), (facetIndex 48), (facetIndex 54), (facetIndex 58), (facetIndex 64), (facetIndex 70), (facetIndex 71), (facetIndex 72)]
theorem leaf0007_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0007 = true := by
  decide +kernel
theorem leaf0007_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0007 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0007_counts_checked
def leavesTable : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf (leaf0000))
 (.leaf (leaf0001)))
 (.branch 3
 (.leaf (leaf0002))
 (.leaf (leaf0003))))
 (.branch 6
 (.branch 5
 (.leaf (leaf0004))
 (.leaf (leaf0005)))
 (.branch 7
 (.leaf (leaf0006))
 (.leaf (leaf0007)))))
def leaves (j : Fin leafCount) : List (Fin data.count) := leavesTable.get j.val

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00035.record019" "{\"atoms\":[{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"group\",\"kind\":1,\"index\":3},{\"tag\":\"group\",\"kind\":1,\"index\":6},{\"tag\":\"group\",\"kind\":1,\"index\":8},{\"tag\":\"group\",\"kind\":1,\"index\":9},{\"tag\":\"group\",\"kind\":1,\"index\":10},{\"tag\":\"group\",\"kind\":1,\"index\":11},{\"tag\":\"group\",\"kind\":1,\"index\":12},{\"tag\":\"group\",\"kind\":1,\"index\":13},{\"tag\":\"group\",\"kind\":1,\"index\":14},{\"tag\":\"group\",\"kind\":1,\"index\":15},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0005\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0010\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0008\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0002\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0013\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0018\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0018\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0014\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0014\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0014\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0021\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0025\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0025\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0022\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0022\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0015\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0015\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"groupKind1\"},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0028\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0028\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0033\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0033\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0029\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0029\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0036\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0036\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0040\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0040\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0037\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0037\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":2}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00035.record019" 115

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00035.record019" "{\"ridges\":[[9,536],[10,521],[10,552],[16,7],[18,7],[19,526],[21,7],[24,162],[24,164],[25,7],[25,545],[26,196],[27,7],[27,70],[27,259],[27,321],[30,280],[31,11],[33,552],[35,266],[35,322],[37,322],[37,336],[40,141],[41,532],[41,536],[43,548],[43,552],[45,532],[45,548],[46,21],[49,225],[50,177],[51,536],[51,552],[53,280],[54,529],[54,536],[55,30],[56,164],[56,168],[58,134],[58,194],[58,208],[60,164],[63,138],[63,402],[64,456],[65,208],[68,652],[69,168],[69,652],[70,148],[70,688],[71,168],[71,688],[72,208],[72,280],[72,456]],\"owners\":[[27,70,[13,58,60],[1,20,23,59]],[31,11,[3,16,19,28,30,35],[2,17,18,29,33,34]],[27,259,[3,30,32],[4,22,37]],[35,266,[63],[3,30,32,62,64]],[27,321,[11,53],[4,35,47]],[35,322,[59,65],[4,27,37,62,64]],[37,322,[64],[4,27,35,59,62,65]],[46,21,[6,16,22,39,41,45],[5,20,21,40,44,47]],[54,529,[6,45,48],[9,51]],[41,532,[70],[6,45,48,67,68]],[45,532,[68],[6,41,48,67,70]],[25,545,[10,51],[7,33,45]],[43,548,[70],[7,25,45,57,67,69]],[45,548,[57,69],[7,25,43,67,70]],[30,280,[72],[8,53,54,62,63]],[53,280,[63],[8,30,54,62,72]],[72,280,[8,30,54],[53,62,63]],[10,521,[9,19,41,54],[33,43]],[9,536,[67,68,71],[41,51,54]],[41,536,[71],[9,51,54,67,68]],[51,536,[68],[9,41,54,67,71]],[54,536,[67,68,71],[9,41,51]],[10,552,[57,67,69,71],[33,43,51]],[33,552,[67,69,71],[10,43,51,57]],[43,552,[71],[10,33,51,57,67,69]],[51,552,[57,69],[10,33,43,67,71]],[37,336,[72],[11,47,53,59,62,65]],[58,134,[12,18,24,56],[13,21,26,55]],[24,162,[14],[12,31,38,60]],[24,164,[66,69,70],[12,42,44,49,56,60]],[56,164,[44,49,70],[12,24,42,60,66,69]],[60,164,[42,44,66,69,70],[12,24,49,56]],[58,194,[34,38,64],[13,26,36,60,61,65]],[26,196,[15],[13,46,49,60]],[63,138,[14,18,31,34,56],[29,55,61,64]],[56,168,[50,71],[14,31,42,66,69]],[69,168,[14,31,50],[42,56,66,71]],[71,168,[14,31,42,56],[50,66,69]],[70,148,[15,21,40,46,55,58],[44,66,68]],[58,208,[52,72],[15,36,46,61,65]],[65,208,[15,46,52],[36,58,61,72]],[72,208,[15,36,46,58],[52,61,65]],[55,30,[16],[]],[40,141,[18,42],[]],[19,526,[57],[]],[49,225,[38],[]],[50,177,[44],[]],[63,402,[65],[]],[64,456,[72],[]],[72,456,[64],[]],[68,652,[69],[]],[69,652,[68],[]],[70,688,[71],[]],[71,688,[70],[]]],\"edges\":[[29,[9,10,19,33,41,43,51,54,57,67,68,69,71]]],\"groupings\":[1,2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00035.record019" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00035.record019\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-19,-18],[-20,-12],[-20,-14],[-20,-19],[-21,-15],[-21,-18],[-21,-19],[-22,-15],[-22,-18],[-22,-21],[-25,-19],[-25,-21],[-26,-24],[-27,-20],[-28,-22],[-29,-26],[-30,-22],[-31,-22],[-31,-24],[-32,-22],[-33,-20],[-36,-20],[-37,-12],[-37,-20],[-37,-27],[-38,-20],[-39,-20],[-40,-21],[-40,-25],[-41,-22],[-41,-31],[-42,-35],[-42,-39],[-45,-44],[-46,-19],[-47,-28],[-47,-29],[-47,-41],[-47,-46],[-48,-24],[-48,-35],[-48,-45],[-48,-46],[-50,-12],[-50,-25],[-50,-35],[-50,-37],[-51,-20],[-51,-50],[-52,-24],[-52,-31],[-52,-40],[-53,-52],[-54,-18],[-54,-21],[-54,-52],[-55,-11],[-55,-15],[-55,-17],[-55,-23],[-55,-52],[-57,-52],[-58,-50],[-59,-36],[-59,-38],[-59,-50],[-60,-50],[-61,-35],[-61,-50],[-62,-45],[-63,-45],[-64,-29],[-64,-47],[-11,-20,-22],[-13,-20,-22],[-16,-20,-22],[-22,8,52,54],[-25,1,11,14,23,24,29],[-22,1,24,26],[-29,55],[-22,6,47],[-29,53,57],[-31,56],[-40,2,11,17,33,35,39],[-48,2,39,42],[-35,62],[-39,60],[-20,5,45],[-37,62],[-39,51,61],[-24,64],[-47,55],[-64,3,24,48],[-5,4,14,35,48],[-4,59,60,63],[-35,63],[-45,60],[-48,59,60,63],[-5,51,59,61,63],[-27,59,61,63],[-37,63],[-45,51,61],[-31,64],[-52,7,13,19,50],[-19,9],[-19,58,61,62],[-50,38,43,62],[-54,36,38,58,61,62],[-52,28,32,56],[-21,10],[-55,9,13,25,28,50],[-50,44,63],[-61,9,25,44],[-63,9,25,36,50],[-62,10,16,34,40,49,52],[-52,46,64],[-57,10,40,46],[-64,10,30,40,52],[-49,11],[-34,13,36],[-14,51],[-43,32],[-44,38],[-55,57],[-56,64],[-64,56],[-60,61],[-61,60],[-62,63],[-63,62],[-1,65],[-2,66],[-3,67],[-4,68],[-5,69],[-6,70],[-7,71],[-8,72],[-9,73],[-10,74],[-65,75],[-75,76],[-66,77],[-77,78],[-78,79],[-76,79],[-68,80],[-67,80],[-70,81],[-69,-70,82],[-81,83],[-82,84],[-80,-82,85],[-72,86],[-71,86],[-74,87],[-73,87],[-73,-74,88],[-87,89],[-88,90],[-86,89],[-86,-87,90],[-83,-90,92],[-84,91],[-84,-89,92],[-85,92],[-92,93],[-79,-91,93],[-93],[-94,24,47,48],[-95,12,25,26,27],[-96,35,37,39,45],[-97,19,50,54],[-98,22,29,31],[-99,15,40,41,42],[-100,18,20],[-101,21,52],[-102,94,95],[-103,94],[-103,95],[-104,96,97],[-105,96],[-105,97],[-106,102],[-106,103,105],[-107,103],[-106,104],[-107,105],[-108,98,99],[-109,98],[-109,99],[-110,100,101],[-111,100],[-111,101],[-112,108],[-112,109,111],[-113,109],[-112,110],[-113,111],[-114,106],[-114,107,113],[-114,112],[114],[-115,58,61,63],[-58,115],[-61,115],[-63,115],[-1,-10,-20,-22,-25,-42,-45,-47,-54,-55,-57,-60,-61],[-5,-9,-20,-22,-26,-35,-40,-47,-54,-55,-57,-62,-63],[-9,-10,-20,-22,-26,-42,-45,-47,-54,-55,-57,-60,-61],[-5,-10,-20,-21,-26,-31,-42,-48,-50,-56,-62,-63,-64],[-5,-6,-20,-22,-26,-42,-48,-50,-52,-56,-62,-63,-64],[-2,-9,-20,-22,-26,-40,-45,-47,-54,-55,-57,-60,-61],[-6,-10,-20,-22,-24,-25,-42,-45,-54,-56,-60,-61,-64],[-6,-9,-19,-22,-26,-37,-42,-48,-52,-56,-62,-63,-64],[4,5,14,27,35,37,45,48,51,59,60,61,63]],\"atoms\":[{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"group\",\"index\":3,\"kind\":1},{\"tag\":\"group\",\"index\":6,\"kind\":1},{\"tag\":\"group\",\"index\":8,\"kind\":1},{\"tag\":\"group\",\"index\":9,\"kind\":1},{\"tag\":\"group\",\"index\":10,\"kind\":1},{\"tag\":\"group\",\"index\":11,\"kind\":1},{\"tag\":\"group\",\"index\":12,\"kind\":1},{\"tag\":\"group\",\"index\":13,\"kind\":1},{\"tag\":\"group\",\"index\":14,\"kind\":1},{\"tag\":\"group\",\"index\":15,\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":24,\"b\":23},{\"tag\":\"incompatible\",\"a\":25,\"b\":17},{\"tag\":\"incompatible\",\"a\":25,\"b\":19},{\"tag\":\"incompatible\",\"a\":25,\"b\":24},{\"tag\":\"incompatible\",\"a\":26,\"b\":20},{\"tag\":\"incompatible\",\"a\":26,\"b\":23},{\"tag\":\"incompatible\",\"a\":26,\"b\":24},{\"tag\":\"incompatible\",\"a\":27,\"b\":20},{\"tag\":\"incompatible\",\"a\":27,\"b\":23},{\"tag\":\"incompatible\",\"a\":27,\"b\":26},{\"tag\":\"incompatible\",\"a\":31,\"b\":24},{\"tag\":\"incompatible\",\"a\":31,\"b\":26},{\"tag\":\"incompatible\",\"a\":32,\"b\":30},{\"tag\":\"incompatible\",\"a\":33,\"b\":25},{\"tag\":\"incompatible\",\"a\":34,\"b\":27},{\"tag\":\"incompatible\",\"a\":35,\"b\":32},{\"tag\":\"incompatible\",\"a\":36,\"b\":27},{\"tag\":\"incompatible\",\"a\":37,\"b\":27},{\"tag\":\"incompatible\",\"a\":37,\"b\":30},{\"tag\":\"incompatible\",\"a\":38,\"b\":27},{\"tag\":\"incompatible\",\"a\":39,\"b\":25},{\"tag\":\"incompatible\",\"a\":42,\"b\":25},{\"tag\":\"incompatible\",\"a\":43,\"b\":17},{\"tag\":\"incompatible\",\"a\":43,\"b\":25},{\"tag\":\"incompatible\",\"a\":43,\"b\":33},{\"tag\":\"incompatible\",\"a\":44,\"b\":25},{\"tag\":\"incompatible\",\"a\":45,\"b\":25},{\"tag\":\"incompatible\",\"a\":46,\"b\":26},{\"tag\":\"incompatible\",\"a\":46,\"b\":31},{\"tag\":\"incompatible\",\"a\":47,\"b\":27},{\"tag\":\"incompatible\",\"a\":47,\"b\":37},{\"tag\":\"incompatible\",\"a\":48,\"b\":41},{\"tag\":\"incompatible\",\"a\":48,\"b\":45},{\"tag\":\"incompatible\",\"a\":51,\"b\":50},{\"tag\":\"incompatible\",\"a\":52,\"b\":24},{\"tag\":\"incompatible\",\"a\":53,\"b\":34},{\"tag\":\"incompatible\",\"a\":53,\"b\":35},{\"tag\":\"incompatible\",\"a\":53,\"b\":47},{\"tag\":\"incompatible\",\"a\":53,\"b\":52},{\"tag\":\"incompatible\",\"a\":54,\"b\":30},{\"tag\":\"incompatible\",\"a\":54,\"b\":41},{\"tag\":\"incompatible\",\"a\":54,\"b\":51},{\"tag\":\"incompatible\",\"a\":54,\"b\":52},{\"tag\":\"incompatible\",\"a\":56,\"b\":17},{\"tag\":\"incompatible\",\"a\":56,\"b\":31},{\"tag\":\"incompatible\",\"a\":56,\"b\":41},{\"tag\":\"incompatible\",\"a\":56,\"b\":43},{\"tag\":\"incompatible\",\"a\":57,\"b\":25},{\"tag\":\"incompatible\",\"a\":57,\"b\":56},{\"tag\":\"incompatible\",\"a\":58,\"b\":30},{\"tag\":\"incompatible\",\"a\":58,\"b\":37},{\"tag\":\"incompatible\",\"a\":58,\"b\":46},{\"tag\":\"incompatible\",\"a\":59,\"b\":58},{\"tag\":\"incompatible\",\"a\":60,\"b\":23},{\"tag\":\"incompatible\",\"a\":60,\"b\":26},{\"tag\":\"incompatible\",\"a\":60,\"b\":58},{\"tag\":\"incompatible\",\"a\":63,\"b\":16},{\"tag\":\"incompatible\",\"a\":63,\"b\":20},{\"tag\":\"incompatible\",\"a\":63,\"b\":22},{\"tag\":\"incompatible\",\"a\":63,\"b\":28},{\"tag\":\"incompatible\",\"a\":63,\"b\":58},{\"tag\":\"incompatible\",\"a\":65,\"b\":58},{\"tag\":\"incompatible\",\"a\":66,\"b\":56},{\"tag\":\"incompatible\",\"a\":67,\"b\":42},{\"tag\":\"incompatible\",\"a\":67,\"b\":44},{\"tag\":\"incompatible\",\"a\":67,\"b\":56},{\"tag\":\"incompatible\",\"a\":68,\"b\":56},{\"tag\":\"incompatible\",\"a\":69,\"b\":41},{\"tag\":\"incompatible\",\"a\":69,\"b\":56},{\"tag\":\"incompatible\",\"a\":70,\"b\":51},{\"tag\":\"incompatible\",\"a\":71,\"b\":51},{\"tag\":\"incompatible\",\"a\":72,\"b\":35},{\"tag\":\"incompatible\",\"a\":72,\"b\":53},{\"tag\":\"three\",\"ridge\":7,\"vertices\":[16,25,27]},{\"tag\":\"three\",\"ridge\":7,\"vertices\":[18,25,27]},{\"tag\":\"three\",\"ridge\":7,\"vertices\":[21,25,27]},{\"tag\":\"mate\",\"ridge\":70,\"a\":27,\"owners\":[13,58,60]},{\"tag\":\"mate\",\"ridge\":11,\"a\":31,\"owners\":[3,16,19,28,30,35]},{\"tag\":\"mate\",\"ridge\":259,\"a\":27,\"owners\":[3,30,32]},{\"tag\":\"mate\",\"ridge\":266,\"a\":35,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":321,\"a\":27,\"owners\":[11,53]},{\"tag\":\"mate\",\"ridge\":322,\"a\":35,\"owners\":[59,65]},{\"tag\":\"mate\",\"ridge\":322,\"a\":37,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":21,\"a\":46,\"owners\":[6,16,22,39,41,45]},{\"tag\":\"mate\",\"ridge\":529,\"a\":54,\"owners\":[6,45,48]},{\"tag\":\"mate\",\"ridge\":532,\"a\":41,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":532,\"a\":45,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":545,\"a\":25,\"owners\":[10,51]},{\"tag\":\"mate\",\"ridge\":548,\"a\":43,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":548,\"a\":45,\"owners\":[57,69]},{\"tag\":\"mate\",\"ridge\":280,\"a\":30,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":280,\"a\":53,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":280,\"a\":72,\"owners\":[8,30,54]},{\"tag\":\"mate\",\"ridge\":521,\"a\":10,\"owners\":[9,19,41,54]},{\"tag\":\"mate\",\"ridge\":536,\"a\":9,\"owners\":[67,68,71]},{\"tag\":\"mate\",\"ridge\":536,\"a\":41,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":536,\"a\":51,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":536,\"a\":54,\"owners\":[67,68,71]},{\"tag\":\"mate\",\"ridge\":552,\"a\":10,\"owners\":[57,67,69,71]},{\"tag\":\"mate\",\"ridge\":552,\"a\":33,\"owners\":[67,69,71]},{\"tag\":\"mate\",\"ridge\":552,\"a\":43,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":552,\"a\":51,\"owners\":[57,69]},{\"tag\":\"mate\",\"ridge\":336,\"a\":37,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":134,\"a\":58,\"owners\":[12,18,24,56]},{\"tag\":\"mate\",\"ridge\":162,\"a\":24,\"owners\":[14]},{\"tag\":\"mate\",\"ridge\":164,\"a\":24,\"owners\":[66,69,70]},{\"tag\":\"mate\",\"ridge\":164,\"a\":56,\"owners\":[44,49,70]},{\"tag\":\"mate\",\"ridge\":164,\"a\":60,\"owners\":[42,44,66,69,70]},{\"tag\":\"mate\",\"ridge\":194,\"a\":58,\"owners\":[34,38,64]},{\"tag\":\"mate\",\"ridge\":196,\"a\":26,\"owners\":[15]},{\"tag\":\"mate\",\"ridge\":138,\"a\":63,\"owners\":[14,18,31,34,56]},{\"tag\":\"mate\",\"ridge\":168,\"a\":56,\"owners\":[50,71]},{\"tag\":\"mate\",\"ridge\":168,\"a\":69,\"owners\":[14,31,50]},{\"tag\":\"mate\",\"ridge\":168,\"a\":71,\"owners\":[14,31,42,56]},{\"tag\":\"mate\",\"ridge\":148,\"a\":70,\"owners\":[15,21,40,46,55,58]},{\"tag\":\"mate\",\"ridge\":208,\"a\":58,\"owners\":[52,72]},{\"tag\":\"mate\",\"ridge\":208,\"a\":65,\"owners\":[15,46,52]},{\"tag\":\"mate\",\"ridge\":208,\"a\":72,\"owners\":[15,36,46,58]},{\"tag\":\"mate\",\"ridge\":30,\"a\":55,\"owners\":[16]},{\"tag\":\"mate\",\"ridge\":141,\"a\":40,\"owners\":[18,42]},{\"tag\":\"mate\",\"ridge\":526,\"a\":19,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":225,\"a\":49,\"owners\":[38]},{\"tag\":\"mate\",\"ridge\":177,\"a\":50,\"owners\":[44]},{\"tag\":\"mate\",\"ridge\":402,\"a\":63,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":456,\"a\":64,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":456,\"a\":72,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":652,\"a\":68,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":652,\"a\":69,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":688,\"a\":70,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":688,\"a\":71,\"owners\":[70]},{\"tag\":\"group_take\",\"kind\":1,\"index\":3,\"member\":3,\"full_literals\":[-1,65]},{\"tag\":\"group_take\",\"kind\":1,\"index\":6,\"member\":6,\"full_literals\":[-2,66]},{\"tag\":\"group_take\",\"kind\":1,\"index\":8,\"member\":8,\"full_literals\":[-3,67]},{\"tag\":\"group_take\",\"kind\":1,\"index\":9,\"member\":9,\"full_literals\":[-4,68]},{\"tag\":\"group_take\",\"kind\":1,\"index\":10,\"member\":10,\"full_literals\":[-5,69]},{\"tag\":\"group_take\",\"kind\":1,\"index\":11,\"member\":11,\"full_literals\":[-6,70]},{\"tag\":\"group_take\",\"kind\":1,\"index\":12,\"member\":12,\"full_literals\":[-7,71]},{\"tag\":\"group_take\",\"kind\":1,\"index\":13,\"member\":13,\"full_literals\":[-8,72]},{\"tag\":\"group_take\",\"kind\":1,\"index\":14,\"member\":14,\"full_literals\":[-9,73]},{\"tag\":\"group_take\",\"kind\":1,\"index\":15,\"member\":15,\"full_literals\":[-10,74]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped1_0004\",\"right_name\":\"grouped1_0006\",\"joined_name\":\"grouped1_0005\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-65,75],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0005\",\"joined_name\":\"grouped1_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-75,76],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped1_0009\",\"right_name\":\"grouped1_0011\",\"joined_name\":\"grouped1_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-66,false,77],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped1_0007\",\"right_name\":\"grouped1_0010\",\"joined_name\":\"grouped1_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-77,78],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0008\",\"joined_name\":\"grouped1_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-78,79],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0008\",\"joined_name\":\"grouped1_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-76,false,79],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-68,80],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-67,false,80],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped1_0017\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-70,81],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped1_0017\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0018\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-69,-70,82],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8,9],\"right\":[10,11],\"left_name\":\"grouped1_0013\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-81,83],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8,9],\"right\":[10,11],\"left_name\":\"grouped1_0013\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0014\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-82,84],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8,9],\"right\":[10,11],\"left_name\":\"grouped1_0013\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0014\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-80,-82,85],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13],\"left_name\":\"grouped1_0020\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"grouped1_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-72,86],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13],\"left_name\":\"grouped1_0020\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"grouped1_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-71,false,86],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14],\"right\":[15],\"left_name\":\"grouped1_0024\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0025\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-74,87],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14],\"right\":[15],\"left_name\":\"grouped1_0024\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0025\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-73,false,87],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14],\"right\":[15],\"left_name\":\"grouped1_0024\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0025\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-73,-74,88],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12,13],\"right\":[14,15],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0025\",\"joined_name\":\"grouped1_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-87,89],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12,13],\"right\":[14,15],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0025\",\"joined_name\":\"grouped1_0022\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-88,90],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12,13],\"right\":[14,15],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0025\",\"joined_name\":\"grouped1_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-86,false,89],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12,13],\"right\":[14,15],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0025\",\"joined_name\":\"grouped1_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-86,-87,90],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8,9,10,11],\"right\":[12,13,14,15],\"left_name\":\"grouped1_0014\",\"right_name\":\"grouped1_0022\",\"joined_name\":\"grouped1_0015\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-83,-90,92],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8,9,10,11],\"right\":[12,13,14,15],\"left_name\":\"grouped1_0014\",\"right_name\":\"grouped1_0022\",\"joined_name\":\"grouped1_0015\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-84,false,91],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8,9,10,11],\"right\":[12,13,14,15],\"left_name\":\"grouped1_0014\",\"right_name\":\"grouped1_0022\",\"joined_name\":\"grouped1_0015\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-84,-89,92],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8,9,10,11],\"right\":[12,13,14,15],\"left_name\":\"grouped1_0014\",\"right_name\":\"grouped1_0022\",\"joined_name\":\"grouped1_0015\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-85,false,92],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7],\"right\":[8,9,10,11,12,13,14,15],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0015\",\"joined_name\":\"groupKind1\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-92,93],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7],\"right\":[8,9,10,11,12,13,14,15],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0015\",\"joined_name\":\"groupKind1\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-79,-91,93],\"grouped\":true,\"kind\":1},{\"tag\":\"quota_upper\",\"kind\":1,\"quota\":2,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[30,53,54],\"full_literals\":[-94,24,47,48]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[17,31,32,33],\"full_literals\":[-95,12,25,26,27]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[41,43,45,51],\"full_literals\":[-96,35,37,39,45]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[24,56,60],\"full_literals\":[-97,19,50,54]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[27,35,37],\"full_literals\":[-98,22,29,31]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[20,46,47,48],\"full_literals\":[-99,15,40,41,42]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[23,25],\"full_literals\":[-100,18,20]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[26,58],\"full_literals\":[-101,21,52]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0027\",\"right_name\":\"grouped2_0031\",\"joined_name\":\"grouped2_0028\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-102,94,95],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0027\",\"right_name\":\"grouped2_0031\",\"joined_name\":\"grouped2_0028\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-103,94,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0027\",\"right_name\":\"grouped2_0031\",\"joined_name\":\"grouped2_0028\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-103,false,95],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0032\",\"right_name\":\"grouped2_0034\",\"joined_name\":\"grouped2_0033\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-104,96,97],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0032\",\"right_name\":\"grouped2_0034\",\"joined_name\":\"grouped2_0033\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-105,96,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0032\",\"right_name\":\"grouped2_0034\",\"joined_name\":\"grouped2_0033\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-105,false,97],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0028\",\"right_name\":\"grouped2_0033\",\"joined_name\":\"grouped2_0029\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-106,102,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0028\",\"right_name\":\"grouped2_0033\",\"joined_name\":\"grouped2_0029\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-106,103,105],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0028\",\"right_name\":\"grouped2_0033\",\"joined_name\":\"grouped2_0029\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-107,103,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0028\",\"right_name\":\"grouped2_0033\",\"joined_name\":\"grouped2_0029\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-106,false,104],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0028\",\"right_name\":\"grouped2_0033\",\"joined_name\":\"grouped2_0029\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-107,false,105],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0035\",\"right_name\":\"grouped2_0038\",\"joined_name\":\"grouped2_0036\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-108,98,99],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0035\",\"right_name\":\"grouped2_0038\",\"joined_name\":\"grouped2_0036\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-109,98,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0035\",\"right_name\":\"grouped2_0038\",\"joined_name\":\"grouped2_0036\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-109,false,99],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0039\",\"right_name\":\"grouped2_0041\",\"joined_name\":\"grouped2_0040\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-110,100,101],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0039\",\"right_name\":\"grouped2_0041\",\"joined_name\":\"grouped2_0040\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-111,100,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0039\",\"right_name\":\"grouped2_0041\",\"joined_name\":\"grouped2_0040\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-111,false,101],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0036\",\"right_name\":\"grouped2_0040\",\"joined_name\":\"grouped2_0037\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-112,108,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0036\",\"right_name\":\"grouped2_0040\",\"joined_name\":\"grouped2_0037\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-112,109,111],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0036\",\"right_name\":\"grouped2_0040\",\"joined_name\":\"grouped2_0037\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-113,109,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0036\",\"right_name\":\"grouped2_0040\",\"joined_name\":\"grouped2_0037\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-112,false,110],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0036\",\"right_name\":\"grouped2_0040\",\"joined_name\":\"grouped2_0037\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-113,false,111],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0029\",\"right_name\":\"grouped2_0037\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-114,106,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0029\",\"right_name\":\"grouped2_0037\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-114,107,113],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0029\",\"right_name\":\"grouped2_0037\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-114,false,112],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[66,69,71],\"full_literals\":[-115,58,61,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":66,\"full_literals\":[-58,115]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":69,\"full_literals\":[-61,115]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":71,\"full_literals\":[-63,115]},{\"tag\":\"block\",\"leaf\":0,\"vertices\":[3,15,25,27,31,48,51,53,60,63,65,68,69]},{\"tag\":\"block\",\"leaf\":1,\"vertices\":[10,14,25,27,32,41,46,53,60,63,65,70,71]},{\"tag\":\"block\",\"leaf\":2,\"vertices\":[14,15,25,27,32,48,51,53,60,63,65,68,69]},{\"tag\":\"block\",\"leaf\":3,\"vertices\":[10,15,25,26,32,37,48,54,56,64,70,71,72]},{\"tag\":\"block\",\"leaf\":4,\"vertices\":[10,11,25,27,32,48,54,56,58,64,70,71,72]},{\"tag\":\"block\",\"leaf\":5,\"vertices\":[6,14,25,27,32,46,51,53,60,63,65,68,69]},{\"tag\":\"block\",\"leaf\":6,\"vertices\":[11,15,25,27,30,31,48,51,60,64,68,69,72]},{\"tag\":\"block\",\"leaf\":7,\"vertices\":[11,14,24,27,32,43,48,54,58,64,70,71,72]},{\"tag\":\"edge\",\"edge\":29,\"owners\":[9,10,19,33,41,43,51,54,57,67,68,69,71]}]}"
  "217 -92 0 169 167 0\n218 -85 0 217 166 0\n219 106 0 203 200 0\n220 112 0 203 202 0\n221 102 0 219 184 0\n222 104 0 219 187 0\n223 108 0 220 195 0\n224 110 0 220 198 0\n225 59 115 51 0 207 101 96 206 102 127 121 95 98 100 99 216 0\n226 115 51 0 222 205 206 207 90 102 96 101 129 172 106 181 225 64 65 66 108 173 0\n227 55 64 48 0 203 125 103 91 80 92 170 179 186 201 197 199 190 194 174 10 15 20 177 109 0\n228 94 52 31 0 221 203 178 179 186 201 197 199 190 193 194 177 6 10 12 176 174 2 14 16 171 0\n229 -21 41 29 15 31 0 223 220 203 6 7 10 28 55 174 189 190 175 196 197 32 33 193 201 176 188 24 48 182 183 172 173 102 69 0\n230 25 -42 -10 -54 -45 -61 -20 -95 -22 -47 -55 0 128 26 123 14 2 124 171 113 210 0\n231 40 -54 -45 -61 -20 -95 -22 -99 -47 -55 24 0 128 3 39 38 37 124 60 58 57 117 175 230 78 208 0\n232 -61 -20 -97 -96 -95 -22 -99 -47 -55 24 0 26 123 27 24 21 14 4 2 124 59 57 68 69 128 172 173 231 29 84 171 113 213 0\n233 64 48 0 224 220 203 91 103 227 58 61 124 228 170 36 37 38 229 177 194 192 199 196 201 190 191 186 188 174 180 182 183 9 176 2 4 14 24 27 48 75 232 102 172 88 32 46 86 96 175 173 29 171 111 209 0\n234 -5 49 34 16 36 14 -70 48 0 218 217 233 135 150 152 153 165 147 148 159 134 133 156 157 94 93 140 139 46 86 96 50 114 115 29 0\n235 -40 48 -20 -22 47 0 203 14 2 18 10 29 52 228 177 170 194 13 199 171 201 180 186 0\n236 -24 -45 -20 -22 -64 0 217 220 73 42 235 48 102 97 26 123 81 136 149 151 163 160 30 17 10 8 126 50 118 177 140 194 156 158 196 162 139 191 154 113 175 138 214 77 0\n237 -45 -20 -22 -64 0 219 26 4 20 122 18 73 42 70 107 236 170 179 228 185 56 183 173 0\n238 -20 -22 -64 0 217 169 203 73 81 136 20 122 10 126 3 4 22 24 26 27 74 75 76 120 123 119 237 88 135 234 150 40 41 152 172 164 165 182 168 161 188 145 146 155 201 144 142 137 199 143 141 194 132 131 177 85 79 104 112 107 212 0\n239 -22 -64 0 224 220 203 126 73 8 9 10 30 81 238 176 192 193 177 199 196 50 52 56 201 191 175 186 188 32 33 179 180 182 183 170 42 172 23 25 47 89 101 173 11 105 171 215 0\n240 -52 45 20 -64 0 220 203 239 72 51 56 174 190 196 197 193 201 176 188 1 182 183 173 46 47 67 172 87 0\n241 -111 52 20 0 193 194 176 177 6 0\n242 -50 35 -96 45 0 47 67 172 87 0\n243 -105 19 50 45 0 224 220 203 182 183 173 54 55 56 177 194 192 199 196 176 201 190 24 27 186 172 179 41 233 72 73 239 170 174 19 0\n244 48 105 0 219 203 188 201 197 190 185 179 233 72 73 239 170 174 19 0\n245 52 19 50 45 0 203 222 243 244 41 188 201 199 194 241 177 24 27 55 172 173 181 0\n246 19 50 45 0 203 243 188 201 197 190 244 43 245 51 53 62 116 82 239 174 0\n247 -19 45 0 224 1 4 7 35 176 192 177 116 240 0\n248 -52 105 0 203 188 201 197 190 244 43 51 53 62 116 82 239 174 0\n249 19 45 0 203 219 246 44 45 46 49 63 69 242 226 204 182 130 188 185 244 201 180 197 199 190 191 194 248 241 177 14 88 5 10 28 110 171 16 174 31 83 103 175 211 0\n250 45 0 247 249 0\n251 -44 0 250 34 0\n252 -48 0 250 42 0\n253 -63 0 250 71 0\n254 64 0 252 233 0\n255 105 0 252 244 0\n256 -50 0 253 251 112 0\n257 -29 0 254 72 0\n258 -47 0 254 73 0\n259 -22 0 254 239 0\n260 97 0 255 183 0\n261 -111 52 0 260 256 194 241 177 4 55 173 0\n262 111 0 220 203 257 259 252 258 199 196 201 190 186 174 179 19 170 0\n263 100 0 262 193 0\n264 52 0 262 261 0\n265 -54 0 264 56 0\n266 19 0 265 256 260 173 0\n267 -18 0 266 1 0\n268 -20 0 266 4 0\n269 0 268 267 263 176 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record019.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record019.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record019.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record019.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record019 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeafTable : ConcreteGrowth.Table (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record019.l) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf (⟨0, by decide⟩))
 (.leaf (⟨1, by decide⟩)))
 (.branch 3
 (.leaf (⟨2, by decide⟩))
 (.leaf (⟨3, by decide⟩))))
 (.branch 6
 (.branch 5
 (.leaf (⟨4, by decide⟩))
 (.leaf (⟨0, by decide⟩)))
 (.branch 7
 (.leaf (⟨1, by decide⟩))
 (.leaf (⟨3, by decide⟩)))))
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record019.l := originalLeafTable.get j.val
def orbitWordTable : ConcreteGrowth.Table (List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record019.g)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([]))
 (.leaf ([])))
 (.branch 3
 (.leaf ([]))
 (.leaf ([]))))
 (.branch 6
 (.branch 5
 (.leaf ([]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 7
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record019.g) := orbitWordTable.get j.val
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record019.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record019.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record019 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record019_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record019_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record019_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record019_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record019_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record019_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record019_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record019 Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record019_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record019_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record019_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00035.record019
