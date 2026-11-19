module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow23Part00022Data
public import GraphInputsRow23Part00022Frames
public import GraphInputsRow23Part00022Leaves
public import GraphInputsRow23Part00022Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00022.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record002
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 202663907377020928, (certNat% 4), (certNat% 5), (certNat% 6), (certNat% 7), (certNat% 8)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), (certNat% 10), (certNat% 11), 16140901064495857664, (certNat% 12), (certNat% 8), (certNat% 13), 189151184349560832]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 7), 15276225329203511296, (certNat% 15), (certNat% 6), (certNat% 16), (certNat% 5), (certNat% 8)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), (certNat% 18), (certNat% 11), 252201579132747776, (certNat% 19), (certNat% 8), 14987979559889010688, (certNat% 20)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), 9370301974697738240, (certNat% 22), 40533496157962240, (certNat% 23), (certNat% 24), (certNat% 25)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), (certNat% 27), (certNat% 28), (certNat% 29), 184084634768769024, 13835058055282163712, (certNat% 24), (certNat% 25)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 30), (certNat% 31), (certNat% 24), 17582068338417205248, (certNat% 25), (certNat% 32), (certNat% 33), (certNat% 16)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), (certNat% 35), (certNat% 36), (certNat% 37), (certNat% 38), (certNat% 25), 9368613124837474304, (certNat% 39), 4611686018427387904]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record002_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00022.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00022.record009
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "7c1e85d0ec1f1e274972728ea959561da4e3386e8785e785b15c5a93a6354d4758b4ad1b61d0f5c368f1364d534ce8b62ccb2ae1b45c570dc8f13c2f07de05c0e81d06c7095232a1615a0e139a14c4a9854358342d60e1344e0b22e0705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "492492492492492492492492492492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record009 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record009 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record009.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record009.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record009.data.quota

def groupMembers1 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 0)]))
 (.branch 2
 (.leaf ([(facetIndex 1)]))
 (.leaf ([(facetIndex 2)]))))
 (.branch 4
 (.leaf ([(facetIndex 3)]))
 (.branch 5
 (.leaf ([(facetIndex 4)]))
 (.leaf ([(facetIndex 5)])))))
 (.branch 9
 (.branch 7
 (.leaf ([(facetIndex 6)]))
 (.branch 8
 (.leaf ([(facetIndex 7)]))
 (.leaf ([(facetIndex 8)]))))
 (.branch 11
 (.branch 10
 (.leaf ([(facetIndex 9)]))
 (.leaf ([(facetIndex 10)])))
 (.branch 12
 (.leaf ([(facetIndex 11)]))
 (.leaf ([(facetIndex 12)]))))))
 (.branch 20
 (.branch 16
 (.branch 14
 (.leaf ([(facetIndex 13)]))
 (.branch 15
 (.leaf ([(facetIndex 14)]))
 (.leaf ([(facetIndex 15)]))))
 (.branch 18
 (.branch 17
 (.leaf ([(facetIndex 16)]))
 (.leaf ([(facetIndex 17)])))
 (.branch 19
 (.leaf ([(facetIndex 18)]))
 (.leaf ([(facetIndex 19)])))))
 (.branch 23
 (.branch 21
 (.leaf ([(facetIndex 20)]))
 (.branch 22
 (.leaf ([(facetIndex 21)]))
 (.leaf ([(facetIndex 22)]))))
 (.branch 25
 (.branch 24
 (.leaf ([(facetIndex 23)]))
 (.leaf ([(facetIndex 24)])))
 (.branch 26
 (.leaf ([(facetIndex 25)]))
 (.leaf ([(facetIndex 26)])))))))
def groupColors1 : PackedGraphCertificate.Fields :=
  ⟨5, sparse_nat% "6b38bdab49ca307b9ac5a928398a418820"⟩
def grouping1 : FacetSat.Grouping data.count where
  count := 27
  members := fun g => groupMembers1.get g
  color := fun c => groupColors1.get c.val
def groupKind1 : List Nat := List.range grouping1.count

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 27), (facetIndex 30), (facetIndex 34), (facetIndex 38)]))
 (.leaf ([(facetIndex 33), (facetIndex 39), (facetIndex 40), (facetIndex 41), (facetIndex 42)])))
 (.branch 3
 (.leaf ([(facetIndex 45), (facetIndex 46), (facetIndex 49), (facetIndex 52)]))
 (.branch 4
 (.leaf ([(facetIndex 37), (facetIndex 54), (facetIndex 67), (facetIndex 74)]))
 (.leaf ([(facetIndex 58), (facetIndex 59), (facetIndex 62), (facetIndex 65)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 56), (facetIndex 69), (facetIndex 75)]))
 (.branch 7
 (.leaf ([(facetIndex 48), (facetIndex 61), (facetIndex 72)]))
 (.leaf ([(facetIndex 51), (facetIndex 64), (facetIndex 73)]))))
 (.branch 9
 (.leaf ([(facetIndex 50), (facetIndex 63), (facetIndex 71)]))
 (.branch 10
 (.leaf ([(facetIndex 29), (facetIndex 32), (facetIndex 36), (facetIndex 44), (facetIndex 47), (facetIndex 53), (facetIndex 55), (facetIndex 57)]))
 (.leaf ([(facetIndex 28), (facetIndex 31), (facetIndex 35), (facetIndex 43), (facetIndex 60), (facetIndex 66), (facetIndex 68), (facetIndex 70)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "53768a5a3a47846a4495939278269229a1111039a019a09az1c;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 11
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped1_0000 : List Nat := [0, 1, 2]
def grouped1_0001 : List Nat := [0, 1, 2, 3, 4, 5]
def grouped1_0002 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
def grouped1_0004 : List Nat := [3]
def grouped1_0005 : List Nat := [3, 4, 5]
def grouped1_0006 : List Nat := [4]
def grouped1_0007 : List Nat := [4, 5]
def grouped1_0008 : List Nat := [5]
def grouped1_0009 : List Nat := [6]
def grouped1_0010 : List Nat := [6, 7, 8]
def grouped1_0011 : List Nat := [6, 7, 8, 9, 10, 11, 12]
def grouped1_0012 : List Nat := [7]
def grouped1_0013 : List Nat := [7, 8]
def grouped1_0014 : List Nat := [8]
def grouped1_0015 : List Nat := [9]
def grouped1_0016 : List Nat := [9, 10]
def grouped1_0017 : List Nat := [9, 10, 11, 12]
def grouped1_0018 : List Nat := [10]
def grouped1_0019 : List Nat := [11]
def grouped1_0020 : List Nat := [11, 12]
def grouped1_0021 : List Nat := [12]
def grouped1_0022 : List Nat := [13]
def grouped1_0023 : List Nat := [13, 14, 15]
def grouped1_0024 : List Nat := [13, 14, 15, 16, 17, 18, 19]
def grouped1_0025 : List Nat := [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]
def grouped1_0026 : List Nat := [14]
def grouped1_0027 : List Nat := [14, 15]
def grouped1_0028 : List Nat := [15]
def grouped1_0029 : List Nat := [16]
def grouped1_0030 : List Nat := [16, 17]
def grouped1_0031 : List Nat := [16, 17, 18, 19]
def grouped1_0032 : List Nat := [17]
def grouped1_0033 : List Nat := [18]
def grouped1_0034 : List Nat := [18, 19]
def grouped1_0035 : List Nat := [19]
def grouped1_0036 : List Nat := [20]
def grouped1_0037 : List Nat := [20, 21, 22]
def grouped1_0038 : List Nat := [20, 21, 22, 23, 24, 25, 26]
def grouped1_0039 : List Nat := [21]
def grouped1_0040 : List Nat := [21, 22]
def grouped1_0041 : List Nat := [22]
def grouped1_0042 : List Nat := [23]
def grouped1_0043 : List Nat := [23, 24]
def grouped1_0044 : List Nat := [23, 24, 25, 26]
def grouped1_0045 : List Nat := [24]
def grouped1_0046 : List Nat := [25]
def grouped1_0047 : List Nat := [25, 26]
def grouped1_0048 : List Nat := [26]
def grouped2_0049 : List Nat := [0]
def grouped2_0050 : List Nat := [0, 1]
def grouped2_0051 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0053 : List Nat := [1]
def grouped2_0054 : List Nat := [2]
def grouped2_0055 : List Nat := [2, 3, 4]
def grouped2_0056 : List Nat := [3]
def grouped2_0057 : List Nat := [3, 4]
def grouped2_0058 : List Nat := [4]
def grouped2_0059 : List Nat := [5]
def grouped2_0060 : List Nat := [5, 6, 7]
def grouped2_0061 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped2_0062 : List Nat := [6]
def grouped2_0063 : List Nat := [6, 7]
def grouped2_0064 : List Nat := [7]
def grouped2_0065 : List Nat := [8]
def grouped2_0066 : List Nat := [8, 9, 10]
def grouped2_0067 : List Nat := [9]
def grouped2_0068 : List Nat := [9, 10]
def grouped2_0069 : List Nat := [10]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record009 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record009_matrix_checked

def leafCount : Nat := 44
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaf0000 : List (Fin data.count) := [(facetIndex 8), (facetIndex 9), (facetIndex 12), (facetIndex 16), (facetIndex 38), (facetIndex 42), (facetIndex 43), (facetIndex 52), (facetIndex 55), (facetIndex 61), (facetIndex 65), (facetIndex 69), (facetIndex 71), (facetIndex 74)]
theorem leaf0000_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0000 = true := by
  decide +kernel
theorem leaf0000_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0000 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0000_counts_checked
def leaf0001 : List (Fin data.count) := [(facetIndex 8), (facetIndex 9), (facetIndex 12), (facetIndex 16), (facetIndex 38), (facetIndex 42), (facetIndex 44), (facetIndex 52), (facetIndex 56), (facetIndex 61), (facetIndex 65), (facetIndex 68), (facetIndex 71), (facetIndex 74)]
theorem leaf0001_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0001 = true := by
  decide +kernel
theorem leaf0001_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0001 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0001_counts_checked
def leaf0002 : List (Fin data.count) := [(facetIndex 8), (facetIndex 9), (facetIndex 13), (facetIndex 18), (facetIndex 38), (facetIndex 42), (facetIndex 43), (facetIndex 52), (facetIndex 53), (facetIndex 62), (facetIndex 64), (facetIndex 67), (facetIndex 71), (facetIndex 75)]
theorem leaf0002_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0002 = true := by
  decide +kernel
theorem leaf0002_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0002 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0002_counts_checked
def leaf0003 : List (Fin data.count) := [(facetIndex 8), (facetIndex 9), (facetIndex 13), (facetIndex 18), (facetIndex 38), (facetIndex 42), (facetIndex 44), (facetIndex 52), (facetIndex 54), (facetIndex 62), (facetIndex 64), (facetIndex 66), (facetIndex 71), (facetIndex 75)]
theorem leaf0003_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0003 = true := by
  decide +kernel
theorem leaf0003_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0003 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0003_counts_checked
def leaf0004 : List (Fin data.count) := [(facetIndex 9), (facetIndex 12), (facetIndex 13), (facetIndex 16), (facetIndex 38), (facetIndex 42), (facetIndex 43), (facetIndex 47), (facetIndex 52), (facetIndex 61), (facetIndex 65), (facetIndex 69), (facetIndex 73), (facetIndex 74)]
theorem leaf0004_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0004 = true := by
  decide +kernel
theorem leaf0004_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0004 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0004_counts_checked
def leaf0005 : List (Fin data.count) := [(facetIndex 8), (facetIndex 18), (facetIndex 19), (facetIndex 20), (facetIndex 38), (facetIndex 42), (facetIndex 44), (facetIndex 46), (facetIndex 51), (facetIndex 54), (facetIndex 62), (facetIndex 63), (facetIndex 72), (facetIndex 75)]
theorem leaf0005_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0005 = true := by
  decide +kernel
theorem leaf0005_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0005 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0005_counts_checked
def leaf0006 : List (Fin data.count) := [(facetIndex 9), (facetIndex 19), (facetIndex 23), (facetIndex 25), (facetIndex 38), (facetIndex 42), (facetIndex 44), (facetIndex 48), (facetIndex 52), (facetIndex 56), (facetIndex 59), (facetIndex 60), (facetIndex 64), (facetIndex 74)]
theorem leaf0006_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0006 = true := by
  decide +kernel
theorem leaf0006_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0006 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0006_counts_checked
def leaf0007 : List (Fin data.count) := [(facetIndex 8), (facetIndex 12), (facetIndex 13), (facetIndex 18), (facetIndex 38), (facetIndex 42), (facetIndex 43), (facetIndex 46), (facetIndex 50), (facetIndex 62), (facetIndex 64), (facetIndex 67), (facetIndex 72), (facetIndex 75)]
theorem leaf0007_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0007 = true := by
  decide +kernel
theorem leaf0007_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0007 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0007_counts_checked
def leaf0008 : List (Fin data.count) := [(facetIndex 9), (facetIndex 13), (facetIndex 18), (facetIndex 24), (facetIndex 38), (facetIndex 42), (facetIndex 43), (facetIndex 48), (facetIndex 52), (facetIndex 62), (facetIndex 64), (facetIndex 67), (facetIndex 71), (facetIndex 75)]
theorem leaf0008_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0008 = true := by
  decide +kernel
theorem leaf0008_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0008 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0008_counts_checked
def leaf0009 : List (Fin data.count) := [(facetIndex 9), (facetIndex 13), (facetIndex 14), (facetIndex 18), (facetIndex 38), (facetIndex 42), (facetIndex 44), (facetIndex 48), (facetIndex 52), (facetIndex 62), (facetIndex 64), (facetIndex 66), (facetIndex 71), (facetIndex 75)]
theorem leaf0009_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0009 = true := by
  decide +kernel
theorem leaf0009_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0009 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0009_counts_checked
def leaf0010 : List (Fin data.count) := [(facetIndex 9), (facetIndex 18), (facetIndex 24), (facetIndex 26), (facetIndex 38), (facetIndex 42), (facetIndex 43), (facetIndex 48), (facetIndex 52), (facetIndex 55), (facetIndex 62), (facetIndex 64), (facetIndex 67), (facetIndex 71)]
theorem leaf0010_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0010 = true := by
  decide +kernel
theorem leaf0010_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0010 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0010_counts_checked
def leaf0011 : List (Fin data.count) := [(facetIndex 9), (facetIndex 15), (facetIndex 16), (facetIndex 19), (facetIndex 38), (facetIndex 42), (facetIndex 44), (facetIndex 48), (facetIndex 52), (facetIndex 56), (facetIndex 65), (facetIndex 68), (facetIndex 71), (facetIndex 74)]
theorem leaf0011_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0011 = true := by
  decide +kernel
theorem leaf0011_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0011 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0011_counts_checked
def leaf0012 : List (Fin data.count) := [(facetIndex 10), (facetIndex 11), (facetIndex 13), (facetIndex 18), (facetIndex 38), (facetIndex 42), (facetIndex 43), (facetIndex 49), (facetIndex 53), (facetIndex 62), (facetIndex 64), (facetIndex 67), (facetIndex 71), (facetIndex 75)]
theorem leaf0012_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0012 = true := by
  decide +kernel
theorem leaf0012_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0012 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0012_counts_checked
def leaf0013 : List (Fin data.count) := [(facetIndex 11), (facetIndex 17), (facetIndex 18), (facetIndex 20), (facetIndex 38), (facetIndex 42), (facetIndex 44), (facetIndex 49), (facetIndex 51), (facetIndex 54), (facetIndex 62), (facetIndex 66), (facetIndex 71), (facetIndex 75)]
theorem leaf0013_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0013 = true := by
  decide +kernel
theorem leaf0013_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0013 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0013_counts_checked
def leaf0014 : List (Fin data.count) := [(facetIndex 9), (facetIndex 15), (facetIndex 16), (facetIndex 19), (facetIndex 38), (facetIndex 42), (facetIndex 43), (facetIndex 48), (facetIndex 52), (facetIndex 55), (facetIndex 65), (facetIndex 69), (facetIndex 71), (facetIndex 74)]
theorem leaf0014_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0014 = true := by
  decide +kernel
theorem leaf0014_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0014 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0014_counts_checked
def leaf0015 : List (Fin data.count) := [(facetIndex 10), (facetIndex 11), (facetIndex 13), (facetIndex 18), (facetIndex 38), (facetIndex 42), (facetIndex 44), (facetIndex 49), (facetIndex 54), (facetIndex 62), (facetIndex 64), (facetIndex 66), (facetIndex 71), (facetIndex 75)]
theorem leaf0015_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0015 = true := by
  decide +kernel
theorem leaf0015_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0015 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0015_counts_checked
def leaf0016 : List (Fin data.count) := [(facetIndex 11), (facetIndex 17), (facetIndex 18), (facetIndex 20), (facetIndex 38), (facetIndex 42), (facetIndex 43), (facetIndex 49), (facetIndex 51), (facetIndex 53), (facetIndex 62), (facetIndex 67), (facetIndex 71), (facetIndex 75)]
theorem leaf0016_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0016 = true := by
  decide +kernel
theorem leaf0016_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0016 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0016_counts_checked
def leaf0017 : List (Fin data.count) := [(facetIndex 11), (facetIndex 15), (facetIndex 16), (facetIndex 20), (facetIndex 38), (facetIndex 42), (facetIndex 44), (facetIndex 49), (facetIndex 51), (facetIndex 54), (facetIndex 65), (facetIndex 66), (facetIndex 71), (facetIndex 75)]
theorem leaf0017_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0017 = true := by
  decide +kernel
theorem leaf0017_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0017 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0017_counts_checked
def leaf0018 : List (Fin data.count) := [(facetIndex 10), (facetIndex 11), (facetIndex 12), (facetIndex 16), (facetIndex 38), (facetIndex 42), (facetIndex 43), (facetIndex 49), (facetIndex 55), (facetIndex 61), (facetIndex 65), (facetIndex 69), (facetIndex 71), (facetIndex 74)]
theorem leaf0018_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0018 = true := by
  decide +kernel
theorem leaf0018_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0018 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0018_counts_checked
def leaf0019 : List (Fin data.count) := [(facetIndex 9), (facetIndex 17), (facetIndex 18), (facetIndex 19), (facetIndex 38), (facetIndex 42), (facetIndex 44), (facetIndex 48), (facetIndex 52), (facetIndex 56), (facetIndex 62), (facetIndex 68), (facetIndex 71), (facetIndex 74)]
theorem leaf0019_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0019 = true := by
  decide +kernel
theorem leaf0019_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0019 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0019_counts_checked
def leaf0020 : List (Fin data.count) := [(facetIndex 11), (facetIndex 15), (facetIndex 16), (facetIndex 20), (facetIndex 38), (facetIndex 42), (facetIndex 43), (facetIndex 49), (facetIndex 51), (facetIndex 53), (facetIndex 65), (facetIndex 67), (facetIndex 71), (facetIndex 75)]
theorem leaf0020_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0020 = true := by
  decide +kernel
theorem leaf0020_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0020 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0020_counts_checked
def leaf0021 : List (Fin data.count) := [(facetIndex 10), (facetIndex 11), (facetIndex 12), (facetIndex 16), (facetIndex 38), (facetIndex 42), (facetIndex 44), (facetIndex 49), (facetIndex 56), (facetIndex 61), (facetIndex 65), (facetIndex 68), (facetIndex 71), (facetIndex 74)]
theorem leaf0021_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0021 = true := by
  decide +kernel
theorem leaf0021_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0021 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0021_counts_checked
def leaf0022 : List (Fin data.count) := [(facetIndex 9), (facetIndex 17), (facetIndex 18), (facetIndex 19), (facetIndex 38), (facetIndex 42), (facetIndex 43), (facetIndex 48), (facetIndex 52), (facetIndex 55), (facetIndex 62), (facetIndex 69), (facetIndex 71), (facetIndex 74)]
theorem leaf0022_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0022 = true := by
  decide +kernel
theorem leaf0022_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0022 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0022_counts_checked
def leaf0023 : List (Fin data.count) := [(facetIndex 9), (facetIndex 16), (facetIndex 19), (facetIndex 20), (facetIndex 38), (facetIndex 42), (facetIndex 44), (facetIndex 48), (facetIndex 52), (facetIndex 56), (facetIndex 60), (facetIndex 65), (facetIndex 73), (facetIndex 74)]
theorem leaf0023_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0023 = true := by
  decide +kernel
theorem leaf0023_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0023 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0023_counts_checked
def leaf0024 : List (Fin data.count) := [(facetIndex 11), (facetIndex 12), (facetIndex 13), (facetIndex 18), (facetIndex 38), (facetIndex 42), (facetIndex 43), (facetIndex 49), (facetIndex 50), (facetIndex 62), (facetIndex 64), (facetIndex 67), (facetIndex 72), (facetIndex 75)]
theorem leaf0024_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0024 = true := by
  decide +kernel
theorem leaf0024_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0024 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0024_counts_checked
def leaf0025 : List (Fin data.count) := [(facetIndex 11), (facetIndex 18), (facetIndex 19), (facetIndex 20), (facetIndex 38), (facetIndex 42), (facetIndex 44), (facetIndex 49), (facetIndex 51), (facetIndex 54), (facetIndex 62), (facetIndex 63), (facetIndex 72), (facetIndex 75)]
theorem leaf0025_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0025 = true := by
  decide +kernel
theorem leaf0025_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0025 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0025_counts_checked
def leaf0026 : List (Fin data.count) := [(facetIndex 11), (facetIndex 12), (facetIndex 13), (facetIndex 15), (facetIndex 38), (facetIndex 42), (facetIndex 43), (facetIndex 49), (facetIndex 50), (facetIndex 59), (facetIndex 64), (facetIndex 67), (facetIndex 72), (facetIndex 75)]
theorem leaf0026_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0026 = true := by
  decide +kernel
theorem leaf0026_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0026 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0026_counts_checked
def leaf0027 : List (Fin data.count) := [(facetIndex 10), (facetIndex 16), (facetIndex 19), (facetIndex 20), (facetIndex 38), (facetIndex 42), (facetIndex 44), (facetIndex 46), (facetIndex 48), (facetIndex 56), (facetIndex 60), (facetIndex 65), (facetIndex 73), (facetIndex 74)]
theorem leaf0027_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0027 = true := by
  decide +kernel
theorem leaf0027_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0027 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0027_counts_checked
def leaf0028 : List (Fin data.count) := [(facetIndex 9), (facetIndex 12), (facetIndex 13), (facetIndex 17), (facetIndex 38), (facetIndex 42), (facetIndex 43), (facetIndex 47), (facetIndex 52), (facetIndex 59), (facetIndex 61), (facetIndex 69), (facetIndex 73), (facetIndex 74)]
theorem leaf0028_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0028 = true := by
  decide +kernel
theorem leaf0028_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0028 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0028_counts_checked
def leaf0029 : List (Fin data.count) := [(facetIndex 12), (facetIndex 16), (facetIndex 23), (facetIndex 25), (facetIndex 38), (facetIndex 42), (facetIndex 43), (facetIndex 46), (facetIndex 47), (facetIndex 51), (facetIndex 61), (facetIndex 65), (facetIndex 69), (facetIndex 74)]
theorem leaf0029_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0029 = true := by
  decide +kernel
theorem leaf0029_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0029 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0029_counts_checked
def leaf0030 : List (Fin data.count) := [(facetIndex 11), (facetIndex 20), (facetIndex 22), (facetIndex 24), (facetIndex 38), (facetIndex 42), (facetIndex 44), (facetIndex 49), (facetIndex 51), (facetIndex 54), (facetIndex 59), (facetIndex 61), (facetIndex 63), (facetIndex 75)]
theorem leaf0030_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0030 = true := by
  decide +kernel
theorem leaf0030_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0030 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0030_counts_checked
def leaf0031 : List (Fin data.count) := [(facetIndex 13), (facetIndex 18), (facetIndex 22), (facetIndex 24), (facetIndex 38), (facetIndex 42), (facetIndex 43), (facetIndex 46), (facetIndex 48), (facetIndex 50), (facetIndex 62), (facetIndex 64), (facetIndex 67), (facetIndex 75)]
theorem leaf0031_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0031 = true := by
  decide +kernel
theorem leaf0031_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0031 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0031_counts_checked
def leaf0032 : List (Fin data.count) := [(facetIndex 11), (facetIndex 15), (facetIndex 19), (facetIndex 20), (facetIndex 38), (facetIndex 42), (facetIndex 44), (facetIndex 49), (facetIndex 51), (facetIndex 54), (facetIndex 59), (facetIndex 63), (facetIndex 72), (facetIndex 75)]
theorem leaf0032_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0032 = true := by
  decide +kernel
theorem leaf0032_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0032 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0032_counts_checked
def leaf0033 : List (Fin data.count) := [(facetIndex 10), (facetIndex 12), (facetIndex 13), (facetIndex 16), (facetIndex 38), (facetIndex 42), (facetIndex 43), (facetIndex 46), (facetIndex 47), (facetIndex 61), (facetIndex 65), (facetIndex 69), (facetIndex 73), (facetIndex 74)]
theorem leaf0033_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0033 = true := by
  decide +kernel
theorem leaf0033_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0033 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0033_counts_checked
def leaf0034 : List (Fin data.count) := [(facetIndex 9), (facetIndex 17), (facetIndex 19), (facetIndex 20), (facetIndex 38), (facetIndex 42), (facetIndex 44), (facetIndex 48), (facetIndex 52), (facetIndex 56), (facetIndex 59), (facetIndex 60), (facetIndex 73), (facetIndex 74)]
theorem leaf0034_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0034 = true := by
  decide +kernel
theorem leaf0034_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0034 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0034_counts_checked
def leaf0035 : List (Fin data.count) := [(facetIndex 11), (facetIndex 16), (facetIndex 20), (facetIndex 24), (facetIndex 38), (facetIndex 42), (facetIndex 44), (facetIndex 49), (facetIndex 51), (facetIndex 54), (facetIndex 61), (facetIndex 65), (facetIndex 71), (facetIndex 75)]
theorem leaf0035_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0035 = true := by
  decide +kernel
theorem leaf0035_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0035 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0035_counts_checked
def leaf0036 : List (Fin data.count) := [(facetIndex 11), (facetIndex 12), (facetIndex 16), (facetIndex 25), (facetIndex 38), (facetIndex 42), (facetIndex 43), (facetIndex 49), (facetIndex 51), (facetIndex 61), (facetIndex 65), (facetIndex 69), (facetIndex 71), (facetIndex 74)]
theorem leaf0036_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0036 = true := by
  decide +kernel
theorem leaf0036_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0036 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0036_counts_checked
def leaf0037 : List (Fin data.count) := [(facetIndex 9), (facetIndex 18), (facetIndex 19), (facetIndex 25), (facetIndex 38), (facetIndex 42), (facetIndex 44), (facetIndex 48), (facetIndex 52), (facetIndex 56), (facetIndex 62), (facetIndex 64), (facetIndex 71), (facetIndex 74)]
theorem leaf0037_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0037 = true := by
  decide +kernel
theorem leaf0037_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0037 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0037_counts_checked
def leaf0038 : List (Fin data.count) := [(facetIndex 11), (facetIndex 16), (facetIndex 20), (facetIndex 21), (facetIndex 38), (facetIndex 42), (facetIndex 43), (facetIndex 49), (facetIndex 51), (facetIndex 53), (facetIndex 61), (facetIndex 65), (facetIndex 71), (facetIndex 75)]
theorem leaf0038_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0038 = true := by
  decide +kernel
theorem leaf0038_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0038 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0038_counts_checked
def leaf0039 : List (Fin data.count) := [(facetIndex 11), (facetIndex 12), (facetIndex 14), (facetIndex 16), (facetIndex 38), (facetIndex 42), (facetIndex 44), (facetIndex 49), (facetIndex 51), (facetIndex 61), (facetIndex 65), (facetIndex 68), (facetIndex 71), (facetIndex 74)]
theorem leaf0039_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0039 = true := by
  decide +kernel
theorem leaf0039_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0039 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0039_counts_checked
def leaf0040 : List (Fin data.count) := [(facetIndex 9), (facetIndex 18), (facetIndex 19), (facetIndex 21), (facetIndex 38), (facetIndex 42), (facetIndex 43), (facetIndex 48), (facetIndex 52), (facetIndex 55), (facetIndex 62), (facetIndex 64), (facetIndex 71), (facetIndex 74)]
theorem leaf0040_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0040 = true := by
  decide +kernel
theorem leaf0040_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0040 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0040_counts_checked
def leaf0041 : List (Fin data.count) := [(facetIndex 11), (facetIndex 16), (facetIndex 24), (facetIndex 26), (facetIndex 38), (facetIndex 42), (facetIndex 44), (facetIndex 49), (facetIndex 51), (facetIndex 54), (facetIndex 61), (facetIndex 65), (facetIndex 68), (facetIndex 71)]
theorem leaf0041_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0041 = true := by
  decide +kernel
theorem leaf0041_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0041 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0041_counts_checked
def leaf0042 : List (Fin data.count) := [(facetIndex 11), (facetIndex 16), (facetIndex 25), (facetIndex 26), (facetIndex 38), (facetIndex 42), (facetIndex 43), (facetIndex 49), (facetIndex 51), (facetIndex 53), (facetIndex 61), (facetIndex 65), (facetIndex 69), (facetIndex 71)]
theorem leaf0042_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0042 = true := by
  decide +kernel
theorem leaf0042_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0042 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0042_counts_checked
def leaf0043 : List (Fin data.count) := [(facetIndex 9), (facetIndex 18), (facetIndex 25), (facetIndex 26), (facetIndex 38), (facetIndex 42), (facetIndex 44), (facetIndex 48), (facetIndex 52), (facetIndex 56), (facetIndex 62), (facetIndex 64), (facetIndex 66), (facetIndex 71)]
theorem leaf0043_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0043 = true := by
  decide +kernel
theorem leaf0043_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0043 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0043_counts_checked
def leavesTable : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (leaf0000))
 (.leaf (leaf0001)))
 (.branch 3
 (.leaf (leaf0002))
 (.branch 4
 (.leaf (leaf0003))
 (.leaf (leaf0004)))))
 (.branch 8
 (.branch 6
 (.leaf (leaf0005))
 (.branch 7
 (.leaf (leaf0006))
 (.leaf (leaf0007))))
 (.branch 9
 (.leaf (leaf0008))
 (.branch 10
 (.leaf (leaf0009))
 (.leaf (leaf0010))))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf (leaf0011))
 (.leaf (leaf0012)))
 (.branch 14
 (.leaf (leaf0013))
 (.branch 15
 (.leaf (leaf0014))
 (.leaf (leaf0015)))))
 (.branch 19
 (.branch 17
 (.leaf (leaf0016))
 (.branch 18
 (.leaf (leaf0017))
 (.leaf (leaf0018))))
 (.branch 20
 (.leaf (leaf0019))
 (.branch 21
 (.leaf (leaf0020))
 (.leaf (leaf0021)))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf (leaf0022))
 (.leaf (leaf0023)))
 (.branch 25
 (.leaf (leaf0024))
 (.branch 26
 (.leaf (leaf0025))
 (.leaf (leaf0026)))))
 (.branch 30
 (.branch 28
 (.leaf (leaf0027))
 (.branch 29
 (.leaf (leaf0028))
 (.leaf (leaf0029))))
 (.branch 31
 (.leaf (leaf0030))
 (.branch 32
 (.leaf (leaf0031))
 (.leaf (leaf0032))))))
 (.branch 38
 (.branch 35
 (.branch 34
 (.leaf (leaf0033))
 (.leaf (leaf0034)))
 (.branch 36
 (.leaf (leaf0035))
 (.branch 37
 (.leaf (leaf0036))
 (.leaf (leaf0037)))))
 (.branch 41
 (.branch 39
 (.leaf (leaf0038))
 (.branch 40
 (.leaf (leaf0039))
 (.leaf (leaf0040))))
 (.branch 42
 (.leaf (leaf0041))
 (.branch 43
 (.leaf (leaf0042))
 (.leaf (leaf0043))))))))
def leaves (j : Fin leafCount) : List (Fin data.count) := leavesTable.get j.val

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00022.record009" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"group\",\"kind\":1,\"index\":4},{\"tag\":\"group\",\"kind\":1,\"index\":6},{\"tag\":\"group\",\"kind\":1,\"index\":7},{\"tag\":\"group\",\"kind\":1,\"index\":8},{\"tag\":\"group\",\"kind\":1,\"index\":9},{\"tag\":\"group\",\"kind\":1,\"index\":10},{\"tag\":\"group\",\"kind\":1,\"index\":11},{\"tag\":\"group\",\"kind\":1,\"index\":13},{\"tag\":\"group\",\"kind\":1,\"index\":14},{\"tag\":\"group\",\"kind\":1,\"index\":16},{\"tag\":\"group\",\"kind\":1,\"index\":17},{\"tag\":\"group\",\"kind\":1,\"index\":18},{\"tag\":\"group\",\"kind\":1,\"index\":20},{\"tag\":\"group\",\"kind\":1,\"index\":21},{\"tag\":\"group\",\"kind\":1,\"index\":22},{\"tag\":\"group\",\"kind\":1,\"index\":23},{\"tag\":\"group\",\"kind\":1,\"index\":24},{\"tag\":\"group\",\"kind\":1,\"index\":25},{\"tag\":\"group\",\"kind\":1,\"index\":26},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0007\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0005\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0013\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0010\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0010\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0016\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0020\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0017\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0011\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0011\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0011\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0002\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0002\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0002\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0027\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0030\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0034\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0031\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0031\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0024\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0024\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0040\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0040\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0037\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0037\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0043\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0043\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0047\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0047\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0044\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0044\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0038\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0038\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0038\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0025\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0025\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":4,\"list_name\":\"grouped1_0025\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":5,\"list_name\":\"groupKind1\"},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group\",\"kind\":2,\"index\":10},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0050\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0057\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0057\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0055\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0055\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0051\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0051\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0063\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0063\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0060\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0060\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0068\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0068\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0066\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0066\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0061\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":6,\"list_name\":\"grouped2_0061\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":10,\"list_name\":\"groupKind2\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":11,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00022.record009" 163

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00022.record009" "{\"ridges\":[[0,11],[2,7],[2,515],[2,517],[2,518],[4,515],[4,522],[6,515],[6,529],[6,530],[7,386],[9,517],[9,521],[11,21],[11,529],[11,532],[14,416],[16,522],[16,524],[18,22],[18,518],[18,530],[18,532],[28,7],[28,11],[31,7],[32,7],[32,21],[34,11],[34,522],[37,11],[37,385],[38,131],[38,138],[38,515],[38,522],[39,259],[42,273],[42,274],[42,515],[42,529],[42,530],[43,289],[44,194],[44,322],[44,448],[45,13],[46,13],[46,21],[46,521],[46,524],[46,532],[47,37],[48,13],[48,37],[48,161],[49,41],[49,44],[49,517],[49,521],[50,100],[51,21],[52,37],[52,49],[52,517],[52,529],[52,532],[53,41],[54,289],[55,49],[56,161],[56,304],[56,416],[57,224],[57,289],[59,522],[59,524],[59,532],[60,70],[61,14],[62,70],[62,74],[62,76],[62,518],[62,522],[63,70],[63,82],[63,112],[64,22],[64,70],[64,84],[64,336],[65,70],[65,84],[65,518],[65,530],[65,532],[66,74],[67,74],[67,200],[67,322],[67,448],[69,82],[69,336],[69,448],[70,224],[70,322],[71,52],[71,84],[71,104],[71,112],[72,44],[72,168],[73,52],[74,168],[74,200],[74,352],[74,416],[74,448],[75,224],[75,336],[75,448]],\"owners\":[[2,7,[0,1,28,29,30,31,32,33],[]],[28,7,[1,2,32,33],[0,29,30,31]],[31,7,[0,2,29,30],[1,28,32,33]],[32,7,[0,2,28,30],[1,29,31,33]],[45,13,[0,9,29,30],[8,27,46,47,48]],[46,13,[0,8,29,30,47,48],[9,27,45]],[48,13,[0,9,27,29,46],[8,30,45,47]],[61,14,[0,16,27,28,59],[15,30,58,60]],[51,21,[1,11,27,32,46],[10,33,45,50]],[18,22,[1,17,27,31,33,58,63,64],[59]],[64,22,[1,18,27,31,59],[17,33,58,63]],[4,515,[2,6,42],[38]],[38,515,[2,6,42],[4]],[49,517,[2,11],[9,52]],[52,517,[2,9],[11,49]],[62,518,[2,18],[16,65]],[65,518,[2,16],[18,62]],[38,131,[7,41,43,44],[3,30,35,36]],[38,138,[19,61,66,67],[3,30,35,37]],[9,521,[4,34,38],[46,49]],[46,521,[4,38],[9,34,49]],[49,521,[4,34,38],[9,46]],[4,522,[16,59,62],[34,38]],[16,522,[4,34,38],[59,62]],[34,522,[16,62],[4,38,59]],[38,522,[16,59,62],[4,34]],[59,522,[4,38],[16,34,62]],[62,522,[4,34,38],[16,59]],[39,259,[7,37,44],[5,33,40,42,43]],[42,273,[13,51,55,56],[5,33,40,41]],[42,274,[20,64,68,69],[5,33,39,41]],[6,529,[11,46,52],[34,42]],[11,529,[6,34,42],[46,52]],[42,529,[11,46,52],[6,34]],[52,529,[6,34,42],[11,46]],[6,530,[18,59,65],[34,42]],[18,530,[6,34,42],[59,65]],[42,530,[18,59,65],[6,34]],[65,530,[6,34,42],[18,59]],[37,385,[14,56,57],[7,41,44,54]],[7,386,[21,67,69,70],[37,41,43]],[47,37,[10,31,51,52],[8,28,48,49,50]],[48,37,[10,31,50,51,52],[8,28,47,49]],[52,37,[8,28,47,48],[10,31,49,50,51]],[49,41,[12,35,53,54],[8,28,45,47]],[53,41,[8,28,45,49],[12,35,47,54]],[49,44,[22,60,71,72],[8,28,45,48]],[72,44,[8,28,45,49],[22,48,60,71]],[16,524,[9,46,49],[59,62]],[46,524,[16,62],[9,49,59]],[59,524,[9,49],[16,46,62]],[52,49,[13,39,55,56],[10,31,45,50]],[55,49,[10,31,45,52],[13,39,50,56]],[71,52,[10,31,51,52],[23,45,63,73]],[73,52,[10,31,45,52],[23,51,63,71]],[11,532,[18,59,65],[46,52]],[18,532,[11,46,52],[59,65]],[46,532,[18,65],[11,52,59]],[52,532,[18,59,65],[11,46]],[59,532,[11,52],[18,46,65]],[65,532,[11,46,52],[18,59]],[48,161,[14,43,56,57],[12,35,53]],[56,161,[12,35,48,53],[14,43,57]],[72,168,[12,35,54],[24,48,66,74]],[74,168,[12,35,48],[24,54,66,72]],[43,289,[13,51,55],[14,39,54,57]],[54,289,[13,39,51,55],[14,43,57]],[57,289,[13,39,51],[14,43,54,55]],[56,304,[25,68,73],[13,39,51,75]],[14,416,[26,70,74,75],[43,54,56]],[56,416,[26,70,74],[14,43,54,75]],[74,416,[14,43,56],[26,54,70,75]],[60,70,[17,32,64,65],[15,29,61,62,63]],[62,70,[17,32,63,64],[15,29,60,61,65]],[63,70,[15,29,61,62],[17,32,60,64,65]],[64,70,[15,29,60,61,62],[17,32,63,65]],[65,70,[15,29,60,61],[17,32,62,63,64]],[62,74,[19,36,66,67],[15,29,58,60]],[66,74,[15,29,58,62],[19,36,60,67]],[67,74,[15,29,58,60,62],[19,36,66]],[62,76,[22,47,71,72],[15,29,58,61]],[63,82,[20,40,69],[17,32,58,65,68]],[69,82,[17,32,58,63,65],[20,40,68]],[64,84,[23,50,71],[17,32,58,65,73]],[65,84,[23,50,71,73],[17,32,58,64]],[71,84,[17,32,64,65],[23,50,58,73]],[44,194,[19,61,66],[21,36,69,70]],[67,200,[24,53,72],[19,36,61,74]],[74,200,[19,36,61],[24,53,67,72]],[44,322,[20,64,68],[21,40,67,70]],[67,322,[20,40,64,68],[21,44,70]],[70,322,[20,40,64],[21,44,67,68]],[64,336,[25,55,75],[20,40,69,73]],[69,336,[25,55,73],[20,40,64,75]],[75,336,[20,40,64],[25,55,69,73]],[44,448,[26,74,75],[21,57,67,69]],[67,448,[26,57,75],[21,44,69,74]],[69,448,[26,57,74],[21,44,67,75]],[74,448,[21,44,69],[26,57,67,75]],[75,448,[21,44,67],[26,57,69,74]],[50,100,[22,60,72],[23,47,63,73]],[71,104,[24,53,66,74],[22,47,60]],[63,112,[25,55,75],[23,50,68,71]],[71,112,[25,55,68,75],[23,50,63]],[57,224,[24,66,72],[26,53,70,75]],[70,224,[24,53,72],[26,57,66,75]],[75,224,[24,53,66,72],[26,57,70]],[74,352,[25,55,68,73],[26,57,70]]],\"edges\":[[29,[4,9,16,34,38,46,49,59,62]],[34,[6,11,18,34,42,46,52,59,65]]],\"groupings\":[1,2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00022.record009" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00022.record009\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-28,-15],[-28,-26],[-29,-4],[-29,-28],[-30,-10],[-31,-17],[-33,-3],[-33,-32],[-34,-29],[-36,-29],[-36,-34],[-36,-35],[-37,-1],[-37,-27],[-37,-28],[-37,-29],[-37,-34],[-37,-35],[-37,-36],[-38,-27],[-38,-30],[-38,-34],[-39,-31],[-39,-35],[-40,-36],[-41,-30],[-41,-31],[-41,-33],[-41,-40],[-42,-30],[-42,-38],[-42,-40],[-43,-31],[-43,-36],[-43,-39],[-43,-40],[-43,-42],[-44,-26],[-44,-33],[-45,-3],[-45,-26],[-45,-30],[-45,-33],[-45,-44],[-46,-39],[-46,-43],[-46,-44],[-47,-27],[-47,-29],[-47,-34],[-47,-44],[-47,-46],[-48,-26],[-48,-27],[-48,-29],[-48,-46],[-48,-47],[-49,-30],[-49,-31],[-49,-35],[-49,-39],[-49,-43],[-49,-44],[-49,-46],[-50,-30],[-50,-32],[-50,-38],[-50,-44],[-50,-49],[-51,-2],[-51,-26],[-51,-30],[-51,-31],[-51,-32],[-51,-45],[-51,-48],[-51,-49],[-51,-50],[-52,-34],[-52,-39],[-52,-43],[-52,-47],[-52,-49],[-53,-34],[-53,-42],[-53,-47],[-53,-52],[-54,-38],[-54,-39],[-54,-43],[-54,-49],[-54,-50],[-55,-38],[-55,-40],[-55,-42],[-55,-50],[-55,-53],[-55,-54],[-56,-39],[-56,-42],[-56,-43],[-56,-46],[-56,-49],[-56,-53],[-56,-54],[-56,-55],[-57,-33],[-57,-45],[-58,-3],[-58,-28],[-58,-31],[-58,-33],[-58,-44],[-58,-45],[-59,-38],[-59,-42],[-59,-46],[-59,-57],[-60,-29],[-60,-35],[-60,-47],[-60,-57],[-60,-59],[-61,-1],[-61,-26],[-61,-27],[-61,-28],[-61,-29],[-61,-57],[-61,-58],[-61,-59],[-61,-60],[-62,-27],[-62,-30],[-62,-31],[-62,-34],[-62,-38],[-62,-42],[-62,-57],[-62,-59],[-63,-31],[-63,-32],[-63,-39],[-63,-50],[-63,-57],[-63,-62],[-64,-2],[-64,-30],[-64,-31],[-64,-32],[-64,-61],[-64,-62],[-64,-63],[-65,-35],[-65,-38],[-65,-42],[-65,-52],[-65,-60],[-65,-62],[-66,-35],[-66,-43],[-66,-60],[-66,-65],[-67,-38],[-67,-42],[-67,-54],[-67,-59],[-67,-62],[-67,-63],[-67,-65],[-68,-39],[-68,-40],[-68,-43],[-68,-63],[-68,-66],[-68,-67],[-69,-38],[-69,-43],[-69,-56],[-69,-62],[-69,-65],[-69,-66],[-69,-68],[-70,-26],[-70,-33],[-70,-44],[-70,-45],[-70,-46],[-70,-57],[-70,-58],[-70,-59],[-70,-62],[-71,-46],[-71,-47],[-71,-52],[-71,-59],[-71,-60],[-71,-65],[-71,-70],[-72,-32],[-72,-49],[-72,-50],[-72,-54],[-72,-62],[-72,-67],[-72,-70],[-73,-52],[-73,-56],[-73,-65],[-73,-66],[-73,-69],[-73,-71],[-74,-40],[-74,-54],[-74,-56],[-74,-67],[-74,-68],[-74,-69],[-74,-72],[-74,-73],[-3,1,2,27,28,29,30,31,32],[-27,2,3,31,32],[-30,1,3,28,29],[-31,1,3,27,29],[-1,-33,-36],[-27,-33,-36],[-44,1,8,28,29],[-45,1,7,28,29,46,47],[-47,1,8,26,28,45],[-60,1,15,26,27,58],[-50,2,10,26,31,45],[-10,-31,-50],[-31,-45,-50],[-17,2,16,26,30,32,57,62,63],[-63,2,17,26,30,58],[-4,3,5,41],[-37,3,5,41],[-3,-4,-5],[-3,-4,-41],[-3,-37,-41],[-48,3,10],[-51,3,8],[-3,-8,-51],[-61,3,17],[-64,3,15],[-3,-17,-61],[-37,6,40,42,43],[-37,18,60,65,66],[-8,4,33,37],[-45,4,37],[-48,4,33,37],[-4,15,58,61],[-15,4,33,37],[-33,15,61],[-37,15,58,61],[-58,4,37],[-61,4,33,37],[-38,6,36,43],[-41,12,50,54,55],[-41,19,63,67,68],[-5,10,45,51],[-10,5,33,41],[-41,10,45,51],[-51,5,33,41],[-5,17,58,64],[-17,5,33,41],[-41,17,58,64],[-64,5,33,41],[-36,13,55,56],[-6,20,66,68,69],[-46,9,30,50,51],[-47,9,30,49,50,51],[-51,7,27,46,47],[-48,11,34,52,53],[-52,7,27,44,48],[-48,21,59,70,71],[-71,7,27,44,48],[-15,8,45,48],[-45,15,61],[-58,8,48],[-51,12,38,54,55],[-54,9,30,44,51],[-70,9,30,50,51],[-72,9,30,44,51],[-10,17,58,64],[-17,10,45,51],[-45,17,64],[-51,17,58,64],[-58,10,51],[-64,10,45,51],[-47,13,42,55,56],[-55,11,34,47,52],[-71,11,34,53],[-73,11,34,47],[-42,12,50,54],[-53,12,38,50,54],[-56,12,38,50],[-55,24,67,72],[-13,25,69,73,74],[-55,25,69,73],[-73,13,42,55],[-59,16,31,63,64],[-61,16,31,62,63],[-62,14,28,60,61],[-63,14,28,59,60,61],[-64,14,28,59,60],[-61,18,35,65,66],[-65,14,28,57,61],[-66,14,28,57,59,61],[-61,21,46,70,71],[-62,19,39,68],[-68,16,31,57,62,64],[-63,22,49,70],[-64,22,49,70,72],[-70,16,31,63,64],[-43,18,60,65],[-66,23,52,71],[-73,18,35,60],[-43,19,63,67],[-66,19,39,63,67],[-69,19,39,63],[-63,24,54,74],[-68,24,54,72],[-74,19,39,63],[-43,25,73,74],[-66,25,56,74],[-68,25,56,73],[-73,20,43,68],[-74,20,43,66],[-49,21,59,71],[-70,23,52,65,73],[-62,24,54,74],[-70,24,54,67,74],[-56,23,65,71],[-69,23,52,71],[-74,23,52,65,71],[-73,24,54,67,72],[-4,75],[-5,76],[-6,77],[-7,78],[-8,79],[-9,80],[-10,81],[-12,82],[-13,83],[-15,84],[-16,85],[-17,86],[-19,87],[-20,88],[-21,89],[-22,90],[-23,91],[-24,92],[-25,93],[-75,94],[-94,95],[-95,96],[-78,97],[-77,97],[-97,98],[-76,98],[-76,-97,99],[-80,100],[-79,100],[-81,101],[-101,102],[-100,102],[-102,103],[-98,103],[-98,-102,104],[-99,-102,105],[-103,106],[-104,107],[-105,108],[-96,-103,107],[-83,109],[-109,110],[-82,110],[-85,111],[-84,111],[-86,112],[-112,113],[-111,113],[-111,-112,114],[-113,115],[-114,116],[-110,-113,116],[-89,117],[-88,-89,118],[-117,119],[-118,120],[-87,119],[-91,121],[-90,-91,122],[-93,123],[-92,123],[-92,-93,124],[-123,125],[-124,126],[-121,125],[-121,-123,126],[-122,126],[-125,127],[-119,127],[-119,-125,128],[-119,-126,129],[-120,-125,129],[-115,-127,130],[-115,-129,132],[-116,-127,131],[-116,-128,132],[-106,-132,133],[-107,-131,133],[-108,-130,133],[-133],[-134,26,29,33,37],[-29,134],[-33,134],[-37,134],[-135,32,38,39,40,41],[-41,135],[-136,44,45,48,51],[-137,36,53,66,73],[-138,57,58,61,64],[-139,55,68,74],[-55,139],[-74,139],[-140,47,60,71],[-47,140],[-141,50,63,72],[-142,49,62,70],[-143,28,31,35,43,46,52,54,56],[-43,143],[-46,143],[-52,143],[-54,143],[-144,27,30,34,42,59,65,67,69],[-145,134],[-145,135],[-134,-135,145],[-146,137,138],[-147,137],[-147,138],[-148,136,147],[-149,136],[-148,146],[-149,147],[-150,145,149],[-151,145],[-150,148],[-151,149],[-145,-149,151],[-152,140,141],[-153,140],[-153,141],[-154,139,153],[-155,139],[-154,152],[-155,153],[-156,143,144],[-157,143],[-157,144],[-158,142,157],[-159,142],[-158,156],[-159,157],[-160,154],[-160,155,159],[-161,155],[-160,158],[-161,159],[-162,150],[-162,151,161],[-162,160],[-151,-161,163],[162],[-163],[-7,-8,-11,-15,-37,-41,-42,-51,-54,-60,-64,-68,-70,-73],[-7,-8,-11,-15,-37,-41,-43,-51,-55,-60,-64,-67,-70,-73],[-7,-8,-12,-17,-37,-41,-42,-51,-52,-61,-63,-66,-70,-74],[-7,-8,-12,-17,-37,-41,-43,-51,-53,-61,-63,-65,-70,-74],[-8,-11,-12,-15,-37,-41,-42,-46,-51,-60,-64,-68,-72,-73],[-7,-17,-18,-19,-37,-41,-43,-45,-50,-53,-61,-62,-71,-74],[-8,-18,-22,-24,-37,-41,-43,-47,-51,-55,-58,-59,-63,-73],[-7,-11,-12,-17,-37,-41,-42,-45,-49,-61,-63,-66,-71,-74],[-8,-12,-17,-23,-37,-41,-42,-47,-51,-61,-63,-66,-70,-74],[-8,-12,-13,-17,-37,-41,-43,-47,-51,-61,-63,-65,-70,-74],[-8,-17,-23,-25,-37,-41,-42,-47,-51,-54,-61,-63,-66,-70],[-8,-14,-15,-18,-37,-41,-43,-47,-51,-55,-64,-67,-70,-73],[-9,-10,-12,-17,-37,-41,-42,-48,-52,-61,-63,-66,-70,-74],[-10,-16,-17,-19,-37,-41,-43,-48,-50,-53,-61,-65,-70,-74],[-8,-14,-15,-18,-37,-41,-42,-47,-51,-54,-64,-68,-70,-73],[-9,-10,-12,-17,-37,-41,-43,-48,-53,-61,-63,-65,-70,-74],[-10,-16,-17,-19,-37,-41,-42,-48,-50,-52,-61,-66,-70,-74],[-10,-14,-15,-19,-37,-41,-43,-48,-50,-53,-64,-65,-70,-74],[-9,-10,-11,-15,-37,-41,-42,-48,-54,-60,-64,-68,-70,-73],[-8,-16,-17,-18,-37,-41,-43,-47,-51,-55,-61,-67,-70,-73],[-10,-14,-15,-19,-37,-41,-42,-48,-50,-52,-64,-66,-70,-74],[-9,-10,-11,-15,-37,-41,-43,-48,-55,-60,-64,-67,-70,-73],[-8,-16,-17,-18,-37,-41,-42,-47,-51,-54,-61,-68,-70,-73],[-8,-15,-18,-19,-37,-41,-43,-47,-51,-55,-59,-64,-72,-73],[-10,-11,-12,-17,-37,-41,-42,-48,-49,-61,-63,-66,-71,-74],[-10,-17,-18,-19,-37,-41,-43,-48,-50,-53,-61,-62,-71,-74],[-10,-11,-12,-14,-37,-41,-42,-48,-49,-58,-63,-66,-71,-74],[-9,-15,-18,-19,-37,-41,-43,-45,-47,-55,-59,-64,-72,-73],[-8,-11,-12,-16,-37,-41,-42,-46,-51,-58,-60,-68,-72,-73],[-11,-15,-22,-24,-37,-41,-42,-45,-46,-50,-60,-64,-68,-73],[-10,-19,-21,-23,-37,-41,-43,-48,-50,-53,-58,-60,-62,-74],[-12,-17,-21,-23,-37,-41,-42,-45,-47,-49,-61,-63,-66,-74],[-10,-14,-18,-19,-37,-41,-43,-48,-50,-53,-58,-62,-71,-74],[-9,-11,-12,-15,-37,-41,-42,-45,-46,-60,-64,-68,-72,-73],[-8,-16,-18,-19,-37,-41,-43,-47,-51,-55,-58,-59,-72,-73],[-10,-15,-19,-23,-37,-41,-43,-48,-50,-53,-60,-64,-70,-74],[-10,-11,-15,-24,-37,-41,-42,-48,-50,-60,-64,-68,-70,-73],[-8,-17,-18,-24,-37,-41,-43,-47,-51,-55,-61,-63,-70,-73],[-10,-15,-19,-20,-37,-41,-42,-48,-50,-52,-60,-64,-70,-74],[-10,-11,-13,-15,-37,-41,-43,-48,-50,-60,-64,-67,-70,-73],[-8,-17,-18,-20,-37,-41,-42,-47,-51,-54,-61,-63,-70,-73],[-10,-15,-23,-25,-37,-41,-43,-48,-50,-53,-60,-64,-67,-70],[-10,-15,-24,-25,-37,-41,-42,-48,-50,-52,-60,-64,-68,-70],[-8,-17,-24,-25,-37,-41,-43,-47,-51,-55,-61,-63,-65,-70],[4,8,15,33,37,45,48,58,61],[5,10,17,33,41,45,51,58,64]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"group\",\"index\":4,\"kind\":1},{\"tag\":\"group\",\"index\":6,\"kind\":1},{\"tag\":\"group\",\"index\":7,\"kind\":1},{\"tag\":\"group\",\"index\":8,\"kind\":1},{\"tag\":\"group\",\"index\":9,\"kind\":1},{\"tag\":\"group\",\"index\":10,\"kind\":1},{\"tag\":\"group\",\"index\":11,\"kind\":1},{\"tag\":\"group\",\"index\":13,\"kind\":1},{\"tag\":\"group\",\"index\":14,\"kind\":1},{\"tag\":\"group\",\"index\":16,\"kind\":1},{\"tag\":\"group\",\"index\":17,\"kind\":1},{\"tag\":\"group\",\"index\":18,\"kind\":1},{\"tag\":\"group\",\"index\":20,\"kind\":1},{\"tag\":\"group\",\"index\":21,\"kind\":1},{\"tag\":\"group\",\"index\":22,\"kind\":1},{\"tag\":\"group\",\"index\":23,\"kind\":1},{\"tag\":\"group\",\"index\":24,\"kind\":1},{\"tag\":\"group\",\"index\":25,\"kind\":1},{\"tag\":\"group\",\"index\":26,\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group\",\"index\":10,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":29,\"b\":16},{\"tag\":\"incompatible\",\"a\":29,\"b\":27},{\"tag\":\"incompatible\",\"a\":30,\"b\":4},{\"tag\":\"incompatible\",\"a\":30,\"b\":29},{\"tag\":\"incompatible\",\"a\":31,\"b\":11},{\"tag\":\"incompatible\",\"a\":32,\"b\":18},{\"tag\":\"incompatible\",\"a\":34,\"b\":2},{\"tag\":\"incompatible\",\"a\":34,\"b\":33},{\"tag\":\"incompatible\",\"a\":35,\"b\":30},{\"tag\":\"incompatible\",\"a\":37,\"b\":30},{\"tag\":\"incompatible\",\"a\":37,\"b\":35},{\"tag\":\"incompatible\",\"a\":37,\"b\":36},{\"tag\":\"incompatible\",\"a\":38,\"b\":0},{\"tag\":\"incompatible\",\"a\":38,\"b\":28},{\"tag\":\"incompatible\",\"a\":38,\"b\":29},{\"tag\":\"incompatible\",\"a\":38,\"b\":30},{\"tag\":\"incompatible\",\"a\":38,\"b\":35},{\"tag\":\"incompatible\",\"a\":38,\"b\":36},{\"tag\":\"incompatible\",\"a\":38,\"b\":37},{\"tag\":\"incompatible\",\"a\":39,\"b\":28},{\"tag\":\"incompatible\",\"a\":39,\"b\":31},{\"tag\":\"incompatible\",\"a\":39,\"b\":35},{\"tag\":\"incompatible\",\"a\":40,\"b\":32},{\"tag\":\"incompatible\",\"a\":40,\"b\":36},{\"tag\":\"incompatible\",\"a\":41,\"b\":37},{\"tag\":\"incompatible\",\"a\":42,\"b\":31},{\"tag\":\"incompatible\",\"a\":42,\"b\":32},{\"tag\":\"incompatible\",\"a\":42,\"b\":34},{\"tag\":\"incompatible\",\"a\":42,\"b\":41},{\"tag\":\"incompatible\",\"a\":43,\"b\":31},{\"tag\":\"incompatible\",\"a\":43,\"b\":39},{\"tag\":\"incompatible\",\"a\":43,\"b\":41},{\"tag\":\"incompatible\",\"a\":44,\"b\":32},{\"tag\":\"incompatible\",\"a\":44,\"b\":37},{\"tag\":\"incompatible\",\"a\":44,\"b\":40},{\"tag\":\"incompatible\",\"a\":44,\"b\":41},{\"tag\":\"incompatible\",\"a\":44,\"b\":43},{\"tag\":\"incompatible\",\"a\":45,\"b\":27},{\"tag\":\"incompatible\",\"a\":45,\"b\":34},{\"tag\":\"incompatible\",\"a\":46,\"b\":2},{\"tag\":\"incompatible\",\"a\":46,\"b\":27},{\"tag\":\"incompatible\",\"a\":46,\"b\":31},{\"tag\":\"incompatible\",\"a\":46,\"b\":34},{\"tag\":\"incompatible\",\"a\":46,\"b\":45},{\"tag\":\"incompatible\",\"a\":47,\"b\":40},{\"tag\":\"incompatible\",\"a\":47,\"b\":44},{\"tag\":\"incompatible\",\"a\":47,\"b\":45},{\"tag\":\"incompatible\",\"a\":48,\"b\":28},{\"tag\":\"incompatible\",\"a\":48,\"b\":30},{\"tag\":\"incompatible\",\"a\":48,\"b\":35},{\"tag\":\"incompatible\",\"a\":48,\"b\":45},{\"tag\":\"incompatible\",\"a\":48,\"b\":47},{\"tag\":\"incompatible\",\"a\":49,\"b\":27},{\"tag\":\"incompatible\",\"a\":49,\"b\":28},{\"tag\":\"incompatible\",\"a\":49,\"b\":30},{\"tag\":\"incompatible\",\"a\":49,\"b\":47},{\"tag\":\"incompatible\",\"a\":49,\"b\":48},{\"tag\":\"incompatible\",\"a\":50,\"b\":31},{\"tag\":\"incompatible\",\"a\":50,\"b\":32},{\"tag\":\"incompatible\",\"a\":50,\"b\":36},{\"tag\":\"incompatible\",\"a\":50,\"b\":40},{\"tag\":\"incompatible\",\"a\":50,\"b\":44},{\"tag\":\"incompatible\",\"a\":50,\"b\":45},{\"tag\":\"incompatible\",\"a\":50,\"b\":47},{\"tag\":\"incompatible\",\"a\":51,\"b\":31},{\"tag\":\"incompatible\",\"a\":51,\"b\":33},{\"tag\":\"incompatible\",\"a\":51,\"b\":39},{\"tag\":\"incompatible\",\"a\":51,\"b\":45},{\"tag\":\"incompatible\",\"a\":51,\"b\":50},{\"tag\":\"incompatible\",\"a\":52,\"b\":1},{\"tag\":\"incompatible\",\"a\":52,\"b\":27},{\"tag\":\"incompatible\",\"a\":52,\"b\":31},{\"tag\":\"incompatible\",\"a\":52,\"b\":32},{\"tag\":\"incompatible\",\"a\":52,\"b\":33},{\"tag\":\"incompatible\",\"a\":52,\"b\":46},{\"tag\":\"incompatible\",\"a\":52,\"b\":49},{\"tag\":\"incompatible\",\"a\":52,\"b\":50},{\"tag\":\"incompatible\",\"a\":52,\"b\":51},{\"tag\":\"incompatible\",\"a\":53,\"b\":35},{\"tag\":\"incompatible\",\"a\":53,\"b\":40},{\"tag\":\"incompatible\",\"a\":53,\"b\":44},{\"tag\":\"incompatible\",\"a\":53,\"b\":48},{\"tag\":\"incompatible\",\"a\":53,\"b\":50},{\"tag\":\"incompatible\",\"a\":54,\"b\":35},{\"tag\":\"incompatible\",\"a\":54,\"b\":43},{\"tag\":\"incompatible\",\"a\":54,\"b\":48},{\"tag\":\"incompatible\",\"a\":54,\"b\":53},{\"tag\":\"incompatible\",\"a\":55,\"b\":39},{\"tag\":\"incompatible\",\"a\":55,\"b\":40},{\"tag\":\"incompatible\",\"a\":55,\"b\":44},{\"tag\":\"incompatible\",\"a\":55,\"b\":50},{\"tag\":\"incompatible\",\"a\":55,\"b\":51},{\"tag\":\"incompatible\",\"a\":56,\"b\":39},{\"tag\":\"incompatible\",\"a\":56,\"b\":41},{\"tag\":\"incompatible\",\"a\":56,\"b\":43},{\"tag\":\"incompatible\",\"a\":56,\"b\":51},{\"tag\":\"incompatible\",\"a\":56,\"b\":54},{\"tag\":\"incompatible\",\"a\":56,\"b\":55},{\"tag\":\"incompatible\",\"a\":57,\"b\":40},{\"tag\":\"incompatible\",\"a\":57,\"b\":43},{\"tag\":\"incompatible\",\"a\":57,\"b\":44},{\"tag\":\"incompatible\",\"a\":57,\"b\":47},{\"tag\":\"incompatible\",\"a\":57,\"b\":50},{\"tag\":\"incompatible\",\"a\":57,\"b\":54},{\"tag\":\"incompatible\",\"a\":57,\"b\":55},{\"tag\":\"incompatible\",\"a\":57,\"b\":56},{\"tag\":\"incompatible\",\"a\":58,\"b\":34},{\"tag\":\"incompatible\",\"a\":58,\"b\":46},{\"tag\":\"incompatible\",\"a\":59,\"b\":2},{\"tag\":\"incompatible\",\"a\":59,\"b\":29},{\"tag\":\"incompatible\",\"a\":59,\"b\":32},{\"tag\":\"incompatible\",\"a\":59,\"b\":34},{\"tag\":\"incompatible\",\"a\":59,\"b\":45},{\"tag\":\"incompatible\",\"a\":59,\"b\":46},{\"tag\":\"incompatible\",\"a\":60,\"b\":39},{\"tag\":\"incompatible\",\"a\":60,\"b\":43},{\"tag\":\"incompatible\",\"a\":60,\"b\":47},{\"tag\":\"incompatible\",\"a\":60,\"b\":58},{\"tag\":\"incompatible\",\"a\":61,\"b\":30},{\"tag\":\"incompatible\",\"a\":61,\"b\":36},{\"tag\":\"incompatible\",\"a\":61,\"b\":48},{\"tag\":\"incompatible\",\"a\":61,\"b\":58},{\"tag\":\"incompatible\",\"a\":61,\"b\":60},{\"tag\":\"incompatible\",\"a\":62,\"b\":0},{\"tag\":\"incompatible\",\"a\":62,\"b\":27},{\"tag\":\"incompatible\",\"a\":62,\"b\":28},{\"tag\":\"incompatible\",\"a\":62,\"b\":29},{\"tag\":\"incompatible\",\"a\":62,\"b\":30},{\"tag\":\"incompatible\",\"a\":62,\"b\":58},{\"tag\":\"incompatible\",\"a\":62,\"b\":59},{\"tag\":\"incompatible\",\"a\":62,\"b\":60},{\"tag\":\"incompatible\",\"a\":62,\"b\":61},{\"tag\":\"incompatible\",\"a\":63,\"b\":28},{\"tag\":\"incompatible\",\"a\":63,\"b\":31},{\"tag\":\"incompatible\",\"a\":63,\"b\":32},{\"tag\":\"incompatible\",\"a\":63,\"b\":35},{\"tag\":\"incompatible\",\"a\":63,\"b\":39},{\"tag\":\"incompatible\",\"a\":63,\"b\":43},{\"tag\":\"incompatible\",\"a\":63,\"b\":58},{\"tag\":\"incompatible\",\"a\":63,\"b\":60},{\"tag\":\"incompatible\",\"a\":64,\"b\":32},{\"tag\":\"incompatible\",\"a\":64,\"b\":33},{\"tag\":\"incompatible\",\"a\":64,\"b\":40},{\"tag\":\"incompatible\",\"a\":64,\"b\":51},{\"tag\":\"incompatible\",\"a\":64,\"b\":58},{\"tag\":\"incompatible\",\"a\":64,\"b\":63},{\"tag\":\"incompatible\",\"a\":65,\"b\":1},{\"tag\":\"incompatible\",\"a\":65,\"b\":31},{\"tag\":\"incompatible\",\"a\":65,\"b\":32},{\"tag\":\"incompatible\",\"a\":65,\"b\":33},{\"tag\":\"incompatible\",\"a\":65,\"b\":62},{\"tag\":\"incompatible\",\"a\":65,\"b\":63},{\"tag\":\"incompatible\",\"a\":65,\"b\":64},{\"tag\":\"incompatible\",\"a\":66,\"b\":36},{\"tag\":\"incompatible\",\"a\":66,\"b\":39},{\"tag\":\"incompatible\",\"a\":66,\"b\":43},{\"tag\":\"incompatible\",\"a\":66,\"b\":53},{\"tag\":\"incompatible\",\"a\":66,\"b\":61},{\"tag\":\"incompatible\",\"a\":66,\"b\":63},{\"tag\":\"incompatible\",\"a\":67,\"b\":36},{\"tag\":\"incompatible\",\"a\":67,\"b\":44},{\"tag\":\"incompatible\",\"a\":67,\"b\":61},{\"tag\":\"incompatible\",\"a\":67,\"b\":66},{\"tag\":\"incompatible\",\"a\":68,\"b\":39},{\"tag\":\"incompatible\",\"a\":68,\"b\":43},{\"tag\":\"incompatible\",\"a\":68,\"b\":55},{\"tag\":\"incompatible\",\"a\":68,\"b\":60},{\"tag\":\"incompatible\",\"a\":68,\"b\":63},{\"tag\":\"incompatible\",\"a\":68,\"b\":64},{\"tag\":\"incompatible\",\"a\":68,\"b\":66},{\"tag\":\"incompatible\",\"a\":69,\"b\":40},{\"tag\":\"incompatible\",\"a\":69,\"b\":41},{\"tag\":\"incompatible\",\"a\":69,\"b\":44},{\"tag\":\"incompatible\",\"a\":69,\"b\":64},{\"tag\":\"incompatible\",\"a\":69,\"b\":67},{\"tag\":\"incompatible\",\"a\":69,\"b\":68},{\"tag\":\"incompatible\",\"a\":70,\"b\":39},{\"tag\":\"incompatible\",\"a\":70,\"b\":44},{\"tag\":\"incompatible\",\"a\":70,\"b\":57},{\"tag\":\"incompatible\",\"a\":70,\"b\":63},{\"tag\":\"incompatible\",\"a\":70,\"b\":66},{\"tag\":\"incompatible\",\"a\":70,\"b\":67},{\"tag\":\"incompatible\",\"a\":70,\"b\":69},{\"tag\":\"incompatible\",\"a\":71,\"b\":27},{\"tag\":\"incompatible\",\"a\":71,\"b\":34},{\"tag\":\"incompatible\",\"a\":71,\"b\":45},{\"tag\":\"incompatible\",\"a\":71,\"b\":46},{\"tag\":\"incompatible\",\"a\":71,\"b\":47},{\"tag\":\"incompatible\",\"a\":71,\"b\":58},{\"tag\":\"incompatible\",\"a\":71,\"b\":59},{\"tag\":\"incompatible\",\"a\":71,\"b\":60},{\"tag\":\"incompatible\",\"a\":71,\"b\":63},{\"tag\":\"incompatible\",\"a\":72,\"b\":47},{\"tag\":\"incompatible\",\"a\":72,\"b\":48},{\"tag\":\"incompatible\",\"a\":72,\"b\":53},{\"tag\":\"incompatible\",\"a\":72,\"b\":60},{\"tag\":\"incompatible\",\"a\":72,\"b\":61},{\"tag\":\"incompatible\",\"a\":72,\"b\":66},{\"tag\":\"incompatible\",\"a\":72,\"b\":71},{\"tag\":\"incompatible\",\"a\":73,\"b\":33},{\"tag\":\"incompatible\",\"a\":73,\"b\":50},{\"tag\":\"incompatible\",\"a\":73,\"b\":51},{\"tag\":\"incompatible\",\"a\":73,\"b\":55},{\"tag\":\"incompatible\",\"a\":73,\"b\":63},{\"tag\":\"incompatible\",\"a\":73,\"b\":68},{\"tag\":\"incompatible\",\"a\":73,\"b\":71},{\"tag\":\"incompatible\",\"a\":74,\"b\":53},{\"tag\":\"incompatible\",\"a\":74,\"b\":57},{\"tag\":\"incompatible\",\"a\":74,\"b\":66},{\"tag\":\"incompatible\",\"a\":74,\"b\":67},{\"tag\":\"incompatible\",\"a\":74,\"b\":70},{\"tag\":\"incompatible\",\"a\":74,\"b\":72},{\"tag\":\"incompatible\",\"a\":75,\"b\":41},{\"tag\":\"incompatible\",\"a\":75,\"b\":55},{\"tag\":\"incompatible\",\"a\":75,\"b\":57},{\"tag\":\"incompatible\",\"a\":75,\"b\":68},{\"tag\":\"incompatible\",\"a\":75,\"b\":69},{\"tag\":\"incompatible\",\"a\":75,\"b\":70},{\"tag\":\"incompatible\",\"a\":75,\"b\":73},{\"tag\":\"incompatible\",\"a\":75,\"b\":74},{\"tag\":\"mate\",\"ridge\":7,\"a\":2,\"owners\":[0,1,28,29,30,31,32,33]},{\"tag\":\"mate\",\"ridge\":7,\"a\":28,\"owners\":[1,2,32,33]},{\"tag\":\"mate\",\"ridge\":7,\"a\":31,\"owners\":[0,2,29,30]},{\"tag\":\"mate\",\"ridge\":7,\"a\":32,\"owners\":[0,2,28,30]},{\"tag\":\"three\",\"ridge\":11,\"vertices\":[0,34,37]},{\"tag\":\"three\",\"ridge\":11,\"vertices\":[28,34,37]},{\"tag\":\"mate\",\"ridge\":13,\"a\":45,\"owners\":[0,9,29,30]},{\"tag\":\"mate\",\"ridge\":13,\"a\":46,\"owners\":[0,8,29,30,47,48]},{\"tag\":\"mate\",\"ridge\":13,\"a\":48,\"owners\":[0,9,27,29,46]},{\"tag\":\"mate\",\"ridge\":14,\"a\":61,\"owners\":[0,16,27,28,59]},{\"tag\":\"mate\",\"ridge\":21,\"a\":51,\"owners\":[1,11,27,32,46]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[11,32,51]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[32,46,51]},{\"tag\":\"mate\",\"ridge\":22,\"a\":18,\"owners\":[1,17,27,31,33,58,63,64]},{\"tag\":\"mate\",\"ridge\":22,\"a\":64,\"owners\":[1,18,27,31,59]},{\"tag\":\"mate\",\"ridge\":515,\"a\":4,\"owners\":[2,6,42]},{\"tag\":\"mate\",\"ridge\":515,\"a\":38,\"owners\":[2,6,42]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[2,4,6]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[2,4,42]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[2,38,42]},{\"tag\":\"mate\",\"ridge\":517,\"a\":49,\"owners\":[2,11]},{\"tag\":\"mate\",\"ridge\":517,\"a\":52,\"owners\":[2,9]},{\"tag\":\"three\",\"ridge\":517,\"vertices\":[2,9,52]},{\"tag\":\"mate\",\"ridge\":518,\"a\":62,\"owners\":[2,18]},{\"tag\":\"mate\",\"ridge\":518,\"a\":65,\"owners\":[2,16]},{\"tag\":\"three\",\"ridge\":518,\"vertices\":[2,18,62]},{\"tag\":\"mate\",\"ridge\":131,\"a\":38,\"owners\":[7,41,43,44]},{\"tag\":\"mate\",\"ridge\":138,\"a\":38,\"owners\":[19,61,66,67]},{\"tag\":\"mate\",\"ridge\":521,\"a\":9,\"owners\":[4,34,38]},{\"tag\":\"mate\",\"ridge\":521,\"a\":46,\"owners\":[4,38]},{\"tag\":\"mate\",\"ridge\":521,\"a\":49,\"owners\":[4,34,38]},{\"tag\":\"mate\",\"ridge\":522,\"a\":4,\"owners\":[16,59,62]},{\"tag\":\"mate\",\"ridge\":522,\"a\":16,\"owners\":[4,34,38]},{\"tag\":\"mate\",\"ridge\":522,\"a\":34,\"owners\":[16,62]},{\"tag\":\"mate\",\"ridge\":522,\"a\":38,\"owners\":[16,59,62]},{\"tag\":\"mate\",\"ridge\":522,\"a\":59,\"owners\":[4,38]},{\"tag\":\"mate\",\"ridge\":522,\"a\":62,\"owners\":[4,34,38]},{\"tag\":\"mate\",\"ridge\":259,\"a\":39,\"owners\":[7,37,44]},{\"tag\":\"mate\",\"ridge\":273,\"a\":42,\"owners\":[13,51,55,56]},{\"tag\":\"mate\",\"ridge\":274,\"a\":42,\"owners\":[20,64,68,69]},{\"tag\":\"mate\",\"ridge\":529,\"a\":6,\"owners\":[11,46,52]},{\"tag\":\"mate\",\"ridge\":529,\"a\":11,\"owners\":[6,34,42]},{\"tag\":\"mate\",\"ridge\":529,\"a\":42,\"owners\":[11,46,52]},{\"tag\":\"mate\",\"ridge\":529,\"a\":52,\"owners\":[6,34,42]},{\"tag\":\"mate\",\"ridge\":530,\"a\":6,\"owners\":[18,59,65]},{\"tag\":\"mate\",\"ridge\":530,\"a\":18,\"owners\":[6,34,42]},{\"tag\":\"mate\",\"ridge\":530,\"a\":42,\"owners\":[18,59,65]},{\"tag\":\"mate\",\"ridge\":530,\"a\":65,\"owners\":[6,34,42]},{\"tag\":\"mate\",\"ridge\":385,\"a\":37,\"owners\":[14,56,57]},{\"tag\":\"mate\",\"ridge\":386,\"a\":7,\"owners\":[21,67,69,70]},{\"tag\":\"mate\",\"ridge\":37,\"a\":47,\"owners\":[10,31,51,52]},{\"tag\":\"mate\",\"ridge\":37,\"a\":48,\"owners\":[10,31,50,51,52]},{\"tag\":\"mate\",\"ridge\":37,\"a\":52,\"owners\":[8,28,47,48]},{\"tag\":\"mate\",\"ridge\":41,\"a\":49,\"owners\":[12,35,53,54]},{\"tag\":\"mate\",\"ridge\":41,\"a\":53,\"owners\":[8,28,45,49]},{\"tag\":\"mate\",\"ridge\":44,\"a\":49,\"owners\":[22,60,71,72]},{\"tag\":\"mate\",\"ridge\":44,\"a\":72,\"owners\":[8,28,45,49]},{\"tag\":\"mate\",\"ridge\":524,\"a\":16,\"owners\":[9,46,49]},{\"tag\":\"mate\",\"ridge\":524,\"a\":46,\"owners\":[16,62]},{\"tag\":\"mate\",\"ridge\":524,\"a\":59,\"owners\":[9,49]},{\"tag\":\"mate\",\"ridge\":49,\"a\":52,\"owners\":[13,39,55,56]},{\"tag\":\"mate\",\"ridge\":49,\"a\":55,\"owners\":[10,31,45,52]},{\"tag\":\"mate\",\"ridge\":52,\"a\":71,\"owners\":[10,31,51,52]},{\"tag\":\"mate\",\"ridge\":52,\"a\":73,\"owners\":[10,31,45,52]},{\"tag\":\"mate\",\"ridge\":532,\"a\":11,\"owners\":[18,59,65]},{\"tag\":\"mate\",\"ridge\":532,\"a\":18,\"owners\":[11,46,52]},{\"tag\":\"mate\",\"ridge\":532,\"a\":46,\"owners\":[18,65]},{\"tag\":\"mate\",\"ridge\":532,\"a\":52,\"owners\":[18,59,65]},{\"tag\":\"mate\",\"ridge\":532,\"a\":59,\"owners\":[11,52]},{\"tag\":\"mate\",\"ridge\":532,\"a\":65,\"owners\":[11,46,52]},{\"tag\":\"mate\",\"ridge\":161,\"a\":48,\"owners\":[14,43,56,57]},{\"tag\":\"mate\",\"ridge\":161,\"a\":56,\"owners\":[12,35,48,53]},{\"tag\":\"mate\",\"ridge\":168,\"a\":72,\"owners\":[12,35,54]},{\"tag\":\"mate\",\"ridge\":168,\"a\":74,\"owners\":[12,35,48]},{\"tag\":\"mate\",\"ridge\":289,\"a\":43,\"owners\":[13,51,55]},{\"tag\":\"mate\",\"ridge\":289,\"a\":54,\"owners\":[13,39,51,55]},{\"tag\":\"mate\",\"ridge\":289,\"a\":57,\"owners\":[13,39,51]},{\"tag\":\"mate\",\"ridge\":304,\"a\":56,\"owners\":[25,68,73]},{\"tag\":\"mate\",\"ridge\":416,\"a\":14,\"owners\":[26,70,74,75]},{\"tag\":\"mate\",\"ridge\":416,\"a\":56,\"owners\":[26,70,74]},{\"tag\":\"mate\",\"ridge\":416,\"a\":74,\"owners\":[14,43,56]},{\"tag\":\"mate\",\"ridge\":70,\"a\":60,\"owners\":[17,32,64,65]},{\"tag\":\"mate\",\"ridge\":70,\"a\":62,\"owners\":[17,32,63,64]},{\"tag\":\"mate\",\"ridge\":70,\"a\":63,\"owners\":[15,29,61,62]},{\"tag\":\"mate\",\"ridge\":70,\"a\":64,\"owners\":[15,29,60,61,62]},{\"tag\":\"mate\",\"ridge\":70,\"a\":65,\"owners\":[15,29,60,61]},{\"tag\":\"mate\",\"ridge\":74,\"a\":62,\"owners\":[19,36,66,67]},{\"tag\":\"mate\",\"ridge\":74,\"a\":66,\"owners\":[15,29,58,62]},{\"tag\":\"mate\",\"ridge\":74,\"a\":67,\"owners\":[15,29,58,60,62]},{\"tag\":\"mate\",\"ridge\":76,\"a\":62,\"owners\":[22,47,71,72]},{\"tag\":\"mate\",\"ridge\":82,\"a\":63,\"owners\":[20,40,69]},{\"tag\":\"mate\",\"ridge\":82,\"a\":69,\"owners\":[17,32,58,63,65]},{\"tag\":\"mate\",\"ridge\":84,\"a\":64,\"owners\":[23,50,71]},{\"tag\":\"mate\",\"ridge\":84,\"a\":65,\"owners\":[23,50,71,73]},{\"tag\":\"mate\",\"ridge\":84,\"a\":71,\"owners\":[17,32,64,65]},{\"tag\":\"mate\",\"ridge\":194,\"a\":44,\"owners\":[19,61,66]},{\"tag\":\"mate\",\"ridge\":200,\"a\":67,\"owners\":[24,53,72]},{\"tag\":\"mate\",\"ridge\":200,\"a\":74,\"owners\":[19,36,61]},{\"tag\":\"mate\",\"ridge\":322,\"a\":44,\"owners\":[20,64,68]},{\"tag\":\"mate\",\"ridge\":322,\"a\":67,\"owners\":[20,40,64,68]},{\"tag\":\"mate\",\"ridge\":322,\"a\":70,\"owners\":[20,40,64]},{\"tag\":\"mate\",\"ridge\":336,\"a\":64,\"owners\":[25,55,75]},{\"tag\":\"mate\",\"ridge\":336,\"a\":69,\"owners\":[25,55,73]},{\"tag\":\"mate\",\"ridge\":336,\"a\":75,\"owners\":[20,40,64]},{\"tag\":\"mate\",\"ridge\":448,\"a\":44,\"owners\":[26,74,75]},{\"tag\":\"mate\",\"ridge\":448,\"a\":67,\"owners\":[26,57,75]},{\"tag\":\"mate\",\"ridge\":448,\"a\":69,\"owners\":[26,57,74]},{\"tag\":\"mate\",\"ridge\":448,\"a\":74,\"owners\":[21,44,69]},{\"tag\":\"mate\",\"ridge\":448,\"a\":75,\"owners\":[21,44,67]},{\"tag\":\"mate\",\"ridge\":100,\"a\":50,\"owners\":[22,60,72]},{\"tag\":\"mate\",\"ridge\":104,\"a\":71,\"owners\":[24,53,66,74]},{\"tag\":\"mate\",\"ridge\":112,\"a\":63,\"owners\":[25,55,75]},{\"tag\":\"mate\",\"ridge\":112,\"a\":71,\"owners\":[25,55,68,75]},{\"tag\":\"mate\",\"ridge\":224,\"a\":57,\"owners\":[24,66,72]},{\"tag\":\"mate\",\"ridge\":224,\"a\":70,\"owners\":[24,53,72]},{\"tag\":\"mate\",\"ridge\":224,\"a\":75,\"owners\":[24,53,66,72]},{\"tag\":\"mate\",\"ridge\":352,\"a\":74,\"owners\":[25,55,68,73]},{\"tag\":\"group_take\",\"kind\":1,\"index\":4,\"member\":4,\"full_literals\":[-4,75]},{\"tag\":\"group_take\",\"kind\":1,\"index\":6,\"member\":6,\"full_literals\":[-5,76]},{\"tag\":\"group_take\",\"kind\":1,\"index\":7,\"member\":7,\"full_literals\":[-6,77]},{\"tag\":\"group_take\",\"kind\":1,\"index\":8,\"member\":8,\"full_literals\":[-7,78]},{\"tag\":\"group_take\",\"kind\":1,\"index\":9,\"member\":9,\"full_literals\":[-8,79]},{\"tag\":\"group_take\",\"kind\":1,\"index\":10,\"member\":10,\"full_literals\":[-9,80]},{\"tag\":\"group_take\",\"kind\":1,\"index\":11,\"member\":11,\"full_literals\":[-10,81]},{\"tag\":\"group_take\",\"kind\":1,\"index\":13,\"member\":13,\"full_literals\":[-12,82]},{\"tag\":\"group_take\",\"kind\":1,\"index\":14,\"member\":14,\"full_literals\":[-13,83]},{\"tag\":\"group_take\",\"kind\":1,\"index\":16,\"member\":16,\"full_literals\":[-15,84]},{\"tag\":\"group_take\",\"kind\":1,\"index\":17,\"member\":17,\"full_literals\":[-16,85]},{\"tag\":\"group_take\",\"kind\":1,\"index\":18,\"member\":18,\"full_literals\":[-17,86]},{\"tag\":\"group_take\",\"kind\":1,\"index\":20,\"member\":20,\"full_literals\":[-19,87]},{\"tag\":\"group_take\",\"kind\":1,\"index\":21,\"member\":21,\"full_literals\":[-20,88]},{\"tag\":\"group_take\",\"kind\":1,\"index\":22,\"member\":22,\"full_literals\":[-21,89]},{\"tag\":\"group_take\",\"kind\":1,\"index\":23,\"member\":23,\"full_literals\":[-22,90]},{\"tag\":\"group_take\",\"kind\":1,\"index\":24,\"member\":24,\"full_literals\":[-23,91]},{\"tag\":\"group_take\",\"kind\":1,\"index\":25,\"member\":25,\"full_literals\":[-24,92]},{\"tag\":\"group_take\",\"kind\":1,\"index\":26,\"member\":26,\"full_literals\":[-25,93]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped1_0006\",\"right_name\":\"grouped1_0008\",\"joined_name\":\"grouped1_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-75,false,94],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped1_0004\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0005\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-94,95],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0005\",\"joined_name\":\"grouped1_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-95,96],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0014\",\"joined_name\":\"grouped1_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-78,97],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0014\",\"joined_name\":\"grouped1_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-77,false,97],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped1_0009\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-97,98],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped1_0009\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-76,false,98],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped1_0009\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-76,-97,99],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-80,100],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-79,false,100],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11],\"right\":[12],\"left_name\":\"grouped1_0019\",\"right_name\":\"grouped1_0021\",\"joined_name\":\"grouped1_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-81,false,101],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[9,10],\"right\":[11,12],\"left_name\":\"grouped1_0016\",\"right_name\":\"grouped1_0020\",\"joined_name\":\"grouped1_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-101,102],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[9,10],\"right\":[11,12],\"left_name\":\"grouped1_0016\",\"right_name\":\"grouped1_0020\",\"joined_name\":\"grouped1_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-100,false,102],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11,12],\"left_name\":\"grouped1_0010\",\"right_name\":\"grouped1_0017\",\"joined_name\":\"grouped1_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-102,103],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11,12],\"left_name\":\"grouped1_0010\",\"right_name\":\"grouped1_0017\",\"joined_name\":\"grouped1_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-98,false,103],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11,12],\"left_name\":\"grouped1_0010\",\"right_name\":\"grouped1_0017\",\"joined_name\":\"grouped1_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-98,-102,104],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11,12],\"left_name\":\"grouped1_0010\",\"right_name\":\"grouped1_0017\",\"joined_name\":\"grouped1_0011\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-99,-102,105],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11,12],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0011\",\"joined_name\":\"grouped1_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-103,106],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11,12],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0011\",\"joined_name\":\"grouped1_0002\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-104,107],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11,12],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0011\",\"joined_name\":\"grouped1_0002\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-105,108],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11,12],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0011\",\"joined_name\":\"grouped1_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-96,-103,107],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14],\"right\":[15],\"left_name\":\"grouped1_0026\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0027\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-83,false,109],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13],\"right\":[14,15],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0027\",\"joined_name\":\"grouped1_0023\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-109,110],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13],\"right\":[14,15],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0027\",\"joined_name\":\"grouped1_0023\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-82,false,110],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16],\"right\":[17],\"left_name\":\"grouped1_0029\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0030\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-85,111],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16],\"right\":[17],\"left_name\":\"grouped1_0029\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0030\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-84,false,111],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[18],\"right\":[19],\"left_name\":\"grouped1_0033\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0034\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-86,false,112],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17],\"right\":[18,19],\"left_name\":\"grouped1_0030\",\"right_name\":\"grouped1_0034\",\"joined_name\":\"grouped1_0031\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-112,113],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17],\"right\":[18,19],\"left_name\":\"grouped1_0030\",\"right_name\":\"grouped1_0034\",\"joined_name\":\"grouped1_0031\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-111,false,113],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17],\"right\":[18,19],\"left_name\":\"grouped1_0030\",\"right_name\":\"grouped1_0034\",\"joined_name\":\"grouped1_0031\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-111,-112,114],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13,14,15],\"right\":[16,17,18,19],\"left_name\":\"grouped1_0023\",\"right_name\":\"grouped1_0031\",\"joined_name\":\"grouped1_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-113,115],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13,14,15],\"right\":[16,17,18,19],\"left_name\":\"grouped1_0023\",\"right_name\":\"grouped1_0031\",\"joined_name\":\"grouped1_0024\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-114,116],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13,14,15],\"right\":[16,17,18,19],\"left_name\":\"grouped1_0023\",\"right_name\":\"grouped1_0031\",\"joined_name\":\"grouped1_0024\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-110,-113,116],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[21],\"right\":[22],\"left_name\":\"grouped1_0039\",\"right_name\":\"grouped1_0041\",\"joined_name\":\"grouped1_0040\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-89,117],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[21],\"right\":[22],\"left_name\":\"grouped1_0039\",\"right_name\":\"grouped1_0041\",\"joined_name\":\"grouped1_0040\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-88,-89,118],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20],\"right\":[21,22],\"left_name\":\"grouped1_0036\",\"right_name\":\"grouped1_0040\",\"joined_name\":\"grouped1_0037\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-117,119],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20],\"right\":[21,22],\"left_name\":\"grouped1_0036\",\"right_name\":\"grouped1_0040\",\"joined_name\":\"grouped1_0037\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-118,120],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20],\"right\":[21,22],\"left_name\":\"grouped1_0036\",\"right_name\":\"grouped1_0040\",\"joined_name\":\"grouped1_0037\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-87,false,119],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[23],\"right\":[24],\"left_name\":\"grouped1_0042\",\"right_name\":\"grouped1_0045\",\"joined_name\":\"grouped1_0043\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-91,121],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[23],\"right\":[24],\"left_name\":\"grouped1_0042\",\"right_name\":\"grouped1_0045\",\"joined_name\":\"grouped1_0043\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-90,-91,122],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[25],\"right\":[26],\"left_name\":\"grouped1_0046\",\"right_name\":\"grouped1_0048\",\"joined_name\":\"grouped1_0047\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-93,123],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[25],\"right\":[26],\"left_name\":\"grouped1_0046\",\"right_name\":\"grouped1_0048\",\"joined_name\":\"grouped1_0047\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-92,false,123],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[25],\"right\":[26],\"left_name\":\"grouped1_0046\",\"right_name\":\"grouped1_0048\",\"joined_name\":\"grouped1_0047\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-92,-93,124],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[23,24],\"right\":[25,26],\"left_name\":\"grouped1_0043\",\"right_name\":\"grouped1_0047\",\"joined_name\":\"grouped1_0044\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-123,125],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[23,24],\"right\":[25,26],\"left_name\":\"grouped1_0043\",\"right_name\":\"grouped1_0047\",\"joined_name\":\"grouped1_0044\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-124,126],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[23,24],\"right\":[25,26],\"left_name\":\"grouped1_0043\",\"right_name\":\"grouped1_0047\",\"joined_name\":\"grouped1_0044\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-121,false,125],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[23,24],\"right\":[25,26],\"left_name\":\"grouped1_0043\",\"right_name\":\"grouped1_0047\",\"joined_name\":\"grouped1_0044\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-121,-123,126],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[23,24],\"right\":[25,26],\"left_name\":\"grouped1_0043\",\"right_name\":\"grouped1_0047\",\"joined_name\":\"grouped1_0044\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-122,false,126],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20,21,22],\"right\":[23,24,25,26],\"left_name\":\"grouped1_0037\",\"right_name\":\"grouped1_0044\",\"joined_name\":\"grouped1_0038\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-125,127],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20,21,22],\"right\":[23,24,25,26],\"left_name\":\"grouped1_0037\",\"right_name\":\"grouped1_0044\",\"joined_name\":\"grouped1_0038\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-119,false,127],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20,21,22],\"right\":[23,24,25,26],\"left_name\":\"grouped1_0037\",\"right_name\":\"grouped1_0044\",\"joined_name\":\"grouped1_0038\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-119,-125,128],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20,21,22],\"right\":[23,24,25,26],\"left_name\":\"grouped1_0037\",\"right_name\":\"grouped1_0044\",\"joined_name\":\"grouped1_0038\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-119,-126,129],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20,21,22],\"right\":[23,24,25,26],\"left_name\":\"grouped1_0037\",\"right_name\":\"grouped1_0044\",\"joined_name\":\"grouped1_0038\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-120,-125,129],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13,14,15,16,17,18,19],\"right\":[20,21,22,23,24,25,26],\"left_name\":\"grouped1_0024\",\"right_name\":\"grouped1_0038\",\"joined_name\":\"grouped1_0025\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-115,-127,130],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13,14,15,16,17,18,19],\"right\":[20,21,22,23,24,25,26],\"left_name\":\"grouped1_0024\",\"right_name\":\"grouped1_0038\",\"joined_name\":\"grouped1_0025\",\"a\":1,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-115,-129,132],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13,14,15,16,17,18,19],\"right\":[20,21,22,23,24,25,26],\"left_name\":\"grouped1_0024\",\"right_name\":\"grouped1_0038\",\"joined_name\":\"grouped1_0025\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-116,-127,131],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13,14,15,16,17,18,19],\"right\":[20,21,22,23,24,25,26],\"left_name\":\"grouped1_0024\",\"right_name\":\"grouped1_0038\",\"joined_name\":\"grouped1_0025\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-116,-128,132],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10,11,12],\"right\":[13,14,15,16,17,18,19,20,21,22,23,24,25,26],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0025\",\"joined_name\":\"groupKind1\",\"a\":1,\"b\":4,\"direction\":\"forward\",\"full_literals\":[-106,-132,133],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10,11,12],\"right\":[13,14,15,16,17,18,19,20,21,22,23,24,25,26],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0025\",\"joined_name\":\"groupKind1\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-107,-131,133],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10,11,12],\"right\":[13,14,15,16,17,18,19,20,21,22,23,24,25,26],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0025\",\"joined_name\":\"groupKind1\",\"a\":3,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-108,-130,133],\"grouped\":true,\"kind\":1},{\"tag\":\"quota_upper\",\"kind\":1,\"quota\":4,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[27,30,34,38],\"full_literals\":[-134,26,29,33,37]},{\"tag\":\"group_take\",\"kind\":2,\"index\":0,\"member\":30,\"full_literals\":[-29,134]},{\"tag\":\"group_take\",\"kind\":2,\"index\":0,\"member\":34,\"full_literals\":[-33,134]},{\"tag\":\"group_take\",\"kind\":2,\"index\":0,\"member\":38,\"full_literals\":[-37,134]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[33,39,40,41,42],\"full_literals\":[-135,32,38,39,40,41]},{\"tag\":\"group_take\",\"kind\":2,\"index\":1,\"member\":42,\"full_literals\":[-41,135]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[45,46,49,52],\"full_literals\":[-136,44,45,48,51]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[37,54,67,74],\"full_literals\":[-137,36,53,66,73]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[58,59,62,65],\"full_literals\":[-138,57,58,61,64]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[56,69,75],\"full_literals\":[-139,55,68,74]},{\"tag\":\"group_take\",\"kind\":2,\"index\":5,\"member\":56,\"full_literals\":[-55,139]},{\"tag\":\"group_take\",\"kind\":2,\"index\":5,\"member\":75,\"full_literals\":[-74,139]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[48,61,72],\"full_literals\":[-140,47,60,71]},{\"tag\":\"group_take\",\"kind\":2,\"index\":6,\"member\":48,\"full_literals\":[-47,140]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[51,64,73],\"full_literals\":[-141,50,63,72]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[50,63,71],\"full_literals\":[-142,49,62,70]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[29,32,36,44,47,53,55,57],\"full_literals\":[-143,28,31,35,43,46,52,54,56]},{\"tag\":\"group_take\",\"kind\":2,\"index\":9,\"member\":44,\"full_literals\":[-43,143]},{\"tag\":\"group_take\",\"kind\":2,\"index\":9,\"member\":47,\"full_literals\":[-46,143]},{\"tag\":\"group_take\",\"kind\":2,\"index\":9,\"member\":53,\"full_literals\":[-52,143]},{\"tag\":\"group_take\",\"kind\":2,\"index\":9,\"member\":55,\"full_literals\":[-54,143]},{\"tag\":\"group_or\",\"kind\":2,\"index\":10,\"members\":[28,31,35,43,60,66,68,70],\"full_literals\":[-144,27,30,34,42,59,65,67,69]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0049\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"grouped2_0050\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-145,134,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0049\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"grouped2_0050\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-145,false,135],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0049\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"grouped2_0050\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-134,-135,145],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0056\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0057\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-146,137,138],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0056\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0057\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-147,137,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0056\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0057\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-147,false,138],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0054\",\"right_name\":\"grouped2_0057\",\"joined_name\":\"grouped2_0055\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-148,136,147],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0054\",\"right_name\":\"grouped2_0057\",\"joined_name\":\"grouped2_0055\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-149,136,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0054\",\"right_name\":\"grouped2_0057\",\"joined_name\":\"grouped2_0055\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-148,false,146],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0054\",\"right_name\":\"grouped2_0057\",\"joined_name\":\"grouped2_0055\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-149,false,147],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0050\",\"right_name\":\"grouped2_0055\",\"joined_name\":\"grouped2_0051\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-150,145,149],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0050\",\"right_name\":\"grouped2_0055\",\"joined_name\":\"grouped2_0051\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-151,145,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0050\",\"right_name\":\"grouped2_0055\",\"joined_name\":\"grouped2_0051\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-150,false,148],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0050\",\"right_name\":\"grouped2_0055\",\"joined_name\":\"grouped2_0051\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-151,false,149],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0050\",\"right_name\":\"grouped2_0055\",\"joined_name\":\"grouped2_0051\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-145,-149,151],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0062\",\"right_name\":\"grouped2_0064\",\"joined_name\":\"grouped2_0063\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-152,140,141],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0062\",\"right_name\":\"grouped2_0064\",\"joined_name\":\"grouped2_0063\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-153,140,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0062\",\"right_name\":\"grouped2_0064\",\"joined_name\":\"grouped2_0063\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-153,false,141],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped2_0059\",\"right_name\":\"grouped2_0063\",\"joined_name\":\"grouped2_0060\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-154,139,153],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped2_0059\",\"right_name\":\"grouped2_0063\",\"joined_name\":\"grouped2_0060\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-155,139,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped2_0059\",\"right_name\":\"grouped2_0063\",\"joined_name\":\"grouped2_0060\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-154,false,152],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped2_0059\",\"right_name\":\"grouped2_0063\",\"joined_name\":\"grouped2_0060\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-155,false,153],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped2_0067\",\"right_name\":\"grouped2_0069\",\"joined_name\":\"grouped2_0068\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-156,143,144],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped2_0067\",\"right_name\":\"grouped2_0069\",\"joined_name\":\"grouped2_0068\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-157,143,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped2_0067\",\"right_name\":\"grouped2_0069\",\"joined_name\":\"grouped2_0068\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-157,false,144],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped2_0065\",\"right_name\":\"grouped2_0068\",\"joined_name\":\"grouped2_0066\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-158,142,157],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped2_0065\",\"right_name\":\"grouped2_0068\",\"joined_name\":\"grouped2_0066\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-159,142,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped2_0065\",\"right_name\":\"grouped2_0068\",\"joined_name\":\"grouped2_0066\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-158,false,156],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped2_0065\",\"right_name\":\"grouped2_0068\",\"joined_name\":\"grouped2_0066\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-159,false,157],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0060\",\"right_name\":\"grouped2_0066\",\"joined_name\":\"grouped2_0061\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-160,154,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0060\",\"right_name\":\"grouped2_0066\",\"joined_name\":\"grouped2_0061\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-160,155,159],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0060\",\"right_name\":\"grouped2_0066\",\"joined_name\":\"grouped2_0061\",\"a\":2,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-161,155,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0060\",\"right_name\":\"grouped2_0066\",\"joined_name\":\"grouped2_0061\",\"a\":3,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-160,false,158],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0060\",\"right_name\":\"grouped2_0066\",\"joined_name\":\"grouped2_0061\",\"a\":3,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-161,false,159],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0061\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":6,\"direction\":\"backward\",\"full_literals\":[-162,150,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0061\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-162,151,161],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0061\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-162,false,160],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0061\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":6,\"direction\":\"forward\",\"full_literals\":[-151,-161,163],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":10,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":2,\"quota\":10,\"grouped\":true},{\"tag\":\"block\",\"leaf\":0,\"vertices\":[8,9,12,16,38,42,43,52,55,61,65,69,71,74]},{\"tag\":\"block\",\"leaf\":1,\"vertices\":[8,9,12,16,38,42,44,52,56,61,65,68,71,74]},{\"tag\":\"block\",\"leaf\":2,\"vertices\":[8,9,13,18,38,42,43,52,53,62,64,67,71,75]},{\"tag\":\"block\",\"leaf\":3,\"vertices\":[8,9,13,18,38,42,44,52,54,62,64,66,71,75]},{\"tag\":\"block\",\"leaf\":4,\"vertices\":[9,12,13,16,38,42,43,47,52,61,65,69,73,74]},{\"tag\":\"block\",\"leaf\":5,\"vertices\":[8,18,19,20,38,42,44,46,51,54,62,63,72,75]},{\"tag\":\"block\",\"leaf\":6,\"vertices\":[9,19,23,25,38,42,44,48,52,56,59,60,64,74]},{\"tag\":\"block\",\"leaf\":7,\"vertices\":[8,12,13,18,38,42,43,46,50,62,64,67,72,75]},{\"tag\":\"block\",\"leaf\":8,\"vertices\":[9,13,18,24,38,42,43,48,52,62,64,67,71,75]},{\"tag\":\"block\",\"leaf\":9,\"vertices\":[9,13,14,18,38,42,44,48,52,62,64,66,71,75]},{\"tag\":\"block\",\"leaf\":10,\"vertices\":[9,18,24,26,38,42,43,48,52,55,62,64,67,71]},{\"tag\":\"block\",\"leaf\":11,\"vertices\":[9,15,16,19,38,42,44,48,52,56,65,68,71,74]},{\"tag\":\"block\",\"leaf\":12,\"vertices\":[10,11,13,18,38,42,43,49,53,62,64,67,71,75]},{\"tag\":\"block\",\"leaf\":13,\"vertices\":[11,17,18,20,38,42,44,49,51,54,62,66,71,75]},{\"tag\":\"block\",\"leaf\":14,\"vertices\":[9,15,16,19,38,42,43,48,52,55,65,69,71,74]},{\"tag\":\"block\",\"leaf\":15,\"vertices\":[10,11,13,18,38,42,44,49,54,62,64,66,71,75]},{\"tag\":\"block\",\"leaf\":16,\"vertices\":[11,17,18,20,38,42,43,49,51,53,62,67,71,75]},{\"tag\":\"block\",\"leaf\":17,\"vertices\":[11,15,16,20,38,42,44,49,51,54,65,66,71,75]},{\"tag\":\"block\",\"leaf\":18,\"vertices\":[10,11,12,16,38,42,43,49,55,61,65,69,71,74]},{\"tag\":\"block\",\"leaf\":19,\"vertices\":[9,17,18,19,38,42,44,48,52,56,62,68,71,74]},{\"tag\":\"block\",\"leaf\":20,\"vertices\":[11,15,16,20,38,42,43,49,51,53,65,67,71,75]},{\"tag\":\"block\",\"leaf\":21,\"vertices\":[10,11,12,16,38,42,44,49,56,61,65,68,71,74]},{\"tag\":\"block\",\"leaf\":22,\"vertices\":[9,17,18,19,38,42,43,48,52,55,62,69,71,74]},{\"tag\":\"block\",\"leaf\":23,\"vertices\":[9,16,19,20,38,42,44,48,52,56,60,65,73,74]},{\"tag\":\"block\",\"leaf\":24,\"vertices\":[11,12,13,18,38,42,43,49,50,62,64,67,72,75]},{\"tag\":\"block\",\"leaf\":25,\"vertices\":[11,18,19,20,38,42,44,49,51,54,62,63,72,75]},{\"tag\":\"block\",\"leaf\":26,\"vertices\":[11,12,13,15,38,42,43,49,50,59,64,67,72,75]},{\"tag\":\"block\",\"leaf\":27,\"vertices\":[10,16,19,20,38,42,44,46,48,56,60,65,73,74]},{\"tag\":\"block\",\"leaf\":28,\"vertices\":[9,12,13,17,38,42,43,47,52,59,61,69,73,74]},{\"tag\":\"block\",\"leaf\":29,\"vertices\":[12,16,23,25,38,42,43,46,47,51,61,65,69,74]},{\"tag\":\"block\",\"leaf\":30,\"vertices\":[11,20,22,24,38,42,44,49,51,54,59,61,63,75]},{\"tag\":\"block\",\"leaf\":31,\"vertices\":[13,18,22,24,38,42,43,46,48,50,62,64,67,75]},{\"tag\":\"block\",\"leaf\":32,\"vertices\":[11,15,19,20,38,42,44,49,51,54,59,63,72,75]},{\"tag\":\"block\",\"leaf\":33,\"vertices\":[10,12,13,16,38,42,43,46,47,61,65,69,73,74]},{\"tag\":\"block\",\"leaf\":34,\"vertices\":[9,17,19,20,38,42,44,48,52,56,59,60,73,74]},{\"tag\":\"block\",\"leaf\":35,\"vertices\":[11,16,20,24,38,42,44,49,51,54,61,65,71,75]},{\"tag\":\"block\",\"leaf\":36,\"vertices\":[11,12,16,25,38,42,43,49,51,61,65,69,71,74]},{\"tag\":\"block\",\"leaf\":37,\"vertices\":[9,18,19,25,38,42,44,48,52,56,62,64,71,74]},{\"tag\":\"block\",\"leaf\":38,\"vertices\":[11,16,20,21,38,42,43,49,51,53,61,65,71,75]},{\"tag\":\"block\",\"leaf\":39,\"vertices\":[11,12,14,16,38,42,44,49,51,61,65,68,71,74]},{\"tag\":\"block\",\"leaf\":40,\"vertices\":[9,18,19,21,38,42,43,48,52,55,62,64,71,74]},{\"tag\":\"block\",\"leaf\":41,\"vertices\":[11,16,24,26,38,42,44,49,51,54,61,65,68,71]},{\"tag\":\"block\",\"leaf\":42,\"vertices\":[11,16,25,26,38,42,43,49,51,53,61,65,69,71]},{\"tag\":\"block\",\"leaf\":43,\"vertices\":[9,18,25,26,38,42,44,48,52,56,62,64,66,71]},{\"tag\":\"edge\",\"edge\":29,\"owners\":[4,9,16,34,38,46,49,59,62]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[6,11,18,34,42,46,52,59,65]}]}"
  "526 150 0 478 474 0\n527 160 0 478 476 0\n528 148 0 526 452 0\n529 154 0 527 469 0\n530 158 0 527 472 0\n531 146 0 528 448 0\n532 152 0 529 460 0\n533 156 0 530 467 0\n534 4 8 134 0 421 420 251 250 256 253 257 524 0\n535 -45 58 61 9 -138 -161 0 471 461 457 473 466 42 44 75 108 187 284 426 152 153 433 432 69 0\n536 58 61 -4 8 9 10 5 33 -138 -161 0 252 535 278 76 263 286 290 525 0\n537 -58 102 0 369 366 342 368 367 344 109 289 242 0\n538 -51 28 27 1 8 29 0 70 72 73 74 242 221 0\n539 -3 51 -61 58 -4 10 5 33 0 151 40 239 246 525 0\n540 -62 34 30 59 27 -144 0 138 159 168 180 439 0\n541 103 134 -138 -161 0 420 419 473 468 464 463 471 461 456 466 370 371 368 369 362 363 367 365 366 360 339 344 343 342 341 534 537 536 124 126 127 131 132 227 538 539 236 241 223 224 263 275 277 282 187 430 50 52 540 433 60 62 103 434 0\n542 -49 31 28 -143 0 60 62 64 83 91 103 434 0\n543 -62 30 -61 -144 0 131 126 136 540 0\n544 -35 68 67 53 34 30 -61 -137 -161 0 131 126 473 468 464 471 459 12 154 160 425 211 220 439 427 95 0\n545 -43 67 53 34 30 -61 -137 -144 0 131 126 34 37 161 178 425 439 209 0\n546 -54 68 -139 0 98 214 427 0\n547 3 -61 29 -149 -161 0 132 127 126 124 449 444 447 473 468 464 463 471 461 457 456 466 459 223 224 542 543 433 186 187 188 199 206 430 50 57 82 86 424 78 432 169 174 544 545 546 434 106 215 427 0\n548 -61 134 -149 -161 0 421 420 419 130 151 257 547 40 238 239 246 262 264 525 0\n549 -4 51 -3 33 0 109 40 238 239 262 266 268 525 0\n550 4 134 0 421 420 249 534 0\n551 -3 134 0 550 420 238 239 549 264 0\n552 -57 49 -142 0 139 189 433 0\n553 -64 -51 -161 0 78 77 471 461 457 473 466 152 153 433 432 206 0\n554 -51 3 61 -138 -161 0 473 468 464 466 70 72 73 74 77 222 552 553 426 190 433 136 140 540 0\n555 -58 51 -136 -159 0 468 464 463 466 110 111 113 114 190 289 542 424 433 5 54 136 140 540 0\n556 -62 -144 0 133 134 136 140 540 0\n557 -49 28 -143 0 59 542 0\n558 -43 34 65 55 27 30 59 -161 0 473 468 464 471 459 37 173 178 427 439 216 0\n559 56 39 43 66 35 55 54 63 31 46 -113 28 131 -137 -143 0 434 87 207 425 269 346 378 379 389 412 405 406 400 394 397 350 356 321 324 299 0\n560 -56 34 65 55 27 30 59 -161 0 473 468 464 471 459 100 179 215 439 427 176 0\n561 34 66 65 35 27 63 31 30 -113 28 131 -137 -161 0 473 468 464 556 466 463 557 433 206 471 461 457 432 96 92 191 188 558 560 434 559 80 0\n562 134 -149 -161 0 417 449 445 444 447 473 468 464 556 463 471 461 457 456 466 459 541 548 550 338 357 551 358 359 377 415 554 555 252 1 347 382 385 557 552 433 426 186 187 188 199 206 147 148 149 150 153 424 222 432 57 92 96 430 120 158 162 561 11 79 84 425 208 220 434 427 173 0\n563 -34 -70 -134 0 185 184 9 17 418 0\n564 -29 71 -140 0 49 119 430 0\n565 -47 28 -149 -161 0 562 473 468 464 556 466 463 557 433 184 185 471 461 456 199 564 418 13 187 186 449 445 447 57 229 424 243 547 554 0\n566 28 31 -149 -161 0 479 417 477 454 562 442 423 449 445 444 473 468 464 556 463 471 461 456 466 557 552 433 184 185 187 190 199 563 564 418 13 18 565 430 132 158 162 426 153 553 268 290 339 344 363 367 368 372 375 415 14 230 148 561 347 385 382 0\n567 -28 -134 0 1 2 4 15 127 254 418 0\n568 -149 -161 0 479 473 468 464 556 463 466 477 454 562 442 423 567 557 566 433 6 73 111 149 185 187 265 285 525 0\n569 -31 -70 0 190 187 185 6 27 73 149 265 285 525 0\n570 10 5 64 51 -70 0 190 187 185 286 263 525 0\n571 -52 66 -137 36 0 87 207 425 0\n572 -43 65 30 -161 0 526 568 450 440 473 468 464 556 466 463 567 557 433 184 185 471 461 456 199 564 418 14 563 206 191 457 37 178 558 439 96 169 432 0\n573 -54 -161 0 526 473 468 464 556 466 463 568 450 440 567 557 433 206 471 461 457 459 92 546 432 174 0\n574 138 30 51 -161 0 526 531 528 573 473 468 464 556 466 463 568 450 440 567 557 433 569 184 185 471 461 456 199 564 418 19 18 14 563 191 188 187 186 445 443 446 424 57 430 158 162 571 572 434 106 560 0\n575 -56 -137 53 30 -161 0 526 568 450 440 473 468 464 556 466 463 567 557 433 184 185 471 461 456 199 564 418 19 14 563 191 106 208 560 425 163 0\n576 30 64 51 -161 0 526 528 573 473 468 464 556 466 463 568 450 440 567 557 433 569 184 185 471 461 456 199 564 418 18 563 190 188 187 186 552 574 426 132 430 57 82 86 424 446 444 575 434 545 572 170 0\n577 64 51 -161 0 526 473 468 464 556 466 463 568 450 440 567 557 433 187 576 5 261 570 0\n578 68 67 -52 65 -41 51 -161 0 528 526 473 468 464 556 466 463 568 450 440 567 557 433 187 186 184 185 471 461 456 199 564 418 19 82 430 162 571 444 446 424 577 148 572 206 457 153 432 96 190 151 255 290 14 563 191 459 427 260 218 329 439 518 0\n579 67 65 56 -41 51 -161 0 528 526 473 468 464 556 466 463 568 450 440 567 557 433 187 186 184 185 471 461 456 199 564 418 19 188 18 573 569 577 148 572 434 82 430 162 571 444 446 424 207 206 457 153 432 190 151 255 290 14 563 191 578 183 323 327 439 522 0\n580 -67 55 -139 0 176 216 427 0\n581 -65 51 -161 0 526 528 568 450 440 473 468 464 556 466 463 567 557 433 184 185 471 461 456 199 564 418 19 187 186 158 163 209 430 57 86 424 425 446 444 0\n582 51 -161 0 526 573 473 468 464 556 466 463 568 450 440 567 557 433 569 184 185 471 461 456 199 564 418 18 14 563 206 191 188 441 457 459 577 148 150 153 432 67 96 580 581 572 560 579 434 80 422 172 213 427 0\n583 -52 -161 0 526 531 582 553 568 450 440 473 468 464 556 466 463 567 557 433 184 185 471 461 456 199 564 418 19 190 552 82 430 132 162 426 571 443 0\n584 55 56 -161 0 531 526 473 466 468 463 568 450 440 567 557 552 464 556 433 190 582 553 188 184 185 471 461 456 199 564 418 18 573 569 583 434 161 72 572 209 19 158 430 86 425 443 426 206 457 78 432 143 36 441 74 155 422 37 174 288 13 14 538 459 281 427 291 489 0\n585 56 -161 0 526 531 583 473 468 464 556 466 463 568 450 440 567 557 433 206 471 461 457 582 78 432 169 143 190 553 288 456 199 564 184 185 418 13 14 538 74 72 573 569 19 18 188 552 441 434 36 161 178 572 155 158 209 422 430 86 425 443 426 584 298 300 523 0\n586 -161 0 526 471 473 459 461 466 468 457 463 464 556 568 450 440 567 557 433 206 582 78 432 174 585 106 215 427 0\n587 151 0 586 478 475 0\n588 145 0 587 451 0\n589 149 0 587 453 0\n590 134 0 588 440 0\n591 135 0 588 441 0\n592 136 0 589 447 0\n593 147 0 589 449 0\n594 -28 0 590 567 0\n595 137 0 593 444 0\n596 138 0 593 445 0\n597 -65 32 26 29 -56 0 595 590 591 208 104 99 155 163 425 19 25 418 422 28 0\n598 -41 -127 -113 -102 50 26 29 -56 0 590 417 106 105 101 100 28 29 259 418 247 345 340 380 361 389 362 412 372 415 375 0\n599 -37 41 -127 -113 -102 3 50 -56 0 417 387 410 416 376 373 101 19 237 339 363 364 372 361 375 340 415 258 412 297 389 345 380 0\n600 -51 -61 -47 -56 0 594 417 590 151 130 129 125 124 194 49 48 215 105 103 102 70 72 74 78 538 243 288 342 349 366 383 369 384 370 387 374 414 411 597 334 354 395 402 405 598 599 418 185 310 352 390 392 408 407 404 403 413 396 398 388 353 355 386 313 332 381 234 348 0\n601 -61 -47 -56 0 592 590 595 527 57 51 49 215 208 106 104 103 125 600 424 43 187 418 19 425 175 427 459 470 466 468 433 464 556 0\n602 -45 -47 -56 0 590 596 595 527 601 49 215 208 106 104 103 41 43 108 114 187 418 426 19 152 425 433 175 466 427 470 459 0\n603 139 50 61 49 0 529 527 596 458 459 457 470 466 468 552 464 556 433 190 206 426 432 153 0\n604 -47 -56 0 592 595 590 591 530 215 208 179 106 104 103 100 99 48 49 50 51 57 601 602 424 71 72 74 78 597 603 580 427 172 175 425 19 418 28 185 422 115 137 439 433 464 465 0\n605 -139 -51 -56 0 595 590 591 530 74 72 71 215 208 179 106 104 103 100 99 580 427 172 175 425 10 11 19 597 418 28 185 226 422 115 137 439 433 464 465 0\n606 -51 -56 0 529 527 604 103 78 605 458 459 603 456 470 132 466 468 430 464 199 556 433 0\n607 -70 -56 0 592 590 595 529 606 604 215 208 106 104 184 185 186 187 199 424 55 418 19 425 162 175 430 427 456 458 0\n608 -159 -56 0 607 103 466 468 433 464 556 0\n609 26 -56 0 527 595 590 594 591 530 208 104 106 215 608 470 459 427 175 425 19 11 10 172 580 607 179 103 100 99 418 7 8 28 225 226 223 597 422 115 137 439 433 464 465 0\n610 -56 0 592 606 609 38 41 53 424 0\n611 -26 0 592 38 41 53 71 424 0\n612 -38 -144 30 27 42 34 0 115 155 164 177 439 0\n613 -39 52 46 54 31 -143 0 610 594 24 35 434 0\n614 144 -33 0 533 530 594 527 596 592 591 185 112 107 43 39 28 8 464 462 468 465 557 470 433 459 461 135 137 146 152 204 456 457 426 432 132 78 92 96 424 56 57 430 195 613 422 172 213 427 0\n615 -159 -33 0 594 614 556 185 466 468 433 463 557 0\n616 -40 -139 0 94 172 213 427 0\n617 -39 -33 0 530 614 556 185 23 45 61 80 89 433 613 465 463 0\n618 -33 0 527 591 8 28 614 615 470 459 616 617 422 20 21 22 31 612 0\n619 37 0 590 611 618 418 3 55 128 249 250 256 253 524 0\n620 -1 0 619 13 0\n621 -27 0 619 14 0\n622 -29 0 619 16 0\n623 -34 0 619 17 0\n624 -35 0 619 18 0\n625 -36 0 619 19 0\n626 -38 30 -144 0 623 621 31 612 0\n627 -45 71 74 -6 70 143 0 417 527 530 533 596 610 438 462 556 463 465 433 69 468 470 461 457 201 432 322 355 398 400 340 361 362 371 374 414 174 153 145 437 436 114 287 426 349 310 383 352 384 390 387 392 411 408 409 401 403 393 399 395 391 356 354 351 326 335 270 0\n628 -60 53 42 67 30 -144 0 623 621 595 625 123 158 162 439 425 211 0\n629 71 60 74 -6 70 143 0 527 530 533 592 462 556 463 465 433 77 63 468 470 461 456 627 430 424 57 0\n630 74 -6 42 70 143 0 527 530 533 623 621 595 625 462 556 463 465 433 69 468 470 461 457 201 432 174 169 58 459 427 97 628 629 196 198 212 439 425 182 0\n631 -71 69 42 67 30 -144 0 623 621 196 198 439 0\n632 -59 71 64 57 51 44 -140 0 596 592 123 131 430 426 57 114 424 0\n633 42 70 143 40 0 527 530 533 619 623 621 595 625 462 556 463 465 433 69 468 470 461 457 201 432 169 153 145 77 63 58 456 435 247 630 218 220 631 632 439 158 163 430 425 86 0\n634 71 -42 -41 -49 143 0 527 625 595 592 619 596 85 69 463 468 470 461 457 201 432 174 459 95 427 220 425 162 438 295 156 116 153 145 77 63 456 437 330 336 430 57 424 114 287 511 426 0\n635 48 -71 -74 -12 -42 -41 -63 -49 0 625 595 623 621 592 596 619 85 293 220 425 153 145 77 63 277 424 114 287 426 487 0\n636 -61 -71 -74 -12 -42 -41 -63 -49 0 625 595 623 619 240 635 241 85 293 220 425 244 504 0\n637 70 143 40 0 533 530 527 591 595 625 623 596 594 619 463 468 470 461 457 459 465 462 556 438 433 58 61 69 201 432 142 145 153 174 626 422 240 633 85 95 116 295 427 220 425 162 634 293 635 241 636 426 305 506 0\n638 -74 -42 143 40 0 527 595 625 594 620 592 611 591 596 619 156 95 85 31 30 637 206 199 190 189 187 186 463 468 470 461 457 456 438 437 220 336 425 162 430 57 229 424 70 74 78 281 432 143 153 235 422 426 488 0\n639 -42 143 40 0 527 595 625 591 592 623 621 611 620 619 596 637 206 199 190 189 187 186 463 468 470 461 457 456 459 438 437 31 85 95 165 638 427 333 171 174 175 432 425 66 78 422 424 263 57 274 430 132 230 516 426 0\n640 -50 74 42 71 59 45 44 -140 -139 -144 0 592 623 621 65 78 96 424 580 427 57 183 430 439 158 0\n641 -73 30 67 42 59 -144 0 623 621 209 211 439 0\n642 74 143 40 0 533 527 591 595 625 623 621 639 637 206 199 191 187 186 463 468 470 461 457 456 459 462 640 432 142 143 169 174 427 93 97 422 26 641 425 163 182 439 0\n643 -47 73 69 67 42 59 45 44 -144 0 592 595 625 623 621 57 86 424 425 72 163 439 0\n644 143 40 0 533 527 596 623 621 462 463 468 470 461 456 637 186 187 189 190 191 199 639 642 216 218 220 643 430 132 158 426 439 148 0\n645 -30 0 618 5 26 42 72 148 261 286 289 525 0\n646 -144 59 65 67 42 -143 0 623 621 645 595 625 529 527 610 624 594 557 556 439 641 178 182 183 218 571 425 86 97 427 458 459 456 470 466 433 188 199 569 434 430 92 132 603 0\n647 -60 -70 74 73 157 -143 0 530 527 596 595 625 610 624 594 569 206 190 188 468 470 461 457 459 557 465 552 132 162 426 571 425 153 97 432 427 92 173 434 0\n648 -70 74 71 73 157 -143 0 527 595 625 610 624 594 468 470 461 456 459 188 569 647 430 82 86 425 161 175 434 546 0\n649 74 71 73 157 -143 0 530 527 595 625 610 624 594 592 596 468 470 461 457 456 459 557 465 552 648 433 135 146 152 204 432 68 78 92 96 427 173 175 571 425 434 86 56 430 424 132 114 426 0\n650 -60 -50 -62 70 -74 71 73 57 59 65 40 0 596 595 625 592 610 624 594 591 619 78 68 66 152 137 135 217 214 644 132 162 426 571 425 114 289 336 424 56 276 613 434 422 311 510 0\n651 70 -74 71 73 -141 -140 -142 59 65 40 0 610 624 594 595 625 219 214 644 557 552 433 135 146 432 650 430 52 82 86 434 425 161 0\n652 -47 31 46 54 73 -143 0 610 624 594 595 625 82 86 434 425 161 0\n653 71 73 157 59 65 40 0 530 527 621 620 596 595 625 610 624 594 611 591 592 619 468 470 461 457 456 644 557 465 552 649 214 219 651 186 187 188 190 569 652 430 132 162 230 426 571 425 147 150 153 331 613 434 432 324 67 78 231 422 424 515 0\n654 61 -74 -53 -19 -18 -41 -43 -50 -62 -71 57 0 596 594 592 619 78 68 152 197 426 304 114 289 424 512 0\n655 45 -61 -74 -53 -19 -18 -41 -43 -50 -62 -71 0 592 619 240 244 78 68 424 263 505 0\n656 73 157 59 65 67 40 0 530 527 610 624 591 595 625 594 622 620 619 468 470 461 457 459 644 557 465 552 653 193 194 195 197 199 433 135 137 146 204 432 66 92 96 613 434 422 161 173 316 319 240 425 427 654 244 655 228 485 0\n657 -62 74 71 52 -141 -140 -139 57 -143 0 610 624 594 592 596 135 146 152 204 432 68 78 92 96 427 173 434 52 56 430 424 132 114 426 0\n658 -50 31 46 74 52 -139 -143 0 610 624 594 92 96 434 427 173 0\n659 59 65 67 42 40 0 530 527 596 610 624 591 594 611 620 592 619 644 557 646 464 468 465 470 552 459 461 456 457 656 207 210 212 220 657 433 186 187 188 190 206 569 658 432 142 143 153 174 426 546 427 132 307 337 434 93 430 422 57 229 267 424 517 0\n660 -63 -43 54 -73 -59 40 0 624 594 527 591 596 619 220 140 644 557 191 433 466 470 459 173 427 35 123 318 196 461 456 430 57 51 131 118 115 142 153 313 322 422 426 632 486 280 0\n661 -59 -58 64 -41 -51 -47 -55 63 -43 70 -73 49 0 624 621 620 594 622 619 527 538 121 318 96 33 140 167 302 433 319 466 514 470 432 461 457 0\n662 -67 50 63 70 49 0 527 168 205 433 432 466 457 470 461 0\n663 64 -41 -51 -47 61 57 -59 -55 63 -43 70 -73 49 0 596 426 661 0\n664 -51 -47 61 57 -55 63 -43 70 -73 40 0 527 624 645 622 594 621 620 591 619 121 318 96 644 557 37 209 662 659 140 433 466 470 461 457 432 319 93 35 33 70 74 538 221 422 663 245 503 0\n665 -47 61 57 -55 63 -43 70 -73 40 0 594 527 591 624 645 592 619 93 35 96 644 557 37 209 662 659 140 433 466 470 461 457 432 200 422 319 212 51 57 121 431 318 664 272 424 632 279 507 0\n666 -55 63 -43 70 -73 40 0 594 527 37 212 209 644 557 96 662 659 140 433 466 470 461 123 456 430 131 665 118 0\n667 -159 70 49 0 466 468 433 464 556 0\n668 -43 54 70 -73 40 0 594 527 644 557 667 470 459 220 209 37 173 427 666 169 660 659 0\n669 59 -55 -144 67 40 0 645 595 625 97 95 659 641 163 425 0\n670 -55 -63 70 40 0 527 530 645 610 624 594 644 557 146 433 465 464 667 470 459 174 546 169 141 461 456 95 97 628 669 117 196 430 82 652 434 668 0\n671 -59 73 54 31 -140 -143 0 117 123 196 652 430 0\n672 -60 73 59 67 40 0 595 625 158 162 659 425 85 0\n673 -51 -66 -52 -42 -12 -74 -41 -70 47 -63 0 596 622 594 620 621 619 190 153 267 145 426 188 538 273 482 0\n674 -42 -12 -74 -41 -70 47 54 73 -63 -143 0 596 610 624 594 595 625 645 592 619 190 153 267 145 426 188 187 186 144 141 37 85 434 425 673 283 424 263 492 0\n675 51 -12 -41 -65 -70 -74 -43 -53 -63 0 596 645 592 619 190 153 267 145 426 187 186 144 283 424 263 495 0\n676 -70 -74 46 54 -53 42 47 -63 40 0 624 610 596 591 622 594 620 621 619 141 644 87 434 169 153 145 144 143 142 190 191 426 659 155 422 296 267 675 538 273 483 0\n677 70 69 54 42 47 73 -63 40 0 594 527 530 645 169 146 141 644 557 667 433 470 465 461 464 456 631 671 430 672 0\n678 46 54 -53 42 47 73 -63 40 0 610 624 594 529 97 87 174 169 141 644 434 178 677 191 199 676 672 427 430 458 456 0\n679 54 -53 42 47 73 -63 40 0 169 678 117 188 659 677 181 0\n680 139 47 50 49 0 529 527 458 459 603 456 470 132 667 430 199 0\n681 42 47 73 -63 40 0 594 595 625 174 644 557 144 680 546 169 679 425 163 182 659 677 191 0\n682 47 73 -63 40 0 591 527 610 624 594 174 169 144 143 142 141 644 557 680 546 681 31 37 95 116 295 422 427 672 674 667 470 461 456 430 193 195 434 0\n683 73 -63 40 0 595 625 591 610 527 594 611 620 592 619 174 169 144 143 142 141 644 557 682 51 52 57 82 86 194 652 425 88 214 546 163 317 422 326 459 603 240 470 131 244 667 659 187 229 424 490 0\n684 40 -54 -63 0 620 611 594 527 592 591 645 624 619 153 91 144 174 546 603 130 680 57 51 459 470 667 187 424 288 229 468 464 132 131 90 88 169 143 142 683 422 328 641 318 520 0\n685 -54 -63 0 527 645 595 625 174 169 144 91 438 546 459 603 680 470 131 86 468 464 684 32 646 641 163 425 0\n686 -40 -47 -63 0 610 624 594 527 82 52 685 141 36 616 434 459 463 470 468 0\n687 -47 -63 0 610 624 594 685 169 141 52 82 686 644 683 434 209 37 660 659 0\n688 40 -63 0 594 687 174 169 144 644 683 557 209 220 680 427 95 670 659 191 0\n689 -63 0 527 594 144 687 688 616 459 680 470 557 468 463 0\n690 -40 47 0 529 527 610 624 594 625 595 36 616 458 459 456 470 468 463 557 680 667 92 188 199 569 430 434 162 571 0\n691 73 -67 -41 -43 -64 -15 -60 -70 -50 74 0 592 595 625 619 78 187 290 162 571 158 68 424 425 331 325 521 0\n692 139 47 0 529 527 592 621 611 620 596 625 595 610 624 594 591 623 619 690 644 557 428 429 458 459 680 456 470 66 67 68 78 92 466 667 555 552 187 188 191 199 569 424 430 132 158 162 230 426 571 290 434 613 37 422 659 691 294 301 519 0\n693 61 -74 -65 -41 -19 -43 -70 -50 0 592 625 595 594 596 619 161 209 425 78 187 263 68 424 190 189 308 426 255 497 0\n694 -43 -70 -50 47 0 592 591 595 625 689 619 78 68 187 424 569 192 191 188 692 96 580 67 66 690 644 35 37 81 161 319 422 659 658 240 263 209 425 693 303 244 493 0\n695 -61 -74 -19 -42 -41 -52 -70 -50 0 592 595 625 689 619 78 187 263 240 571 68 424 569 192 303 244 496 0\n696 -70 -50 -139 40 0 592 610 624 625 595 591 689 594 596 619 96 580 92 78 68 67 66 644 187 188 189 190 191 569 424 57 694 434 80 157 571 422 659 175 320 263 427 695 309 426 255 500 0\n697 31 46 43 -140 67 54 40 0 610 624 594 644 434 82 195 207 430 671 672 0\n698 -31 -50 0 618 78 6 27 111 149 233 232 265 525 0\n699 -46 -50 -139 40 0 594 527 591 592 621 611 620 596 623 619 644 557 696 667 470 461 456 96 580 202 92 78 68 67 66 45 52 56 117 193 422 424 430 108 114 132 158 230 672 426 659 220 337 294 314 427 509 0\n700 -50 -139 40 0 594 527 644 557 92 96 580 696 667 470 461 456 698 699 697 37 668 652 671 672 659 430 198 0\n701 -65 -140 -43 -143 0 90 46 33 158 198 209 430 652 0\n702 -140 67 -43 40 0 90 37 33 644 701 659 191 671 668 0\n703 140 50 49 0 532 689 527 455 456 432 461 206 470 667 0\n704 51 -41 -11 -60 -70 -67 -43 50 0 689 529 625 595 620 611 621 596 645 592 619 190 189 132 426 230 161 205 432 457 458 580 97 425 187 186 283 424 290 501 0\n705 47 -43 50 40 0 689 529 625 595 623 611 596 591 622 594 620 621 619 161 644 557 703 702 205 432 457 458 580 97 425 662 199 190 189 164 81 46 35 430 292 132 230 426 150 422 704 538 273 481 0\n706 -64 -41 -18 -47 -55 -70 -67 -43 0 625 595 620 611 592 594 619 187 186 57 424 229 243 121 161 97 425 167 245 306 491 0\n707 -43 50 40 0 529 595 625 594 611 620 592 591 689 596 619 644 557 703 33 35 161 701 702 164 205 662 432 186 187 189 190 457 458 580 97 425 705 57 121 229 424 248 74 422 706 315 426 267 499 0\n708 -67 43 50 -143 0 689 610 624 594 625 595 557 703 166 662 188 199 569 434 82 571 430 162 0\n709 -51 -41 -42 -73 -60 47 -68 -54 -70 0 611 596 623 622 594 620 621 619 294 190 189 132 426 230 188 538 273 480 0\n710 47 -70 50 40 0 689 529 594 621 611 620 596 623 591 645 592 619 188 644 707 708 557 703 569 697 98 214 206 432 457 458 427 89 88 199 191 190 189 187 186 430 132 158 230 672 426 659 294 150 422 709 283 424 290 498 0\n711 -64 -41 -42 -47 -68 -54 -70 0 624 625 595 620 611 592 594 619 187 186 57 424 229 243 175 86 425 121 318 191 245 306 494 0\n712 -70 50 40 0 689 529 527 594 611 620 592 595 625 624 645 591 596 619 644 707 708 557 703 186 187 188 189 190 191 192 206 569 432 697 457 88 89 98 214 461 458 470 427 468 175 464 710 57 86 121 229 424 425 318 74 641 422 711 312 426 267 502 0\n713 -31 50 40 0 527 689 594 530 645 591 712 644 557 667 470 461 457 432 204 433 465 464 626 200 23 27 422 0\n714 51 -42 -68 -73 -12 -60 -41 -46 -72 50 0 623 645 592 596 619 52 294 132 122 56 47 271 424 114 279 426 513 0\n715 -64 -51 -42 -68 -73 -12 -60 -41 -46 -72 0 623 621 620 594 622 619 538 52 294 240 245 484 0\n716 50 40 0 527 689 530 645 591 623 622 594 620 621 596 619 644 557 703 707 708 712 667 470 459 461 457 432 200 203 204 219 433 465 464 626 713 697 45 52 117 193 422 430 669 259 122 132 158 672 427 659 294 714 538 715 312 426 508 0\n717 40 0 594 527 592 644 557 716 68 78 700 459 692 470 57 667 424 187 0\n718 -139 0 717 616 0\n719 47 0 717 690 0\n720 153 0 718 529 458 0\n721 -155 0 718 459 0\n722 -44 0 719 51 0\n723 -48 0 719 57 0\n724 141 0 720 457 0\n725 159 0 721 527 470 0\n726 157 0 725 468 0\n727 143 0 726 463 0\n728 -49 0 727 594 557 0\n729 70 0 728 725 667 0\n730 -45 0 729 187 0\n731 -72 0 729 206 0\n732 51 0 730 592 722 723 424 0\n733 50 0 731 724 689 432 0\n734 0 732 733 78 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record009.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record009.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record009.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record009.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record009 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeafTable : ConcreteGrowth.Table (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record009.l) :=
(.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (⟨0, by decide⟩))
 (.leaf (⟨1, by decide⟩)))
 (.branch 3
 (.leaf (⟨2, by decide⟩))
 (.branch 4
 (.leaf (⟨3, by decide⟩))
 (.leaf (⟨4, by decide⟩)))))
 (.branch 8
 (.branch 6
 (.leaf (⟨5, by decide⟩))
 (.branch 7
 (.leaf (⟨6, by decide⟩))
 (.leaf (⟨7, by decide⟩))))
 (.branch 9
 (.leaf (⟨8, by decide⟩))
 (.branch 10
 (.leaf (⟨9, by decide⟩))
 (.leaf (⟨10, by decide⟩))))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf (⟨0, by decide⟩))
 (.leaf (⟨0, by decide⟩)))
 (.branch 14
 (.leaf (⟨0, by decide⟩))
 (.branch 15
 (.leaf (⟨1, by decide⟩))
 (.leaf (⟨1, by decide⟩)))))
 (.branch 19
 (.branch 17
 (.leaf (⟨1, by decide⟩))
 (.branch 18
 (.leaf (⟨2, by decide⟩))
 (.leaf (⟨2, by decide⟩))))
 (.branch 20
 (.leaf (⟨2, by decide⟩))
 (.branch 21
 (.leaf (⟨3, by decide⟩))
 (.leaf (⟨3, by decide⟩)))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf (⟨3, by decide⟩))
 (.leaf (⟨4, by decide⟩)))
 (.branch 25
 (.leaf (⟨4, by decide⟩))
 (.branch 26
 (.leaf (⟨4, by decide⟩))
 (.leaf (⟨5, by decide⟩)))))
 (.branch 30
 (.branch 28
 (.leaf (⟨5, by decide⟩))
 (.branch 29
 (.leaf (⟨5, by decide⟩))
 (.leaf (⟨6, by decide⟩))))
 (.branch 31
 (.leaf (⟨6, by decide⟩))
 (.branch 32
 (.leaf (⟨6, by decide⟩))
 (.leaf (⟨7, by decide⟩))))))
 (.branch 38
 (.branch 35
 (.branch 34
 (.leaf (⟨7, by decide⟩))
 (.leaf (⟨7, by decide⟩)))
 (.branch 36
 (.leaf (⟨8, by decide⟩))
 (.branch 37
 (.leaf (⟨8, by decide⟩))
 (.leaf (⟨8, by decide⟩)))))
 (.branch 41
 (.branch 39
 (.leaf (⟨9, by decide⟩))
 (.branch 40
 (.leaf (⟨9, by decide⟩))
 (.leaf (⟨9, by decide⟩))))
 (.branch 42
 (.leaf (⟨10, by decide⟩))
 (.branch 43
 (.leaf (⟨10, by decide⟩))
 (.leaf (⟨10, by decide⟩))))))))
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record009.l := originalLeafTable.get j.val
def orbitWordTable : ConcreteGrowth.Table (List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record009.g)) :=
(.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([]))
 (.leaf ([])))
 (.branch 3
 (.leaf ([]))
 (.branch 4
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 8
 (.branch 6
 (.leaf ([]))
 (.branch 7
 (.leaf ([]))
 (.leaf ([]))))
 (.branch 9
 (.leaf ([]))
 (.branch 10
 (.leaf ([]))
 (.leaf ([]))))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨2, by decide⟩])))
 (.branch 14
 (.leaf ([⟨3, by decide⟩]))
 (.branch 15
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨2, by decide⟩])))))
 (.branch 19
 (.branch 17
 (.leaf ([⟨3, by decide⟩]))
 (.branch 18
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨2, by decide⟩]))))
 (.branch 20
 (.leaf ([⟨3, by decide⟩]))
 (.branch 21
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨2, by decide⟩])))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf ([⟨3, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 25
 (.leaf ([⟨2, by decide⟩]))
 (.branch 26
 (.leaf ([⟨3, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))
 (.branch 30
 (.branch 28
 (.leaf ([⟨2, by decide⟩]))
 (.branch 29
 (.leaf ([⟨3, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))
 (.branch 31
 (.leaf ([⟨2, by decide⟩]))
 (.branch 32
 (.leaf ([⟨3, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))))
 (.branch 38
 (.branch 35
 (.branch 34
 (.leaf ([⟨2, by decide⟩]))
 (.leaf ([⟨3, by decide⟩])))
 (.branch 36
 (.leaf ([⟨1, by decide⟩]))
 (.branch 37
 (.leaf ([⟨2, by decide⟩]))
 (.leaf ([⟨3, by decide⟩])))))
 (.branch 41
 (.branch 39
 (.leaf ([⟨1, by decide⟩]))
 (.branch 40
 (.leaf ([⟨2, by decide⟩]))
 (.leaf ([⟨3, by decide⟩]))))
 (.branch 42
 (.leaf ([⟨1, by decide⟩]))
 (.branch 43
 (.leaf ([⟨2, by decide⟩]))
 (.leaf ([⟨3, by decide⟩]))))))))
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record009.g) := orbitWordTable.get j.val
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record009.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record009.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record009 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record009_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record009 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record009_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record009_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00022.record009

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00022.record023
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2364da4e33a2e1ba1e0f9d16c5c971565c5595556359354d3362d4b46d8743d70e9364cd38cd332ce8b92e2b2ac6b86c9b0ee4751cc789d2719d1725c5723c1f4d0ca858368384e0b9c1645313254549615454358344d0b4c384c930ce0b22c4b0ae0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "92492492492492492492492492492492492492249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record023 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record023 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record023.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 40), (facetIndex 57), (facetIndex 63), (facetIndex 71), (facetIndex 72)]))
 (.leaf ([(facetIndex 67), (facetIndex 68), (facetIndex 73), (facetIndex 74)])))
 (.branch 3
 (.leaf ([(facetIndex 33), (facetIndex 77), (facetIndex 78), (facetIndex 79), (facetIndex 80)]))
 (.branch 4
 (.leaf ([(facetIndex 36), (facetIndex 38), (facetIndex 52), (facetIndex 58), (facetIndex 66), (facetIndex 81)]))
 (.leaf ([(facetIndex 32), (facetIndex 43), (facetIndex 44), (facetIndex 45), (facetIndex 46), (facetIndex 47), (facetIndex 48), (facetIndex 49), (facetIndex 50)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 69), (facetIndex 70)]))
 (.branch 7
 (.leaf ([(facetIndex 42), (facetIndex 59), (facetIndex 65)]))
 (.leaf ([(facetIndex 35), (facetIndex 51), (facetIndex 53), (facetIndex 54), (facetIndex 55), (facetIndex 56)]))))
 (.branch 9
 (.leaf ([(facetIndex 39), (facetIndex 75), (facetIndex 76), (facetIndex 82)]))
 (.branch 10
 (.leaf ([(facetIndex 60), (facetIndex 61), (facetIndex 62), (facetIndex 64)]))
 (.leaf ([(facetIndex 34), (facetIndex 37), (facetIndex 41)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "83222288110055113690999630777737444444446a083a37a24z20;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 11
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2, 3, 4]
def grouped2_0006 : List Nat := [5]
def grouped2_0007 : List Nat := [5, 6, 7]
def grouped2_0008 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped2_0009 : List Nat := [6]
def grouped2_0010 : List Nat := [6, 7]
def grouped2_0011 : List Nat := [7]
def grouped2_0012 : List Nat := [8]
def grouped2_0013 : List Nat := [8, 9, 10]
def grouped2_0014 : List Nat := [9]
def grouped2_0015 : List Nat := [9, 10]
def grouped2_0016 : List Nat := [10]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record023 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record023_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00022.record023" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group\",\"kind\":2,\"index\":10},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":6,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":10,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00022.record023" 34

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00022.record023" "{\"ridges\":[[10,146],[35,146],[41,324],[44,146],[51,146],[54,146],[55,146],[56,146],[64,324],[67,324],[68,145],[70,324],[73,145],[74,145]],\"owners\":[[68,145,[10,44,51,54,56],[23,35,73,74]],[73,145,[10,35,44,54,56],[23,51,68,74]],[74,145,[10,35,44,51,56],[23,54,68,73]],[10,146,[],[35,44,51,54,55,56]],[35,146,[],[10,44,51,54,55,56]],[44,146,[],[10,35,51,54,55,56]],[51,146,[],[10,35,44,54,55,56]],[54,146,[],[10,35,44,51,55,56]],[55,146,[],[10,35,44,51,54,56]],[56,146,[],[10,35,44,51,54,55]],[41,324,[],[20,64,67,70,71]],[64,324,[],[20,41,67,70,71]],[67,324,[],[20,41,64,70,71]],[70,324,[],[20,41,64,67,71]]],\"edges\":[],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00022.record023" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00022.record023\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-12,-4],[-13,-4],[-14,-8],[-18,-2],[-17,1,6,7,9,11],[-20,1,3,6,9,11],[-21,1,3,6,7,11],[-1],[-3],[-6],[-7],[-9],[-10],[-11],[-5],[-15],[-16],[-19],[-22,16,17,20,21],[-23,18,19],[-24,3,7,8,9,10,11],[-25,12,13,14,15],[-26,2,4,5],[-27,22],[-28,27],[-29,24],[-30,23],[-30,29],[-31,25],[-31,26],[-32,31],[-33,30],[-33,32],[-34,28,33],[34]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group\",\"index\":10,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":60,\"b\":37},{\"tag\":\"incompatible\",\"a\":61,\"b\":37},{\"tag\":\"incompatible\",\"a\":62,\"b\":53},{\"tag\":\"incompatible\",\"a\":69,\"b\":34},{\"tag\":\"mate\",\"ridge\":145,\"a\":68,\"owners\":[10,44,51,54,56]},{\"tag\":\"mate\",\"ridge\":145,\"a\":73,\"owners\":[10,35,44,54,56]},{\"tag\":\"mate\",\"ridge\":145,\"a\":74,\"owners\":[10,35,44,51,56]},{\"tag\":\"mate\",\"ridge\":146,\"a\":10,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":146,\"a\":35,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":146,\"a\":44,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":146,\"a\":51,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":146,\"a\":54,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":146,\"a\":55,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":146,\"a\":56,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":324,\"a\":41,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":324,\"a\":64,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":324,\"a\":67,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":324,\"a\":70,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[67,68,73,74],\"full_literals\":[-22,16,17,20,21]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[69,70],\"full_literals\":[-23,18,19]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[35,51,53,54,55,56],\"full_literals\":[-24,3,7,8,9,10,11]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[60,61,62,64],\"full_literals\":[-25,12,13,14,15]},{\"tag\":\"group_or\",\"kind\":2,\"index\":10,\"members\":[34,37,41],\"full_literals\":[-26,2,4,5]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-27,false,22],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-28,27,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-29,false,24],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-30,23,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-30,false,29],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-31,25,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-31,false,26],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-32,false,31],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-33,30,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0008\",\"a\":3,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-33,false,32],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-34,28,33],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":10,\"grouped\":true}]}"
  "36 -21 0 14 8 9 10 11 7 0\n37 -20 0 14 8 9 10 12 6 0\n38 -17 0 14 8 10 11 12 5 0\n39 -22 0 17 38 37 36 19 0\n40 -23 18 0 18 20 0\n41 -24 8 0 9 11 12 13 14 21 0\n42 -25 12 13 14 0 16 22 0\n43 -26 2 4 0 15 23 0\n44 -27 0 39 24 0\n45 -28 0 44 25 0\n46 -34 33 0 45 34 0\n47 33 0 35 46 0\n48 30 0 47 32 0\n49 32 0 47 33 0\n50 23 0 48 27 0\n51 29 0 48 28 0\n52 31 0 49 31 0\n53 18 0 50 40 0\n54 24 0 51 26 0\n55 25 0 52 29 0\n56 26 0 52 30 0\n57 -2 0 53 4 0\n58 8 0 54 41 0\n59 4 0 57 56 43 0\n60 -14 0 58 3 0\n61 -12 0 59 1 0\n62 -13 0 59 2 0\n63 0 61 62 55 60 42 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record023.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record023.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record023.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record023.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record023 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record023.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record023.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record023.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record023.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record023 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record023_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record023_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record023_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record023_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record023_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record023_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record023_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record023 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record023_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record023_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record023_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00022.record023

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00022.record024
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1d26c9ca8d936938ce8b86e8783e745b1726354d64d3362d1b61d0f5a358f13a4d5334e332ce8b62e4b52e2b4acab1ae1b26c3b91d4731e2749c6745c9715c8f07dc26493232a160da0e1382e705914c4c9854358344d0b58350cc348e1344c930ce0b22c4b0ae0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "92492492492492492492492492492492492492449249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record024 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record024 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record024.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record024.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record024.data.quota

def groupMembers1 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 17
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
 (.branch 16
 (.leaf ([(facetIndex 15)]))
 (.leaf ([(facetIndex 16)])))))))
 (.branch 26
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf ([(facetIndex 17)]))
 (.leaf ([(facetIndex 18)])))
 (.branch 20
 (.leaf ([(facetIndex 19)]))
 (.leaf ([(facetIndex 20)]))))
 (.branch 23
 (.branch 22
 (.leaf ([(facetIndex 21)]))
 (.leaf ([(facetIndex 22)])))
 (.branch 24
 (.leaf ([(facetIndex 23)]))
 (.branch 25
 (.leaf ([(facetIndex 24)]))
 (.leaf ([(facetIndex 25)]))))))
 (.branch 30
 (.branch 28
 (.branch 27
 (.leaf ([(facetIndex 26)]))
 (.leaf ([(facetIndex 27)])))
 (.branch 29
 (.leaf ([(facetIndex 28)]))
 (.leaf ([(facetIndex 29)]))))
 (.branch 32
 (.branch 31
 (.leaf ([(facetIndex 30)]))
 (.leaf ([(facetIndex 31)])))
 (.branch 33
 (.leaf ([(facetIndex 32)]))
 (.branch 34
 (.leaf ([(facetIndex 33)]))
 (.leaf ([(facetIndex 34)]))))))))
def groupColors1 : PackedGraphCertificate.Fields :=
  ⟨6, sparse_nat% "228607de75c6da6585d65544d24503ce34c2ca2481c61440c2040"⟩
def grouping1 : FacetSat.Grouping data.count where
  count := 35
  members := fun g => groupMembers1.get g
  color := fun c => groupColors1.get c.val
def groupKind1 : List Nat := List.range grouping1.count

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 51), (facetIndex 53), (facetIndex 55), (facetIndex 73), (facetIndex 84)]))
 (.branch 2
 (.leaf ([(facetIndex 37), (facetIndex 59), (facetIndex 60), (facetIndex 75), (facetIndex 86)]))
 (.leaf ([(facetIndex 50), (facetIndex 57), (facetIndex 64), (facetIndex 74), (facetIndex 85)]))))
 (.branch 4
 (.leaf ([(facetIndex 35), (facetIndex 36), (facetIndex 45), (facetIndex 54), (facetIndex 70), (facetIndex 81)]))
 (.branch 5
 (.leaf ([(facetIndex 39), (facetIndex 41), (facetIndex 44), (facetIndex 71), (facetIndex 82)]))
 (.leaf ([(facetIndex 78), (facetIndex 79), (facetIndex 80)])))))
 (.branch 9
 (.branch 7
 (.leaf ([(facetIndex 42), (facetIndex 52), (facetIndex 58), (facetIndex 68), (facetIndex 72), (facetIndex 83)]))
 (.branch 8
 (.leaf ([(facetIndex 46), (facetIndex 47), (facetIndex 48), (facetIndex 56), (facetIndex 61)]))
 (.leaf ([(facetIndex 65), (facetIndex 66), (facetIndex 76), (facetIndex 77)]))))
 (.branch 10
 (.leaf ([(facetIndex 62), (facetIndex 63)]))
 (.branch 11
 (.leaf ([(facetIndex 40), (facetIndex 49), (facetIndex 67)]))
 (.leaf ([(facetIndex 38), (facetIndex 43), (facetIndex 69)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "12064355588120643b6a88299711627030602a77734b64a4b133z23;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 12
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped1_0000 : List Nat := [0]
def grouped1_0001 : List Nat := [0, 1]
def grouped1_0002 : List Nat := [0, 1, 2, 3]
def grouped1_0003 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]
def grouped1_0004 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
def grouped1_0006 : List Nat := [1]
def grouped1_0007 : List Nat := [2, 3]
def grouped1_0008 : List Nat := [4, 5]
def grouped1_0009 : List Nat := [4, 5, 6, 7]
def grouped1_0010 : List Nat := [6]
def grouped1_0011 : List Nat := [6, 7]
def grouped1_0012 : List Nat := [7]
def grouped1_0013 : List Nat := [8, 9, 10, 11, 12, 13, 14, 15, 16]
def grouped1_0014 : List Nat := [17, 18, 19, 20]
def grouped1_0015 : List Nat := [17, 18, 19, 20, 21, 22, 23, 24, 25]
def grouped1_0016 : List Nat := [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]
def grouped1_0017 : List Nat := [21]
def grouped1_0018 : List Nat := [21, 22]
def grouped1_0019 : List Nat := [21, 22, 23, 24, 25]
def grouped1_0020 : List Nat := [22]
def grouped1_0021 : List Nat := [23, 24, 25]
def grouped1_0022 : List Nat := [26]
def grouped1_0023 : List Nat := [26, 27]
def grouped1_0024 : List Nat := [26, 27, 28, 29]
def grouped1_0025 : List Nat := [26, 27, 28, 29, 30, 31, 32, 33, 34]
def grouped1_0026 : List Nat := [27]
def grouped1_0027 : List Nat := [28]
def grouped1_0028 : List Nat := [28, 29]
def grouped1_0029 : List Nat := [29]
def grouped1_0030 : List Nat := [30]
def grouped1_0031 : List Nat := [30, 31]
def grouped1_0032 : List Nat := [30, 31, 32, 33, 34]
def grouped1_0033 : List Nat := [31]
def grouped1_0034 : List Nat := [32]
def grouped1_0035 : List Nat := [32, 33, 34]
def grouped1_0036 : List Nat := [33]
def grouped1_0037 : List Nat := [33, 34]
def grouped1_0038 : List Nat := [34]
def grouped2_0039 : List Nat := [0]
def grouped2_0040 : List Nat := [0, 1, 2]
def grouped2_0041 : List Nat := [0, 1, 2, 3, 4, 5]
def grouped2_0043 : List Nat := [1]
def grouped2_0044 : List Nat := [1, 2]
def grouped2_0045 : List Nat := [2]
def grouped2_0046 : List Nat := [3]
def grouped2_0047 : List Nat := [3, 4, 5]
def grouped2_0048 : List Nat := [4]
def grouped2_0049 : List Nat := [4, 5]
def grouped2_0050 : List Nat := [5]
def grouped2_0051 : List Nat := [6]
def grouped2_0052 : List Nat := [6, 7, 8]
def grouped2_0053 : List Nat := [6, 7, 8, 9, 10, 11]
def grouped2_0054 : List Nat := [7]
def grouped2_0055 : List Nat := [7, 8]
def grouped2_0056 : List Nat := [8]
def grouped2_0057 : List Nat := [9]
def grouped2_0058 : List Nat := [9, 10, 11]
def grouped2_0059 : List Nat := [10]
def grouped2_0060 : List Nat := [10, 11]
def grouped2_0061 : List Nat := [11]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record024 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record024_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00022.record024" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"kind\":1,\"index\":0},{\"tag\":\"group\",\"kind\":1,\"index\":7},{\"tag\":\"group\",\"kind\":1,\"index\":21},{\"tag\":\"group\",\"kind\":1,\"index\":22},{\"tag\":\"group\",\"kind\":1,\"index\":27},{\"tag\":\"group\",\"kind\":1,\"index\":28},{\"tag\":\"group\",\"kind\":1,\"index\":29},{\"tag\":\"group\",\"kind\":1,\"index\":30},{\"tag\":\"group\",\"kind\":1,\"index\":34},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0002\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0011\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0009\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0004\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0004\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0018\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0019\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0015\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0028\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0024\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0031\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0037\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0035\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0032\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0032\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0025\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0025\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0016\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":4,\"list_name\":\"grouped1_0016\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":5,\"list_name\":\"groupKind1\"},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group\",\"kind\":2,\"index\":10},{\"tag\":\"group\",\"kind\":2,\"index\":11},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0044\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0040\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0049\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0047\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0047\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0041\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":6,\"list_name\":\"grouped2_0041\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0055\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0052\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0060\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0060\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0058\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0058\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0058\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0053\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0053\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":6,\"list_name\":\"grouped2_0053\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":10,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00022.record024" 139

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00022.record024" "{\"ridges\":[[3,67],[3,69],[3,70],[5,41],[5,42],[7,131],[7,137],[8,515],[8,521],[8,522],[10,19],[12,19],[17,13],[17,41],[17,44],[18,13],[18,76],[19,13],[19,517],[19,521],[19,524],[20,21],[21,517],[21,529],[22,137],[24,145],[26,14],[26,38],[26,42],[26,44],[27,14],[27,70],[27,76],[28,14],[28,518],[28,522],[28,524],[29,22],[29,38],[30,518],[30,530],[31,138],[33,146],[37,19],[37,70],[40,38],[40,69],[40,70],[43,69],[43,70],[43,131],[44,69],[44,70],[45,69],[45,70],[45,517],[45,518],[48,19],[48,521],[48,522],[50,41],[50,42],[51,41],[51,42],[52,41],[52,42],[52,515],[52,521],[52,522],[54,67],[54,515],[54,521],[54,522],[56,515],[56,521],[56,522],[61,131],[61,529],[61,530],[63,67],[65,13],[65,21],[65,41],[65,44],[66,13],[66,524],[66,529],[67,44],[67,76],[68,44],[68,521],[68,524],[69,13],[69,76],[69,137],[70,76],[70,521],[70,524],[71,21],[72,517],[72,529],[73,137],[74,145],[75,145],[75,321],[75,448],[76,14],[76,22],[76,42],[76,44],[77,14],[77,22],[77,524],[77,530],[78,44],[79,522],[80,14],[80,70],[80,76],[80,138],[80,200],[81,76],[81,522],[81,524],[82,22],[82,38],[83,518],[83,530],[84,138],[85,50],[85,146],[86,146]],\"owners\":[[76,14,[0,27,28,36,80],[26,35,77]],[20,21,[1,21,35,37,38,39,66],[65,71]],[65,21,[1,21,37,38,39],[20,35,66,71]],[71,21,[1,21,35,37,38,66],[20,39,65]],[29,22,[1,30,35,37,38,39,77],[76,82]],[76,22,[1,30,37,38,39],[29,35,77,82]],[77,22,[1,29,37,38,39,82],[30,35,76]],[82,22,[1,30,35,37,38,77],[29,39,76]],[3,69,[18,67,69,70],[37,40,43,44,45]],[40,69,[18,69,70],[3,37,43,44,45,67]],[43,69,[18,67,70],[3,37,40,44,45,69]],[44,69,[18,67,69,70],[3,37,40,43,45]],[45,69,[18,67,69],[3,37,40,43,44,70]],[3,70,[27,78,80,81],[37,40,43,44,45]],[27,70,[3,37,40,43,44,45],[78,80,81]],[37,70,[27,78,80,81],[3,40,43,44,45]],[40,70,[27,80,81],[3,37,43,44,45,78]],[43,70,[27,78,81],[3,37,40,44,45,80]],[44,70,[27,78,80,81],[3,37,40,43,45]],[45,70,[27,78,80],[3,37,40,43,44,81]],[80,70,[3,37,40,44,45],[27,43,78,81]],[8,515,[4,12,42,45,58,61,62],[52,54,56]],[52,515,[4,12,45,61,62],[8,42,54,56,58]],[54,515,[4,12,42,58,61,62],[8,45,52,56]],[56,515,[4,12,42,45,58,62],[8,52,54,61]],[5,41,[17,65,67,68],[46,49,50,51,52]],[17,41,[5,46,49,50,51,52],[65,67,68]],[50,41,[17,65,67,68],[5,46,49,51,52]],[51,41,[17,65,67,68],[5,46,49,50,52]],[52,41,[17,65,67],[5,46,49,50,51,68]],[65,41,[5,49,50,51,52],[17,46,67,68]],[5,42,[26,76,78,79],[46,49,50,51,52]],[26,42,[5,46,49,50,51,52],[76,78,79]],[50,42,[26,76,78,79],[5,46,49,51,52]],[51,42,[26,76,78,79],[5,46,49,50,52]],[52,42,[26,76,78],[5,46,49,50,51,79]],[76,42,[5,49,50,51,52],[26,46,78,79]],[7,137,[22,69,73],[36,47,50,55,56]],[22,137,[7,36,47,50,55,56],[69,73]],[69,137,[7,47,50,55,56],[22,36,73]],[73,137,[7,36,47,50,56],[22,55,69]],[31,138,[7,36,47,50,55,56],[80,84]],[80,138,[7,47,50,55,56],[31,36,84]],[84,138,[7,36,47,50,56],[31,55,80]],[8,521,[19,66,68,70],[48,52,54,56]],[19,521,[8,48,52,54,56],[66,68,70]],[48,521,[19,68,70],[8,52,54,56,66]],[52,521,[19,66,70],[8,48,54,56,68]],[54,521,[19,66,68],[8,48,52,56,70]],[56,521,[19,66,68,70],[8,48,52,54]],[68,521,[8,48,54,56],[19,52,66,70]],[70,521,[8,48,52,56],[19,54,66,68]],[8,522,[28,77,79,81],[48,52,54,56]],[28,522,[8,48,52,54,56],[77,79,81]],[48,522,[28,79,81],[8,52,54,56,77]],[52,522,[28,77,81],[8,48,54,56,79]],[54,522,[28,77,79],[8,48,52,56,81]],[56,522,[28,77,79,81],[8,48,52,54]],[79,522,[8,48,54,56],[28,52,77,81]],[81,522,[8,48,52,56],[28,54,77,79]],[85,50,[9,29,46,58,76,83],[32,57]],[24,145,[10,38,47,57,59,61],[74,75]],[74,145,[10,38,47,59,61],[24,57,75]],[75,145,[10,38,47,57,61],[24,59,74]],[33,146,[10,38,47,57,59,61],[85,86]],[85,146,[10,38,47,59,61],[33,57,86]],[86,146,[10,38,47,57,61],[33,59,85]],[21,529,[12,48,58,61,62],[66,72]],[61,529,[21,66,72],[12,48,58,62]],[66,529,[12,58,61,62],[21,48,72]],[72,529,[12,48,61,62],[21,58,66]],[30,530,[12,48,58,61,62],[77,83]],[61,530,[30,77,83],[12,48,58,62]],[77,530,[12,58,61,62],[30,48,83]],[83,530,[12,48,61,62],[30,58,77]],[75,321,[15,44,53,63],[25,60,73]],[17,44,[26,76,78,79],[65,67,68]],[26,44,[17,65,67,68],[76,78,79]],[65,44,[26,78,79],[17,67,68,76]],[67,44,[26,76,79],[17,65,68,78]],[68,44,[26,76,78],[17,65,67,79]],[76,44,[17,67,68],[26,65,78,79]],[78,44,[17,65,68],[26,67,76,79]],[18,76,[27,78,80,81],[67,69,70]],[27,76,[18,67,69,70],[78,80,81]],[67,76,[27,80,81],[18,69,70,78]],[69,76,[27,78,81],[18,67,70,80]],[70,76,[27,78,80],[18,67,69,81]],[80,76,[18,67,70],[27,69,78,81]],[81,76,[18,67,69],[27,70,78,80]],[19,524,[28,77,79,81],[66,68,70]],[28,524,[19,66,68,70],[77,79,81]],[66,524,[28,79,81],[19,68,70,77]],[68,524,[28,77,81],[19,66,70,79]],[70,524,[28,77,79],[19,66,68,81]],[77,524,[19,68,70],[28,66,79,81]],[81,524,[19,66,68],[28,70,77,79]],[80,200,[22,73],[31,69,84]],[75,448,[34,84],[25,73,86]]],\"edges\":[[18,[1,20,21,29,30,35,37,38,39,65,66,71,72,76,77,82,83]],[20,[3,18,27,37,40,43,44,45,67,69,70,78,80,81]],[25,[5,17,26,46,49,50,51,52,65,67,68,76,78,79]],[27,[7,22,31,36,47,50,55,56,69,73,80,84]],[29,[8,19,28,48,52,54,56,66,68,70,77,79,81]],[32,[10,24,33,38,47,57,59,61,74,75,85,86]],[34,[12,21,30,48,58,61,62,66,72,77,83]]],\"groupings\":[1,2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00022.record024" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00022.record024\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-27,-3],[-28,-5],[-29,-4],[-30,-10],[-30,-29],[-32,-2],[-32,-30],[-32,-31],[-33,-29],[-34,-11],[-35,-34],[-36,-2],[-36,-27],[-36,-29],[-36,-30],[-36,-32],[-37,-32],[-38,-27],[-38,-28],[-38,-34],[-39,-30],[-39,-36],[-40,-6],[-40,-28],[-40,-38],[-41,-7],[-41,-28],[-41,-40],[-42,-28],[-42,-32],[-43,-6],[-43,-28],[-43,-41],[-44,-32],[-44,-34],[-45,-36],[-45,-38],[-45,-41],[-46,-9],[-47,-40],[-48,-10],[-48,-29],[-48,-39],[-49,-9],[-49,-29],[-49,-30],[-49,-48],[-50,-6],[-50,-28],[-50,-29],[-50,-41],[-50,-46],[-50,-47],[-52,-8],[-52,-9],[-52,-27],[-52,-29],[-52,-30],[-52,-37],[-52,-38],[-52,-39],[-52,-46],[-52,-47],[-52,-48],[-52,-49],[-52,-50],[-52,-51],[-53,-9],[-53,-29],[-53,-30],[-53,-38],[-53,-48],[-53,-50],[-53,-51],[-53,-52],[-54,-31],[-54,-32],[-54,-34],[-54,-35],[-54,-37],[-54,-40],[-54,-42],[-56,-32],[-56,-33],[-56,-38],[-57,-36],[-57,-38],[-57,-56],[-58,-14],[-58,-28],[-58,-54],[-58,-57],[-59,-13],[-59,-28],[-59,-57],[-59,-58],[-60,-28],[-60,-40],[-60,-45],[-60,-58],[-60,-59],[-61,-12],[-61,-56],[-61,-57],[-61,-58],[-61,-59],[-61,-60],[-63,-30],[-63,-43],[-63,-56],[-63,-59],[-64,-50],[-65,-53],[-66,-29],[-66,-55],[-66,-64],[-66,-65],[-67,-32],[-67,-33],[-67,-38],[-67,-57],[-68,-36],[-68,-38],[-68,-56],[-68,-67],[-69,-21],[-69,-28],[-69,-32],[-69,-67],[-69,-68],[-70,-20],[-70,-28],[-70,-33],[-70,-43],[-70,-59],[-70,-63],[-70,-68],[-70,-69],[-71,-30],[-71,-34],[-71,-40],[-71,-45],[-71,-60],[-71,-70],[-72,-19],[-72,-67],[-72,-68],[-72,-69],[-72,-70],[-74,-30],[-74,-67],[-74,-70],[-75,-50],[-75,-71],[-76,-53],[-77,-29],[-77,-46],[-12,-13,-57],[-12,-14,-60],[-12,-57,-60],[-14,-56,-60],[-67,1,20,21,28,71],[-19,-20,-21],[-19,-21,-71],[-19,-68,-71],[-20,-21,-67],[-21,-67,-71],[-9,-10,-29],[-9,-29,-39],[-15,2,16,27,29,30,31,57],[-56,2,16,29,30,31],[-62,2,16,27,29,30,57],[-22,2,23,27,29,30,31,68],[-67,2,23,29,30,31],[-68,2,22,29,30,31,73],[-73,2,23,27,29,30,68],[-19,-22,-32],[-19,-32,-73],[-3,-45,-54],[-3,13,58,60,61],[-32,13,60,61],[-34,13,58,61],[-35,13,58,60,61],[-36,13,58,60],[-3,20,69,71,72],[-20,3,29,32,34,35,36],[-29,20,69,71,72],[-32,20,71,72],[-34,20,69,72],[-35,20,69,71,72],[-36,20,69,71],[-71,3,29,32,35,36],[-7,4,10,33,36,49,52,53],[-43,4,10,36,52,53],[-45,4,10,33,49,52,53],[-47,4,10,33,36,49,53],[-14,-16,-36],[-14,-36,-63],[-21,-23,-36],[-21,-36,-74],[-5,12,56,58,59],[-12,5,37,40,41,42,43],[-41,12,56,58,59],[-42,12,56,58,59],[-43,12,56,58],[-56,5,40,41,42,43],[-5,19,67,69,70],[-19,5,37,40,41,42,43],[-41,19,67,69,70],[-42,19,67,69,70],[-43,19,67,69],[-67,5,40,41,42,43],[-6,-34,-52],[-6,17,60,64],[-17,6,28,38,41,46,47],[-60,6,38,41,46,47],[-64,6,28,38,41,47],[-24,6,28,38,41,46,47],[-71,6,38,41,46,47],[-75,6,28,38,41,47],[-7,14,57,59,61],[-14,7,39,43,45,47],[-39,14,59,61],[-43,14,57,61],[-45,14,57,59],[-47,14,57,59,61],[-59,7,39,45,47],[-61,7,39,43,47],[-7,21,68,70,72],[-21,7,39,43,45,47],[-39,21,70,72],[-43,21,68,72],[-45,21,68,70],[-47,21,68,70,72],[-70,7,39,45,47],[-72,7,39,43,47],[-76,8,22,37,49,67,74],[-18,9,30,38,48,50,52],[-65,9,30,38,50,52],[-66,9,30,38,48,52],[-25,9,30,38,48,50,52],[-76,9,30,38,50,52],[-77,9,30,38,48,52],[-16,10,39,49,52,53],[-52,16,57,63],[-57,10,49,52,53],[-63,10,39,52,53],[-23,10,39,49,52,53],[-52,23,68,74],[-68,10,49,52,53],[-74,10,39,52,53],[-66,11,35,44,54],[-12,19,67,69,70],[-19,12,56,58,59],[-56,19,69,70],[-58,19,67,70],[-59,19,67,69],[-67,12,58,59],[-69,12,56,59],[-13,20,69,71,72],[-20,13,58,60,61],[-58,20,71,72],[-60,20,69,72],[-61,20,69,71],[-71,13,58,61],[-72,13,58,60],[-14,21,68,70,72],[-21,14,57,59,61],[-57,21,70,72],[-59,21,68,72],[-61,21,68,70],[-68,14,59,61],[-72,14,57,59],[-71,17,64],[-66,26,75],[-1,78],[-6,79],[-16,80],[-17,81],[-20,82],[-21,83],[-22,84],[-23,85],[-26,86],[-78,87],[-87,88],[-79,89],[-89,90],[-90,91],[-88,-90,92],[-91,93],[-92,94],[-80,-81,95],[-95,96],[-96,97],[-82,98],[-84,99],[-83,99],[-99,100],[-98,100],[-85,101],[-86,102],[-102,103],[-101,104],[-101,-103,105],[-104,106],[-105,107],[-100,-104,107],[-97,-106,108],[-97,-107,109],[-93,-109,110],[-94,-108,110],[-110],[-111,42,44,46,64,75],[-112,29,50,51,66,77],[-50,112],[-66,112],[-77,112],[-113,41,48,55,65,76],[-114,27,28,36,45,61,72],[-115,69,70,71],[-116,33,43,49,59,63,74],[-117,37,38,39,47,52],[-118,56,57,67,68],[-119,53,54],[-120,32,40,58],[-121,30,34,60],[-122,112],[-122,113],[-123,111],[-123,122],[-124,115],[-125,114,124],[-126,114],[-126,124],[-128,123],[-127,125],[-128,126],[-129,117],[-129,118],[-130,116],[-130,129],[-131,120,121],[-132,120],[-132,121],[-133,119,131],[-134,119,132],[-135,119],[-134,131],[-135,132],[-136,130,134],[-137,130,135],[-136,133],[-137,134],[-138,135],[-139,127,138],[-139,128,137],[-139,136],[139],[2,15,16,22,23,27,29,30,31,56,57,62,63,67,68,73,74],[3,13,20,29,32,34,35,36,58,60,61,69,71,72],[5,12,19,37,40,41,42,43,56,58,59,67,69,70],[6,17,24,28,38,41,46,47,60,64,71,75],[7,14,21,39,43,45,47,57,59,61,68,70,72],[9,18,25,30,38,48,50,52,65,66,76,77],[10,16,23,39,49,52,53,57,63,68,74]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"index\":0,\"kind\":1},{\"tag\":\"group\",\"index\":7,\"kind\":1},{\"tag\":\"group\",\"index\":21,\"kind\":1},{\"tag\":\"group\",\"index\":22,\"kind\":1},{\"tag\":\"group\",\"index\":27,\"kind\":1},{\"tag\":\"group\",\"index\":28,\"kind\":1},{\"tag\":\"group\",\"index\":29,\"kind\":1},{\"tag\":\"group\",\"index\":30,\"kind\":1},{\"tag\":\"group\",\"index\":34,\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group\",\"index\":10,\"kind\":2},{\"tag\":\"group\",\"index\":11,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":35,\"b\":3},{\"tag\":\"incompatible\",\"a\":36,\"b\":5},{\"tag\":\"incompatible\",\"a\":37,\"b\":4},{\"tag\":\"incompatible\",\"a\":38,\"b\":12},{\"tag\":\"incompatible\",\"a\":38,\"b\":37},{\"tag\":\"incompatible\",\"a\":40,\"b\":1},{\"tag\":\"incompatible\",\"a\":40,\"b\":38},{\"tag\":\"incompatible\",\"a\":40,\"b\":39},{\"tag\":\"incompatible\",\"a\":42,\"b\":37},{\"tag\":\"incompatible\",\"a\":43,\"b\":15},{\"tag\":\"incompatible\",\"a\":44,\"b\":43},{\"tag\":\"incompatible\",\"a\":45,\"b\":1},{\"tag\":\"incompatible\",\"a\":45,\"b\":35},{\"tag\":\"incompatible\",\"a\":45,\"b\":37},{\"tag\":\"incompatible\",\"a\":45,\"b\":38},{\"tag\":\"incompatible\",\"a\":45,\"b\":40},{\"tag\":\"incompatible\",\"a\":46,\"b\":40},{\"tag\":\"incompatible\",\"a\":47,\"b\":35},{\"tag\":\"incompatible\",\"a\":47,\"b\":36},{\"tag\":\"incompatible\",\"a\":47,\"b\":43},{\"tag\":\"incompatible\",\"a\":48,\"b\":38},{\"tag\":\"incompatible\",\"a\":48,\"b\":45},{\"tag\":\"incompatible\",\"a\":49,\"b\":7},{\"tag\":\"incompatible\",\"a\":49,\"b\":36},{\"tag\":\"incompatible\",\"a\":49,\"b\":47},{\"tag\":\"incompatible\",\"a\":50,\"b\":8},{\"tag\":\"incompatible\",\"a\":50,\"b\":36},{\"tag\":\"incompatible\",\"a\":50,\"b\":49},{\"tag\":\"incompatible\",\"a\":51,\"b\":36},{\"tag\":\"incompatible\",\"a\":51,\"b\":40},{\"tag\":\"incompatible\",\"a\":52,\"b\":7},{\"tag\":\"incompatible\",\"a\":52,\"b\":36},{\"tag\":\"incompatible\",\"a\":52,\"b\":50},{\"tag\":\"incompatible\",\"a\":53,\"b\":40},{\"tag\":\"incompatible\",\"a\":53,\"b\":43},{\"tag\":\"incompatible\",\"a\":54,\"b\":45},{\"tag\":\"incompatible\",\"a\":54,\"b\":47},{\"tag\":\"incompatible\",\"a\":54,\"b\":50},{\"tag\":\"incompatible\",\"a\":55,\"b\":10},{\"tag\":\"incompatible\",\"a\":56,\"b\":49},{\"tag\":\"incompatible\",\"a\":57,\"b\":12},{\"tag\":\"incompatible\",\"a\":57,\"b\":37},{\"tag\":\"incompatible\",\"a\":57,\"b\":48},{\"tag\":\"incompatible\",\"a\":58,\"b\":10},{\"tag\":\"incompatible\",\"a\":58,\"b\":37},{\"tag\":\"incompatible\",\"a\":58,\"b\":38},{\"tag\":\"incompatible\",\"a\":58,\"b\":57},{\"tag\":\"incompatible\",\"a\":59,\"b\":7},{\"tag\":\"incompatible\",\"a\":59,\"b\":36},{\"tag\":\"incompatible\",\"a\":59,\"b\":37},{\"tag\":\"incompatible\",\"a\":59,\"b\":50},{\"tag\":\"incompatible\",\"a\":59,\"b\":55},{\"tag\":\"incompatible\",\"a\":59,\"b\":56},{\"tag\":\"incompatible\",\"a\":61,\"b\":9},{\"tag\":\"incompatible\",\"a\":61,\"b\":10},{\"tag\":\"incompatible\",\"a\":61,\"b\":35},{\"tag\":\"incompatible\",\"a\":61,\"b\":37},{\"tag\":\"incompatible\",\"a\":61,\"b\":38},{\"tag\":\"incompatible\",\"a\":61,\"b\":46},{\"tag\":\"incompatible\",\"a\":61,\"b\":47},{\"tag\":\"incompatible\",\"a\":61,\"b\":48},{\"tag\":\"incompatible\",\"a\":61,\"b\":55},{\"tag\":\"incompatible\",\"a\":61,\"b\":56},{\"tag\":\"incompatible\",\"a\":61,\"b\":57},{\"tag\":\"incompatible\",\"a\":61,\"b\":58},{\"tag\":\"incompatible\",\"a\":61,\"b\":59},{\"tag\":\"incompatible\",\"a\":61,\"b\":60},{\"tag\":\"incompatible\",\"a\":62,\"b\":10},{\"tag\":\"incompatible\",\"a\":62,\"b\":37},{\"tag\":\"incompatible\",\"a\":62,\"b\":38},{\"tag\":\"incompatible\",\"a\":62,\"b\":47},{\"tag\":\"incompatible\",\"a\":62,\"b\":57},{\"tag\":\"incompatible\",\"a\":62,\"b\":59},{\"tag\":\"incompatible\",\"a\":62,\"b\":60},{\"tag\":\"incompatible\",\"a\":62,\"b\":61},{\"tag\":\"incompatible\",\"a\":63,\"b\":39},{\"tag\":\"incompatible\",\"a\":63,\"b\":40},{\"tag\":\"incompatible\",\"a\":63,\"b\":43},{\"tag\":\"incompatible\",\"a\":63,\"b\":44},{\"tag\":\"incompatible\",\"a\":63,\"b\":46},{\"tag\":\"incompatible\",\"a\":63,\"b\":49},{\"tag\":\"incompatible\",\"a\":63,\"b\":51},{\"tag\":\"incompatible\",\"a\":65,\"b\":40},{\"tag\":\"incompatible\",\"a\":65,\"b\":42},{\"tag\":\"incompatible\",\"a\":65,\"b\":47},{\"tag\":\"incompatible\",\"a\":66,\"b\":45},{\"tag\":\"incompatible\",\"a\":66,\"b\":47},{\"tag\":\"incompatible\",\"a\":66,\"b\":65},{\"tag\":\"incompatible\",\"a\":67,\"b\":19},{\"tag\":\"incompatible\",\"a\":67,\"b\":36},{\"tag\":\"incompatible\",\"a\":67,\"b\":63},{\"tag\":\"incompatible\",\"a\":67,\"b\":66},{\"tag\":\"incompatible\",\"a\":68,\"b\":18},{\"tag\":\"incompatible\",\"a\":68,\"b\":36},{\"tag\":\"incompatible\",\"a\":68,\"b\":66},{\"tag\":\"incompatible\",\"a\":68,\"b\":67},{\"tag\":\"incompatible\",\"a\":69,\"b\":36},{\"tag\":\"incompatible\",\"a\":69,\"b\":49},{\"tag\":\"incompatible\",\"a\":69,\"b\":54},{\"tag\":\"incompatible\",\"a\":69,\"b\":67},{\"tag\":\"incompatible\",\"a\":69,\"b\":68},{\"tag\":\"incompatible\",\"a\":70,\"b\":17},{\"tag\":\"incompatible\",\"a\":70,\"b\":65},{\"tag\":\"incompatible\",\"a\":70,\"b\":66},{\"tag\":\"incompatible\",\"a\":70,\"b\":67},{\"tag\":\"incompatible\",\"a\":70,\"b\":68},{\"tag\":\"incompatible\",\"a\":70,\"b\":69},{\"tag\":\"incompatible\",\"a\":72,\"b\":38},{\"tag\":\"incompatible\",\"a\":72,\"b\":52},{\"tag\":\"incompatible\",\"a\":72,\"b\":65},{\"tag\":\"incompatible\",\"a\":72,\"b\":68},{\"tag\":\"incompatible\",\"a\":73,\"b\":59},{\"tag\":\"incompatible\",\"a\":74,\"b\":62},{\"tag\":\"incompatible\",\"a\":75,\"b\":37},{\"tag\":\"incompatible\",\"a\":75,\"b\":64},{\"tag\":\"incompatible\",\"a\":75,\"b\":73},{\"tag\":\"incompatible\",\"a\":75,\"b\":74},{\"tag\":\"incompatible\",\"a\":76,\"b\":40},{\"tag\":\"incompatible\",\"a\":76,\"b\":42},{\"tag\":\"incompatible\",\"a\":76,\"b\":47},{\"tag\":\"incompatible\",\"a\":76,\"b\":66},{\"tag\":\"incompatible\",\"a\":77,\"b\":45},{\"tag\":\"incompatible\",\"a\":77,\"b\":47},{\"tag\":\"incompatible\",\"a\":77,\"b\":65},{\"tag\":\"incompatible\",\"a\":77,\"b\":76},{\"tag\":\"incompatible\",\"a\":78,\"b\":28},{\"tag\":\"incompatible\",\"a\":78,\"b\":36},{\"tag\":\"incompatible\",\"a\":78,\"b\":40},{\"tag\":\"incompatible\",\"a\":78,\"b\":76},{\"tag\":\"incompatible\",\"a\":78,\"b\":77},{\"tag\":\"incompatible\",\"a\":79,\"b\":27},{\"tag\":\"incompatible\",\"a\":79,\"b\":36},{\"tag\":\"incompatible\",\"a\":79,\"b\":42},{\"tag\":\"incompatible\",\"a\":79,\"b\":52},{\"tag\":\"incompatible\",\"a\":79,\"b\":68},{\"tag\":\"incompatible\",\"a\":79,\"b\":72},{\"tag\":\"incompatible\",\"a\":79,\"b\":77},{\"tag\":\"incompatible\",\"a\":79,\"b\":78},{\"tag\":\"incompatible\",\"a\":80,\"b\":38},{\"tag\":\"incompatible\",\"a\":80,\"b\":43},{\"tag\":\"incompatible\",\"a\":80,\"b\":49},{\"tag\":\"incompatible\",\"a\":80,\"b\":54},{\"tag\":\"incompatible\",\"a\":80,\"b\":69},{\"tag\":\"incompatible\",\"a\":80,\"b\":79},{\"tag\":\"incompatible\",\"a\":81,\"b\":26},{\"tag\":\"incompatible\",\"a\":81,\"b\":76},{\"tag\":\"incompatible\",\"a\":81,\"b\":77},{\"tag\":\"incompatible\",\"a\":81,\"b\":78},{\"tag\":\"incompatible\",\"a\":81,\"b\":79},{\"tag\":\"incompatible\",\"a\":83,\"b\":38},{\"tag\":\"incompatible\",\"a\":83,\"b\":76},{\"tag\":\"incompatible\",\"a\":83,\"b\":79},{\"tag\":\"incompatible\",\"a\":84,\"b\":59},{\"tag\":\"incompatible\",\"a\":84,\"b\":80},{\"tag\":\"incompatible\",\"a\":85,\"b\":62},{\"tag\":\"incompatible\",\"a\":86,\"b\":37},{\"tag\":\"incompatible\",\"a\":86,\"b\":55},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[17,18,66]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[17,19,69]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[17,66,69]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[19,65,69]},{\"tag\":\"mate\",\"ridge\":14,\"a\":76,\"owners\":[0,27,28,36,80]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[26,27,28]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[26,28,80]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[26,77,80]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[27,28,76]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[28,76,80]},{\"tag\":\"three\",\"ridge\":19,\"vertices\":[10,12,37]},{\"tag\":\"three\",\"ridge\":19,\"vertices\":[10,37,48]},{\"tag\":\"mate\",\"ridge\":21,\"a\":20,\"owners\":[1,21,35,37,38,39,66]},{\"tag\":\"mate\",\"ridge\":21,\"a\":65,\"owners\":[1,21,37,38,39]},{\"tag\":\"mate\",\"ridge\":21,\"a\":71,\"owners\":[1,21,35,37,38,66]},{\"tag\":\"mate\",\"ridge\":22,\"a\":29,\"owners\":[1,30,35,37,38,39,77]},{\"tag\":\"mate\",\"ridge\":22,\"a\":76,\"owners\":[1,30,37,38,39]},{\"tag\":\"mate\",\"ridge\":22,\"a\":77,\"owners\":[1,29,37,38,39,82]},{\"tag\":\"mate\",\"ridge\":22,\"a\":82,\"owners\":[1,30,35,37,38,77]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[26,29,40]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[26,40,82]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[3,54,63]},{\"tag\":\"mate\",\"ridge\":69,\"a\":3,\"owners\":[18,67,69,70]},{\"tag\":\"mate\",\"ridge\":69,\"a\":40,\"owners\":[18,69,70]},{\"tag\":\"mate\",\"ridge\":69,\"a\":43,\"owners\":[18,67,70]},{\"tag\":\"mate\",\"ridge\":69,\"a\":44,\"owners\":[18,67,69,70]},{\"tag\":\"mate\",\"ridge\":69,\"a\":45,\"owners\":[18,67,69]},{\"tag\":\"mate\",\"ridge\":70,\"a\":3,\"owners\":[27,78,80,81]},{\"tag\":\"mate\",\"ridge\":70,\"a\":27,\"owners\":[3,37,40,43,44,45]},{\"tag\":\"mate\",\"ridge\":70,\"a\":37,\"owners\":[27,78,80,81]},{\"tag\":\"mate\",\"ridge\":70,\"a\":40,\"owners\":[27,80,81]},{\"tag\":\"mate\",\"ridge\":70,\"a\":43,\"owners\":[27,78,81]},{\"tag\":\"mate\",\"ridge\":70,\"a\":44,\"owners\":[27,78,80,81]},{\"tag\":\"mate\",\"ridge\":70,\"a\":45,\"owners\":[27,78,80]},{\"tag\":\"mate\",\"ridge\":70,\"a\":80,\"owners\":[3,37,40,44,45]},{\"tag\":\"mate\",\"ridge\":515,\"a\":8,\"owners\":[4,12,42,45,58,61,62]},{\"tag\":\"mate\",\"ridge\":515,\"a\":52,\"owners\":[4,12,45,61,62]},{\"tag\":\"mate\",\"ridge\":515,\"a\":54,\"owners\":[4,12,42,58,61,62]},{\"tag\":\"mate\",\"ridge\":515,\"a\":56,\"owners\":[4,12,42,45,58,62]},{\"tag\":\"three\",\"ridge\":517,\"vertices\":[19,21,45]},{\"tag\":\"three\",\"ridge\":517,\"vertices\":[19,45,72]},{\"tag\":\"three\",\"ridge\":518,\"vertices\":[28,30,45]},{\"tag\":\"three\",\"ridge\":518,\"vertices\":[28,45,83]},{\"tag\":\"mate\",\"ridge\":41,\"a\":5,\"owners\":[17,65,67,68]},{\"tag\":\"mate\",\"ridge\":41,\"a\":17,\"owners\":[5,46,49,50,51,52]},{\"tag\":\"mate\",\"ridge\":41,\"a\":50,\"owners\":[17,65,67,68]},{\"tag\":\"mate\",\"ridge\":41,\"a\":51,\"owners\":[17,65,67,68]},{\"tag\":\"mate\",\"ridge\":41,\"a\":52,\"owners\":[17,65,67]},{\"tag\":\"mate\",\"ridge\":41,\"a\":65,\"owners\":[5,49,50,51,52]},{\"tag\":\"mate\",\"ridge\":42,\"a\":5,\"owners\":[26,76,78,79]},{\"tag\":\"mate\",\"ridge\":42,\"a\":26,\"owners\":[5,46,49,50,51,52]},{\"tag\":\"mate\",\"ridge\":42,\"a\":50,\"owners\":[26,76,78,79]},{\"tag\":\"mate\",\"ridge\":42,\"a\":51,\"owners\":[26,76,78,79]},{\"tag\":\"mate\",\"ridge\":42,\"a\":52,\"owners\":[26,76,78]},{\"tag\":\"mate\",\"ridge\":42,\"a\":76,\"owners\":[5,49,50,51,52]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[7,43,61]},{\"tag\":\"mate\",\"ridge\":137,\"a\":7,\"owners\":[22,69,73]},{\"tag\":\"mate\",\"ridge\":137,\"a\":22,\"owners\":[7,36,47,50,55,56]},{\"tag\":\"mate\",\"ridge\":137,\"a\":69,\"owners\":[7,47,50,55,56]},{\"tag\":\"mate\",\"ridge\":137,\"a\":73,\"owners\":[7,36,47,50,56]},{\"tag\":\"mate\",\"ridge\":138,\"a\":31,\"owners\":[7,36,47,50,55,56]},{\"tag\":\"mate\",\"ridge\":138,\"a\":80,\"owners\":[7,47,50,55,56]},{\"tag\":\"mate\",\"ridge\":138,\"a\":84,\"owners\":[7,36,47,50,56]},{\"tag\":\"mate\",\"ridge\":521,\"a\":8,\"owners\":[19,66,68,70]},{\"tag\":\"mate\",\"ridge\":521,\"a\":19,\"owners\":[8,48,52,54,56]},{\"tag\":\"mate\",\"ridge\":521,\"a\":48,\"owners\":[19,68,70]},{\"tag\":\"mate\",\"ridge\":521,\"a\":52,\"owners\":[19,66,70]},{\"tag\":\"mate\",\"ridge\":521,\"a\":54,\"owners\":[19,66,68]},{\"tag\":\"mate\",\"ridge\":521,\"a\":56,\"owners\":[19,66,68,70]},{\"tag\":\"mate\",\"ridge\":521,\"a\":68,\"owners\":[8,48,54,56]},{\"tag\":\"mate\",\"ridge\":521,\"a\":70,\"owners\":[8,48,52,56]},{\"tag\":\"mate\",\"ridge\":522,\"a\":8,\"owners\":[28,77,79,81]},{\"tag\":\"mate\",\"ridge\":522,\"a\":28,\"owners\":[8,48,52,54,56]},{\"tag\":\"mate\",\"ridge\":522,\"a\":48,\"owners\":[28,79,81]},{\"tag\":\"mate\",\"ridge\":522,\"a\":52,\"owners\":[28,77,81]},{\"tag\":\"mate\",\"ridge\":522,\"a\":54,\"owners\":[28,77,79]},{\"tag\":\"mate\",\"ridge\":522,\"a\":56,\"owners\":[28,77,79,81]},{\"tag\":\"mate\",\"ridge\":522,\"a\":79,\"owners\":[8,48,54,56]},{\"tag\":\"mate\",\"ridge\":522,\"a\":81,\"owners\":[8,48,52,56]},{\"tag\":\"mate\",\"ridge\":50,\"a\":85,\"owners\":[9,29,46,58,76,83]},{\"tag\":\"mate\",\"ridge\":145,\"a\":24,\"owners\":[10,38,47,57,59,61]},{\"tag\":\"mate\",\"ridge\":145,\"a\":74,\"owners\":[10,38,47,59,61]},{\"tag\":\"mate\",\"ridge\":145,\"a\":75,\"owners\":[10,38,47,57,61]},{\"tag\":\"mate\",\"ridge\":146,\"a\":33,\"owners\":[10,38,47,57,59,61]},{\"tag\":\"mate\",\"ridge\":146,\"a\":85,\"owners\":[10,38,47,59,61]},{\"tag\":\"mate\",\"ridge\":146,\"a\":86,\"owners\":[10,38,47,57,61]},{\"tag\":\"mate\",\"ridge\":529,\"a\":21,\"owners\":[12,48,58,61,62]},{\"tag\":\"mate\",\"ridge\":529,\"a\":61,\"owners\":[21,66,72]},{\"tag\":\"mate\",\"ridge\":529,\"a\":66,\"owners\":[12,58,61,62]},{\"tag\":\"mate\",\"ridge\":529,\"a\":72,\"owners\":[12,48,61,62]},{\"tag\":\"mate\",\"ridge\":530,\"a\":30,\"owners\":[12,48,58,61,62]},{\"tag\":\"mate\",\"ridge\":530,\"a\":61,\"owners\":[30,77,83]},{\"tag\":\"mate\",\"ridge\":530,\"a\":77,\"owners\":[12,58,61,62]},{\"tag\":\"mate\",\"ridge\":530,\"a\":83,\"owners\":[12,48,61,62]},{\"tag\":\"mate\",\"ridge\":321,\"a\":75,\"owners\":[15,44,53,63]},{\"tag\":\"mate\",\"ridge\":44,\"a\":17,\"owners\":[26,76,78,79]},{\"tag\":\"mate\",\"ridge\":44,\"a\":26,\"owners\":[17,65,67,68]},{\"tag\":\"mate\",\"ridge\":44,\"a\":65,\"owners\":[26,78,79]},{\"tag\":\"mate\",\"ridge\":44,\"a\":67,\"owners\":[26,76,79]},{\"tag\":\"mate\",\"ridge\":44,\"a\":68,\"owners\":[26,76,78]},{\"tag\":\"mate\",\"ridge\":44,\"a\":76,\"owners\":[17,67,68]},{\"tag\":\"mate\",\"ridge\":44,\"a\":78,\"owners\":[17,65,68]},{\"tag\":\"mate\",\"ridge\":76,\"a\":18,\"owners\":[27,78,80,81]},{\"tag\":\"mate\",\"ridge\":76,\"a\":27,\"owners\":[18,67,69,70]},{\"tag\":\"mate\",\"ridge\":76,\"a\":67,\"owners\":[27,80,81]},{\"tag\":\"mate\",\"ridge\":76,\"a\":69,\"owners\":[27,78,81]},{\"tag\":\"mate\",\"ridge\":76,\"a\":70,\"owners\":[27,78,80]},{\"tag\":\"mate\",\"ridge\":76,\"a\":80,\"owners\":[18,67,70]},{\"tag\":\"mate\",\"ridge\":76,\"a\":81,\"owners\":[18,67,69]},{\"tag\":\"mate\",\"ridge\":524,\"a\":19,\"owners\":[28,77,79,81]},{\"tag\":\"mate\",\"ridge\":524,\"a\":28,\"owners\":[19,66,68,70]},{\"tag\":\"mate\",\"ridge\":524,\"a\":66,\"owners\":[28,79,81]},{\"tag\":\"mate\",\"ridge\":524,\"a\":68,\"owners\":[28,77,81]},{\"tag\":\"mate\",\"ridge\":524,\"a\":70,\"owners\":[28,77,79]},{\"tag\":\"mate\",\"ridge\":524,\"a\":77,\"owners\":[19,68,70]},{\"tag\":\"mate\",\"ridge\":524,\"a\":81,\"owners\":[19,66,68]},{\"tag\":\"mate\",\"ridge\":200,\"a\":80,\"owners\":[22,73]},{\"tag\":\"mate\",\"ridge\":448,\"a\":75,\"owners\":[34,84]},{\"tag\":\"group_take\",\"kind\":1,\"index\":0,\"member\":0,\"full_literals\":[-1,78]},{\"tag\":\"group_take\",\"kind\":1,\"index\":7,\"member\":7,\"full_literals\":[-6,79]},{\"tag\":\"group_take\",\"kind\":1,\"index\":21,\"member\":21,\"full_literals\":[-16,80]},{\"tag\":\"group_take\",\"kind\":1,\"index\":22,\"member\":22,\"full_literals\":[-17,81]},{\"tag\":\"group_take\",\"kind\":1,\"index\":27,\"member\":27,\"full_literals\":[-20,82]},{\"tag\":\"group_take\",\"kind\":1,\"index\":28,\"member\":28,\"full_literals\":[-21,83]},{\"tag\":\"group_take\",\"kind\":1,\"index\":29,\"member\":29,\"full_literals\":[-22,84]},{\"tag\":\"group_take\",\"kind\":1,\"index\":30,\"member\":30,\"full_literals\":[-23,85]},{\"tag\":\"group_take\",\"kind\":1,\"index\":34,\"member\":34,\"full_literals\":[-26,86]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0006\",\"joined_name\":\"grouped1_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-78,false,87],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-87,false,88],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped1_0010\",\"right_name\":\"grouped1_0012\",\"joined_name\":\"grouped1_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-79,89],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped1_0008\",\"right_name\":\"grouped1_0011\",\"joined_name\":\"grouped1_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-89,90],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0009\",\"joined_name\":\"grouped1_0003\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-90,91],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0009\",\"joined_name\":\"grouped1_0003\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-88,-90,92],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7],\"right\":[8,9,10,11,12,13,14,15,16],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-91,false,93],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7],\"right\":[8,9,10,11,12,13,14,15,16],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0004\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-92,false,94],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[21],\"right\":[22],\"left_name\":\"grouped1_0017\",\"right_name\":\"grouped1_0020\",\"joined_name\":\"grouped1_0018\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-80,-81,95],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[21,22],\"right\":[23,24,25],\"left_name\":\"grouped1_0018\",\"right_name\":\"grouped1_0021\",\"joined_name\":\"grouped1_0019\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-95,false,96],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17,18,19,20],\"right\":[21,22,23,24,25],\"left_name\":\"grouped1_0014\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0015\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-96,97],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[26],\"right\":[27],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0023\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-82,98],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[28],\"right\":[29],\"left_name\":\"grouped1_0027\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0028\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-84,99],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[28],\"right\":[29],\"left_name\":\"grouped1_0027\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-83,false,99],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[26,27],\"right\":[28,29],\"left_name\":\"grouped1_0023\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-99,100],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[26,27],\"right\":[28,29],\"left_name\":\"grouped1_0023\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-98,false,100],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[30],\"right\":[31],\"left_name\":\"grouped1_0030\",\"right_name\":\"grouped1_0033\",\"joined_name\":\"grouped1_0031\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-85,false,101],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[33],\"right\":[34],\"left_name\":\"grouped1_0036\",\"right_name\":\"grouped1_0038\",\"joined_name\":\"grouped1_0037\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-86,102],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[32],\"right\":[33,34],\"left_name\":\"grouped1_0034\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0035\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-102,103],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[30,31],\"right\":[32,33,34],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0032\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-101,false,104],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[30,31],\"right\":[32,33,34],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0032\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-101,-103,105],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[26,27,28,29],\"right\":[30,31,32,33,34],\"left_name\":\"grouped1_0024\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0025\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-104,106],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[26,27,28,29],\"right\":[30,31,32,33,34],\"left_name\":\"grouped1_0024\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0025\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-105,107],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[26,27,28,29],\"right\":[30,31,32,33,34],\"left_name\":\"grouped1_0024\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0025\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-100,-104,107],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17,18,19,20,21,22,23,24,25],\"right\":[26,27,28,29,30,31,32,33,34],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0025\",\"joined_name\":\"grouped1_0016\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-97,-106,108],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17,18,19,20,21,22,23,24,25],\"right\":[26,27,28,29,30,31,32,33,34],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0025\",\"joined_name\":\"grouped1_0016\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-97,-107,109],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],\"right\":[17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34],\"left_name\":\"grouped1_0004\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"groupKind1\",\"a\":1,\"b\":4,\"direction\":\"forward\",\"full_literals\":[-93,-109,110],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],\"right\":[17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34],\"left_name\":\"grouped1_0004\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"groupKind1\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-94,-108,110],\"grouped\":true,\"kind\":1},{\"tag\":\"quota_upper\",\"kind\":1,\"quota\":4,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[51,53,55,73,84],\"full_literals\":[-111,42,44,46,64,75]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[37,59,60,75,86],\"full_literals\":[-112,29,50,51,66,77]},{\"tag\":\"group_take\",\"kind\":2,\"index\":1,\"member\":59,\"full_literals\":[-50,112]},{\"tag\":\"group_take\",\"kind\":2,\"index\":1,\"member\":75,\"full_literals\":[-66,112]},{\"tag\":\"group_take\",\"kind\":2,\"index\":1,\"member\":86,\"full_literals\":[-77,112]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[50,57,64,74,85],\"full_literals\":[-113,41,48,55,65,76]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[35,36,45,54,70,81],\"full_literals\":[-114,27,28,36,45,61,72]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[78,79,80],\"full_literals\":[-115,69,70,71]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[42,52,58,68,72,83],\"full_literals\":[-116,33,43,49,59,63,74]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[46,47,48,56,61],\"full_literals\":[-117,37,38,39,47,52]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[65,66,76,77],\"full_literals\":[-118,56,57,67,68]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[62,63],\"full_literals\":[-119,53,54]},{\"tag\":\"group_or\",\"kind\":2,\"index\":10,\"members\":[40,49,67],\"full_literals\":[-120,32,40,58]},{\"tag\":\"group_or\",\"kind\":2,\"index\":11,\"members\":[38,43,69],\"full_literals\":[-121,30,34,60]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped2_0043\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0044\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-122,112,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped2_0043\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0044\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-122,false,113],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0039\",\"right_name\":\"grouped2_0044\",\"joined_name\":\"grouped2_0040\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-123,111,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0039\",\"right_name\":\"grouped2_0044\",\"joined_name\":\"grouped2_0040\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-123,false,122],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0048\",\"right_name\":\"grouped2_0050\",\"joined_name\":\"grouped2_0049\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-124,false,115],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0047\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-125,114,124],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0047\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-126,114,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0047\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-126,false,124],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0041\",\"a\":2,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-128,123,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0041\",\"a\":3,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-127,false,125],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0041\",\"a\":3,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-128,false,126],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0054\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0055\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-129,117,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0054\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0055\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-129,false,118],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0055\",\"joined_name\":\"grouped2_0052\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-130,116,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0055\",\"joined_name\":\"grouped2_0052\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-130,false,129],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped2_0059\",\"right_name\":\"grouped2_0061\",\"joined_name\":\"grouped2_0060\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-131,120,121],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped2_0059\",\"right_name\":\"grouped2_0061\",\"joined_name\":\"grouped2_0060\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-132,120,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped2_0059\",\"right_name\":\"grouped2_0061\",\"joined_name\":\"grouped2_0060\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-132,false,121],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0060\",\"joined_name\":\"grouped2_0058\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-133,119,131],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0060\",\"joined_name\":\"grouped2_0058\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-134,119,132],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0060\",\"joined_name\":\"grouped2_0058\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-135,119,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0060\",\"joined_name\":\"grouped2_0058\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-134,false,131],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0060\",\"joined_name\":\"grouped2_0058\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-135,false,132],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0053\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-136,130,134],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0053\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-137,130,135],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0053\",\"a\":3,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-136,false,133],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0053\",\"a\":3,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-137,false,134],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0053\",\"a\":3,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-138,false,135],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-139,127,138],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-139,128,137],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"groupKind2\",\"a\":6,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-139,false,136],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":10,\"grouped\":true},{\"tag\":\"edge\",\"edge\":18,\"owners\":[1,20,21,29,30,35,37,38,39,65,66,71,72,76,77,82,83]},{\"tag\":\"edge\",\"edge\":20,\"owners\":[3,18,27,37,40,43,44,45,67,69,70,78,80,81]},{\"tag\":\"edge\",\"edge\":25,\"owners\":[5,17,26,46,49,50,51,52,65,67,68,76,78,79]},{\"tag\":\"edge\",\"edge\":27,\"owners\":[7,22,31,36,47,50,55,56,69,73,80,84]},{\"tag\":\"edge\",\"edge\":29,\"owners\":[8,19,28,48,52,54,56,66,68,70,77,79,81]},{\"tag\":\"edge\",\"edge\":32,\"owners\":[10,24,33,38,47,57,59,61,74,75,85,86]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[12,21,30,48,58,61,62,66,72,77,83]}]}"
  "367 136 0 359 358 0\n368 133 0 367 353 0\n369 -54 -120 0 77 81 91 326 0\n370 112 -53 0 155 113 75 72 71 70 68 316 317 318 238 241 365 0\n371 -53 0 68 70 71 72 75 370 69 73 74 243 240 315 0\n372 -38 -118 0 85 87 120 123 324 0\n373 38 50 66 30 48 52 77 9 0 239 242 238 241 365 0\n374 -38 30 119 0 367 359 348 18 19 20 25 37 372 340 342 351 352 347 357 344 345 338 327 334 335 100 107 143 332 326 16 128 320 321 149 0\n375 -50 38 0 48 49 51 52 53 112 153 215 218 216 219 363 0\n376 30 48 52 77 9 119 0 374 375 240 373 0\n377 -30 52 0 371 4 21 46 108 150 246 244 248 250 366 0\n378 30 52 119 77 9 0 371 376 41 43 47 246 251 247 244 248 250 366 0\n379 52 77 9 119 0 377 378 0\n380 6 41 71 28 60 64 47 46 38 0 220 218 215 363 0\n381 41 71 28 60 -80 -104 74 65 64 55 -52 119 0 359 313 306 65 64 63 62 60 59 58 54 380 213 214 277 327 279 287 345 293 288 347 294 289 354 295 291 357 309 311 336 312 310 331 292 308 329 290 299 300 319 286 297 298 296 285 282 281 280 276 237 162 0\n382 -41 57 68 -52 0 63 61 26 33 38 228 236 227 235 222 230 364 0\n383 -71 -80 -101 41 -66 47 46 38 0 313 116 154 219 274 275 277 279 284 287 293 302 288 294 303 289 295 305 291 307 311 310 0\n384 -28 41 37 0 2 24 29 32 90 94 127 132 202 208 206 212 362 0\n385 -130 67 43 59 63 74 57 68 49 0 341 342 322 340 84 324 0\n386 130 70 58 40 71 119 0 367 359 348 351 352 347 357 344 338 326 335 128 332 321 0\n387 -130 43 59 63 74 57 68 49 0 341 385 322 119 0\n388 63 74 57 68 -66 -52 119 0 249 283 301 304 59 382 384 117 116 115 65 63 62 60 245 278 383 381 98 100 101 216 31 387 386 131 138 149 263 0\n389 -60 -63 57 68 -52 119 0 136 111 110 109 63 61 98 99 100 107 143 386 342 340 324 129 146 258 263 159 166 221 364 0\n390 71 69 60 70 41 64 -52 119 0 359 59 384 63 62 60 58 380 321 213 332 327 335 345 338 347 357 354 0\n391 -34 -66 54 0 10 11 35 252 0\n392 21 72 43 59 70 57 68 -52 0 63 61 229 267 271 233 364 0\n393 -21 70 -118 60 57 68 64 -52 119 0 382 126 390 167 164 324 255 0\n394 -72 70 -118 57 68 0 145 146 148 255 324 0\n395 70 -118 119 60 57 68 64 -52 0 393 394 232 270 392 0\n396 -70 57 68 -66 -52 119 0 136 152 388 0\n397 -118 57 68 -66 -52 119 0 396 382 116 63 62 60 395 394 101 107 216 389 31 388 392 151 268 324 161 0\n398 57 68 34 -66 -52 119 0 367 58 396 397 340 342 351 347 345 327 98 100 143 386 0\n399 -60 70 -57 37 0 121 95 92 88 98 160 201 254 204 259 203 205 362 0\n400 -32 -115 -111 70 64 46 0 30 34 128 314 321 154 0\n401 70 -57 34 64 47 46 38 37 30 119 0 368 359 92 346 399 327 345 343 347 354 357 336 338 330 335 332 400 326 23 24 28 141 380 0\n402 -57 34 64 47 46 38 37 30 29 119 0 86 92 104 401 131 138 144 149 185 190 188 263 260 361 0\n403 124 72 36 34 30 27 119 0 359 348 355 356 337 335 333 338 357 354 347 345 327 97 99 107 320 0\n404 41 69 59 70 19 37 40 12 42 43 56 67 5 0 362 256 0\n405 77 -112 9 54 0 371 325 379 56 57 58 59 60 62 63 66 67 315 116 391 402 398 122 124 125 130 137 147 403 332 321 141 165 207 253 210 209 211 257 404 0\n406 19 56 67 43 59 42 41 40 69 37 70 0 207 253 404 0\n407 130 58 40 70 119 0 367 351 386 347 139 140 143 345 327 0\n408 -57 -12 58 -19 69 37 70 29 0 102 145 86 399 269 158 163 164 180 181 182 183 361 0\n409 -59 69 29 0 93 96 101 106 180 181 182 183 266 261 265 184 361 0\n410 120 69 70 119 0 368 359 346 344 343 347 354 357 338 335 332 321 139 140 143 327 0\n411 12 67 56 42 58 40 59 69 37 70 0 201 203 205 404 254 0\n412 58 40 69 37 70 29 119 0 410 409 407 326 342 6 7 8 30 83 118 340 411 253 408 177 178 324 175 0\n413 -58 59 70 0 89 92 105 221 226 268 224 225 273 272 223 364 0\n414 -40 46 0 23 24 25 28 40 98 141 217 380 0\n415 69 70 -77 119 0 157 414 156 409 410 413 412 326 17 0\n416 70 -77 119 0 415 126 130 148 233 229 267 269 231 234 232 270 271 364 0\n417 -77 119 0 156 416 131 138 144 149 185 191 189 190 264 263 260 188 262 361 0\n418 -70 -116 49 0 133 134 135 136 152 322 0\n419 58 70 -120 40 37 29 119 0 412 326 128 0\n420 70 -120 119 40 37 29 0 419 96 413 0\n421 9 54 0 371 359 325 417 348 379 405 57 59 62 65 328 414 331 336 357 352 354 341 347 344 418 420 0\n422 -69 70 0 126 130 148 233 229 267 269 231 234 232 270 271 364 0\n423 29 70 54 0 371 325 422 410 421 39 414 409 413 420 326 17 0\n424 7 70 59 14 21 39 43 72 47 57 45 68 0 364 228 0\n425 70 54 0 371 421 55 44 423 3 9 14 169 168 193 194 195 246 250 196 236 227 222 230 424 0\n426 20 72 69 71 0 185 191 189 190 264 263 260 188 187 262 361 0\n427 -70 0 131 138 144 149 426 0\n428 -69 0 427 422 0\n429 54 0 427 425 0\n430 -31 0 429 76 0\n431 -32 0 429 77 0\n432 -34 0 429 78 0\n433 -35 0 429 79 0\n434 -37 0 429 80 0\n435 -40 0 429 81 0\n436 -42 0 429 82 0\n437 -58 0 429 91 0\n438 -120 0 429 369 0\n439 -132 0 438 344 0\n440 -135 0 439 350 0\n441 -138 0 440 355 0\n442 127 0 441 359 356 0\n443 125 0 442 337 0\n444 -28 0 434 27 384 0\n445 71 61 36 29 72 0 427 428 431 433 432 443 429 444 321 426 332 186 333 1 179 320 0\n446 61 36 72 29 0 359 444 438 432 431 433 445 139 142 143 192 327 1 343 320 349 334 354 338 357 0\n447 12 56 59 0 427 434 435 428 436 437 201 203 205 258 254 404 0\n448 -61 59 0 102 103 447 0\n449 130 30 0 367 440 359 438 432 428 427 351 352 349 357 343 338 327 335 143 332 321 0\n450 14 21 59 68 39 7 72 47 57 45 0 427 424 232 0\n451 21 29 72 0 428 427 409 448 446 122 86 36 22 229 267 234 450 0\n452 29 72 0 428 430 409 448 446 12 13 15 86 122 451 268 200 199 197 198 173 174 176 170 171 172 360 0\n453 -29 0 434 371 3 5 9 14 42 45 50 57 114 156 449 342 339 340 372 373 169 168 323 196 0\n454 -59 0 453 428 409 0\n455 72 0 453 452 0\n456 -19 0 455 145 0\n457 -67 0 455 146 0\n458 -56 0 456 428 427 255 0\n459 -41 0 456 428 457 427 209 0\n460 -43 0 456 428 457 211 0\n461 0 456 457 454 458 459 460 436 435 428 434 427 406 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record024.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record024.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record024.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record024.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record024 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record024.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record024.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record024.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record024.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record024 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record024_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record024_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record024_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record024_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record024_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record024_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record024_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record024 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record024_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record024_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record024_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00022.record024
