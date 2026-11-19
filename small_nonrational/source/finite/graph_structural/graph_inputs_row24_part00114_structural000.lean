module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00114Data
public import GraphInputsRow24Part00114Frames
public import GraphInputsRow24Part00114Leaves
public import GraphInputsRow24Part00114Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00114.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record001
def vertexColumn : Fields := ⟨10, hexnat% "1b8751b49713cb49d26ab1a66a5a719a6399969595635a4e8791e17ad16c5a9666594e4b9694e565655355352d64d4b61d4745d0f6c368ce3a4d9394cd362e4b8ad2b2ae1b46c9b16d8791cc749ca719e1745c9715e0f43c4f07d2c471a24a9264382e944d1864550b41d90cc328e0b0ac4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36da6d36da6db6da69b69b6da4db4924926d269249b6d24936d2491249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨66, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨80, by decide⟩, ⟨85, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4001f0683e3e00000", 18014673387388928, hexnat% "100010000a0000000000000", hexnat% "401800300000000000", hexnat% "2100000000010000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "144187c344302600000", 282026343137280, hexnat% "10000000080000000800000", 3298551660544, hexnat% "2100000002000080000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "41078264201600000", hexnat% "10001000080000000800000", hexnat% "400800100002000000", hexnat% "2100000002010080000000", 1407379715391488, 550829555712]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2100000042210080400000", hexnat% "100000000a8000000800000", hexnat% "441810000000000000", 6871964450816, 1407388305326080, hexnat% "1000000100002200000", 550829555712]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00114.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00114.record009
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "761b49713c749b23c9ca6695a3693a699964d8b6c3a4e4b91e1783e6c4f1666593653969595955352d64d4b61d4745d0f6c368ce364cd34ccb31cd8b32d2b46c9b16c3b61e4789d2729d1725c570dd0f13c2f07db04d11c68a4a49a0e438d12c649164358341d90cc328e0b12e0709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1a69a6db6d34d249b49a4db69269249269a6d36d36924db492449249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record009 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record009 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record009.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record009.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record009.data.quota

def groupMembers1 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 0)]))
 (.leaf ([(facetIndex 1)])))
 (.branch 3
 (.leaf ([(facetIndex 2)]))
 (.branch 4
 (.leaf ([(facetIndex 3)]))
 (.leaf ([(facetIndex 4)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 5)]))
 (.branch 7
 (.leaf ([(facetIndex 6)]))
 (.leaf ([(facetIndex 7)]))))
 (.branch 9
 (.leaf ([(facetIndex 8)]))
 (.branch 10
 (.leaf ([(facetIndex 9)]))
 (.leaf ([(facetIndex 10)]))))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf ([(facetIndex 11)]))
 (.branch 13
 (.leaf ([(facetIndex 12)]))
 (.leaf ([(facetIndex 13)]))))
 (.branch 15
 (.leaf ([(facetIndex 14)]))
 (.branch 16
 (.leaf ([(facetIndex 15)]))
 (.leaf ([(facetIndex 16)])))))
 (.branch 20
 (.branch 18
 (.leaf ([(facetIndex 17)]))
 (.branch 19
 (.leaf ([(facetIndex 18)]))
 (.leaf ([(facetIndex 19)]))))
 (.branch 21
 (.leaf ([(facetIndex 20)]))
 (.branch 22
 (.leaf ([(facetIndex 21)]))
 (.leaf ([(facetIndex 22)])))))))
def groupColors1 : PackedGraphCertificate.Fields :=
  ⟨5, sparse_nat% "5ab49ca307b9ac5a928398a418820"⟩
def grouping1 : FacetSat.Grouping data.count where
  count := 23
  members := fun g => groupMembers1.get g
  color := fun c => groupColors1.get c.val
def groupKind1 : List Nat := List.range grouping1.count

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 41), (facetIndex 46), (facetIndex 48), (facetIndex 50)]))
 (.leaf ([(facetIndex 63), (facetIndex 66)])))
 (.branch 3
 (.leaf ([(facetIndex 25), (facetIndex 26), (facetIndex 72), (facetIndex 73)]))
 (.leaf ([(facetIndex 24), (facetIndex 33), (facetIndex 34)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 31), (facetIndex 57), (facetIndex 77), (facetIndex 88)]))
 (.leaf ([(facetIndex 51), (facetIndex 71), (facetIndex 86)])))
 (.branch 7
 (.leaf ([(facetIndex 52), (facetIndex 54), (facetIndex 56), (facetIndex 64)]))
 (.branch 8
 (.leaf ([(facetIndex 32), (facetIndex 49), (facetIndex 53), (facetIndex 58), (facetIndex 67)]))
 (.leaf ([(facetIndex 23), (facetIndex 27), (facetIndex 37), (facetIndex 44), (facetIndex 70), (facetIndex 75), (facetIndex 84)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "405080000004080225800710610000746067650700008000000800337400082238z17;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 28), (facetIndex 59)]))
 (.leaf ([(facetIndex 69), (facetIndex 87)])))
 (.branch 3
 (.leaf ([(facetIndex 38), (facetIndex 42), (facetIndex 82)]))
 (.branch 4
 (.leaf ([(facetIndex 65), (facetIndex 79), (facetIndex 89)]))
 (.leaf ([(facetIndex 30), (facetIndex 35), (facetIndex 40)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 39), (facetIndex 55), (facetIndex 60)]))
 (.leaf ([(facetIndex 45), (facetIndex 61), (facetIndex 62)])))
 (.branch 8
 (.leaf ([(facetIndex 29), (facetIndex 36), (facetIndex 43), (facetIndex 47), (facetIndex 80), (facetIndex 81)]))
 (.branch 9
 (.leaf ([(facetIndex 68), (facetIndex 74), (facetIndex 83), (facetIndex 85)]))
 (.leaf ([(facetIndex 76), (facetIndex 78)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "3010808277390908000018003006650000500000007060720452074000047z1d;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped1_0000 : List Nat := [0]
def grouped1_0001 : List Nat := [0, 1]
def grouped1_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped1_0003 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
def grouped1_0005 : List Nat := [1]
def grouped1_0006 : List Nat := [2]
def grouped1_0007 : List Nat := [2, 3, 4]
def grouped1_0008 : List Nat := [3, 4]
def grouped1_0009 : List Nat := [5]
def grouped1_0010 : List Nat := [5, 6, 7]
def grouped1_0011 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped1_0012 : List Nat := [6]
def grouped1_0013 : List Nat := [6, 7]
def grouped1_0014 : List Nat := [7]
def grouped1_0015 : List Nat := [8]
def grouped1_0016 : List Nat := [8, 9, 10]
def grouped1_0017 : List Nat := [9]
def grouped1_0018 : List Nat := [9, 10]
def grouped1_0019 : List Nat := [10]
def grouped1_0020 : List Nat := [11]
def grouped1_0021 : List Nat := [11, 12, 13]
def grouped1_0022 : List Nat := [11, 12, 13, 14, 15, 16]
def grouped1_0023 : List Nat := [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]
def grouped1_0024 : List Nat := [12]
def grouped1_0025 : List Nat := [12, 13]
def grouped1_0026 : List Nat := [13]
def grouped1_0027 : List Nat := [14]
def grouped1_0028 : List Nat := [14, 15, 16]
def grouped1_0029 : List Nat := [15]
def grouped1_0030 : List Nat := [15, 16]
def grouped1_0031 : List Nat := [16]
def grouped1_0032 : List Nat := [17]
def grouped1_0033 : List Nat := [17, 18, 19]
def grouped1_0034 : List Nat := [17, 18, 19, 20, 21, 22]
def grouped1_0035 : List Nat := [18]
def grouped1_0036 : List Nat := [18, 19]
def grouped1_0037 : List Nat := [19]
def grouped1_0038 : List Nat := [20]
def grouped1_0039 : List Nat := [20, 21, 22]
def grouped1_0040 : List Nat := [21]
def grouped1_0041 : List Nat := [21, 22]
def grouped1_0042 : List Nat := [22]
def grouped2_0043 : List Nat := [0]
def grouped2_0044 : List Nat := [0, 1]
def grouped2_0045 : List Nat := [0, 1, 2, 3]
def grouped2_0047 : List Nat := [1]
def grouped2_0048 : List Nat := [2]
def grouped2_0049 : List Nat := [2, 3]
def grouped2_0050 : List Nat := [3]
def grouped2_0051 : List Nat := [4]
def grouped2_0052 : List Nat := [4, 5]
def grouped2_0053 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0054 : List Nat := [5]
def grouped2_0055 : List Nat := [6]
def grouped2_0056 : List Nat := [6, 7, 8]
def grouped2_0057 : List Nat := [7]
def grouped2_0058 : List Nat := [7, 8]
def grouped2_0059 : List Nat := [8]
def grouped3_0060 : List Nat := [0]
def grouped3_0061 : List Nat := [0, 1]
def grouped3_0062 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0064 : List Nat := [1]
def grouped3_0065 : List Nat := [2]
def grouped3_0066 : List Nat := [2, 3, 4]
def grouped3_0067 : List Nat := [3]
def grouped3_0068 : List Nat := [3, 4]
def grouped3_0069 : List Nat := [4]
def grouped3_0070 : List Nat := [5]
def grouped3_0071 : List Nat := [5, 6]
def grouped3_0072 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0073 : List Nat := [6]
def grouped3_0074 : List Nat := [7]
def grouped3_0075 : List Nat := [7, 8, 9]
def grouped3_0076 : List Nat := [8]
def grouped3_0077 : List Nat := [8, 9]
def grouped3_0078 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record009 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record009_matrix_checked

def leafCount : Nat := 69
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaf0000 : List (Fin data.count) := [(facetIndex 2), (facetIndex 11), (facetIndex 12), (facetIndex 20), (facetIndex 27), (facetIndex 49), (facetIndex 50), (facetIndex 54), (facetIndex 66), (facetIndex 71), (facetIndex 72), (facetIndex 82), (facetIndex 88), (facetIndex 89)]
theorem leaf0000_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0000 = true := by
  decide +kernel
theorem leaf0000_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0000 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0000_counts_checked
def leaf0001 : List (Fin data.count) := [(facetIndex 2), (facetIndex 11), (facetIndex 12), (facetIndex 20), (facetIndex 31), (facetIndex 50), (facetIndex 54), (facetIndex 58), (facetIndex 66), (facetIndex 71), (facetIndex 72), (facetIndex 82), (facetIndex 84), (facetIndex 89)]
theorem leaf0001_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0001 = true := by
  decide +kernel
theorem leaf0001_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0001 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0001_counts_checked
def leaf0002 : List (Fin data.count) := [(facetIndex 2), (facetIndex 9), (facetIndex 10), (facetIndex 21), (facetIndex 31), (facetIndex 50), (facetIndex 53), (facetIndex 64), (facetIndex 66), (facetIndex 71), (facetIndex 72), (facetIndex 82), (facetIndex 84), (facetIndex 89)]
theorem leaf0002_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0002 = true := by
  decide +kernel
theorem leaf0002_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0002 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0002_counts_checked
def leaf0003 : List (Fin data.count) := [(facetIndex 2), (facetIndex 8), (facetIndex 9), (facetIndex 20), (facetIndex 31), (facetIndex 50), (facetIndex 58), (facetIndex 64), (facetIndex 66), (facetIndex 71), (facetIndex 72), (facetIndex 82), (facetIndex 84), (facetIndex 89)]
theorem leaf0003_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0003 = true := by
  decide +kernel
theorem leaf0003_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0003 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0003_counts_checked
def leaf0004 : List (Fin data.count) := [(facetIndex 2), (facetIndex 8), (facetIndex 9), (facetIndex 20), (facetIndex 27), (facetIndex 49), (facetIndex 50), (facetIndex 64), (facetIndex 66), (facetIndex 71), (facetIndex 72), (facetIndex 82), (facetIndex 88), (facetIndex 89)]
theorem leaf0004_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0004 = true := by
  decide +kernel
theorem leaf0004_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0004 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0004_counts_checked
def leaf0005 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 9), (facetIndex 19), (facetIndex 27), (facetIndex 50), (facetIndex 53), (facetIndex 64), (facetIndex 66), (facetIndex 71), (facetIndex 72), (facetIndex 82), (facetIndex 88), (facetIndex 89)]
theorem leaf0005_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0005 = true := by
  decide +kernel
theorem leaf0005_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0005 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0005_counts_checked
def leaf0006 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 9), (facetIndex 19), (facetIndex 32), (facetIndex 50), (facetIndex 51), (facetIndex 64), (facetIndex 66), (facetIndex 70), (facetIndex 72), (facetIndex 82), (facetIndex 88), (facetIndex 89)]
theorem leaf0006_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0006 = true := by
  decide +kernel
theorem leaf0006_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0006 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0006_counts_checked
def leaf0007 : List (Fin data.count) := [(facetIndex 1), (facetIndex 2), (facetIndex 9), (facetIndex 17), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 64), (facetIndex 66), (facetIndex 70), (facetIndex 72), (facetIndex 82), (facetIndex 88), (facetIndex 89)]
theorem leaf0007_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0007 = true := by
  decide +kernel
theorem leaf0007_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0007 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0007_counts_checked
def leaf0008 : List (Fin data.count) := [(facetIndex 7), (facetIndex 8), (facetIndex 10), (facetIndex 18), (facetIndex 33), (facetIndex 48), (facetIndex 56), (facetIndex 63), (facetIndex 67), (facetIndex 73), (facetIndex 77), (facetIndex 80), (facetIndex 85), (facetIndex 86)]
theorem leaf0008_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0008 = true := by
  decide +kernel
theorem leaf0008_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0008 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0008_counts_checked
def leaf0009 : List (Fin data.count) := [(facetIndex 7), (facetIndex 10), (facetIndex 12), (facetIndex 18), (facetIndex 33), (facetIndex 48), (facetIndex 54), (facetIndex 63), (facetIndex 67), (facetIndex 73), (facetIndex 77), (facetIndex 80), (facetIndex 85), (facetIndex 86)]
theorem leaf0009_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0009 = true := by
  decide +kernel
theorem leaf0009_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0009 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0009_counts_checked
def leaf0010 : List (Fin data.count) := [(facetIndex 7), (facetIndex 18), (facetIndex 20), (facetIndex 21), (facetIndex 33), (facetIndex 48), (facetIndex 51), (facetIndex 56), (facetIndex 63), (facetIndex 67), (facetIndex 73), (facetIndex 77), (facetIndex 80), (facetIndex 85)]
theorem leaf0010_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0010 = true := by
  decide +kernel
theorem leaf0010_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0010 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0010_counts_checked
def leaf0011 : List (Fin data.count) := [(facetIndex 7), (facetIndex 10), (facetIndex 12), (facetIndex 15), (facetIndex 33), (facetIndex 48), (facetIndex 54), (facetIndex 63), (facetIndex 67), (facetIndex 72), (facetIndex 77), (facetIndex 80), (facetIndex 85), (facetIndex 86)]
theorem leaf0011_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0011 = true := by
  decide +kernel
theorem leaf0011_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0011 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0011_counts_checked
def leaf0012 : List (Fin data.count) := [(facetIndex 7), (facetIndex 9), (facetIndex 14), (facetIndex 21), (facetIndex 33), (facetIndex 48), (facetIndex 53), (facetIndex 57), (facetIndex 64), (facetIndex 71), (facetIndex 72), (facetIndex 82), (facetIndex 84), (facetIndex 89)]
theorem leaf0012_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0012 = true := by
  decide +kernel
theorem leaf0012_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0012 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0012_counts_checked
def leaf0013 : List (Fin data.count) := [(facetIndex 7), (facetIndex 9), (facetIndex 14), (facetIndex 21), (facetIndex 33), (facetIndex 48), (facetIndex 51), (facetIndex 64), (facetIndex 67), (facetIndex 70), (facetIndex 72), (facetIndex 77), (facetIndex 82), (facetIndex 89)]
theorem leaf0013_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0013 = true := by
  decide +kernel
theorem leaf0013_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0013 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0013_counts_checked
def leaf0014 : List (Fin data.count) := [(facetIndex 6), (facetIndex 7), (facetIndex 9), (facetIndex 17), (facetIndex 33), (facetIndex 49), (facetIndex 51), (facetIndex 64), (facetIndex 66), (facetIndex 70), (facetIndex 72), (facetIndex 82), (facetIndex 88), (facetIndex 89)]
theorem leaf0014_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0014 = true := by
  decide +kernel
theorem leaf0014_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0014 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0014_counts_checked
def leaf0015 : List (Fin data.count) := [(facetIndex 9), (facetIndex 16), (facetIndex 17), (facetIndex 18), (facetIndex 33), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 64), (facetIndex 66), (facetIndex 70), (facetIndex 82), (facetIndex 88), (facetIndex 89)]
theorem leaf0015_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0015 = true := by
  decide +kernel
theorem leaf0015_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0015 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0015_counts_checked
def leaf0016 : List (Fin data.count) := [(facetIndex 11), (facetIndex 16), (facetIndex 17), (facetIndex 18), (facetIndex 33), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 56), (facetIndex 66), (facetIndex 70), (facetIndex 82), (facetIndex 88), (facetIndex 89)]
theorem leaf0016_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0016 = true := by
  decide +kernel
theorem leaf0016_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0016 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0016_counts_checked
def leaf0017 : List (Fin data.count) := [(facetIndex 9), (facetIndex 17), (facetIndex 18), (facetIndex 20), (facetIndex 33), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 64), (facetIndex 66), (facetIndex 73), (facetIndex 79), (facetIndex 81), (facetIndex 88)]
theorem leaf0017_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0017 = true := by
  decide +kernel
theorem leaf0017_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0017 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0017_counts_checked
def leaf0018 : List (Fin data.count) := [(facetIndex 11), (facetIndex 17), (facetIndex 18), (facetIndex 20), (facetIndex 33), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 56), (facetIndex 66), (facetIndex 73), (facetIndex 79), (facetIndex 81), (facetIndex 88)]
theorem leaf0018_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0018 = true := by
  decide +kernel
theorem leaf0018_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0018 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0018_counts_checked
def leaf0019 : List (Fin data.count) := [(facetIndex 5), (facetIndex 8), (facetIndex 10), (facetIndex 18), (facetIndex 33), (facetIndex 50), (facetIndex 56), (facetIndex 63), (facetIndex 67), (facetIndex 73), (facetIndex 77), (facetIndex 80), (facetIndex 85), (facetIndex 86)]
theorem leaf0019_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0019 = true := by
  decide +kernel
theorem leaf0019_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0019 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0019_counts_checked
def leaf0020 : List (Fin data.count) := [(facetIndex 5), (facetIndex 10), (facetIndex 12), (facetIndex 18), (facetIndex 33), (facetIndex 50), (facetIndex 54), (facetIndex 63), (facetIndex 67), (facetIndex 73), (facetIndex 77), (facetIndex 80), (facetIndex 85), (facetIndex 86)]
theorem leaf0020_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0020 = true := by
  decide +kernel
theorem leaf0020_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0020 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0020_counts_checked
def leaf0021 : List (Fin data.count) := [(facetIndex 5), (facetIndex 18), (facetIndex 20), (facetIndex 21), (facetIndex 33), (facetIndex 50), (facetIndex 51), (facetIndex 56), (facetIndex 63), (facetIndex 67), (facetIndex 73), (facetIndex 77), (facetIndex 80), (facetIndex 85)]
theorem leaf0021_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0021 = true := by
  decide +kernel
theorem leaf0021_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0021 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0021_counts_checked
def leaf0022 : List (Fin data.count) := [(facetIndex 9), (facetIndex 17), (facetIndex 18), (facetIndex 20), (facetIndex 33), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 64), (facetIndex 66), (facetIndex 73), (facetIndex 80), (facetIndex 85), (facetIndex 88)]
theorem leaf0022_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0022 = true := by
  decide +kernel
theorem leaf0022_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0022 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0022_counts_checked
def leaf0023 : List (Fin data.count) := [(facetIndex 11), (facetIndex 17), (facetIndex 18), (facetIndex 20), (facetIndex 33), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 56), (facetIndex 66), (facetIndex 73), (facetIndex 80), (facetIndex 85), (facetIndex 88)]
theorem leaf0023_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0023 = true := by
  decide +kernel
theorem leaf0023_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0023 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0023_counts_checked
def leaf0024 : List (Fin data.count) := [(facetIndex 13), (facetIndex 17), (facetIndex 18), (facetIndex 20), (facetIndex 33), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 56), (facetIndex 63), (facetIndex 73), (facetIndex 80), (facetIndex 85), (facetIndex 88)]
theorem leaf0024_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0024 = true := by
  decide +kernel
theorem leaf0024_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0024 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0024_counts_checked
def leaf0025 : List (Fin data.count) := [(facetIndex 8), (facetIndex 17), (facetIndex 18), (facetIndex 22), (facetIndex 33), (facetIndex 49), (facetIndex 50), (facetIndex 56), (facetIndex 57), (facetIndex 63), (facetIndex 73), (facetIndex 80), (facetIndex 85), (facetIndex 86)]
theorem leaf0025_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0025 = true := by
  decide +kernel
theorem leaf0025_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0025 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0025_counts_checked
def leaf0026 : List (Fin data.count) := [(facetIndex 12), (facetIndex 17), (facetIndex 18), (facetIndex 22), (facetIndex 33), (facetIndex 49), (facetIndex 50), (facetIndex 54), (facetIndex 57), (facetIndex 63), (facetIndex 73), (facetIndex 80), (facetIndex 85), (facetIndex 86)]
theorem leaf0026_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0026 = true := by
  decide +kernel
theorem leaf0026_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0026 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0026_counts_checked
def leaf0027 : List (Fin data.count) := [(facetIndex 9), (facetIndex 17), (facetIndex 18), (facetIndex 20), (facetIndex 33), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 64), (facetIndex 66), (facetIndex 73), (facetIndex 82), (facetIndex 88), (facetIndex 89)]
theorem leaf0027_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0027 = true := by
  decide +kernel
theorem leaf0027_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0027 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0027_counts_checked
def leaf0028 : List (Fin data.count) := [(facetIndex 9), (facetIndex 18), (facetIndex 20), (facetIndex 22), (facetIndex 33), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 64), (facetIndex 66), (facetIndex 73), (facetIndex 75), (facetIndex 82), (facetIndex 89)]
theorem leaf0028_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0028 = true := by
  decide +kernel
theorem leaf0028_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0028 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0028_counts_checked
def leaf0029 : List (Fin data.count) := [(facetIndex 11), (facetIndex 17), (facetIndex 18), (facetIndex 20), (facetIndex 33), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 56), (facetIndex 66), (facetIndex 73), (facetIndex 82), (facetIndex 88), (facetIndex 89)]
theorem leaf0029_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0029 = true := by
  decide +kernel
theorem leaf0029_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0029 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0029_counts_checked
def leaf0030 : List (Fin data.count) := [(facetIndex 11), (facetIndex 18), (facetIndex 20), (facetIndex 22), (facetIndex 33), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 56), (facetIndex 66), (facetIndex 73), (facetIndex 75), (facetIndex 82), (facetIndex 89)]
theorem leaf0030_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0030 = true := by
  decide +kernel
theorem leaf0030_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0030 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0030_counts_checked
def leaf0031 : List (Fin data.count) := [(facetIndex 11), (facetIndex 12), (facetIndex 14), (facetIndex 18), (facetIndex 32), (facetIndex 34), (facetIndex 48), (facetIndex 54), (facetIndex 57), (facetIndex 73), (facetIndex 82), (facetIndex 84), (facetIndex 86), (facetIndex 89)]
theorem leaf0031_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0031 = true := by
  decide +kernel
theorem leaf0031_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0031 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0031_counts_checked
def leaf0032 : List (Fin data.count) := [(facetIndex 11), (facetIndex 12), (facetIndex 14), (facetIndex 18), (facetIndex 27), (facetIndex 34), (facetIndex 48), (facetIndex 54), (facetIndex 67), (facetIndex 73), (facetIndex 77), (facetIndex 82), (facetIndex 86), (facetIndex 89)]
theorem leaf0032_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0032 = true := by
  decide +kernel
theorem leaf0032_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0032 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0032_counts_checked
def leaf0033 : List (Fin data.count) := [(facetIndex 12), (facetIndex 18), (facetIndex 19), (facetIndex 22), (facetIndex 32), (facetIndex 34), (facetIndex 48), (facetIndex 54), (facetIndex 57), (facetIndex 63), (facetIndex 73), (facetIndex 80), (facetIndex 85), (facetIndex 86)]
theorem leaf0033_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0033 = true := by
  decide +kernel
theorem leaf0033_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0033 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0033_counts_checked
def leaf0034 : List (Fin data.count) := [(facetIndex 1), (facetIndex 10), (facetIndex 12), (facetIndex 18), (facetIndex 34), (facetIndex 48), (facetIndex 54), (facetIndex 63), (facetIndex 67), (facetIndex 73), (facetIndex 77), (facetIndex 80), (facetIndex 85), (facetIndex 86)]
theorem leaf0034_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0034 = true := by
  decide +kernel
theorem leaf0034_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0034 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0034_counts_checked
def leaf0035 : List (Fin data.count) := [(facetIndex 8), (facetIndex 9), (facetIndex 14), (facetIndex 18), (facetIndex 32), (facetIndex 34), (facetIndex 48), (facetIndex 57), (facetIndex 64), (facetIndex 73), (facetIndex 82), (facetIndex 84), (facetIndex 86), (facetIndex 89)]
theorem leaf0035_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0035 = true := by
  decide +kernel
theorem leaf0035_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0035 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0035_counts_checked
def leaf0036 : List (Fin data.count) := [(facetIndex 8), (facetIndex 9), (facetIndex 14), (facetIndex 18), (facetIndex 27), (facetIndex 34), (facetIndex 48), (facetIndex 64), (facetIndex 67), (facetIndex 73), (facetIndex 77), (facetIndex 82), (facetIndex 86), (facetIndex 89)]
theorem leaf0036_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0036 = true := by
  decide +kernel
theorem leaf0036_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0036 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0036_counts_checked
def leaf0037 : List (Fin data.count) := [(facetIndex 9), (facetIndex 11), (facetIndex 12), (facetIndex 17), (facetIndex 33), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 66), (facetIndex 70), (facetIndex 72), (facetIndex 82), (facetIndex 88), (facetIndex 89)]
theorem leaf0037_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0037 = true := by
  decide +kernel
theorem leaf0037_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0037 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0037_counts_checked
def leaf0038 : List (Fin data.count) := [(facetIndex 5), (facetIndex 9), (facetIndex 14), (facetIndex 21), (facetIndex 33), (facetIndex 50), (facetIndex 53), (facetIndex 57), (facetIndex 64), (facetIndex 71), (facetIndex 72), (facetIndex 82), (facetIndex 84), (facetIndex 89)]
theorem leaf0038_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0038 = true := by
  decide +kernel
theorem leaf0038_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0038 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0038_counts_checked
def leaf0039 : List (Fin data.count) := [(facetIndex 5), (facetIndex 9), (facetIndex 14), (facetIndex 21), (facetIndex 33), (facetIndex 50), (facetIndex 51), (facetIndex 64), (facetIndex 67), (facetIndex 70), (facetIndex 72), (facetIndex 77), (facetIndex 82), (facetIndex 89)]
theorem leaf0039_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0039 = true := by
  decide +kernel
theorem leaf0039_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0039 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0039_counts_checked
def leaf0040 : List (Fin data.count) := [(facetIndex 9), (facetIndex 13), (facetIndex 14), (facetIndex 17), (facetIndex 33), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 64), (facetIndex 70), (facetIndex 72), (facetIndex 82), (facetIndex 88), (facetIndex 89)]
theorem leaf0040_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0040 = true := by
  decide +kernel
theorem leaf0040_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0040 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0040_counts_checked
def leaf0041 : List (Fin data.count) := [(facetIndex 9), (facetIndex 10), (facetIndex 14), (facetIndex 19), (facetIndex 33), (facetIndex 44), (facetIndex 50), (facetIndex 53), (facetIndex 64), (facetIndex 71), (facetIndex 72), (facetIndex 82), (facetIndex 88), (facetIndex 89)]
theorem leaf0041_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0041 = true := by
  decide +kernel
theorem leaf0041_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0041 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0041_counts_checked
def leaf0042 : List (Fin data.count) := [(facetIndex 5), (facetIndex 9), (facetIndex 10), (facetIndex 19), (facetIndex 33), (facetIndex 50), (facetIndex 53), (facetIndex 64), (facetIndex 66), (facetIndex 71), (facetIndex 72), (facetIndex 79), (facetIndex 81), (facetIndex 88)]
theorem leaf0042_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0042 = true := by
  decide +kernel
theorem leaf0042_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0042 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0042_counts_checked
def leaf0043 : List (Fin data.count) := [(facetIndex 5), (facetIndex 9), (facetIndex 10), (facetIndex 19), (facetIndex 33), (facetIndex 50), (facetIndex 53), (facetIndex 64), (facetIndex 66), (facetIndex 71), (facetIndex 72), (facetIndex 80), (facetIndex 85), (facetIndex 88)]
theorem leaf0043_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0043 = true := by
  decide +kernel
theorem leaf0043_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0043 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0043_counts_checked
def leaf0044 : List (Fin data.count) := [(facetIndex 5), (facetIndex 8), (facetIndex 9), (facetIndex 20), (facetIndex 33), (facetIndex 50), (facetIndex 58), (facetIndex 64), (facetIndex 66), (facetIndex 71), (facetIndex 72), (facetIndex 82), (facetIndex 84), (facetIndex 89)]
theorem leaf0044_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0044 = true := by
  decide +kernel
theorem leaf0044_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0044 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0044_counts_checked
def leaf0045 : List (Fin data.count) := [(facetIndex 5), (facetIndex 8), (facetIndex 9), (facetIndex 22), (facetIndex 33), (facetIndex 50), (facetIndex 58), (facetIndex 64), (facetIndex 66), (facetIndex 70), (facetIndex 72), (facetIndex 77), (facetIndex 82), (facetIndex 89)]
theorem leaf0045_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0045 = true := by
  decide +kernel
theorem leaf0045_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0045 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0045_counts_checked
def leaf0046 : List (Fin data.count) := [(facetIndex 5), (facetIndex 9), (facetIndex 21), (facetIndex 22), (facetIndex 33), (facetIndex 50), (facetIndex 51), (facetIndex 64), (facetIndex 66), (facetIndex 70), (facetIndex 72), (facetIndex 77), (facetIndex 82), (facetIndex 89)]
theorem leaf0046_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0046 = true := by
  decide +kernel
theorem leaf0046_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0046 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0046_counts_checked
def leaf0047 : List (Fin data.count) := [(facetIndex 5), (facetIndex 9), (facetIndex 17), (facetIndex 19), (facetIndex 33), (facetIndex 50), (facetIndex 51), (facetIndex 64), (facetIndex 66), (facetIndex 70), (facetIndex 72), (facetIndex 82), (facetIndex 88), (facetIndex 89)]
theorem leaf0047_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0047 = true := by
  decide +kernel
theorem leaf0047_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0047 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0047_counts_checked
def leaf0048 : List (Fin data.count) := [(facetIndex 5), (facetIndex 9), (facetIndex 10), (facetIndex 21), (facetIndex 33), (facetIndex 50), (facetIndex 53), (facetIndex 64), (facetIndex 66), (facetIndex 71), (facetIndex 72), (facetIndex 82), (facetIndex 84), (facetIndex 89)]
theorem leaf0048_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0048 = true := by
  decide +kernel
theorem leaf0048_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0048 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0048_counts_checked
def leaf0049 : List (Fin data.count) := [(facetIndex 5), (facetIndex 9), (facetIndex 10), (facetIndex 19), (facetIndex 33), (facetIndex 50), (facetIndex 53), (facetIndex 64), (facetIndex 66), (facetIndex 71), (facetIndex 72), (facetIndex 82), (facetIndex 88), (facetIndex 89)]
theorem leaf0049_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0049 = true := by
  decide +kernel
theorem leaf0049_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0049 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0049_counts_checked
def leaf0050 : List (Fin data.count) := [(facetIndex 8), (facetIndex 9), (facetIndex 10), (facetIndex 20), (facetIndex 33), (facetIndex 49), (facetIndex 50), (facetIndex 64), (facetIndex 66), (facetIndex 71), (facetIndex 72), (facetIndex 79), (facetIndex 81), (facetIndex 88)]
theorem leaf0050_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0050 = true := by
  decide +kernel
theorem leaf0050_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0050 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0050_counts_checked
def leaf0051 : List (Fin data.count) := [(facetIndex 8), (facetIndex 9), (facetIndex 10), (facetIndex 20), (facetIndex 33), (facetIndex 49), (facetIndex 50), (facetIndex 64), (facetIndex 66), (facetIndex 71), (facetIndex 72), (facetIndex 80), (facetIndex 85), (facetIndex 88)]
theorem leaf0051_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0051 = true := by
  decide +kernel
theorem leaf0051_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0051 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0051_counts_checked
def leaf0052 : List (Fin data.count) := [(facetIndex 8), (facetIndex 9), (facetIndex 10), (facetIndex 20), (facetIndex 33), (facetIndex 49), (facetIndex 50), (facetIndex 64), (facetIndex 66), (facetIndex 71), (facetIndex 72), (facetIndex 82), (facetIndex 88), (facetIndex 89)]
theorem leaf0052_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0052 = true := by
  decide +kernel
theorem leaf0052_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0052 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0052_counts_checked
def leaf0053 : List (Fin data.count) := [(facetIndex 8), (facetIndex 9), (facetIndex 10), (facetIndex 17), (facetIndex 33), (facetIndex 49), (facetIndex 50), (facetIndex 64), (facetIndex 66), (facetIndex 70), (facetIndex 72), (facetIndex 82), (facetIndex 88), (facetIndex 89)]
theorem leaf0053_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0053 = true := by
  decide +kernel
theorem leaf0053_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0053 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0053_counts_checked
def leaf0054 : List (Fin data.count) := [(facetIndex 9), (facetIndex 15), (facetIndex 17), (facetIndex 20), (facetIndex 33), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 64), (facetIndex 66), (facetIndex 72), (facetIndex 79), (facetIndex 81), (facetIndex 88)]
theorem leaf0054_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0054 = true := by
  decide +kernel
theorem leaf0054_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0054 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0054_counts_checked
def leaf0055 : List (Fin data.count) := [(facetIndex 9), (facetIndex 15), (facetIndex 17), (facetIndex 20), (facetIndex 33), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 64), (facetIndex 66), (facetIndex 72), (facetIndex 80), (facetIndex 85), (facetIndex 88)]
theorem leaf0055_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0055 = true := by
  decide +kernel
theorem leaf0055_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0055 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0055_counts_checked
def leaf0056 : List (Fin data.count) := [(facetIndex 9), (facetIndex 15), (facetIndex 17), (facetIndex 20), (facetIndex 33), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 64), (facetIndex 66), (facetIndex 72), (facetIndex 82), (facetIndex 88), (facetIndex 89)]
theorem leaf0056_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0056 = true := by
  decide +kernel
theorem leaf0056_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0056 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0056_counts_checked
def leaf0057 : List (Fin data.count) := [(facetIndex 9), (facetIndex 15), (facetIndex 20), (facetIndex 22), (facetIndex 33), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 64), (facetIndex 66), (facetIndex 72), (facetIndex 75), (facetIndex 82), (facetIndex 89)]
theorem leaf0057_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0057 = true := by
  decide +kernel
theorem leaf0057_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0057 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0057_counts_checked
def leaf0058 : List (Fin data.count) := [(facetIndex 9), (facetIndex 17), (facetIndex 21), (facetIndex 22), (facetIndex 33), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 64), (facetIndex 66), (facetIndex 70), (facetIndex 72), (facetIndex 82), (facetIndex 89)]
theorem leaf0058_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0058 = true := by
  decide +kernel
theorem leaf0058_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0058 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0058_counts_checked
def leaf0059 : List (Fin data.count) := [(facetIndex 10), (facetIndex 11), (facetIndex 12), (facetIndex 20), (facetIndex 33), (facetIndex 49), (facetIndex 50), (facetIndex 54), (facetIndex 66), (facetIndex 71), (facetIndex 72), (facetIndex 79), (facetIndex 81), (facetIndex 88)]
theorem leaf0059_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0059 = true := by
  decide +kernel
theorem leaf0059_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0059 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0059_counts_checked
def leaf0060 : List (Fin data.count) := [(facetIndex 10), (facetIndex 11), (facetIndex 12), (facetIndex 20), (facetIndex 33), (facetIndex 49), (facetIndex 50), (facetIndex 54), (facetIndex 66), (facetIndex 71), (facetIndex 72), (facetIndex 80), (facetIndex 85), (facetIndex 88)]
theorem leaf0060_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0060 = true := by
  decide +kernel
theorem leaf0060_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0060 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0060_counts_checked
def leaf0061 : List (Fin data.count) := [(facetIndex 10), (facetIndex 11), (facetIndex 12), (facetIndex 20), (facetIndex 33), (facetIndex 49), (facetIndex 50), (facetIndex 54), (facetIndex 66), (facetIndex 71), (facetIndex 72), (facetIndex 82), (facetIndex 88), (facetIndex 89)]
theorem leaf0061_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0061 = true := by
  decide +kernel
theorem leaf0061_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0061 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0061_counts_checked
def leaf0062 : List (Fin data.count) := [(facetIndex 10), (facetIndex 11), (facetIndex 12), (facetIndex 17), (facetIndex 33), (facetIndex 49), (facetIndex 50), (facetIndex 54), (facetIndex 66), (facetIndex 70), (facetIndex 72), (facetIndex 82), (facetIndex 88), (facetIndex 89)]
theorem leaf0062_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0062 = true := by
  decide +kernel
theorem leaf0062_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0062 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0062_counts_checked
def leaf0063 : List (Fin data.count) := [(facetIndex 5), (facetIndex 11), (facetIndex 12), (facetIndex 20), (facetIndex 33), (facetIndex 50), (facetIndex 54), (facetIndex 58), (facetIndex 66), (facetIndex 71), (facetIndex 72), (facetIndex 82), (facetIndex 84), (facetIndex 89)]
theorem leaf0063_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0063 = true := by
  decide +kernel
theorem leaf0063_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0063 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0063_counts_checked
def leaf0064 : List (Fin data.count) := [(facetIndex 5), (facetIndex 11), (facetIndex 12), (facetIndex 22), (facetIndex 33), (facetIndex 50), (facetIndex 54), (facetIndex 58), (facetIndex 66), (facetIndex 70), (facetIndex 72), (facetIndex 77), (facetIndex 82), (facetIndex 89)]
theorem leaf0064_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0064 = true := by
  decide +kernel
theorem leaf0064_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0064 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0064_counts_checked
def leaf0065 : List (Fin data.count) := [(facetIndex 12), (facetIndex 20), (facetIndex 21), (facetIndex 22), (facetIndex 33), (facetIndex 49), (facetIndex 50), (facetIndex 54), (facetIndex 57), (facetIndex 63), (facetIndex 71), (facetIndex 72), (facetIndex 80), (facetIndex 85)]
theorem leaf0065_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0065 = true := by
  decide +kernel
theorem leaf0065_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0065 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0065_counts_checked
def leaf0066 : List (Fin data.count) := [(facetIndex 10), (facetIndex 12), (facetIndex 13), (facetIndex 20), (facetIndex 33), (facetIndex 49), (facetIndex 50), (facetIndex 54), (facetIndex 63), (facetIndex 71), (facetIndex 72), (facetIndex 80), (facetIndex 85), (facetIndex 88)]
theorem leaf0066_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0066 = true := by
  decide +kernel
theorem leaf0066_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0066 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0066_counts_checked
def leaf0067 : List (Fin data.count) := [(facetIndex 12), (facetIndex 15), (facetIndex 17), (facetIndex 22), (facetIndex 33), (facetIndex 49), (facetIndex 50), (facetIndex 54), (facetIndex 57), (facetIndex 63), (facetIndex 72), (facetIndex 80), (facetIndex 85), (facetIndex 86)]
theorem leaf0067_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0067 = true := by
  decide +kernel
theorem leaf0067_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0067 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0067_counts_checked
def leaf0068 : List (Fin data.count) := [(facetIndex 5), (facetIndex 10), (facetIndex 12), (facetIndex 15), (facetIndex 33), (facetIndex 50), (facetIndex 54), (facetIndex 63), (facetIndex 67), (facetIndex 72), (facetIndex 77), (facetIndex 80), (facetIndex 85), (facetIndex 86)]
theorem leaf0068_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0068 = true := by
  decide +kernel
theorem leaf0068_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0068 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0068_counts_checked
def leavesTable : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 34
 (.branch 17
 (.branch 8
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
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (leaf0008))
 (.leaf (leaf0009)))
 (.branch 11
 (.leaf (leaf0010))
 (.leaf (leaf0011))))
 (.branch 14
 (.branch 13
 (.leaf (leaf0012))
 (.leaf (leaf0013)))
 (.branch 15
 (.leaf (leaf0014))
 (.branch 16
 (.leaf (leaf0015))
 (.leaf (leaf0016)))))))
 (.branch 25
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf (leaf0017))
 (.leaf (leaf0018)))
 (.branch 20
 (.leaf (leaf0019))
 (.leaf (leaf0020))))
 (.branch 23
 (.branch 22
 (.leaf (leaf0021))
 (.leaf (leaf0022)))
 (.branch 24
 (.leaf (leaf0023))
 (.leaf (leaf0024)))))
 (.branch 29
 (.branch 27
 (.branch 26
 (.leaf (leaf0025))
 (.leaf (leaf0026)))
 (.branch 28
 (.leaf (leaf0027))
 (.leaf (leaf0028))))
 (.branch 31
 (.branch 30
 (.leaf (leaf0029))
 (.leaf (leaf0030)))
 (.branch 32
 (.leaf (leaf0031))
 (.branch 33
 (.leaf (leaf0032))
 (.leaf (leaf0033))))))))
 (.branch 51
 (.branch 42
 (.branch 38
 (.branch 36
 (.branch 35
 (.leaf (leaf0034))
 (.leaf (leaf0035)))
 (.branch 37
 (.leaf (leaf0036))
 (.leaf (leaf0037))))
 (.branch 40
 (.branch 39
 (.leaf (leaf0038))
 (.leaf (leaf0039)))
 (.branch 41
 (.leaf (leaf0040))
 (.leaf (leaf0041)))))
 (.branch 46
 (.branch 44
 (.branch 43
 (.leaf (leaf0042))
 (.leaf (leaf0043)))
 (.branch 45
 (.leaf (leaf0044))
 (.leaf (leaf0045))))
 (.branch 48
 (.branch 47
 (.leaf (leaf0046))
 (.leaf (leaf0047)))
 (.branch 49
 (.leaf (leaf0048))
 (.branch 50
 (.leaf (leaf0049))
 (.leaf (leaf0050)))))))
 (.branch 60
 (.branch 55
 (.branch 53
 (.branch 52
 (.leaf (leaf0051))
 (.leaf (leaf0052)))
 (.branch 54
 (.leaf (leaf0053))
 (.leaf (leaf0054))))
 (.branch 57
 (.branch 56
 (.leaf (leaf0055))
 (.leaf (leaf0056)))
 (.branch 58
 (.leaf (leaf0057))
 (.branch 59
 (.leaf (leaf0058))
 (.leaf (leaf0059))))))
 (.branch 64
 (.branch 62
 (.branch 61
 (.leaf (leaf0060))
 (.leaf (leaf0061)))
 (.branch 63
 (.leaf (leaf0062))
 (.leaf (leaf0063))))
 (.branch 66
 (.branch 65
 (.leaf (leaf0064))
 (.leaf (leaf0065)))
 (.branch 67
 (.leaf (leaf0066))
 (.branch 68
 (.leaf (leaf0067))
 (.leaf (leaf0068)))))))))
def leaves (j : Fin leafCount) : List (Fin data.count) := leavesTable.get j.val

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00114.record009" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"kind\":1,\"index\":1},{\"tag\":\"group\",\"kind\":1,\"index\":2},{\"tag\":\"group\",\"kind\":1,\"index\":5},{\"tag\":\"group\",\"kind\":1,\"index\":6},{\"tag\":\"group\",\"kind\":1,\"index\":7},{\"tag\":\"group\",\"kind\":1,\"index\":9},{\"tag\":\"group\",\"kind\":1,\"index\":11},{\"tag\":\"group\",\"kind\":1,\"index\":12},{\"tag\":\"group\",\"kind\":1,\"index\":13},{\"tag\":\"group\",\"kind\":1,\"index\":15},{\"tag\":\"group\",\"kind\":1,\"index\":17},{\"tag\":\"group\",\"kind\":1,\"index\":18},{\"tag\":\"group\",\"kind\":1,\"index\":19},{\"tag\":\"group\",\"kind\":1,\"index\":20},{\"tag\":\"group\",\"kind\":1,\"index\":21},{\"tag\":\"group\",\"kind\":1,\"index\":22},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0007\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0002\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0002\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0013\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0010\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0018\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0016\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0011\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0011\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0025\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0025\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0021\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0021\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0030\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0028\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0022\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0022\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0036\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0033\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0033\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0041\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0039\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0039\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0034\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0034\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0034\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":4,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":5,\"list_name\":\"groupKind1\"},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0044\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0044\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0049\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0049\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0045\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0045\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0052\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0052\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0058\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0058\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0056\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0056\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0053\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0053\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":9,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0061\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0068\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0068\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0066\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0066\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0062\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0062\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0062\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0071\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0077\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0075\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0075\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0072\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0072\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0072\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00114.record009" 192

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00114.record009" "{\"ridges\":[[0,7],[0,14],[2,517],[3,11],[3,73],[4,515],[5,35],[5,161],[5,162],[6,67],[6,194],[7,67],[7,577],[7,578],[8,13],[8,21],[9,13],[11,73],[11,88],[12,577],[14,208],[17,262],[17,292],[18,74],[18,522],[18,578],[19,386],[20,28],[20,268],[23,7],[23,14],[25,67],[26,7],[26,13],[28,86],[31,7],[31,37],[32,7],[32,35],[32,290],[33,35],[33,37],[33,38],[33,515],[33,517],[34,7],[34,577],[34,578],[36,35],[36,58],[37,11],[37,67],[37,74],[37,88],[38,131],[39,266],[39,275],[40,35],[40,266],[41,11],[41,73],[41,74],[41,194],[42,393],[43,35],[43,114],[45,35],[45,49],[46,194],[47,275],[48,67],[48,162],[48,194],[49,35],[49,131],[49,161],[49,290],[50,131],[50,193],[50,194],[50,515],[50,578],[51,13],[51,25],[51,28],[51,49],[51,52],[52,88],[53,13],[53,21],[53,276],[53,280],[54,21],[54,25],[54,28],[54,521],[56,13],[56,73],[56,577],[56,584],[57,52],[57,145],[57,176],[58,276],[58,304],[60,389],[61,389],[63,73],[63,88],[63,145],[63,208],[64,25],[64,88],[64,521],[64,584],[66,49],[66,81],[66,161],[66,176],[66,193],[66,208],[67,49],[67,145],[67,304],[67,400],[69,86],[70,262],[70,266],[70,280],[71,14],[71,266],[71,268],[71,290],[72,14],[72,74],[72,518],[72,524],[72,578],[72,584],[73,266],[73,268],[73,522],[73,524],[74,38],[75,304],[77,162],[77,292],[77,416],[79,154],[80,74],[80,88],[80,266],[80,280],[80,338],[81,154],[81,280],[82,74],[82,194],[82,266],[82,456],[83,114],[84,162],[84,290],[84,386],[84,400],[85,338],[86,28],[86,52],[86,280],[87,28],[87,596],[88,52],[88,276],[88,292],[88,416],[89,88],[89,456]],\"owners\":[[34,7,[0,1,23,26,27,29,30,31,32,35],[2,25,28]],[3,11,[0,4,23,24,26,36,38,39,40,42],[37,41]],[37,11,[0,4,24,26,40,42],[3,23,36,38,39,41]],[41,11,[0,4,23,24,26,36,39,40],[3,37,38,42]],[9,13,[0,8,24,25,26,51,52,53,55],[56]],[51,13,[0,9,25,26,56],[8,24,52,53,55]],[53,13,[0,9,24,25,56],[8,26,51,52,55]],[56,13,[0,8,24,26,51,53,55],[9,25,52]],[72,14,[0,15,23,24,68,70,71],[16,25,69]],[32,35,[5,36,43,44,48],[1,24,27,33,40,45,49]],[33,35,[5,36,40,43,44,45,48,49],[1,24,27,32]],[49,35,[1,24,27,33,36,43],[5,32,40,44,45,48]],[31,37,[10,51,55,58],[1,24,32,33,57,61]],[33,37,[10,51,55,57,58,61],[1,24,31,32]],[33,38,[17,68,71,74,75,77],[1,24,27,31]],[74,38,[1,17,24,33,71],[27,31,68,75,77]],[2,517,[9,54,56,59],[33,34]],[33,517,[9,54,56,59],[2,34]],[72,518,[2,33],[16,34,73]],[6,67,[3,7,25,28,34,37,43],[46,48]],[25,67,[6,7,43,46,48],[3,28,34,37]],[48,67,[3,7,25,28,34,37],[6,43,46]],[56,73,[3,11,41,63],[12,25,52]],[18,74,[3,25,37,41,69,79,80,82],[72]],[54,521,[4,12],[9,64]],[64,521,[4,9],[12,54]],[18,522,[4,16,73],[]],[73,522,[4,18],[16]],[50,131,[5,29,31,35,38,42,44,47,49],[6,41,46]],[5,161,[13,57,61,66,67],[31,48,49]],[49,161,[13,57,66],[5,31,48,61,67]],[66,161,[5,31,49,61],[13,48,57,67]],[5,162,[19,74,77,83,84],[31,44,48]],[48,162,[19,74,77,84],[5,31,44,83]],[77,162,[5,44,48,83],[19,31,74,84]],[84,162,[5,31,48],[19,44,74,77,83]],[50,193,[14,63,66],[6,41,48]],[66,193,[6,41,50],[14,48,63]],[6,194,[79,82,83,85],[41,46,48,50]],[41,194,[83,85],[6,46,48,50,79,82]],[46,194,[82],[6,41,48,50,79,83,85]],[48,194,[79,82,85],[6,41,46,50,83]],[50,194,[79,82,83,85],[6,41,46,48]],[82,194,[6,46,48,50,83],[41,79,85]],[7,577,[12,56,59,64],[34,50]],[12,577,[7,34,50,59],[56,64]],[34,577,[12,64],[7,50,56,59]],[56,577,[7,50],[12,34,59,64]],[7,578,[18,72],[34,50]],[18,578,[7,34,50],[72]],[34,578,[18],[7,50,72]],[50,578,[18,72],[7,34]],[72,578,[7,50],[18,34]],[8,21,[10,27,28,29,30,57,58,59,60],[23,52,53,54]],[53,21,[10,27,28,29,57,59],[8,23,30,52,54,58,60]],[54,21,[10,27,28,29,30,57,58,60],[8,23,52,53,59]],[51,25,[11,37,38,39,63,64,65],[8,23,36,53,54,62]],[54,25,[11,36,37,38,39,62,63,65],[8,23,51,53,64]],[64,25,[8,23,36,38,39,51,53,62,65],[11,37,54,63]],[20,28,[8,23,51,52,54,68,69,87],[70,86]],[51,28,[20,69,70,87],[8,23,52,54,68,86]],[54,28,[20,68,69,70,86],[8,23,51,52,87]],[86,28,[8,23,52,54,69,87],[20,51,68,70]],[72,524,[9,54],[16,56,73,87]],[73,524,[9,54,56,87],[16,72]],[51,49,[13,43,44,45,66,67],[10,27,36,58,62]],[66,49,[10,27,36,45,51,58,62],[13,43,44,67]],[67,49,[10,27,36,43,51],[13,44,45,58,62,66]],[51,52,[21,74,75,88],[10,27,57,68,86]],[57,52,[21,68,75,86],[10,27,51,74,88]],[86,52,[10,27,57,74],[21,51,68,75,88]],[88,52,[10,27,51,68],[21,57,74,75,86]],[66,81,[11,28,37,52,59,64],[14,43,46]],[11,88,[69,79,80,87,89],[37,52,63,64]],[37,88,[87,89],[11,52,63,64,69,79,80]],[52,88,[79,80,89],[11,37,63,64,69,87]],[63,88,[69,80,87],[11,37,52,64,79,89]],[64,88,[69,79,80,89],[11,37,52,63,87]],[80,88,[11,52,63,64,87],[37,69,79,89]],[89,88,[11,37,52,64,69,87],[63,79,80]],[56,584,[18],[12,64,72,87]],[64,584,[18,72],[12,56,87]],[72,584,[12,64],[18,56,87]],[57,145,[14,38,46,47,63,65],[13,29,44,60,67]],[63,145,[13,29,44,47,57,60,67],[14,38,46,65]],[67,145,[14,29,38,46,63],[13,44,47,57,60,65]],[57,176,[22,83,84],[13,44,66,74,88]],[66,176,[22,74,84,88],[13,44,57,83]],[14,208,[79,83,85,89],[46,63,66]],[63,208,[83,85],[14,46,66,79,89]],[66,208,[79,85,89],[14,46,63,83]],[17,262,[15,26,30,35,70,73,76],[32,75,77]],[70,262,[17,32,35,77],[15,26,30,73,75,76]],[70,266,[40,42,82],[15,26,39,71,73,78,80,81]],[71,266,[39,42,80,81,82],[15,26,40,70,73,78]],[73,266,[39,40,42,78,80,81,82],[15,26,70,71]],[80,266,[15,26,40,42,71,73],[39,70,78,81,82]],[20,268,[15,26,55,71,73],[53,86]],[71,268,[20,53],[15,26,55,73,86]],[73,268,[20,53,55,86],[15,26,71]],[32,290,[19,78,84],[17,40,45,49,71,75]],[49,290,[17,71,75,78],[19,32,40,45,84]],[71,290,[19,45,49,84],[17,32,40,75,78]],[84,290,[17,32,40,71],[19,45,49,75,78]],[17,292,[21,55,58,61,86,88],[32,71,77]],[77,292,[21,55,58,86],[17,32,61,71,88]],[88,292,[17,32,55,71],[21,58,61,77,86]],[19,386,[35,42,47,76,81,82,85],[49,77,84]],[84,386,[35,42,82],[19,47,49,76,77,81,85]],[77,416,[22,67],[19,49,61,88]],[88,416,[19,49],[22,61,67,77]],[53,276,[21,75,76,88],[20,30,58,60,70]],[58,276,[20,70,76],[21,30,53,60,75,88]],[88,276,[20,30,53,70],[21,58,60,75,76]],[53,280,[78,80,81,89],[20,39,62,65,70,86]],[70,280,[62,65,89],[20,39,53,78,80,81,86]],[80,280,[20,53,62,65,86],[39,70,78,81,89]],[81,280,[20,53,62,86],[39,65,70,78,80,89]],[86,280,[39,65,80,81,89],[20,53,62,70,78]],[58,304,[22,78,84],[21,45,62,67,75,86]],[67,304,[21,75,78,86],[22,45,58,62,84]],[75,304,[22,62,67],[21,45,58,78,84,86]],[67,400,[76,81,85,89],[22,47,60,65,84,88]],[84,400,[60,65,89],[22,47,67,76,81,85,88]],[28,86,[69],[]],[69,86,[28],[]],[39,275,[30,45,47],[]],[47,275,[30,39,45],[]],[60,389,[35,61],[]],[61,389,[35,60],[]],[36,58,[68,78],[]],[79,154,[38,81],[]],[81,154,[38,79],[]],[42,393,[65],[]],[43,114,[83],[]],[83,114,[43],[]],[87,596,[59],[]],[80,338,[85],[]],[85,338,[80],[]],[82,456,[89],[]],[89,456,[82],[]]],\"edges\":[[31,[11,14,28,37,43,46,52,59,63,64,66,69,79,80,83,85,87,89]],[39,[6,14,41,46,48,50,63,66,79,82,83,85,89]],[41,[7,12,18,34,50,56,59,64,72,87]]],\"groupings\":[1,2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00114.record009" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00114.record009\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-25,-3],[-26,-25],[-27,-25],[-32,-28],[-33,-27],[-33,-28],[-33,-32],[-34,-1],[-34,-24],[-34,-25],[-34,-26],[-34,-27],[-34,-28],[-34,-29],[-34,-30],[-34,-31],[-34,-32],[-34,-33],[-35,-5],[-35,-8],[-35,-25],[-35,-26],[-35,-34],[-36,-33],[-36,-34],[-38,-13],[-39,-28],[-40,-33],[-41,-32],[-41,-33],[-42,-8],[-42,-26],[-42,-35],[-42,-38],[-43,-33],[-46,-45],[-47,-28],[-47,-38],[-47,-45],[-48,-33],[-49,-6],[-49,-7],[-49,-32],[-49,-45],[-50,-6],[-50,-27],[-50,-31],[-50,-32],[-50,-40],[-50,-41],[-50,-43],[-50,-45],[-50,-46],[-50,-49],[-51,-4],[-51,-7],[-51,-8],[-51,-26],[-51,-35],[-51,-38],[-51,-49],[-52,-9],[-52,-24],[-52,-25],[-52,-28],[-52,-37],[-52,-41],[-53,-26],[-53,-35],[-53,-38],[-53,-52],[-54,-27],[-54,-40],[-54,-43],[-54,-46],[-54,-50],[-54,-52],[-55,-10],[-55,-26],[-55,-27],[-55,-52],[-55,-54],[-56,-50],[-56,-52],[-57,-26],[-57,-35],[-57,-38],[-58,-28],[-58,-45],[-58,-52],[-59,-27],[-59,-28],[-59,-40],[-59,-41],[-59,-43],[-59,-50],[-59,-52],[-59,-54],[-59,-58],[-60,-52],[-60,-55],[-61,-33],[-62,-50],[-62,-59],[-63,-33],[-63,-50],[-63,-52],[-63,-59],[-64,-29],[-64,-42],[-64,-44],[-64,-53],[-64,-60],[-65,-12],[-65,-38],[-65,-42],[-65,-57],[-65,-64],[-66,-33],[-66,-50],[-66,-54],[-66,-59],[-67,-39],[-67,-44],[-67,-45],[-67,-47],[-67,-48],[-67,-49],[-67,-58],[-67,-61],[-67,-64],[-67,-66],[-68,-27],[-68,-40],[-68,-41],[-68,-43],[-68,-45],[-68,-50],[-68,-58],[-68,-63],[-68,-66],[-68,-67],[-69,-45],[-69,-52],[-70,-35],[-71,-27],[-71,-28],[-71,-37],[-71,-39],[-71,-44],[-71,-45],[-71,-47],[-71,-48],[-71,-54],[-71,-56],[-71,-70],[-72,-25],[-72,-27],[-72,-33],[-72,-36],[-72,-37],[-72,-41],[-72,-52],[-72,-56],[-72,-63],[-72,-69],[-72,-71],[-73,-5],[-73,-19],[-73,-27],[-73,-29],[-73,-35],[-73,-53],[-73,-57],[-73,-60],[-73,-70],[-74,-1],[-74,-24],[-74,-25],[-74,-27],[-74,-69],[-74,-70],[-74,-71],[-74,-72],[-74,-73],[-75,-50],[-76,-18],[-76,-33],[-76,-47],[-76,-59],[-76,-71],[-76,-72],[-77,-71],[-77,-72],[-78,-30],[-78,-33],[-78,-50],[-78,-58],[-78,-62],[-78,-72],[-78,-76],[-79,-52],[-79,-71],[-79,-78],[-80,-28],[-80,-38],[-80,-45],[-80,-71],[-80,-76],[-81,-28],[-82,-28],[-82,-38],[-82,-45],[-82,-71],[-82,-76],[-84,-45],[-84,-50],[-84,-67],[-84,-71],[-85,-37],[-85,-39],[-85,-40],[-85,-45],[-85,-46],[-85,-47],[-85,-48],[-85,-50],[-85,-62],[-85,-68],[-85,-69],[-85,-71],[-85,-75],[-85,-77],[-85,-78],[-85,-79],[-85,-80],[-85,-81],[-85,-82],[-85,-84],[-86,-24],[-86,-28],[-86,-30],[-86,-37],[-86,-44],[-86,-45],[-86,-69],[-86,-71],[-86,-75],[-86,-76],[-86,-79],[-86,-84],[-86,-85],[-87,-25],[-87,-37],[-87,-52],[-87,-54],[-87,-59],[-87,-71],[-87,-72],[-87,-76],[-88,-35],[-88,-55],[-88,-73],[-89,-32],[-89,-59],[-89,-62],[-89,-68],[-89,-76],[-89,-85],[-89,-87],[-35,1,2,24,27,28,30,31,32,33,36],[-1,-32,-35],[-1,-33,-35],[-24,-32,-35],[-24,-33,-35],[-27,-32,-35],[-4,1,5,24,25,27,37,39,40,41,43],[-38,1,5,25,27,41,43],[-42,1,5,24,25,27,37,40,41],[-10,1,9,25,26,27,52,53,54,56],[-52,1,10,26,27,57],[-54,1,10,25,26,57],[-57,1,9,25,27,52,54,56],[-9,-27,-57],[-27,-52,-57],[-73,1,16,24,25,69,71,72],[-1,-72,-73],[-24,-72,-73],[-33,6,37,44,45,49],[-34,6,37,41,44,45,46,49,50],[-50,2,25,28,34,37,44],[-6,-34,-37],[-6,-34,-41],[-6,-34,-46],[-34,-37,-50],[-34,-44,-50],[-32,11,52,56,59],[-34,11,52,56,58,59,62],[-34,18,69,72,75,76,78],[-75,2,18,25,34,72],[-5,-34,-51],[-3,10,55,57,60],[-34,10,55,57,60],[-73,3,34],[-7,4,8,26,29,35,38,44],[-26,7,8,44,47,49],[-49,4,8,26,29,35,38],[-8,-38,-49],[-57,4,12,42,64],[-4,-57,-64],[-12,-42,-57],[-19,4,26,38,42,70,80,81,83],[-19,-38,-83],[-42,-73,-81],[-55,5,13],[-65,5,10],[-19,5,17,74],[-74,5,19],[-51,6,30,32,36,39,43,45,48,50],[-39,-50,-51],[-6,14,58,62,67,68],[-50,14,58,67],[-67,6,32,50,62],[-6,20,75,78,84,85],[-49,20,75,78,85],[-78,6,45,49,84],[-85,6,32,49],[-51,15,64,67],[-67,7,42,51],[-7,80,83,84,86],[-42,84,86],[-47,83],[-49,80,83,86],[-51,80,83,84,86],[-83,7,47,49,51,84],[-8,13,57,60,65],[-13,8,35,51,60],[-35,13,65],[-57,8,51],[-8,19,73],[-19,8,35,51],[-35,19],[-51,19,73],[-73,8,51],[-9,11,28,29,30,31,58,59,60,61],[-54,11,28,29,30,58,60],[-55,11,28,29,30,31,58,59,61],[-52,12,38,39,40,64,65,66],[-55,12,37,38,39,40,63,64,66],[-65,9,24,37,39,40,52,54,63,66],[-21,9,24,52,53,55,69,70,88],[-52,21,70,71,88],[-55,21,69,70,71,87],[-87,9,24,53,55,70,88],[-21,-52,-88],[-73,10,55],[-74,10,55,57,88],[-52,14,44,45,46,67,68],[-67,11,28,37,46,52,59,63],[-68,11,28,37,44,52],[-46,-52,-67],[-52,22,75,76,89],[-58,22,69,76,87],[-87,11,28,58,75],[-89,11,28,52,69],[-67,12,29,38,53,60,65],[-12,70,80,81,88,90],[-38,88,90],[-53,80,81,90],[-64,70,81,88],[-65,70,80,81,90],[-81,12,53,64,65,88],[-90,12,38,53,65,70,88],[-57,19],[-65,19,73],[-73,13,65],[-58,15,39,47,48,64,66],[-64,14,30,45,48,58,61,68],[-68,15,30,39,47,64],[-58,23,84,85],[-67,23,75,85,89],[-15,80,84,86,90],[-64,84,86],[-67,80,86,90],[-18,16,27,31,36,71,74,77],[-71,18,33,36,78],[-71,41,43,83],[-72,40,43,81,82,83],[-74,40,41,43,79,81,82,83],[-81,16,27,41,43,72,74],[-40,-74,-83],[-41,-74,-83],[-21,16,27,56,72,74],[-72,21,54],[-74,21,54,56,87],[-33,20,79,85],[-50,18,72,76,79],[-72,20,46,50,85],[-85,18,33,41,72],[-18,22,56,59,62,87,89],[-78,22,56,59,87],[-89,18,33,56,72],[-20,36,43,48,77,82,83,86],[-85,36,43,83],[-78,23,68],[-89,20,50],[-54,22,76,77,89],[-59,21,71,77],[-89,21,31,54,71],[-54,79,81,82,90],[-71,63,66,90],[-81,21,54,63,66,87],[-82,21,54,63,87],[-87,40,66,81,82,90],[-59,23,79,85],[-68,22,76,79,87],[-76,23,63,68],[-68,77,82,86,90],[-85,61,66,90],[-29,70],[-70,29],[-40,31,46,48],[-48,31,40,46],[-61,36,62],[-62,36,61],[-37,69,79],[-80,39,82],[-82,39,80],[-43,66],[-44,84],[-84,44],[-88,60],[-81,86],[-86,81],[-83,90],[-90,83],[-2,91],[-3,92],[-93,6],[-6,93],[-94,7],[-95,8],[-8,95],[-10,96],[-12,97],[-13,98],[-14,99],[-16,100],[-18,101],[-19,102],[-20,103],[-21,104],[-22,105],[-23,106],[-91,107],[-92,108],[-108,109],[-107,-108,110],[-111,94,95],[-95,111],[-112,93,111],[-111,112],[-93,112],[-96,113],[-113,114],[-114,115],[-112,115],[-112,-114,116],[-115,117],[-116,118],[-109,-115,118],[-110,-115,119],[-98,120],[-98,-99,121],[-120,122],[-121,123],[-97,122],[-100,124],[-124,125],[-125,126],[-122,126],[-122,-125,127],[-123,127],[-103,128],[-102,128],[-128,129],[-101,129],[-101,-128,130],[-106,131],[-105,131],[-131,132],[-104,132],[-104,-131,133],[-132,134],[-133,135],[-129,-132,135],[-129,-133,136],[-130,-132,136],[-136,138],[-126,-134,137],[-126,-135,138],[-126,-136,139],[-127,-135,139],[-117,-139,140],[-118,-138,140],[-119,-137,140],[-140],[-141,42,47,49,51],[-51,141],[-142,64,67],[-67,142],[-143,26,27,73,74],[-73,143],[-144,25,34,35],[-25,144],[-34,144],[-145,32,58,78,89],[-89,145],[-146,52,72,87],[-52,146],[-147,53,55,57,65],[-65,147],[-148,33,50,54,59,68],[-50,148],[-149,24,28,38,45,71,76,85],[-38,149],[-71,149],[-76,149],[-150,141,142],[-151,141],[-151,142],[-141,-142,151],[-152,143,144],[-153,143],[-153,144],[-143,-144,153],[-154,150],[-154,151,153],[-155,151],[-154,152],[-155,153],[-151,-153,155],[-156,145,146],[-157,145],[-157,146],[-145,-146,157],[-158,148,149],[-159,148],[-159,149],[-148,-149,159],[-160,147,159],[-161,147],[-160,158],[-161,159],[-147,-159,161],[-162,156],[-162,157,161],[-163,157],[-162,160],[-163,161],[-157,-161,163],[-164,154],[-164,155,163],[-164,162],[-155,-163,165],[164],[-165],[-166,29,60],[-29,166],[-60,166],[-167,70,88],[-70,167],[-88,167],[-168,39,43,83],[-39,168],[-43,168],[-83,168],[-169,66,80,90],[-66,169],[-80,169],[-90,169],[-170,31,36,41],[-31,170],[-36,170],[-41,170],[-171,40,56,61],[-40,171],[-56,171],[-61,171],[-172,46,62,63],[-46,172],[-62,172],[-63,172],[-173,30,37,44,48,81,82],[-37,173],[-44,173],[-81,173],[-174,69,75,84,86],[-69,174],[-84,174],[-86,174],[-175,77,79],[-77,175],[-79,175],[-176,166,167],[-167,176],[-166,176],[-177,169,170],[-170,177],[-169,177],[-178,170],[-179,168,177],[-177,179],[-180,168,178],[-168,179],[-168,-177,180],[-181,176,179],[-179,181],[-182,176,180],[-180,182],[-176,181],[-176,-180,183],[-184,171,172],[-172,184],[-171,184],[-185,174,175],[-175,185],[-174,185],[-186,173,185],[-185,186],[-173,186],[-173,-185,187],[-188,184,186],[-186,188],[-187,189],[-184,188],[-184,-186,189],[-184,-187,190],[-190,192],[-191,182,188],[-181,-189,192],[-182,-188,192],[-183,192],[191],[-192],[-3,-12,-13,-21,-28,-50,-51,-55,-67,-72,-73,-83,-89,-90],[-3,-12,-13,-21,-32,-51,-55,-59,-67,-72,-73,-83,-85,-90],[-3,-10,-11,-22,-32,-51,-54,-65,-67,-72,-73,-83,-85,-90],[-3,-9,-10,-21,-32,-51,-59,-65,-67,-72,-73,-83,-85,-90],[-3,-9,-10,-21,-28,-50,-51,-65,-67,-72,-73,-83,-89,-90],[-3,-6,-10,-20,-28,-51,-54,-65,-67,-72,-73,-83,-89,-90],[-3,-6,-10,-20,-33,-51,-52,-65,-67,-71,-73,-83,-89,-90],[-2,-3,-10,-18,-50,-51,-52,-65,-67,-71,-73,-83,-89,-90],[-8,-9,-11,-19,-34,-49,-57,-64,-68,-74,-78,-81,-86,-87],[-8,-11,-13,-19,-34,-49,-55,-64,-68,-74,-78,-81,-86,-87],[-8,-19,-21,-22,-34,-49,-52,-57,-64,-68,-74,-78,-81,-86],[-8,-11,-13,-16,-34,-49,-55,-64,-68,-73,-78,-81,-86,-87],[-8,-10,-15,-22,-34,-49,-54,-58,-65,-72,-73,-83,-85,-90],[-8,-10,-15,-22,-34,-49,-52,-65,-68,-71,-73,-78,-83,-90],[-7,-8,-10,-18,-34,-50,-52,-65,-67,-71,-73,-83,-89,-90],[-10,-17,-18,-19,-34,-50,-51,-52,-65,-67,-71,-83,-89,-90],[-12,-17,-18,-19,-34,-50,-51,-52,-57,-67,-71,-83,-89,-90],[-10,-18,-19,-21,-34,-50,-51,-52,-65,-67,-74,-80,-82,-89],[-12,-18,-19,-21,-34,-50,-51,-52,-57,-67,-74,-80,-82,-89],[-6,-9,-11,-19,-34,-51,-57,-64,-68,-74,-78,-81,-86,-87],[-6,-11,-13,-19,-34,-51,-55,-64,-68,-74,-78,-81,-86,-87],[-6,-19,-21,-22,-34,-51,-52,-57,-64,-68,-74,-78,-81,-86],[-10,-18,-19,-21,-34,-50,-51,-52,-65,-67,-74,-81,-86,-89],[-12,-18,-19,-21,-34,-50,-51,-52,-57,-67,-74,-81,-86,-89],[-14,-18,-19,-21,-34,-50,-51,-52,-57,-64,-74,-81,-86,-89],[-9,-18,-19,-23,-34,-50,-51,-57,-58,-64,-74,-81,-86,-87],[-13,-18,-19,-23,-34,-50,-51,-55,-58,-64,-74,-81,-86,-87],[-10,-18,-19,-21,-34,-50,-51,-52,-65,-67,-74,-83,-89,-90],[-10,-19,-21,-23,-34,-50,-51,-52,-65,-67,-74,-76,-83,-90],[-12,-18,-19,-21,-34,-50,-51,-52,-57,-67,-74,-83,-89,-90],[-12,-19,-21,-23,-34,-50,-51,-52,-57,-67,-74,-76,-83,-90],[-12,-13,-15,-19,-33,-35,-49,-55,-58,-74,-83,-85,-87,-90],[-12,-13,-15,-19,-28,-35,-49,-55,-68,-74,-78,-83,-87,-90],[-13,-19,-20,-23,-33,-35,-49,-55,-58,-64,-74,-81,-86,-87],[-2,-11,-13,-19,-35,-49,-55,-64,-68,-74,-78,-81,-86,-87],[-9,-10,-15,-19,-33,-35,-49,-58,-65,-74,-83,-85,-87,-90],[-9,-10,-15,-19,-28,-35,-49,-65,-68,-74,-78,-83,-87,-90],[-10,-12,-13,-18,-34,-50,-51,-52,-67,-71,-73,-83,-89,-90],[-6,-10,-15,-22,-34,-51,-54,-58,-65,-72,-73,-83,-85,-90],[-6,-10,-15,-22,-34,-51,-52,-65,-68,-71,-73,-78,-83,-90],[-10,-14,-15,-18,-34,-50,-51,-52,-65,-71,-73,-83,-89,-90],[-10,-11,-15,-20,-34,-45,-51,-54,-65,-72,-73,-83,-89,-90],[-6,-10,-11,-20,-34,-51,-54,-65,-67,-72,-73,-80,-82,-89],[-6,-10,-11,-20,-34,-51,-54,-65,-67,-72,-73,-81,-86,-89],[-6,-9,-10,-21,-34,-51,-59,-65,-67,-72,-73,-83,-85,-90],[-6,-9,-10,-23,-34,-51,-59,-65,-67,-71,-73,-78,-83,-90],[-6,-10,-22,-23,-34,-51,-52,-65,-67,-71,-73,-78,-83,-90],[-6,-10,-18,-20,-34,-51,-52,-65,-67,-71,-73,-83,-89,-90],[-6,-10,-11,-22,-34,-51,-54,-65,-67,-72,-73,-83,-85,-90],[-6,-10,-11,-20,-34,-51,-54,-65,-67,-72,-73,-83,-89,-90],[-9,-10,-11,-21,-34,-50,-51,-65,-67,-72,-73,-80,-82,-89],[-9,-10,-11,-21,-34,-50,-51,-65,-67,-72,-73,-81,-86,-89],[-9,-10,-11,-21,-34,-50,-51,-65,-67,-72,-73,-83,-89,-90],[-9,-10,-11,-18,-34,-50,-51,-65,-67,-71,-73,-83,-89,-90],[-10,-16,-18,-21,-34,-50,-51,-52,-65,-67,-73,-80,-82,-89],[-10,-16,-18,-21,-34,-50,-51,-52,-65,-67,-73,-81,-86,-89],[-10,-16,-18,-21,-34,-50,-51,-52,-65,-67,-73,-83,-89,-90],[-10,-16,-21,-23,-34,-50,-51,-52,-65,-67,-73,-76,-83,-90],[-10,-18,-22,-23,-34,-50,-51,-52,-65,-67,-71,-73,-83,-90],[-11,-12,-13,-21,-34,-50,-51,-55,-67,-72,-73,-80,-82,-89],[-11,-12,-13,-21,-34,-50,-51,-55,-67,-72,-73,-81,-86,-89],[-11,-12,-13,-21,-34,-50,-51,-55,-67,-72,-73,-83,-89,-90],[-11,-12,-13,-18,-34,-50,-51,-55,-67,-71,-73,-83,-89,-90],[-6,-12,-13,-21,-34,-51,-55,-59,-67,-72,-73,-83,-85,-90],[-6,-12,-13,-23,-34,-51,-55,-59,-67,-71,-73,-78,-83,-90],[-13,-21,-22,-23,-34,-50,-51,-55,-58,-64,-72,-73,-81,-86],[-11,-13,-14,-21,-34,-50,-51,-55,-64,-72,-73,-81,-86,-89],[-13,-16,-18,-23,-34,-50,-51,-55,-58,-64,-73,-81,-86,-87],[-6,-11,-13,-16,-34,-51,-55,-64,-68,-73,-78,-81,-86,-87],[12,15,29,38,44,47,53,60,64,65,67,70,80,81,84,86,88,90],[7,15,42,47,49,51,64,67,80,83,84,86,90],[8,13,19,35,51,57,60,65,73,88]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"index\":1,\"kind\":1},{\"tag\":\"group\",\"index\":2,\"kind\":1},{\"tag\":\"group\",\"index\":5,\"kind\":1},{\"tag\":\"group\",\"index\":6,\"kind\":1},{\"tag\":\"group\",\"index\":7,\"kind\":1},{\"tag\":\"group\",\"index\":9,\"kind\":1},{\"tag\":\"group\",\"index\":11,\"kind\":1},{\"tag\":\"group\",\"index\":12,\"kind\":1},{\"tag\":\"group\",\"index\":13,\"kind\":1},{\"tag\":\"group\",\"index\":15,\"kind\":1},{\"tag\":\"group\",\"index\":17,\"kind\":1},{\"tag\":\"group\",\"index\":18,\"kind\":1},{\"tag\":\"group\",\"index\":19,\"kind\":1},{\"tag\":\"group\",\"index\":20,\"kind\":1},{\"tag\":\"group\",\"index\":21,\"kind\":1},{\"tag\":\"group\",\"index\":22,\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":24,\"b\":2},{\"tag\":\"incompatible\",\"a\":25,\"b\":24},{\"tag\":\"incompatible\",\"a\":26,\"b\":24},{\"tag\":\"incompatible\",\"a\":31,\"b\":27},{\"tag\":\"incompatible\",\"a\":32,\"b\":26},{\"tag\":\"incompatible\",\"a\":32,\"b\":27},{\"tag\":\"incompatible\",\"a\":32,\"b\":31},{\"tag\":\"incompatible\",\"a\":33,\"b\":0},{\"tag\":\"incompatible\",\"a\":33,\"b\":23},{\"tag\":\"incompatible\",\"a\":33,\"b\":24},{\"tag\":\"incompatible\",\"a\":33,\"b\":25},{\"tag\":\"incompatible\",\"a\":33,\"b\":26},{\"tag\":\"incompatible\",\"a\":33,\"b\":27},{\"tag\":\"incompatible\",\"a\":33,\"b\":28},{\"tag\":\"incompatible\",\"a\":33,\"b\":29},{\"tag\":\"incompatible\",\"a\":33,\"b\":30},{\"tag\":\"incompatible\",\"a\":33,\"b\":31},{\"tag\":\"incompatible\",\"a\":33,\"b\":32},{\"tag\":\"incompatible\",\"a\":34,\"b\":4},{\"tag\":\"incompatible\",\"a\":34,\"b\":7},{\"tag\":\"incompatible\",\"a\":34,\"b\":24},{\"tag\":\"incompatible\",\"a\":34,\"b\":25},{\"tag\":\"incompatible\",\"a\":34,\"b\":33},{\"tag\":\"incompatible\",\"a\":35,\"b\":32},{\"tag\":\"incompatible\",\"a\":35,\"b\":33},{\"tag\":\"incompatible\",\"a\":37,\"b\":12},{\"tag\":\"incompatible\",\"a\":38,\"b\":27},{\"tag\":\"incompatible\",\"a\":39,\"b\":32},{\"tag\":\"incompatible\",\"a\":40,\"b\":31},{\"tag\":\"incompatible\",\"a\":40,\"b\":32},{\"tag\":\"incompatible\",\"a\":41,\"b\":7},{\"tag\":\"incompatible\",\"a\":41,\"b\":25},{\"tag\":\"incompatible\",\"a\":41,\"b\":34},{\"tag\":\"incompatible\",\"a\":41,\"b\":37},{\"tag\":\"incompatible\",\"a\":42,\"b\":32},{\"tag\":\"incompatible\",\"a\":45,\"b\":44},{\"tag\":\"incompatible\",\"a\":46,\"b\":27},{\"tag\":\"incompatible\",\"a\":46,\"b\":37},{\"tag\":\"incompatible\",\"a\":46,\"b\":44},{\"tag\":\"incompatible\",\"a\":47,\"b\":32},{\"tag\":\"incompatible\",\"a\":48,\"b\":5},{\"tag\":\"incompatible\",\"a\":48,\"b\":6},{\"tag\":\"incompatible\",\"a\":48,\"b\":31},{\"tag\":\"incompatible\",\"a\":48,\"b\":44},{\"tag\":\"incompatible\",\"a\":49,\"b\":5},{\"tag\":\"incompatible\",\"a\":49,\"b\":26},{\"tag\":\"incompatible\",\"a\":49,\"b\":30},{\"tag\":\"incompatible\",\"a\":49,\"b\":31},{\"tag\":\"incompatible\",\"a\":49,\"b\":39},{\"tag\":\"incompatible\",\"a\":49,\"b\":40},{\"tag\":\"incompatible\",\"a\":49,\"b\":42},{\"tag\":\"incompatible\",\"a\":49,\"b\":44},{\"tag\":\"incompatible\",\"a\":49,\"b\":45},{\"tag\":\"incompatible\",\"a\":49,\"b\":48},{\"tag\":\"incompatible\",\"a\":50,\"b\":3},{\"tag\":\"incompatible\",\"a\":50,\"b\":6},{\"tag\":\"incompatible\",\"a\":50,\"b\":7},{\"tag\":\"incompatible\",\"a\":50,\"b\":25},{\"tag\":\"incompatible\",\"a\":50,\"b\":34},{\"tag\":\"incompatible\",\"a\":50,\"b\":37},{\"tag\":\"incompatible\",\"a\":50,\"b\":48},{\"tag\":\"incompatible\",\"a\":51,\"b\":8},{\"tag\":\"incompatible\",\"a\":51,\"b\":23},{\"tag\":\"incompatible\",\"a\":51,\"b\":24},{\"tag\":\"incompatible\",\"a\":51,\"b\":27},{\"tag\":\"incompatible\",\"a\":51,\"b\":36},{\"tag\":\"incompatible\",\"a\":51,\"b\":40},{\"tag\":\"incompatible\",\"a\":52,\"b\":25},{\"tag\":\"incompatible\",\"a\":52,\"b\":34},{\"tag\":\"incompatible\",\"a\":52,\"b\":37},{\"tag\":\"incompatible\",\"a\":52,\"b\":51},{\"tag\":\"incompatible\",\"a\":53,\"b\":26},{\"tag\":\"incompatible\",\"a\":53,\"b\":39},{\"tag\":\"incompatible\",\"a\":53,\"b\":42},{\"tag\":\"incompatible\",\"a\":53,\"b\":45},{\"tag\":\"incompatible\",\"a\":53,\"b\":49},{\"tag\":\"incompatible\",\"a\":53,\"b\":51},{\"tag\":\"incompatible\",\"a\":54,\"b\":9},{\"tag\":\"incompatible\",\"a\":54,\"b\":25},{\"tag\":\"incompatible\",\"a\":54,\"b\":26},{\"tag\":\"incompatible\",\"a\":54,\"b\":51},{\"tag\":\"incompatible\",\"a\":54,\"b\":53},{\"tag\":\"incompatible\",\"a\":55,\"b\":49},{\"tag\":\"incompatible\",\"a\":55,\"b\":51},{\"tag\":\"incompatible\",\"a\":56,\"b\":25},{\"tag\":\"incompatible\",\"a\":56,\"b\":34},{\"tag\":\"incompatible\",\"a\":56,\"b\":37},{\"tag\":\"incompatible\",\"a\":57,\"b\":27},{\"tag\":\"incompatible\",\"a\":57,\"b\":44},{\"tag\":\"incompatible\",\"a\":57,\"b\":51},{\"tag\":\"incompatible\",\"a\":58,\"b\":26},{\"tag\":\"incompatible\",\"a\":58,\"b\":27},{\"tag\":\"incompatible\",\"a\":58,\"b\":39},{\"tag\":\"incompatible\",\"a\":58,\"b\":40},{\"tag\":\"incompatible\",\"a\":58,\"b\":42},{\"tag\":\"incompatible\",\"a\":58,\"b\":49},{\"tag\":\"incompatible\",\"a\":58,\"b\":51},{\"tag\":\"incompatible\",\"a\":58,\"b\":53},{\"tag\":\"incompatible\",\"a\":58,\"b\":57},{\"tag\":\"incompatible\",\"a\":59,\"b\":51},{\"tag\":\"incompatible\",\"a\":59,\"b\":54},{\"tag\":\"incompatible\",\"a\":60,\"b\":32},{\"tag\":\"incompatible\",\"a\":61,\"b\":49},{\"tag\":\"incompatible\",\"a\":61,\"b\":58},{\"tag\":\"incompatible\",\"a\":62,\"b\":32},{\"tag\":\"incompatible\",\"a\":62,\"b\":49},{\"tag\":\"incompatible\",\"a\":62,\"b\":51},{\"tag\":\"incompatible\",\"a\":62,\"b\":58},{\"tag\":\"incompatible\",\"a\":63,\"b\":28},{\"tag\":\"incompatible\",\"a\":63,\"b\":41},{\"tag\":\"incompatible\",\"a\":63,\"b\":43},{\"tag\":\"incompatible\",\"a\":63,\"b\":52},{\"tag\":\"incompatible\",\"a\":63,\"b\":59},{\"tag\":\"incompatible\",\"a\":64,\"b\":11},{\"tag\":\"incompatible\",\"a\":64,\"b\":37},{\"tag\":\"incompatible\",\"a\":64,\"b\":41},{\"tag\":\"incompatible\",\"a\":64,\"b\":56},{\"tag\":\"incompatible\",\"a\":64,\"b\":63},{\"tag\":\"incompatible\",\"a\":65,\"b\":32},{\"tag\":\"incompatible\",\"a\":65,\"b\":49},{\"tag\":\"incompatible\",\"a\":65,\"b\":53},{\"tag\":\"incompatible\",\"a\":65,\"b\":58},{\"tag\":\"incompatible\",\"a\":66,\"b\":38},{\"tag\":\"incompatible\",\"a\":66,\"b\":43},{\"tag\":\"incompatible\",\"a\":66,\"b\":44},{\"tag\":\"incompatible\",\"a\":66,\"b\":46},{\"tag\":\"incompatible\",\"a\":66,\"b\":47},{\"tag\":\"incompatible\",\"a\":66,\"b\":48},{\"tag\":\"incompatible\",\"a\":66,\"b\":57},{\"tag\":\"incompatible\",\"a\":66,\"b\":60},{\"tag\":\"incompatible\",\"a\":66,\"b\":63},{\"tag\":\"incompatible\",\"a\":66,\"b\":65},{\"tag\":\"incompatible\",\"a\":67,\"b\":26},{\"tag\":\"incompatible\",\"a\":67,\"b\":39},{\"tag\":\"incompatible\",\"a\":67,\"b\":40},{\"tag\":\"incompatible\",\"a\":67,\"b\":42},{\"tag\":\"incompatible\",\"a\":67,\"b\":44},{\"tag\":\"incompatible\",\"a\":67,\"b\":49},{\"tag\":\"incompatible\",\"a\":67,\"b\":57},{\"tag\":\"incompatible\",\"a\":67,\"b\":62},{\"tag\":\"incompatible\",\"a\":67,\"b\":65},{\"tag\":\"incompatible\",\"a\":67,\"b\":66},{\"tag\":\"incompatible\",\"a\":68,\"b\":44},{\"tag\":\"incompatible\",\"a\":68,\"b\":51},{\"tag\":\"incompatible\",\"a\":69,\"b\":34},{\"tag\":\"incompatible\",\"a\":70,\"b\":26},{\"tag\":\"incompatible\",\"a\":70,\"b\":27},{\"tag\":\"incompatible\",\"a\":70,\"b\":36},{\"tag\":\"incompatible\",\"a\":70,\"b\":38},{\"tag\":\"incompatible\",\"a\":70,\"b\":43},{\"tag\":\"incompatible\",\"a\":70,\"b\":44},{\"tag\":\"incompatible\",\"a\":70,\"b\":46},{\"tag\":\"incompatible\",\"a\":70,\"b\":47},{\"tag\":\"incompatible\",\"a\":70,\"b\":53},{\"tag\":\"incompatible\",\"a\":70,\"b\":55},{\"tag\":\"incompatible\",\"a\":70,\"b\":69},{\"tag\":\"incompatible\",\"a\":71,\"b\":24},{\"tag\":\"incompatible\",\"a\":71,\"b\":26},{\"tag\":\"incompatible\",\"a\":71,\"b\":32},{\"tag\":\"incompatible\",\"a\":71,\"b\":35},{\"tag\":\"incompatible\",\"a\":71,\"b\":36},{\"tag\":\"incompatible\",\"a\":71,\"b\":40},{\"tag\":\"incompatible\",\"a\":71,\"b\":51},{\"tag\":\"incompatible\",\"a\":71,\"b\":55},{\"tag\":\"incompatible\",\"a\":71,\"b\":62},{\"tag\":\"incompatible\",\"a\":71,\"b\":68},{\"tag\":\"incompatible\",\"a\":71,\"b\":70},{\"tag\":\"incompatible\",\"a\":72,\"b\":4},{\"tag\":\"incompatible\",\"a\":72,\"b\":18},{\"tag\":\"incompatible\",\"a\":72,\"b\":26},{\"tag\":\"incompatible\",\"a\":72,\"b\":28},{\"tag\":\"incompatible\",\"a\":72,\"b\":34},{\"tag\":\"incompatible\",\"a\":72,\"b\":52},{\"tag\":\"incompatible\",\"a\":72,\"b\":56},{\"tag\":\"incompatible\",\"a\":72,\"b\":59},{\"tag\":\"incompatible\",\"a\":72,\"b\":69},{\"tag\":\"incompatible\",\"a\":73,\"b\":0},{\"tag\":\"incompatible\",\"a\":73,\"b\":23},{\"tag\":\"incompatible\",\"a\":73,\"b\":24},{\"tag\":\"incompatible\",\"a\":73,\"b\":26},{\"tag\":\"incompatible\",\"a\":73,\"b\":68},{\"tag\":\"incompatible\",\"a\":73,\"b\":69},{\"tag\":\"incompatible\",\"a\":73,\"b\":70},{\"tag\":\"incompatible\",\"a\":73,\"b\":71},{\"tag\":\"incompatible\",\"a\":73,\"b\":72},{\"tag\":\"incompatible\",\"a\":74,\"b\":49},{\"tag\":\"incompatible\",\"a\":75,\"b\":17},{\"tag\":\"incompatible\",\"a\":75,\"b\":32},{\"tag\":\"incompatible\",\"a\":75,\"b\":46},{\"tag\":\"incompatible\",\"a\":75,\"b\":58},{\"tag\":\"incompatible\",\"a\":75,\"b\":70},{\"tag\":\"incompatible\",\"a\":75,\"b\":71},{\"tag\":\"incompatible\",\"a\":76,\"b\":70},{\"tag\":\"incompatible\",\"a\":76,\"b\":71},{\"tag\":\"incompatible\",\"a\":77,\"b\":29},{\"tag\":\"incompatible\",\"a\":77,\"b\":32},{\"tag\":\"incompatible\",\"a\":77,\"b\":49},{\"tag\":\"incompatible\",\"a\":77,\"b\":57},{\"tag\":\"incompatible\",\"a\":77,\"b\":61},{\"tag\":\"incompatible\",\"a\":77,\"b\":71},{\"tag\":\"incompatible\",\"a\":77,\"b\":75},{\"tag\":\"incompatible\",\"a\":78,\"b\":51},{\"tag\":\"incompatible\",\"a\":78,\"b\":70},{\"tag\":\"incompatible\",\"a\":78,\"b\":77},{\"tag\":\"incompatible\",\"a\":79,\"b\":27},{\"tag\":\"incompatible\",\"a\":79,\"b\":37},{\"tag\":\"incompatible\",\"a\":79,\"b\":44},{\"tag\":\"incompatible\",\"a\":79,\"b\":70},{\"tag\":\"incompatible\",\"a\":79,\"b\":75},{\"tag\":\"incompatible\",\"a\":80,\"b\":27},{\"tag\":\"incompatible\",\"a\":81,\"b\":27},{\"tag\":\"incompatible\",\"a\":81,\"b\":37},{\"tag\":\"incompatible\",\"a\":81,\"b\":44},{\"tag\":\"incompatible\",\"a\":81,\"b\":70},{\"tag\":\"incompatible\",\"a\":81,\"b\":75},{\"tag\":\"incompatible\",\"a\":83,\"b\":44},{\"tag\":\"incompatible\",\"a\":83,\"b\":49},{\"tag\":\"incompatible\",\"a\":83,\"b\":66},{\"tag\":\"incompatible\",\"a\":83,\"b\":70},{\"tag\":\"incompatible\",\"a\":84,\"b\":36},{\"tag\":\"incompatible\",\"a\":84,\"b\":38},{\"tag\":\"incompatible\",\"a\":84,\"b\":39},{\"tag\":\"incompatible\",\"a\":84,\"b\":44},{\"tag\":\"incompatible\",\"a\":84,\"b\":45},{\"tag\":\"incompatible\",\"a\":84,\"b\":46},{\"tag\":\"incompatible\",\"a\":84,\"b\":47},{\"tag\":\"incompatible\",\"a\":84,\"b\":49},{\"tag\":\"incompatible\",\"a\":84,\"b\":61},{\"tag\":\"incompatible\",\"a\":84,\"b\":67},{\"tag\":\"incompatible\",\"a\":84,\"b\":68},{\"tag\":\"incompatible\",\"a\":84,\"b\":70},{\"tag\":\"incompatible\",\"a\":84,\"b\":74},{\"tag\":\"incompatible\",\"a\":84,\"b\":76},{\"tag\":\"incompatible\",\"a\":84,\"b\":77},{\"tag\":\"incompatible\",\"a\":84,\"b\":78},{\"tag\":\"incompatible\",\"a\":84,\"b\":79},{\"tag\":\"incompatible\",\"a\":84,\"b\":80},{\"tag\":\"incompatible\",\"a\":84,\"b\":81},{\"tag\":\"incompatible\",\"a\":84,\"b\":83},{\"tag\":\"incompatible\",\"a\":85,\"b\":23},{\"tag\":\"incompatible\",\"a\":85,\"b\":27},{\"tag\":\"incompatible\",\"a\":85,\"b\":29},{\"tag\":\"incompatible\",\"a\":85,\"b\":36},{\"tag\":\"incompatible\",\"a\":85,\"b\":43},{\"tag\":\"incompatible\",\"a\":85,\"b\":44},{\"tag\":\"incompatible\",\"a\":85,\"b\":68},{\"tag\":\"incompatible\",\"a\":85,\"b\":70},{\"tag\":\"incompatible\",\"a\":85,\"b\":74},{\"tag\":\"incompatible\",\"a\":85,\"b\":75},{\"tag\":\"incompatible\",\"a\":85,\"b\":78},{\"tag\":\"incompatible\",\"a\":85,\"b\":83},{\"tag\":\"incompatible\",\"a\":85,\"b\":84},{\"tag\":\"incompatible\",\"a\":86,\"b\":24},{\"tag\":\"incompatible\",\"a\":86,\"b\":36},{\"tag\":\"incompatible\",\"a\":86,\"b\":51},{\"tag\":\"incompatible\",\"a\":86,\"b\":53},{\"tag\":\"incompatible\",\"a\":86,\"b\":58},{\"tag\":\"incompatible\",\"a\":86,\"b\":70},{\"tag\":\"incompatible\",\"a\":86,\"b\":71},{\"tag\":\"incompatible\",\"a\":86,\"b\":75},{\"tag\":\"incompatible\",\"a\":87,\"b\":34},{\"tag\":\"incompatible\",\"a\":87,\"b\":54},{\"tag\":\"incompatible\",\"a\":87,\"b\":72},{\"tag\":\"incompatible\",\"a\":88,\"b\":31},{\"tag\":\"incompatible\",\"a\":88,\"b\":58},{\"tag\":\"incompatible\",\"a\":88,\"b\":61},{\"tag\":\"incompatible\",\"a\":88,\"b\":67},{\"tag\":\"incompatible\",\"a\":88,\"b\":75},{\"tag\":\"incompatible\",\"a\":88,\"b\":84},{\"tag\":\"incompatible\",\"a\":88,\"b\":86},{\"tag\":\"mate\",\"ridge\":7,\"a\":34,\"owners\":[0,1,23,26,27,29,30,31,32,35]},{\"tag\":\"three\",\"ridge\":7,\"vertices\":[0,31,34]},{\"tag\":\"three\",\"ridge\":7,\"vertices\":[0,32,34]},{\"tag\":\"three\",\"ridge\":7,\"vertices\":[23,31,34]},{\"tag\":\"three\",\"ridge\":7,\"vertices\":[23,32,34]},{\"tag\":\"three\",\"ridge\":7,\"vertices\":[26,31,34]},{\"tag\":\"mate\",\"ridge\":11,\"a\":3,\"owners\":[0,4,23,24,26,36,38,39,40,42]},{\"tag\":\"mate\",\"ridge\":11,\"a\":37,\"owners\":[0,4,24,26,40,42]},{\"tag\":\"mate\",\"ridge\":11,\"a\":41,\"owners\":[0,4,23,24,26,36,39,40]},{\"tag\":\"mate\",\"ridge\":13,\"a\":9,\"owners\":[0,8,24,25,26,51,52,53,55]},{\"tag\":\"mate\",\"ridge\":13,\"a\":51,\"owners\":[0,9,25,26,56]},{\"tag\":\"mate\",\"ridge\":13,\"a\":53,\"owners\":[0,9,24,25,56]},{\"tag\":\"mate\",\"ridge\":13,\"a\":56,\"owners\":[0,8,24,26,51,53,55]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[8,26,56]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[26,51,56]},{\"tag\":\"mate\",\"ridge\":14,\"a\":72,\"owners\":[0,15,23,24,68,70,71]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[0,71,72]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[23,71,72]},{\"tag\":\"mate\",\"ridge\":35,\"a\":32,\"owners\":[5,36,43,44,48]},{\"tag\":\"mate\",\"ridge\":35,\"a\":33,\"owners\":[5,36,40,43,44,45,48,49]},{\"tag\":\"mate\",\"ridge\":35,\"a\":49,\"owners\":[1,24,27,33,36,43]},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[5,33,36]},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[5,33,40]},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[5,33,45]},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[33,36,49]},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[33,43,49]},{\"tag\":\"mate\",\"ridge\":37,\"a\":31,\"owners\":[10,51,55,58]},{\"tag\":\"mate\",\"ridge\":37,\"a\":33,\"owners\":[10,51,55,57,58,61]},{\"tag\":\"mate\",\"ridge\":38,\"a\":33,\"owners\":[17,68,71,74,75,77]},{\"tag\":\"mate\",\"ridge\":38,\"a\":74,\"owners\":[1,17,24,33,71]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[4,33,50]},{\"tag\":\"mate\",\"ridge\":517,\"a\":2,\"owners\":[9,54,56,59]},{\"tag\":\"mate\",\"ridge\":517,\"a\":33,\"owners\":[9,54,56,59]},{\"tag\":\"mate\",\"ridge\":518,\"a\":72,\"owners\":[2,33]},{\"tag\":\"mate\",\"ridge\":67,\"a\":6,\"owners\":[3,7,25,28,34,37,43]},{\"tag\":\"mate\",\"ridge\":67,\"a\":25,\"owners\":[6,7,43,46,48]},{\"tag\":\"mate\",\"ridge\":67,\"a\":48,\"owners\":[3,7,25,28,34,37]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[7,37,48]},{\"tag\":\"mate\",\"ridge\":73,\"a\":56,\"owners\":[3,11,41,63]},{\"tag\":\"three\",\"ridge\":73,\"vertices\":[3,56,63]},{\"tag\":\"three\",\"ridge\":73,\"vertices\":[11,41,56]},{\"tag\":\"mate\",\"ridge\":74,\"a\":18,\"owners\":[3,25,37,41,69,79,80,82]},{\"tag\":\"three\",\"ridge\":74,\"vertices\":[18,37,82]},{\"tag\":\"three\",\"ridge\":74,\"vertices\":[41,72,80]},{\"tag\":\"mate\",\"ridge\":521,\"a\":54,\"owners\":[4,12]},{\"tag\":\"mate\",\"ridge\":521,\"a\":64,\"owners\":[4,9]},{\"tag\":\"mate\",\"ridge\":522,\"a\":18,\"owners\":[4,16,73]},{\"tag\":\"mate\",\"ridge\":522,\"a\":73,\"owners\":[4,18]},{\"tag\":\"mate\",\"ridge\":131,\"a\":50,\"owners\":[5,29,31,35,38,42,44,47,49]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[38,49,50]},{\"tag\":\"mate\",\"ridge\":161,\"a\":5,\"owners\":[13,57,61,66,67]},{\"tag\":\"mate\",\"ridge\":161,\"a\":49,\"owners\":[13,57,66]},{\"tag\":\"mate\",\"ridge\":161,\"a\":66,\"owners\":[5,31,49,61]},{\"tag\":\"mate\",\"ridge\":162,\"a\":5,\"owners\":[19,74,77,83,84]},{\"tag\":\"mate\",\"ridge\":162,\"a\":48,\"owners\":[19,74,77,84]},{\"tag\":\"mate\",\"ridge\":162,\"a\":77,\"owners\":[5,44,48,83]},{\"tag\":\"mate\",\"ridge\":162,\"a\":84,\"owners\":[5,31,48]},{\"tag\":\"mate\",\"ridge\":193,\"a\":50,\"owners\":[14,63,66]},{\"tag\":\"mate\",\"ridge\":193,\"a\":66,\"owners\":[6,41,50]},{\"tag\":\"mate\",\"ridge\":194,\"a\":6,\"owners\":[79,82,83,85]},{\"tag\":\"mate\",\"ridge\":194,\"a\":41,\"owners\":[83,85]},{\"tag\":\"mate\",\"ridge\":194,\"a\":46,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":194,\"a\":48,\"owners\":[79,82,85]},{\"tag\":\"mate\",\"ridge\":194,\"a\":50,\"owners\":[79,82,83,85]},{\"tag\":\"mate\",\"ridge\":194,\"a\":82,\"owners\":[6,46,48,50,83]},{\"tag\":\"mate\",\"ridge\":577,\"a\":7,\"owners\":[12,56,59,64]},{\"tag\":\"mate\",\"ridge\":577,\"a\":12,\"owners\":[7,34,50,59]},{\"tag\":\"mate\",\"ridge\":577,\"a\":34,\"owners\":[12,64]},{\"tag\":\"mate\",\"ridge\":577,\"a\":56,\"owners\":[7,50]},{\"tag\":\"mate\",\"ridge\":578,\"a\":7,\"owners\":[18,72]},{\"tag\":\"mate\",\"ridge\":578,\"a\":18,\"owners\":[7,34,50]},{\"tag\":\"mate\",\"ridge\":578,\"a\":34,\"owners\":[18]},{\"tag\":\"mate\",\"ridge\":578,\"a\":50,\"owners\":[18,72]},{\"tag\":\"mate\",\"ridge\":578,\"a\":72,\"owners\":[7,50]},{\"tag\":\"mate\",\"ridge\":21,\"a\":8,\"owners\":[10,27,28,29,30,57,58,59,60]},{\"tag\":\"mate\",\"ridge\":21,\"a\":53,\"owners\":[10,27,28,29,57,59]},{\"tag\":\"mate\",\"ridge\":21,\"a\":54,\"owners\":[10,27,28,29,30,57,58,60]},{\"tag\":\"mate\",\"ridge\":25,\"a\":51,\"owners\":[11,37,38,39,63,64,65]},{\"tag\":\"mate\",\"ridge\":25,\"a\":54,\"owners\":[11,36,37,38,39,62,63,65]},{\"tag\":\"mate\",\"ridge\":25,\"a\":64,\"owners\":[8,23,36,38,39,51,53,62,65]},{\"tag\":\"mate\",\"ridge\":28,\"a\":20,\"owners\":[8,23,51,52,54,68,69,87]},{\"tag\":\"mate\",\"ridge\":28,\"a\":51,\"owners\":[20,69,70,87]},{\"tag\":\"mate\",\"ridge\":28,\"a\":54,\"owners\":[20,68,69,70,86]},{\"tag\":\"mate\",\"ridge\":28,\"a\":86,\"owners\":[8,23,52,54,69,87]},{\"tag\":\"three\",\"ridge\":28,\"vertices\":[20,51,87]},{\"tag\":\"mate\",\"ridge\":524,\"a\":72,\"owners\":[9,54]},{\"tag\":\"mate\",\"ridge\":524,\"a\":73,\"owners\":[9,54,56,87]},{\"tag\":\"mate\",\"ridge\":49,\"a\":51,\"owners\":[13,43,44,45,66,67]},{\"tag\":\"mate\",\"ridge\":49,\"a\":66,\"owners\":[10,27,36,45,51,58,62]},{\"tag\":\"mate\",\"ridge\":49,\"a\":67,\"owners\":[10,27,36,43,51]},{\"tag\":\"three\",\"ridge\":49,\"vertices\":[45,51,66]},{\"tag\":\"mate\",\"ridge\":52,\"a\":51,\"owners\":[21,74,75,88]},{\"tag\":\"mate\",\"ridge\":52,\"a\":57,\"owners\":[21,68,75,86]},{\"tag\":\"mate\",\"ridge\":52,\"a\":86,\"owners\":[10,27,57,74]},{\"tag\":\"mate\",\"ridge\":52,\"a\":88,\"owners\":[10,27,51,68]},{\"tag\":\"mate\",\"ridge\":81,\"a\":66,\"owners\":[11,28,37,52,59,64]},{\"tag\":\"mate\",\"ridge\":88,\"a\":11,\"owners\":[69,79,80,87,89]},{\"tag\":\"mate\",\"ridge\":88,\"a\":37,\"owners\":[87,89]},{\"tag\":\"mate\",\"ridge\":88,\"a\":52,\"owners\":[79,80,89]},{\"tag\":\"mate\",\"ridge\":88,\"a\":63,\"owners\":[69,80,87]},{\"tag\":\"mate\",\"ridge\":88,\"a\":64,\"owners\":[69,79,80,89]},{\"tag\":\"mate\",\"ridge\":88,\"a\":80,\"owners\":[11,52,63,64,87]},{\"tag\":\"mate\",\"ridge\":88,\"a\":89,\"owners\":[11,37,52,64,69,87]},{\"tag\":\"mate\",\"ridge\":584,\"a\":56,\"owners\":[18]},{\"tag\":\"mate\",\"ridge\":584,\"a\":64,\"owners\":[18,72]},{\"tag\":\"mate\",\"ridge\":584,\"a\":72,\"owners\":[12,64]},{\"tag\":\"mate\",\"ridge\":145,\"a\":57,\"owners\":[14,38,46,47,63,65]},{\"tag\":\"mate\",\"ridge\":145,\"a\":63,\"owners\":[13,29,44,47,57,60,67]},{\"tag\":\"mate\",\"ridge\":145,\"a\":67,\"owners\":[14,29,38,46,63]},{\"tag\":\"mate\",\"ridge\":176,\"a\":57,\"owners\":[22,83,84]},{\"tag\":\"mate\",\"ridge\":176,\"a\":66,\"owners\":[22,74,84,88]},{\"tag\":\"mate\",\"ridge\":208,\"a\":14,\"owners\":[79,83,85,89]},{\"tag\":\"mate\",\"ridge\":208,\"a\":63,\"owners\":[83,85]},{\"tag\":\"mate\",\"ridge\":208,\"a\":66,\"owners\":[79,85,89]},{\"tag\":\"mate\",\"ridge\":262,\"a\":17,\"owners\":[15,26,30,35,70,73,76]},{\"tag\":\"mate\",\"ridge\":262,\"a\":70,\"owners\":[17,32,35,77]},{\"tag\":\"mate\",\"ridge\":266,\"a\":70,\"owners\":[40,42,82]},{\"tag\":\"mate\",\"ridge\":266,\"a\":71,\"owners\":[39,42,80,81,82]},{\"tag\":\"mate\",\"ridge\":266,\"a\":73,\"owners\":[39,40,42,78,80,81,82]},{\"tag\":\"mate\",\"ridge\":266,\"a\":80,\"owners\":[15,26,40,42,71,73]},{\"tag\":\"three\",\"ridge\":266,\"vertices\":[39,73,82]},{\"tag\":\"three\",\"ridge\":266,\"vertices\":[40,73,82]},{\"tag\":\"mate\",\"ridge\":268,\"a\":20,\"owners\":[15,26,55,71,73]},{\"tag\":\"mate\",\"ridge\":268,\"a\":71,\"owners\":[20,53]},{\"tag\":\"mate\",\"ridge\":268,\"a\":73,\"owners\":[20,53,55,86]},{\"tag\":\"mate\",\"ridge\":290,\"a\":32,\"owners\":[19,78,84]},{\"tag\":\"mate\",\"ridge\":290,\"a\":49,\"owners\":[17,71,75,78]},{\"tag\":\"mate\",\"ridge\":290,\"a\":71,\"owners\":[19,45,49,84]},{\"tag\":\"mate\",\"ridge\":290,\"a\":84,\"owners\":[17,32,40,71]},{\"tag\":\"mate\",\"ridge\":292,\"a\":17,\"owners\":[21,55,58,61,86,88]},{\"tag\":\"mate\",\"ridge\":292,\"a\":77,\"owners\":[21,55,58,86]},{\"tag\":\"mate\",\"ridge\":292,\"a\":88,\"owners\":[17,32,55,71]},{\"tag\":\"mate\",\"ridge\":386,\"a\":19,\"owners\":[35,42,47,76,81,82,85]},{\"tag\":\"mate\",\"ridge\":386,\"a\":84,\"owners\":[35,42,82]},{\"tag\":\"mate\",\"ridge\":416,\"a\":77,\"owners\":[22,67]},{\"tag\":\"mate\",\"ridge\":416,\"a\":88,\"owners\":[19,49]},{\"tag\":\"mate\",\"ridge\":276,\"a\":53,\"owners\":[21,75,76,88]},{\"tag\":\"mate\",\"ridge\":276,\"a\":58,\"owners\":[20,70,76]},{\"tag\":\"mate\",\"ridge\":276,\"a\":88,\"owners\":[20,30,53,70]},{\"tag\":\"mate\",\"ridge\":280,\"a\":53,\"owners\":[78,80,81,89]},{\"tag\":\"mate\",\"ridge\":280,\"a\":70,\"owners\":[62,65,89]},{\"tag\":\"mate\",\"ridge\":280,\"a\":80,\"owners\":[20,53,62,65,86]},{\"tag\":\"mate\",\"ridge\":280,\"a\":81,\"owners\":[20,53,62,86]},{\"tag\":\"mate\",\"ridge\":280,\"a\":86,\"owners\":[39,65,80,81,89]},{\"tag\":\"mate\",\"ridge\":304,\"a\":58,\"owners\":[22,78,84]},{\"tag\":\"mate\",\"ridge\":304,\"a\":67,\"owners\":[21,75,78,86]},{\"tag\":\"mate\",\"ridge\":304,\"a\":75,\"owners\":[22,62,67]},{\"tag\":\"mate\",\"ridge\":400,\"a\":67,\"owners\":[76,81,85,89]},{\"tag\":\"mate\",\"ridge\":400,\"a\":84,\"owners\":[60,65,89]},{\"tag\":\"mate\",\"ridge\":86,\"a\":28,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":86,\"a\":69,\"owners\":[28]},{\"tag\":\"mate\",\"ridge\":275,\"a\":39,\"owners\":[30,45,47]},{\"tag\":\"mate\",\"ridge\":275,\"a\":47,\"owners\":[30,39,45]},{\"tag\":\"mate\",\"ridge\":389,\"a\":60,\"owners\":[35,61]},{\"tag\":\"mate\",\"ridge\":389,\"a\":61,\"owners\":[35,60]},{\"tag\":\"mate\",\"ridge\":58,\"a\":36,\"owners\":[68,78]},{\"tag\":\"mate\",\"ridge\":154,\"a\":79,\"owners\":[38,81]},{\"tag\":\"mate\",\"ridge\":154,\"a\":81,\"owners\":[38,79]},{\"tag\":\"mate\",\"ridge\":393,\"a\":42,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":114,\"a\":43,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":114,\"a\":83,\"owners\":[43]},{\"tag\":\"mate\",\"ridge\":596,\"a\":87,\"owners\":[59]},{\"tag\":\"mate\",\"ridge\":338,\"a\":80,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":338,\"a\":85,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":456,\"a\":82,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":456,\"a\":89,\"owners\":[82]},{\"tag\":\"group_take\",\"kind\":1,\"index\":1,\"member\":1,\"full_literals\":[-2,91]},{\"tag\":\"group_take\",\"kind\":1,\"index\":2,\"member\":2,\"full_literals\":[-3,92]},{\"tag\":\"group_or\",\"kind\":1,\"index\":5,\"members\":[5],\"full_literals\":[-93,6]},{\"tag\":\"group_take\",\"kind\":1,\"index\":5,\"member\":5,\"full_literals\":[-6,93]},{\"tag\":\"group_or\",\"kind\":1,\"index\":6,\"members\":[6],\"full_literals\":[-94,7]},{\"tag\":\"group_or\",\"kind\":1,\"index\":7,\"members\":[7],\"full_literals\":[-95,8]},{\"tag\":\"group_take\",\"kind\":1,\"index\":7,\"member\":7,\"full_literals\":[-8,95]},{\"tag\":\"group_take\",\"kind\":1,\"index\":9,\"member\":9,\"full_literals\":[-10,96]},{\"tag\":\"group_take\",\"kind\":1,\"index\":11,\"member\":11,\"full_literals\":[-12,97]},{\"tag\":\"group_take\",\"kind\":1,\"index\":12,\"member\":12,\"full_literals\":[-13,98]},{\"tag\":\"group_take\",\"kind\":1,\"index\":13,\"member\":13,\"full_literals\":[-14,99]},{\"tag\":\"group_take\",\"kind\":1,\"index\":15,\"member\":15,\"full_literals\":[-16,100]},{\"tag\":\"group_take\",\"kind\":1,\"index\":17,\"member\":17,\"full_literals\":[-18,101]},{\"tag\":\"group_take\",\"kind\":1,\"index\":18,\"member\":18,\"full_literals\":[-19,102]},{\"tag\":\"group_take\",\"kind\":1,\"index\":19,\"member\":19,\"full_literals\":[-20,103]},{\"tag\":\"group_take\",\"kind\":1,\"index\":20,\"member\":20,\"full_literals\":[-21,104]},{\"tag\":\"group_take\",\"kind\":1,\"index\":21,\"member\":21,\"full_literals\":[-22,105]},{\"tag\":\"group_take\",\"kind\":1,\"index\":22,\"member\":22,\"full_literals\":[-23,106]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0005\",\"joined_name\":\"grouped1_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-91,107],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped1_0006\",\"right_name\":\"grouped1_0008\",\"joined_name\":\"grouped1_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-92,false,108],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-108,109],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-107,-108,110],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0014\",\"joined_name\":\"grouped1_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-111,94,95],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0014\",\"joined_name\":\"grouped1_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-95,111],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped1_0009\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0010\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-112,93,111],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped1_0009\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-111,112],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped1_0009\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-93,false,112],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped1_0017\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-96,false,113],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-113,114],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped1_0010\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-114,115],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped1_0010\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-112,false,115],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped1_0010\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-112,-114,116],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0011\",\"joined_name\":\"grouped1_0003\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-115,117],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0011\",\"joined_name\":\"grouped1_0003\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-116,118],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0011\",\"joined_name\":\"grouped1_0003\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-109,-115,118],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0011\",\"joined_name\":\"grouped1_0003\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-110,-115,119],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13],\"left_name\":\"grouped1_0024\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0025\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-98,false,120],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13],\"left_name\":\"grouped1_0024\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0025\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-98,-99,121],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11],\"right\":[12,13],\"left_name\":\"grouped1_0020\",\"right_name\":\"grouped1_0025\",\"joined_name\":\"grouped1_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-120,122],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11],\"right\":[12,13],\"left_name\":\"grouped1_0020\",\"right_name\":\"grouped1_0025\",\"joined_name\":\"grouped1_0021\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-121,123],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11],\"right\":[12,13],\"left_name\":\"grouped1_0020\",\"right_name\":\"grouped1_0025\",\"joined_name\":\"grouped1_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-97,false,122],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15],\"right\":[16],\"left_name\":\"grouped1_0029\",\"right_name\":\"grouped1_0031\",\"joined_name\":\"grouped1_0030\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-100,false,124],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14],\"right\":[15,16],\"left_name\":\"grouped1_0027\",\"right_name\":\"grouped1_0030\",\"joined_name\":\"grouped1_0028\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-124,125],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11,12,13],\"right\":[14,15,16],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-125,126],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11,12,13],\"right\":[14,15,16],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-122,false,126],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11,12,13],\"right\":[14,15,16],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-122,-125,127],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11,12,13],\"right\":[14,15,16],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0022\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-123,false,127],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[18],\"right\":[19],\"left_name\":\"grouped1_0035\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0036\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-103,128],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[18],\"right\":[19],\"left_name\":\"grouped1_0035\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0036\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-102,false,128],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17],\"right\":[18,19],\"left_name\":\"grouped1_0032\",\"right_name\":\"grouped1_0036\",\"joined_name\":\"grouped1_0033\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-128,129],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17],\"right\":[18,19],\"left_name\":\"grouped1_0032\",\"right_name\":\"grouped1_0036\",\"joined_name\":\"grouped1_0033\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-101,false,129],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17],\"right\":[18,19],\"left_name\":\"grouped1_0032\",\"right_name\":\"grouped1_0036\",\"joined_name\":\"grouped1_0033\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-101,-128,130],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[21],\"right\":[22],\"left_name\":\"grouped1_0040\",\"right_name\":\"grouped1_0042\",\"joined_name\":\"grouped1_0041\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-106,131],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[21],\"right\":[22],\"left_name\":\"grouped1_0040\",\"right_name\":\"grouped1_0042\",\"joined_name\":\"grouped1_0041\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-105,false,131],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20],\"right\":[21,22],\"left_name\":\"grouped1_0038\",\"right_name\":\"grouped1_0041\",\"joined_name\":\"grouped1_0039\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-131,132],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20],\"right\":[21,22],\"left_name\":\"grouped1_0038\",\"right_name\":\"grouped1_0041\",\"joined_name\":\"grouped1_0039\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-104,false,132],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20],\"right\":[21,22],\"left_name\":\"grouped1_0038\",\"right_name\":\"grouped1_0041\",\"joined_name\":\"grouped1_0039\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-104,-131,133],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17,18,19],\"right\":[20,21,22],\"left_name\":\"grouped1_0033\",\"right_name\":\"grouped1_0039\",\"joined_name\":\"grouped1_0034\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-132,134],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17,18,19],\"right\":[20,21,22],\"left_name\":\"grouped1_0033\",\"right_name\":\"grouped1_0039\",\"joined_name\":\"grouped1_0034\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-133,135],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17,18,19],\"right\":[20,21,22],\"left_name\":\"grouped1_0033\",\"right_name\":\"grouped1_0039\",\"joined_name\":\"grouped1_0034\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-129,-132,135],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17,18,19],\"right\":[20,21,22],\"left_name\":\"grouped1_0033\",\"right_name\":\"grouped1_0039\",\"joined_name\":\"grouped1_0034\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-129,-133,136],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17,18,19],\"right\":[20,21,22],\"left_name\":\"grouped1_0033\",\"right_name\":\"grouped1_0039\",\"joined_name\":\"grouped1_0034\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-130,-132,136],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11,12,13,14,15,16],\"right\":[17,18,19,20,21,22],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0034\",\"joined_name\":\"grouped1_0023\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-136,138],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11,12,13,14,15,16],\"right\":[17,18,19,20,21,22],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0034\",\"joined_name\":\"grouped1_0023\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-126,-134,137],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11,12,13,14,15,16],\"right\":[17,18,19,20,21,22],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0034\",\"joined_name\":\"grouped1_0023\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-126,-135,138],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11,12,13,14,15,16],\"right\":[17,18,19,20,21,22],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0034\",\"joined_name\":\"grouped1_0023\",\"a\":1,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-126,-136,139],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11,12,13,14,15,16],\"right\":[17,18,19,20,21,22],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0034\",\"joined_name\":\"grouped1_0023\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-127,-135,139],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10],\"right\":[11,12,13,14,15,16,17,18,19,20,21,22],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"groupKind1\",\"a\":1,\"b\":4,\"direction\":\"forward\",\"full_literals\":[-117,-139,140],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10],\"right\":[11,12,13,14,15,16,17,18,19,20,21,22],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"groupKind1\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-118,-138,140],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10],\"right\":[11,12,13,14,15,16,17,18,19,20,21,22],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"groupKind1\",\"a\":3,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-119,-137,140],\"grouped\":true,\"kind\":1},{\"tag\":\"quota_upper\",\"kind\":1,\"quota\":4,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[41,46,48,50],\"full_literals\":[-141,42,47,49,51]},{\"tag\":\"group_take\",\"kind\":2,\"index\":0,\"member\":50,\"full_literals\":[-51,141]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[63,66],\"full_literals\":[-142,64,67]},{\"tag\":\"group_take\",\"kind\":2,\"index\":1,\"member\":66,\"full_literals\":[-67,142]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[25,26,72,73],\"full_literals\":[-143,26,27,73,74]},{\"tag\":\"group_take\",\"kind\":2,\"index\":2,\"member\":72,\"full_literals\":[-73,143]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[24,33,34],\"full_literals\":[-144,25,34,35]},{\"tag\":\"group_take\",\"kind\":2,\"index\":3,\"member\":24,\"full_literals\":[-25,144]},{\"tag\":\"group_take\",\"kind\":2,\"index\":3,\"member\":33,\"full_literals\":[-34,144]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[31,57,77,88],\"full_literals\":[-145,32,58,78,89]},{\"tag\":\"group_take\",\"kind\":2,\"index\":4,\"member\":88,\"full_literals\":[-89,145]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[51,71,86],\"full_literals\":[-146,52,72,87]},{\"tag\":\"group_take\",\"kind\":2,\"index\":5,\"member\":51,\"full_literals\":[-52,146]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[52,54,56,64],\"full_literals\":[-147,53,55,57,65]},{\"tag\":\"group_take\",\"kind\":2,\"index\":6,\"member\":64,\"full_literals\":[-65,147]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[32,49,53,58,67],\"full_literals\":[-148,33,50,54,59,68]},{\"tag\":\"group_take\",\"kind\":2,\"index\":7,\"member\":49,\"full_literals\":[-50,148]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[23,27,37,44,70,75,84],\"full_literals\":[-149,24,28,38,45,71,76,85]},{\"tag\":\"group_take\",\"kind\":2,\"index\":8,\"member\":37,\"full_literals\":[-38,149]},{\"tag\":\"group_take\",\"kind\":2,\"index\":8,\"member\":70,\"full_literals\":[-71,149]},{\"tag\":\"group_take\",\"kind\":2,\"index\":8,\"member\":75,\"full_literals\":[-76,149]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0043\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0044\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-150,141,142],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0043\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0044\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-151,141,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0043\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0044\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-151,false,142],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0043\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0044\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-141,-142,151],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0048\",\"right_name\":\"grouped2_0050\",\"joined_name\":\"grouped2_0049\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-152,143,144],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0048\",\"right_name\":\"grouped2_0050\",\"joined_name\":\"grouped2_0049\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-153,143,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0048\",\"right_name\":\"grouped2_0050\",\"joined_name\":\"grouped2_0049\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-153,false,144],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0048\",\"right_name\":\"grouped2_0050\",\"joined_name\":\"grouped2_0049\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-143,-144,153],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0044\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0045\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-154,150,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0044\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0045\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-154,151,153],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0044\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0045\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-155,151,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0044\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0045\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-154,false,152],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0044\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0045\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-155,false,153],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0044\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0045\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-151,-153,155],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0052\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-156,145,146],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0052\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-157,145,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0052\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-157,false,146],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0052\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-145,-146,157],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0059\",\"joined_name\":\"grouped2_0058\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-158,148,149],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0059\",\"joined_name\":\"grouped2_0058\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-159,148,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0059\",\"joined_name\":\"grouped2_0058\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-159,false,149],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0059\",\"joined_name\":\"grouped2_0058\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-148,-149,159],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0055\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0056\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-160,147,159],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0055\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0056\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-161,147,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0055\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0056\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-160,false,158],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0055\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0056\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-161,false,159],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0055\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0056\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-147,-159,161],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0053\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-162,156,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0053\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-162,157,161],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0053\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-163,157,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0053\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-162,false,160],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0053\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-163,false,161],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0053\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-157,-161,163],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0045\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-164,154,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0045\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-164,155,163],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0045\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-164,false,162],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0045\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":5,\"direction\":\"forward\",\"full_literals\":[-155,-163,165],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[28,59],\"full_literals\":[-166,29,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":28,\"full_literals\":[-29,166]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":59,\"full_literals\":[-60,166]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[69,87],\"full_literals\":[-167,70,88]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":69,\"full_literals\":[-70,167]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":87,\"full_literals\":[-88,167]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[38,42,82],\"full_literals\":[-168,39,43,83]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":38,\"full_literals\":[-39,168]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":42,\"full_literals\":[-43,168]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":82,\"full_literals\":[-83,168]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[65,79,89],\"full_literals\":[-169,66,80,90]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":65,\"full_literals\":[-66,169]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":79,\"full_literals\":[-80,169]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":89,\"full_literals\":[-90,169]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[30,35,40],\"full_literals\":[-170,31,36,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":30,\"full_literals\":[-31,170]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":35,\"full_literals\":[-36,170]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":40,\"full_literals\":[-41,170]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[39,55,60],\"full_literals\":[-171,40,56,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":39,\"full_literals\":[-40,171]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":55,\"full_literals\":[-56,171]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":60,\"full_literals\":[-61,171]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[45,61,62],\"full_literals\":[-172,46,62,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":45,\"full_literals\":[-46,172]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":61,\"full_literals\":[-62,172]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":62,\"full_literals\":[-63,172]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[29,36,43,47,80,81],\"full_literals\":[-173,30,37,44,48,81,82]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":36,\"full_literals\":[-37,173]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":43,\"full_literals\":[-44,173]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":80,\"full_literals\":[-81,173]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[68,74,83,85],\"full_literals\":[-174,69,75,84,86]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":68,\"full_literals\":[-69,174]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":83,\"full_literals\":[-84,174]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":85,\"full_literals\":[-86,174]},{\"tag\":\"group_or\",\"kind\":3,\"index\":9,\"members\":[76,78],\"full_literals\":[-175,77,79]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":76,\"full_literals\":[-77,175]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":78,\"full_literals\":[-79,175]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0060\",\"right_name\":\"grouped3_0064\",\"joined_name\":\"grouped3_0061\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-176,166,167],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0060\",\"right_name\":\"grouped3_0064\",\"joined_name\":\"grouped3_0061\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-167,176],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0060\",\"right_name\":\"grouped3_0064\",\"joined_name\":\"grouped3_0061\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-166,false,176],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0067\",\"right_name\":\"grouped3_0069\",\"joined_name\":\"grouped3_0068\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-177,169,170],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0067\",\"right_name\":\"grouped3_0069\",\"joined_name\":\"grouped3_0068\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-170,177],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0067\",\"right_name\":\"grouped3_0069\",\"joined_name\":\"grouped3_0068\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-169,false,177],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0067\",\"right_name\":\"grouped3_0069\",\"joined_name\":\"grouped3_0068\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-178,false,170],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0065\",\"right_name\":\"grouped3_0068\",\"joined_name\":\"grouped3_0066\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-179,168,177],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0065\",\"right_name\":\"grouped3_0068\",\"joined_name\":\"grouped3_0066\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-177,179],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0065\",\"right_name\":\"grouped3_0068\",\"joined_name\":\"grouped3_0066\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-180,168,178],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0065\",\"right_name\":\"grouped3_0068\",\"joined_name\":\"grouped3_0066\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-168,false,179],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0065\",\"right_name\":\"grouped3_0068\",\"joined_name\":\"grouped3_0066\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-168,-177,180],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0061\",\"right_name\":\"grouped3_0066\",\"joined_name\":\"grouped3_0062\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-181,176,179],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0061\",\"right_name\":\"grouped3_0066\",\"joined_name\":\"grouped3_0062\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-179,181],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0061\",\"right_name\":\"grouped3_0066\",\"joined_name\":\"grouped3_0062\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-182,176,180],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0061\",\"right_name\":\"grouped3_0066\",\"joined_name\":\"grouped3_0062\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-180,182],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0061\",\"right_name\":\"grouped3_0066\",\"joined_name\":\"grouped3_0062\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-176,false,181],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0061\",\"right_name\":\"grouped3_0066\",\"joined_name\":\"grouped3_0062\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-176,-180,183],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0070\",\"right_name\":\"grouped3_0073\",\"joined_name\":\"grouped3_0071\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-184,171,172],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0070\",\"right_name\":\"grouped3_0073\",\"joined_name\":\"grouped3_0071\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-172,184],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0070\",\"right_name\":\"grouped3_0073\",\"joined_name\":\"grouped3_0071\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-171,false,184],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0076\",\"right_name\":\"grouped3_0078\",\"joined_name\":\"grouped3_0077\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-185,174,175],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0076\",\"right_name\":\"grouped3_0078\",\"joined_name\":\"grouped3_0077\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-175,185],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0076\",\"right_name\":\"grouped3_0078\",\"joined_name\":\"grouped3_0077\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-174,false,185],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0074\",\"right_name\":\"grouped3_0077\",\"joined_name\":\"grouped3_0075\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-186,173,185],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0074\",\"right_name\":\"grouped3_0077\",\"joined_name\":\"grouped3_0075\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-185,186],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0074\",\"right_name\":\"grouped3_0077\",\"joined_name\":\"grouped3_0075\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-173,false,186],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0074\",\"right_name\":\"grouped3_0077\",\"joined_name\":\"grouped3_0075\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-173,-185,187],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0071\",\"right_name\":\"grouped3_0075\",\"joined_name\":\"grouped3_0072\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-188,184,186],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0071\",\"right_name\":\"grouped3_0075\",\"joined_name\":\"grouped3_0072\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-186,188],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0071\",\"right_name\":\"grouped3_0075\",\"joined_name\":\"grouped3_0072\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-187,189],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0071\",\"right_name\":\"grouped3_0075\",\"joined_name\":\"grouped3_0072\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-184,false,188],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0071\",\"right_name\":\"grouped3_0075\",\"joined_name\":\"grouped3_0072\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-184,-186,189],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0071\",\"right_name\":\"grouped3_0075\",\"joined_name\":\"grouped3_0072\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-184,-187,190],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0062\",\"right_name\":\"grouped3_0072\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-190,192],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0062\",\"right_name\":\"grouped3_0072\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-191,182,188],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0062\",\"right_name\":\"grouped3_0072\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-181,-189,192],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0062\",\"right_name\":\"grouped3_0072\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-182,-188,192],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0062\",\"right_name\":\"grouped3_0072\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-183,false,192],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"block\",\"leaf\":0,\"vertices\":[2,11,12,20,27,49,50,54,66,71,72,82,88,89]},{\"tag\":\"block\",\"leaf\":1,\"vertices\":[2,11,12,20,31,50,54,58,66,71,72,82,84,89]},{\"tag\":\"block\",\"leaf\":2,\"vertices\":[2,9,10,21,31,50,53,64,66,71,72,82,84,89]},{\"tag\":\"block\",\"leaf\":3,\"vertices\":[2,8,9,20,31,50,58,64,66,71,72,82,84,89]},{\"tag\":\"block\",\"leaf\":4,\"vertices\":[2,8,9,20,27,49,50,64,66,71,72,82,88,89]},{\"tag\":\"block\",\"leaf\":5,\"vertices\":[2,5,9,19,27,50,53,64,66,71,72,82,88,89]},{\"tag\":\"block\",\"leaf\":6,\"vertices\":[2,5,9,19,32,50,51,64,66,70,72,82,88,89]},{\"tag\":\"block\",\"leaf\":7,\"vertices\":[1,2,9,17,49,50,51,64,66,70,72,82,88,89]},{\"tag\":\"block\",\"leaf\":8,\"vertices\":[7,8,10,18,33,48,56,63,67,73,77,80,85,86]},{\"tag\":\"block\",\"leaf\":9,\"vertices\":[7,10,12,18,33,48,54,63,67,73,77,80,85,86]},{\"tag\":\"block\",\"leaf\":10,\"vertices\":[7,18,20,21,33,48,51,56,63,67,73,77,80,85]},{\"tag\":\"block\",\"leaf\":11,\"vertices\":[7,10,12,15,33,48,54,63,67,72,77,80,85,86]},{\"tag\":\"block\",\"leaf\":12,\"vertices\":[7,9,14,21,33,48,53,57,64,71,72,82,84,89]},{\"tag\":\"block\",\"leaf\":13,\"vertices\":[7,9,14,21,33,48,51,64,67,70,72,77,82,89]},{\"tag\":\"block\",\"leaf\":14,\"vertices\":[6,7,9,17,33,49,51,64,66,70,72,82,88,89]},{\"tag\":\"block\",\"leaf\":15,\"vertices\":[9,16,17,18,33,49,50,51,64,66,70,82,88,89]},{\"tag\":\"block\",\"leaf\":16,\"vertices\":[11,16,17,18,33,49,50,51,56,66,70,82,88,89]},{\"tag\":\"block\",\"leaf\":17,\"vertices\":[9,17,18,20,33,49,50,51,64,66,73,79,81,88]},{\"tag\":\"block\",\"leaf\":18,\"vertices\":[11,17,18,20,33,49,50,51,56,66,73,79,81,88]},{\"tag\":\"block\",\"leaf\":19,\"vertices\":[5,8,10,18,33,50,56,63,67,73,77,80,85,86]},{\"tag\":\"block\",\"leaf\":20,\"vertices\":[5,10,12,18,33,50,54,63,67,73,77,80,85,86]},{\"tag\":\"block\",\"leaf\":21,\"vertices\":[5,18,20,21,33,50,51,56,63,67,73,77,80,85]},{\"tag\":\"block\",\"leaf\":22,\"vertices\":[9,17,18,20,33,49,50,51,64,66,73,80,85,88]},{\"tag\":\"block\",\"leaf\":23,\"vertices\":[11,17,18,20,33,49,50,51,56,66,73,80,85,88]},{\"tag\":\"block\",\"leaf\":24,\"vertices\":[13,17,18,20,33,49,50,51,56,63,73,80,85,88]},{\"tag\":\"block\",\"leaf\":25,\"vertices\":[8,17,18,22,33,49,50,56,57,63,73,80,85,86]},{\"tag\":\"block\",\"leaf\":26,\"vertices\":[12,17,18,22,33,49,50,54,57,63,73,80,85,86]},{\"tag\":\"block\",\"leaf\":27,\"vertices\":[9,17,18,20,33,49,50,51,64,66,73,82,88,89]},{\"tag\":\"block\",\"leaf\":28,\"vertices\":[9,18,20,22,33,49,50,51,64,66,73,75,82,89]},{\"tag\":\"block\",\"leaf\":29,\"vertices\":[11,17,18,20,33,49,50,51,56,66,73,82,88,89]},{\"tag\":\"block\",\"leaf\":30,\"vertices\":[11,18,20,22,33,49,50,51,56,66,73,75,82,89]},{\"tag\":\"block\",\"leaf\":31,\"vertices\":[11,12,14,18,32,34,48,54,57,73,82,84,86,89]},{\"tag\":\"block\",\"leaf\":32,\"vertices\":[11,12,14,18,27,34,48,54,67,73,77,82,86,89]},{\"tag\":\"block\",\"leaf\":33,\"vertices\":[12,18,19,22,32,34,48,54,57,63,73,80,85,86]},{\"tag\":\"block\",\"leaf\":34,\"vertices\":[1,10,12,18,34,48,54,63,67,73,77,80,85,86]},{\"tag\":\"block\",\"leaf\":35,\"vertices\":[8,9,14,18,32,34,48,57,64,73,82,84,86,89]},{\"tag\":\"block\",\"leaf\":36,\"vertices\":[8,9,14,18,27,34,48,64,67,73,77,82,86,89]},{\"tag\":\"block\",\"leaf\":37,\"vertices\":[9,11,12,17,33,49,50,51,66,70,72,82,88,89]},{\"tag\":\"block\",\"leaf\":38,\"vertices\":[5,9,14,21,33,50,53,57,64,71,72,82,84,89]},{\"tag\":\"block\",\"leaf\":39,\"vertices\":[5,9,14,21,33,50,51,64,67,70,72,77,82,89]},{\"tag\":\"block\",\"leaf\":40,\"vertices\":[9,13,14,17,33,49,50,51,64,70,72,82,88,89]},{\"tag\":\"block\",\"leaf\":41,\"vertices\":[9,10,14,19,33,44,50,53,64,71,72,82,88,89]},{\"tag\":\"block\",\"leaf\":42,\"vertices\":[5,9,10,19,33,50,53,64,66,71,72,79,81,88]},{\"tag\":\"block\",\"leaf\":43,\"vertices\":[5,9,10,19,33,50,53,64,66,71,72,80,85,88]},{\"tag\":\"block\",\"leaf\":44,\"vertices\":[5,8,9,20,33,50,58,64,66,71,72,82,84,89]},{\"tag\":\"block\",\"leaf\":45,\"vertices\":[5,8,9,22,33,50,58,64,66,70,72,77,82,89]},{\"tag\":\"block\",\"leaf\":46,\"vertices\":[5,9,21,22,33,50,51,64,66,70,72,77,82,89]},{\"tag\":\"block\",\"leaf\":47,\"vertices\":[5,9,17,19,33,50,51,64,66,70,72,82,88,89]},{\"tag\":\"block\",\"leaf\":48,\"vertices\":[5,9,10,21,33,50,53,64,66,71,72,82,84,89]},{\"tag\":\"block\",\"leaf\":49,\"vertices\":[5,9,10,19,33,50,53,64,66,71,72,82,88,89]},{\"tag\":\"block\",\"leaf\":50,\"vertices\":[8,9,10,20,33,49,50,64,66,71,72,79,81,88]},{\"tag\":\"block\",\"leaf\":51,\"vertices\":[8,9,10,20,33,49,50,64,66,71,72,80,85,88]},{\"tag\":\"block\",\"leaf\":52,\"vertices\":[8,9,10,20,33,49,50,64,66,71,72,82,88,89]},{\"tag\":\"block\",\"leaf\":53,\"vertices\":[8,9,10,17,33,49,50,64,66,70,72,82,88,89]},{\"tag\":\"block\",\"leaf\":54,\"vertices\":[9,15,17,20,33,49,50,51,64,66,72,79,81,88]},{\"tag\":\"block\",\"leaf\":55,\"vertices\":[9,15,17,20,33,49,50,51,64,66,72,80,85,88]},{\"tag\":\"block\",\"leaf\":56,\"vertices\":[9,15,17,20,33,49,50,51,64,66,72,82,88,89]},{\"tag\":\"block\",\"leaf\":57,\"vertices\":[9,15,20,22,33,49,50,51,64,66,72,75,82,89]},{\"tag\":\"block\",\"leaf\":58,\"vertices\":[9,17,21,22,33,49,50,51,64,66,70,72,82,89]},{\"tag\":\"block\",\"leaf\":59,\"vertices\":[10,11,12,20,33,49,50,54,66,71,72,79,81,88]},{\"tag\":\"block\",\"leaf\":60,\"vertices\":[10,11,12,20,33,49,50,54,66,71,72,80,85,88]},{\"tag\":\"block\",\"leaf\":61,\"vertices\":[10,11,12,20,33,49,50,54,66,71,72,82,88,89]},{\"tag\":\"block\",\"leaf\":62,\"vertices\":[10,11,12,17,33,49,50,54,66,70,72,82,88,89]},{\"tag\":\"block\",\"leaf\":63,\"vertices\":[5,11,12,20,33,50,54,58,66,71,72,82,84,89]},{\"tag\":\"block\",\"leaf\":64,\"vertices\":[5,11,12,22,33,50,54,58,66,70,72,77,82,89]},{\"tag\":\"block\",\"leaf\":65,\"vertices\":[12,20,21,22,33,49,50,54,57,63,71,72,80,85]},{\"tag\":\"block\",\"leaf\":66,\"vertices\":[10,12,13,20,33,49,50,54,63,71,72,80,85,88]},{\"tag\":\"block\",\"leaf\":67,\"vertices\":[12,15,17,22,33,49,50,54,57,63,72,80,85,86]},{\"tag\":\"block\",\"leaf\":68,\"vertices\":[5,10,12,15,33,50,54,63,67,72,77,80,85,86]},{\"tag\":\"edge\",\"edge\":31,\"owners\":[11,14,28,37,43,46,52,59,63,64,66,69,79,80,83,85,87,89]},{\"tag\":\"edge\",\"edge\":39,\"owners\":[6,14,41,46,48,50,63,66,79,82,83,85,89]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[7,12,18,34,50,56,59,64,72,87]}]}"
  "p cnf 192 717\n-25 -3 0\n-26 -25 0\n-27 -25 0\n-32 -28 0\n-33 -27 0\n-33 -28 0\n-33 -32 0\n-34 -1 0\n-34 -24 0\n-34 -25 0\n-34 -26 0\n-34 -27 0\n-34 -28 0\n-34 -29 0\n-34 -30 0\n-34 -31 0\n-34 -32 0\n-34 -33 0\n-35 -5 0\n-35 -8 0\n-35 -25 0\n-35 -26 0\n-35 -34 0\n-36 -33 0\n-36 -34 0\n-38 -13 0\n-39 -28 0\n-40 -33 0\n-41 -32 0\n-41 -33 0\n-42 -8 0\n-42 -26 0\n-42 -35 0\n-42 -38 0\n-43 -33 0\n-46 -45 0\n-47 -28 0\n-47 -38 0\n-47 -45 0\n-48 -33 0\n-49 -6 0\n-49 -7 0\n-49 -32 0\n-49 -45 0\n-50 -6 0\n-50 -27 0\n-50 -31 0\n-50 -32 0\n-50 -40 0\n-50 -41 0\n-50 -43 0\n-50 -45 0\n-50 -46 0\n-50 -49 0\n-51 -4 0\n-51 -7 0\n-51 -8 0\n-51 -26 0\n-51 -35 0\n-51 -38 0\n-51 -49 0\n-52 -9 0\n-52 -24 0\n-52 -25 0\n-52 -28 0\n-52 -37 0\n-52 -41 0\n-53 -26 0\n-53 -35 0\n-53 -38 0\n-53 -52 0\n-54 -27 0\n-54 -40 0\n-54 -43 0\n-54 -46 0\n-54 -50 0\n-54 -52 0\n-55 -10 0\n-55 -26 0\n-55 -27 0\n-55 -52 0\n-55 -54 0\n-56 -50 0\n-56 -52 0\n-57 -26 0\n-57 -35 0\n-57 -38 0\n-58 -28 0\n-58 -45 0\n-58 -52 0\n-59 -27 0\n-59 -28 0\n-59 -40 0\n-59 -41 0\n-59 -43 0\n-59 -50 0\n-59 -52 0\n-59 -54 0\n-59 -58 0\n-60 -52 0\n-60 -55 0\n-61 -33 0\n-62 -50 0\n-62 -59 0\n-63 -33 0\n-63 -50 0\n-63 -52 0\n-63 -59 0\n-64 -29 0\n-64 -42 0\n-64 -44 0\n-64 -53 0\n-64 -60 0\n-65 -12 0\n-65 -38 0\n-65 -42 0\n-65 -57 0\n-65 -64 0\n-66 -33 0\n-66 -50 0\n-66 -54 0\n-66 -59 0\n-67 -39 0\n-67 -44 0\n-67 -45 0\n-67 -47 0\n-67 -48 0\n-67 -49 0\n-67 -58 0\n-67 -61 0\n-67 -64 0\n-67 -66 0\n-68 -27 0\n-68 -40 0\n-68 -41 0\n-68 -43 0\n-68 -45 0\n-68 -50 0\n-68 -58 0\n-68 -63 0\n-68 -66 0\n-68 -67 0\n-69 -45 0\n-69 -52 0\n-70 -35 0\n-71 -27 0\n-71 -28 0\n-71 -37 0\n-71 -39 0\n-71 -44 0\n-71 -45 0\n-71 -47 0\n-71 -48 0\n-71 -54 0\n-71 -56 0\n-71 -70 0\n-72 -25 0\n-72 -27 0\n-72 -33 0\n-72 -36 0\n-72 -37 0\n-72 -41 0\n-72 -52 0\n-72 -56 0\n-72 -63 0\n-72 -69 0\n-72 -71 0\n-73 -5 0\n-73 -19 0\n-73 -27 0\n-73 -29 0\n-73 -35 0\n-73 -53 0\n-73 -57 0\n-73 -60 0\n-73 -70 0\n-74 -1 0\n-74 -24 0\n-74 -25 0\n-74 -27 0\n-74 -69 0\n-74 -70 0\n-74 -71 0\n-74 -72 0\n-74 -73 0\n-75 -50 0\n-76 -18 0\n-76 -33 0\n-76 -47 0\n-76 -59 0\n-76 -71 0\n-76 -72 0\n-77 -71 0\n-77 -72 0\n-78 -30 0\n-78 -33 0\n-78 -50 0\n-78 -58 0\n-78 -62 0\n-78 -72 0\n-78 -76 0\n-79 -52 0\n-79 -71 0\n-79 -78 0\n-80 -28 0\n-80 -38 0\n-80 -45 0\n-80 -71 0\n-80 -76 0\n-81 -28 0\n-82 -28 0\n-82 -38 0\n-82 -45 0\n-82 -71 0\n-82 -76 0\n-84 -45 0\n-84 -50 0\n-84 -67 0\n-84 -71 0\n-85 -37 0\n-85 -39 0\n-85 -40 0\n-85 -45 0\n-85 -46 0\n-85 -47 0\n-85 -48 0\n-85 -50 0\n-85 -62 0\n-85 -68 0\n-85 -69 0\n-85 -71 0\n-85 -75 0\n-85 -77 0\n-85 -78 0\n-85 -79 0\n-85 -80 0\n-85 -81 0\n-85 -82 0\n-85 -84 0\n-86 -24 0\n-86 -28 0\n-86 -30 0\n-86 -37 0\n-86 -44 0\n-86 -45 0\n-86 -69 0\n-86 -71 0\n-86 -75 0\n-86 -76 0\n-86 -79 0\n-86 -84 0\n-86 -85 0\n-87 -25 0\n-87 -37 0\n-87 -52 0\n-87 -54 0\n-87 -59 0\n-87 -71 0\n-87 -72 0\n-87 -76 0\n-88 -35 0\n-88 -55 0\n-88 -73 0\n-89 -32 0\n-89 -59 0\n-89 -62 0\n-89 -68 0\n-89 -76 0\n-89 -85 0\n-89 -87 0\n-35 1 2 24 27 28 30 31 32 33 36 0\n-1 -32 -35 0\n-1 -33 -35 0\n-24 -32 -35 0\n-24 -33 -35 0\n-27 -32 -35 0\n-4 1 5 24 25 27 37 39 40 41 43 0\n-38 1 5 25 27 41 43 0\n-42 1 5 24 25 27 37 40 41 0\n-10 1 9 25 26 27 52 53 54 56 0\n-52 1 10 26 27 57 0\n-54 1 10 25 26 57 0\n-57 1 9 25 27 52 54 56 0\n-9 -27 -57 0\n-27 -52 -57 0\n-73 1 16 24 25 69 71 72 0\n-1 -72 -73 0\n-24 -72 -73 0\n-33 6 37 44 45 49 0\n-34 6 37 41 44 45 46 49 50 0\n-50 2 25 28 34 37 44 0\n-6 -34 -37 0\n-6 -34 -41 0\n-6 -34 -46 0\n-34 -37 -50 0\n-34 -44 -50 0\n-32 11 52 56 59 0\n-34 11 52 56 58 59 62 0\n-34 18 69 72 75 76 78 0\n-75 2 18 25 34 72 0\n-5 -34 -51 0\n-3 10 55 57 60 0\n-34 10 55 57 60 0\n-73 3 34 0\n-7 4 8 26 29 35 38 44 0\n-26 7 8 44 47 49 0\n-49 4 8 26 29 35 38 0\n-8 -38 -49 0\n-57 4 12 42 64 0\n-4 -57 -64 0\n-12 -42 -57 0\n-19 4 26 38 42 70 80 81 83 0\n-19 -38 -83 0\n-42 -73 -81 0\n-55 5 13 0\n-65 5 10 0\n-19 5 17 74 0\n-74 5 19 0\n-51 6 30 32 36 39 43 45 48 50 0\n-39 -50 -51 0\n-6 14 58 62 67 68 0\n-50 14 58 67 0\n-67 6 32 50 62 0\n-6 20 75 78 84 85 0\n-49 20 75 78 85 0\n-78 6 45 49 84 0\n-85 6 32 49 0\n-51 15 64 67 0\n-67 7 42 51 0\n-7 80 83 84 86 0\n-42 84 86 0\n-47 83 0\n-49 80 83 86 0\n-51 80 83 84 86 0\n-83 7 47 49 51 84 0\n-8 13 57 60 65 0\n-13 8 35 51 60 0\n-35 13 65 0\n-57 8 51 0\n-8 19 73 0\n-19 8 35 51 0\n-35 19 0\n-51 19 73 0\n-73 8 51 0\n-9 11 28 29 30 31 58 59 60 61 0\n-54 11 28 29 30 58 60 0\n-55 11 28 29 30 31 58 59 61 0\n-52 12 38 39 40 64 65 66 0\n-55 12 37 38 39 40 63 64 66 0\n-65 9 24 37 39 40 52 54 63 66 0\n-21 9 24 52 53 55 69 70 88 0\n-52 21 70 71 88 0\n-55 21 69 70 71 87 0\n-87 9 24 53 55 70 88 0\n-21 -52 -88 0\n-73 10 55 0\n-74 10 55 57 88 0\n-52 14 44 45 46 67 68 0\n-67 11 28 37 46 52 59 63 0\n-68 11 28 37 44 52 0\n-46 -52 -67 0\n-52 22 75 76 89 0\n-58 22 69 76 87 0\n-87 11 28 58 75 0\n-89 11 28 52 69 0\n-67 12 29 38 53 60 65 0\n-12 70 80 81 88 90 0\n-38 88 90 0\n-53 80 81 90 0\n-64 70 81 88 0\n-65 70 80 81 90 0\n-81 12 53 64 65 88 0\n-90 12 38 53 65 70 88 0\n-57 19 0\n-65 19 73 0\n-73 13 65 0\n-58 15 39 47 48 64 66 0\n-64 14 30 45 48 58 61 68 0\n-68 15 30 39 47 64 0\n-58 23 84 85 0\n-67 23 75 85 89 0\n-15 80 84 86 90 0\n-64 84 86 0\n-67 80 86 90 0\n-18 16 27 31 36 71 74 77 0\n-71 18 33 36 78 0\n-71 41 43 83 0\n-72 40 43 81 82 83 0\n-74 40 41 43 79 81 82 83 0\n-81 16 27 41 43 72 74 0\n-40 -74 -83 0\n-41 -74 -83 0\n-21 16 27 56 72 74 0\n-72 21 54 0\n-74 21 54 56 87 0\n-33 20 79 85 0\n-50 18 72 76 79 0\n-72 20 46 50 85 0\n-85 18 33 41 72 0\n-18 22 56 59 62 87 89 0\n-78 22 56 59 87 0\n-89 18 33 56 72 0\n-20 36 43 48 77 82 83 86 0\n-85 36 43 83 0\n-78 23 68 0\n-89 20 50 0\n-54 22 76 77 89 0\n-59 21 71 77 0\n-89 21 31 54 71 0\n-54 79 81 82 90 0\n-71 63 66 90 0\n-81 21 54 63 66 87 0\n-82 21 54 63 87 0\n-87 40 66 81 82 90 0\n-59 23 79 85 0\n-68 22 76 79 87 0\n-76 23 63 68 0\n-68 77 82 86 90 0\n-85 61 66 90 0\n-29 70 0\n-70 29 0\n-40 31 46 48 0\n-48 31 40 46 0\n-61 36 62 0\n-62 36 61 0\n-37 69 79 0\n-80 39 82 0\n-82 39 80 0\n-43 66 0\n-44 84 0\n-84 44 0\n-88 60 0\n-81 86 0\n-86 81 0\n-83 90 0\n-90 83 0\n-2 91 0\n-3 92 0\n-93 6 0\n-6 93 0\n-94 7 0\n-95 8 0\n-8 95 0\n-10 96 0\n-12 97 0\n-13 98 0\n-14 99 0\n-16 100 0\n-18 101 0\n-19 102 0\n-20 103 0\n-21 104 0\n-22 105 0\n-23 106 0\n-91 107 0\n-92 108 0\n-108 109 0\n-107 -108 110 0\n-111 94 95 0\n-95 111 0\n-112 93 111 0\n-111 112 0\n-93 112 0\n-96 113 0\n-113 114 0\n-114 115 0\n-112 115 0\n-112 -114 116 0\n-115 117 0\n-116 118 0\n-109 -115 118 0\n-110 -115 119 0\n-98 120 0\n-98 -99 121 0\n-120 122 0\n-121 123 0\n-97 122 0\n-100 124 0\n-124 125 0\n-125 126 0\n-122 126 0\n-122 -125 127 0\n-123 127 0\n-103 128 0\n-102 128 0\n-128 129 0\n-101 129 0\n-101 -128 130 0\n-106 131 0\n-105 131 0\n-131 132 0\n-104 132 0\n-104 -131 133 0\n-132 134 0\n-133 135 0\n-129 -132 135 0\n-129 -133 136 0\n-130 -132 136 0\n-136 138 0\n-126 -134 137 0\n-126 -135 138 0\n-126 -136 139 0\n-127 -135 139 0\n-117 -139 140 0\n-118 -138 140 0\n-119 -137 140 0\n-140 0\n-141 42 47 49 51 0\n-51 141 0\n-142 64 67 0\n-67 142 0\n-143 26 27 73 74 0\n-73 143 0\n-144 25 34 35 0\n-25 144 0\n-34 144 0\n-145 32 58 78 89 0\n-89 145 0\n-146 52 72 87 0\n-52 146 0\n-147 53 55 57 65 0\n-65 147 0\n-148 33 50 54 59 68 0\n-50 148 0\n-149 24 28 38 45 71 76 85 0\n-38 149 0\n-71 149 0\n-76 149 0\n-150 141 142 0\n-151 141 0\n-151 142 0\n-141 -142 151 0\n-152 143 144 0\n-153 143 0\n-153 144 0\n-143 -144 153 0\n-154 150 0\n-154 151 153 0\n-155 151 0\n-154 152 0\n-155 153 0\n-151 -153 155 0\n-156 145 146 0\n-157 145 0\n-157 146 0\n-145 -146 157 0\n-158 148 149 0\n-159 148 0\n-159 149 0\n-148 -149 159 0\n-160 147 159 0\n-161 147 0\n-160 158 0\n-161 159 0\n-147 -159 161 0\n-162 156 0\n-162 157 161 0\n-163 157 0\n-162 160 0\n-163 161 0\n-157 -161 163 0\n-164 154 0\n-164 155 163 0\n-164 162 0\n-155 -163 165 0\n164 0\n-165 0\n-166 29 60 0\n-29 166 0\n-60 166 0\n-167 70 88 0\n-70 167 0\n-88 167 0\n-168 39 43 83 0\n-39 168 0\n-43 168 0\n-83 168 0\n-169 66 80 90 0\n-66 169 0\n-80 169 0\n-90 169 0\n-170 31 36 41 0\n-31 170 0\n-36 170 0\n-41 170 0\n-171 40 56 61 0\n-40 171 0\n-56 171 0\n-61 171 0\n-172 46 62 63 0\n-46 172 0\n-62 172 0\n-63 172 0\n-173 30 37 44 48 81 82 0\n-37 173 0\n-44 173 0\n-81 173 0\n-174 69 75 84 86 0\n-69 174 0\n-84 174 0\n-86 174 0\n-175 77 79 0\n-77 175 0\n-79 175 0\n-176 166 167 0\n-167 176 0\n-166 176 0\n-177 169 170 0\n-170 177 0\n-169 177 0\n-178 170 0\n-179 168 177 0\n-177 179 0\n-180 168 178 0\n-168 179 0\n-168 -177 180 0\n-181 176 179 0\n-179 181 0\n-182 176 180 0\n-180 182 0\n-176 181 0\n-176 -180 183 0\n-184 171 172 0\n-172 184 0\n-171 184 0\n-185 174 175 0\n-175 185 0\n-174 185 0\n-186 173 185 0\n-185 186 0\n-173 186 0\n-173 -185 187 0\n-188 184 186 0\n-186 188 0\n-187 189 0\n-184 188 0\n-184 -186 189 0\n-184 -187 190 0\n-190 192 0\n-191 182 188 0\n-181 -189 192 0\n-182 -188 192 0\n-183 192 0\n191 0\n-192 0\n-3 -12 -13 -21 -28 -50 -51 -55 -67 -72 -73 -83 -89 -90 0\n-3 -12 -13 -21 -32 -51 -55 -59 -67 -72 -73 -83 -85 -90 0\n-3 -10 -11 -22 -32 -51 -54 -65 -67 -72 -73 -83 -85 -90 0\n-3 -9 -10 -21 -32 -51 -59 -65 -67 -72 -73 -83 -85 -90 0\n-3 -9 -10 -21 -28 -50 -51 -65 -67 -72 -73 -83 -89 -90 0\n-3 -6 -10 -20 -28 -51 -54 -65 -67 -72 -73 -83 -89 -90 0\n-3 -6 -10 -20 -33 -51 -52 -65 -67 -71 -73 -83 -89 -90 0\n-2 -3 -10 -18 -50 -51 -52 -65 -67 -71 -73 -83 -89 -90 0\n-8 -9 -11 -19 -34 -49 -57 -64 -68 -74 -78 -81 -86 -87 0\n-8 -11 -13 -19 -34 -49 -55 -64 -68 -74 -78 -81 -86 -87 0\n-8 -19 -21 -22 -34 -49 -52 -57 -64 -68 -74 -78 -81 -86 0\n-8 -11 -13 -16 -34 -49 -55 -64 -68 -73 -78 -81 -86 -87 0\n-8 -10 -15 -22 -34 -49 -54 -58 -65 -72 -73 -83 -85 -90 0\n-8 -10 -15 -22 -34 -49 -52 -65 -68 -71 -73 -78 -83 -90 0\n-7 -8 -10 -18 -34 -50 -52 -65 -67 -71 -73 -83 -89 -90 0\n-10 -17 -18 -19 -34 -50 -51 -52 -65 -67 -71 -83 -89 -90 0\n-12 -17 -18 -19 -34 -50 -51 -52 -57 -67 -71 -83 -89 -90 0\n-10 -18 -19 -21 -34 -50 -51 -52 -65 -67 -74 -80 -82 -89 0\n-12 -18 -19 -21 -34 -50 -51 -52 -57 -67 -74 -80 -82 -89 0\n-6 -9 -11 -19 -34 -51 -57 -64 -68 -74 -78 -81 -86 -87 0\n-6 -11 -13 -19 -34 -51 -55 -64 -68 -74 -78 -81 -86 -87 0\n-6 -19 -21 -22 -34 -51 -52 -57 -64 -68 -74 -78 -81 -86 0\n-10 -18 -19 -21 -34 -50 -51 -52 -65 -67 -74 -81 -86 -89 0\n-12 -18 -19 -21 -34 -50 -51 -52 -57 -67 -74 -81 -86 -89 0\n-14 -18 -19 -21 -34 -50 -51 -52 -57 -64 -74 -81 -86 -89 0\n-9 -18 -19 -23 -34 -50 -51 -57 -58 -64 -74 -81 -86 -87 0\n-13 -18 -19 -23 -34 -50 -51 -55 -58 -64 -74 -81 -86 -87 0\n-10 -18 -19 -21 -34 -50 -51 -52 -65 -67 -74 -83 -89 -90 0\n-10 -19 -21 -23 -34 -50 -51 -52 -65 -67 -74 -76 -83 -90 0\n-12 -18 -19 -21 -34 -50 -51 -52 -57 -67 -74 -83 -89 -90 0\n-12 -19 -21 -23 -34 -50 -51 -52 -57 -67 -74 -76 -83 -90 0\n-12 -13 -15 -19 -33 -35 -49 -55 -58 -74 -83 -85 -87 -90 0\n-12 -13 -15 -19 -28 -35 -49 -55 -68 -74 -78 -83 -87 -90 0\n-13 -19 -20 -23 -33 -35 -49 -55 -58 -64 -74 -81 -86 -87 0\n-2 -11 -13 -19 -35 -49 -55 -64 -68 -74 -78 -81 -86 -87 0\n-9 -10 -15 -19 -33 -35 -49 -58 -65 -74 -83 -85 -87 -90 0\n-9 -10 -15 -19 -28 -35 -49 -65 -68 -74 -78 -83 -87 -90 0\n-10 -12 -13 -18 -34 -50 -51 -52 -67 -71 -73 -83 -89 -90 0\n-6 -10 -15 -22 -34 -51 -54 -58 -65 -72 -73 -83 -85 -90 0\n-6 -10 -15 -22 -34 -51 -52 -65 -68 -71 -73 -78 -83 -90 0\n-10 -14 -15 -18 -34 -50 -51 -52 -65 -71 -73 -83 -89 -90 0\n-10 -11 -15 -20 -34 -45 -51 -54 -65 -72 -73 -83 -89 -90 0\n-6 -10 -11 -20 -34 -51 -54 -65 -67 -72 -73 -80 -82 -89 0\n-6 -10 -11 -20 -34 -51 -54 -65 -67 -72 -73 -81 -86 -89 0\n-6 -9 -10 -21 -34 -51 -59 -65 -67 -72 -73 -83 -85 -90 0\n-6 -9 -10 -23 -34 -51 -59 -65 -67 -71 -73 -78 -83 -90 0\n-6 -10 -22 -23 -34 -51 -52 -65 -67 -71 -73 -78 -83 -90 0\n-6 -10 -18 -20 -34 -51 -52 -65 -67 -71 -73 -83 -89 -90 0\n-6 -10 -11 -22 -34 -51 -54 -65 -67 -72 -73 -83 -85 -90 0\n-6 -10 -11 -20 -34 -51 -54 -65 -67 -72 -73 -83 -89 -90 0\n-9 -10 -11 -21 -34 -50 -51 -65 -67 -72 -73 -80 -82 -89 0\n-9 -10 -11 -21 -34 -50 -51 -65 -67 -72 -73 -81 -86 -89 0\n-9 -10 -11 -21 -34 -50 -51 -65 -67 -72 -73 -83 -89 -90 0\n-9 -10 -11 -18 -34 -50 -51 -65 -67 -71 -73 -83 -89 -90 0\n-10 -16 -18 -21 -34 -50 -51 -52 -65 -67 -73 -80 -82 -89 0\n-10 -16 -18 -21 -34 -50 -51 -52 -65 -67 -73 -81 -86 -89 0\n-10 -16 -18 -21 -34 -50 -51 -52 -65 -67 -73 -83 -89 -90 0\n-10 -16 -21 -23 -34 -50 -51 -52 -65 -67 -73 -76 -83 -90 0\n-10 -18 -22 -23 -34 -50 -51 -52 -65 -67 -71 -73 -83 -90 0\n-11 -12 -13 -21 -34 -50 -51 -55 -67 -72 -73 -80 -82 -89 0\n-11 -12 -13 -21 -34 -50 -51 -55 -67 -72 -73 -81 -86 -89 0\n-11 -12 -13 -21 -34 -50 -51 -55 -67 -72 -73 -83 -89 -90 0\n-11 -12 -13 -18 -34 -50 -51 -55 -67 -71 -73 -83 -89 -90 0\n-6 -12 -13 -21 -34 -51 -55 -59 -67 -72 -73 -83 -85 -90 0\n-6 -12 -13 -23 -34 -51 -55 -59 -67 -71 -73 -78 -83 -90 0\n-13 -21 -22 -23 -34 -50 -51 -55 -58 -64 -72 -73 -81 -86 0\n-11 -13 -14 -21 -34 -50 -51 -55 -64 -72 -73 -81 -86 -89 0\n-13 -16 -18 -23 -34 -50 -51 -55 -58 -64 -73 -81 -86 -87 0\n-6 -11 -13 -16 -34 -51 -55 -64 -68 -73 -78 -81 -86 -87 0\n12 15 29 38 44 47 53 60 64 65 67 70 80 81 84 86 88 90 0\n7 15 42 47 49 51 64 67 80 83 84 86 90 0\n8 13 19 35 51 57 60 65 73 88 0\n"
  "718 154 0 566 562 0\n719 162 0 566 564 0\n720 150 0 718 537 0\n721 152 0 718 540 0\n722 156 0 719 556 0\n723 160 0 719 559 0\n724 158 0 723 553 0\n725 -190 0 645 639 0\n726 -183 0 645 643 0\n727 173 181 0 618 613 610 581 621 606 573 368 615 577 332 580 607 570 569 572 596 597 431 434 370 369 367 371 382 384 715 0\n728 86 40 181 0 566 618 615 575 613 610 580 428 581 621 606 573 368 579 572 577 576 433 384 370 367 371 388 414 510 348 519 531 545 539 558 563 0\n729 112 -52 72 67 184 181 0 719 723 566 618 615 576 613 609 584 577 404 625 587 728 245 610 581 621 606 573 368 241 240 585 387 249 525 549 554 560 563 541 535 64 539 531 510 118 112 551 81 521 86 514 17 534 85 285 174 512 374 310 572 352 90 557 544 434 251 250 244 243 624 591 607 569 462 463 460 440 443 307 339 290 326 322 397 517 670 0\n730 111 -112 -74 -34 -57 -21 -52 87 -64 -145 -148 -86 0 18 17 374 97 90 77 434 250 249 460 461 443 439 339 45 523 267 416 517 667 0\n731 95 -111 4 35 26 44 181 0 618 613 610 581 621 606 573 368 607 569 443 459 305 441 0\n732 72 87 67 184 181 0 724 723 719 566 618 615 576 613 609 584 577 404 625 587 728 245 610 581 621 606 573 368 241 240 585 387 249 525 549 554 560 563 539 531 510 118 112 110 541 535 534 530 557 545 544 551 547 434 250 244 332 572 519 64 77 81 90 97 352 521 85 86 174 310 374 285 514 512 17 18 729 730 731 442 57 508 54 523 267 416 517 656 0\n733 -8 139 78 74 27 25 87 -64 184 181 0 723 566 118 112 110 618 615 576 613 609 584 577 404 625 587 728 245 610 581 621 606 573 368 241 240 585 387 249 525 549 554 560 563 541 535 534 539 530 551 251 250 248 246 242 583 624 591 423 589 332 572 20 57 514 508 11 325 512 451 174 376 484 521 446 486 353 473 452 475 492 481 496 502 503 497 483 493 476 489 490 474 454 453 447 380 416 378 0\n734 -7 42 -141 47 0 42 56 508 0\n735 -112 87 67 184 181 0 723 566 507 732 200 184 158 157 618 615 577 332 576 613 609 584 404 625 587 728 245 610 581 621 606 573 368 241 240 585 387 249 525 549 554 560 563 539 530 531 510 110 734 441 118 112 541 534 551 251 250 248 246 244 624 592 572 467 469 504 733 442 459 461 439 41 324 306 451 512 484 174 376 486 521 446 353 473 452 475 492 481 496 502 503 497 483 493 476 489 490 474 454 453 447 380 416 321 0\n736 58 -21 -55 -50 -34 -73 -51 -72 -64 67 -145 -86 56 62 0 96 17 118 376 200 163 434 298 517 322 712 0\n737 49 87 67 184 181 0 723 719 566 735 462 460 443 463 440 732 184 158 157 618 615 577 332 576 613 609 584 404 625 587 728 245 610 581 621 606 573 368 241 240 585 387 249 525 549 554 560 563 539 530 531 510 110 734 118 112 541 535 534 557 544 551 434 251 246 244 243 588 624 592 591 572 508 306 59 512 514 174 376 290 521 353 736 363 380 711 0\n738 87 67 184 181 0 723 566 618 615 576 613 609 584 577 404 625 587 728 245 610 581 621 606 573 368 241 240 585 387 249 525 549 554 560 563 539 531 510 118 112 541 534 551 732 158 184 735 462 460 443 737 61 339 344 521 512 79 0\n739 -55 74 -49 -87 -64 -144 -143 -145 -148 -86 179 0 61 54 43 270 259 257 256 255 253 118 434 244 243 241 613 609 585 615 576 79 80 512 390 172 344 376 514 18 523 139 360 517 657 0\n740 74 -49 -87 -64 -86 181 0 724 723 719 566 118 112 618 615 576 613 609 584 577 404 245 610 581 621 606 573 368 241 240 585 387 249 525 549 554 560 563 541 535 534 557 544 551 547 572 739 521 354 85 174 284 512 0\n741 -57 -74 -49 -87 -64 -144 -145 -148 -86 56 0 180 177 61 54 43 270 257 256 255 253 434 244 243 241 86 374 339 283 514 18 523 139 360 517 654 0\n742 -8 -55 57 -74 -49 -87 -64 -144 -145 -148 -86 60 0 185 54 43 270 257 256 255 253 118 434 244 243 241 20 336 340 514 18 523 139 360 517 655 0\n743 35 8 57 73 51 65 176 0 607 570 606 573 341 337 717 0\n744 58 -49 -87 -64 171 181 0 723 566 719 724 621 118 61 587 728 740 185 588 618 615 576 613 609 584 577 404 245 610 581 606 573 368 241 240 585 387 249 525 547 549 554 557 544 560 563 541 535 741 607 570 112 551 521 742 743 342 338 180 177 54 43 270 257 256 434 242 589 583 569 517 347 196 523 271 680 0\n745 -49 -87 -64 171 181 0 724 723 719 566 257 256 118 112 618 615 576 613 609 584 577 404 587 728 245 610 581 621 606 573 368 241 240 585 387 249 525 549 554 560 563 541 535 557 544 551 547 434 251 248 588 607 570 54 61 740 185 741 521 742 743 338 342 744 139 198 380 523 325 679 0\n746 -58 -55 -74 -34 -51 -87 -64 -148 -86 85 0 301 315 318 18 259 257 256 434 251 249 248 246 139 198 380 523 299 672 0\n747 -55 -74 -87 -64 171 181 0 724 719 566 618 615 577 332 576 613 609 584 404 587 728 245 610 581 621 606 573 368 241 240 585 387 249 525 549 554 560 563 539 530 110 745 508 541 535 253 59 514 301 318 18 17 270 257 256 557 544 547 434 251 242 589 583 607 569 315 746 517 347 197 326 666 523 0\n748 58 -9 -57 -74 -34 -51 49 -87 -64 -145 -148 -86 0 301 318 18 17 270 257 256 434 251 248 245 241 517 364 197 326 665 523 0\n749 -74 -87 -64 171 181 0 724 723 719 566 618 615 577 332 576 613 609 584 404 587 728 245 610 581 621 606 573 368 241 240 585 387 249 525 549 554 560 563 539 530 110 745 508 541 535 253 59 514 301 18 259 257 256 118 112 557 544 551 547 434 251 248 246 572 318 747 521 354 748 139 198 380 523 299 671 0\n750 -58 -55 -16 -73 -34 -51 -87 -64 -148 -86 85 0 118 376 18 259 257 256 434 251 249 248 246 139 198 380 523 299 713 0\n751 67 184 181 0 724 723 719 566 618 615 576 613 609 584 577 404 625 587 728 245 610 581 621 606 573 368 241 240 585 387 249 525 549 554 560 563 541 535 534 539 531 530 557 544 551 547 434 251 242 589 332 583 607 569 510 110 112 118 738 253 256 257 259 270 745 508 58 59 514 12 17 18 749 512 390 174 376 521 750 517 347 197 326 714 523 0\n752 -53 74 25 -153 0 535 534 68 69 173 514 512 12 0\n753 -34 -87 68 58 -145 -148 0 270 257 256 17 18 517 523 197 0\n754 -35 49 -141 47 0 33 59 508 0\n755 34 35 -144 -143 0 514 1 2 3 179 304 512 0\n756 -9 -65 -10 -50 -73 184 181 0 724 566 719 751 129 618 615 576 613 609 584 577 404 625 587 728 245 610 581 621 606 573 368 241 240 585 387 249 525 549 554 557 544 560 563 541 534 535 332 539 530 128 754 755 17 197 517 547 142 753 579 624 593 434 76 412 96 314 508 545 242 589 583 607 570 569 62 345 697 519 0\n757 55 -50 74 184 181 0 723 724 566 719 751 129 618 615 576 613 609 584 577 404 625 587 728 245 610 581 621 606 573 368 241 240 585 387 249 525 549 554 557 544 560 563 541 534 535 332 539 530 128 754 755 17 197 517 547 142 753 579 624 593 434 76 412 12 11 512 314 508 174 10 752 551 250 243 575 356 521 756 350 163 390 397 701 0\n758 -50 74 184 181 0 719 724 566 618 615 577 332 576 613 609 584 404 625 587 728 245 610 581 621 606 573 368 241 240 585 387 249 525 549 554 560 563 539 530 751 128 434 541 534 535 754 755 12 11 512 314 508 168 547 557 544 129 142 753 17 131 545 243 242 589 624 593 579 583 607 569 575 76 96 197 412 517 757 81 349 347 315 519 706 0\n759 -89 -6 50 -51 -73 53 87 -34 -67 -146 -147 -148 -86 166 0 174 18 11 10 8 142 129 434 242 241 570 569 265 406 523 77 82 282 346 519 521 689 0\n760 74 184 181 0 723 566 719 724 618 615 576 613 609 584 577 404 625 587 728 245 610 581 621 606 573 368 241 240 585 387 249 525 547 549 554 557 544 751 129 142 560 563 541 534 535 332 539 530 128 754 755 753 18 17 12 11 10 545 551 434 242 583 624 591 423 575 607 752 512 314 508 758 319 759 517 200 519 77 97 523 0\n761 -65 -51 -89 -50 -21 -52 -74 -34 -67 -86 0 185 343 301 250 249 184 397 434 316 668 0\n762 -51 -89 -50 -21 -52 -74 -34 -67 -147 -86 88 0 250 249 184 397 81 71 185 131 434 343 761 372 521 669 0\n763 184 181 0 724 723 719 566 618 613 610 581 621 606 573 368 615 576 609 585 577 387 584 404 332 572 625 587 728 240 241 245 249 525 549 547 554 551 560 557 563 544 545 539 541 530 534 535 751 128 129 142 754 755 17 18 753 760 184 185 519 77 97 352 523 197 517 762 508 31 116 339 743 0\n764 181 0 725 618 613 615 610 577 580 581 332 727 763 638 632 628 600 601 331 330 382 383 334 333 384 716 0\n765 -189 0 764 645 641 0\n766 -187 0 765 635 0\n767 -163 -89 50 72 33 0 270 267 265 558 560 545 554 519 548 77 523 0\n768 -64 70 0 766 111 113 431 432 383 370 601 597 628 632 0\n769 -82 -149 71 -34 0 13 9 212 213 215 238 525 0\n770 -173 82 69 -34 0 766 765 16 15 631 632 637 627 628 624 625 604 600 601 591 587 426 430 433 423 594 0\n771 -85 -163 72 -34 0 560 554 548 558 545 544 18 17 227 229 234 269 517 90 99 519 523 256 0\n772 -38 176 60 73 35 0 26 60 87 115 336 743 0\n773 -45 -163 72 -34 0 560 554 548 558 545 544 18 52 89 137 753 519 77 97 523 0\n774 -76 -157 72 32 0 545 544 201 260 268 519 517 90 0\n775 142 -74 -34 0 720 566 185 184 183 181 23 17 13 9 531 529 539 563 558 560 552 554 549 769 770 596 597 431 434 331 771 773 774 525 26 38 60 70 87 115 206 508 521 333 308 101 262 313 717 0\n776 132 -148 89 50 76 77 68 71 33 0 491 492 490 452 453 408 407 523 0\n777 76 -149 -74 -34 0 726 645 566 719 507 14 421 768 775 510 123 183 769 427 181 770 597 434 384 436 577 581 610 616 620 642 634 630 627 603 636 624 593 23 185 622 607 570 772 606 573 392 391 218 331 595 142 132 129 128 126 125 184 18 17 13 9 525 227 234 269 399 771 327 517 449 563 440 544 539 463 557 530 467 554 508 469 548 55 343 504 450 485 488 776 498 499 502 505 481 470 477 468 445 465 309 349 464 357 444 0\n778 12 -149 -74 -34 0 645 726 722 719 566 185 14 421 768 775 510 128 126 218 181 183 769 770 597 434 331 17 184 777 774 558 563 539 530 508 343 55 18 142 557 554 548 190 260 129 201 268 517 543 519 77 523 123 427 384 436 577 581 610 616 622 606 573 352 620 642 636 624 593 417 23 607 570 772 391 132 12 11 8 309 348 281 674 0\n779 -149 -74 -34 0 726 645 719 722 566 14 421 768 775 510 218 142 129 128 126 123 185 184 183 181 18 17 769 770 427 597 434 384 331 436 581 577 610 616 620 622 642 606 636 573 624 593 777 190 201 260 268 774 417 517 557 558 543 552 554 563 519 548 539 71 77 81 352 530 523 508 343 778 114 676 521 0\n780 -83 -12 -74 -34 0 723 719 724 566 14 421 768 775 510 128 126 779 549 554 560 563 539 530 184 547 129 142 557 544 753 545 519 81 71 551 114 521 311 508 374 17 18 97 77 523 197 517 202 528 397 84 395 435 675 0\n781 -12 -74 -34 0 723 566 724 719 14 421 768 775 510 129 779 549 554 557 544 17 18 142 547 184 753 545 519 97 77 523 197 517 202 528 397 127 16 361 422 100 432 84 395 81 71 67 560 563 539 530 551 132 429 218 128 126 114 521 374 311 508 762 433 780 389 334 664 0\n782 83 -74 -34 0 566 719 724 14 421 768 775 510 132 184 779 547 129 142 549 554 557 544 753 545 519 127 16 361 422 123 526 781 348 84 77 395 18 97 523 17 197 517 128 126 560 563 539 530 116 508 761 433 11 12 8 117 281 185 375 202 528 397 67 429 218 389 334 663 0\n783 -74 -34 0 724 719 566 14 421 768 18 17 16 12 11 8 184 185 775 510 123 126 127 128 129 132 142 779 526 528 549 547 554 560 557 563 544 545 539 753 519 530 77 84 97 202 361 523 395 422 197 397 517 781 348 116 117 375 508 281 782 435 673 0\n784 -65 -19 -51 -50 -34 0 718 566 783 12 11 169 512 534 541 563 558 545 524 14 421 768 538 531 510 129 138 544 753 60 227 52 13 9 560 554 549 197 17 517 268 525 167 519 106 120 411 51 50 387 25 18 386 301 317 316 661 0\n785 -19 -51 -50 -34 0 718 566 301 60 524 227 197 138 120 106 52 51 50 783 14 421 768 25 18 17 13 12 11 9 169 317 512 534 541 538 563 531 558 560 510 544 545 552 554 129 753 517 549 268 525 167 386 387 411 519 71 81 100 784 366 521 662 0\n786 65 -89 -83 -52 -67 -51 -50 -34 0 723 163 83 18 402 268 435 11 12 785 374 8 281 81 343 175 173 60 227 52 14 13 9 376 366 521 683 551 525 549 0\n787 -89 -83 -52 -67 -51 -50 -34 0 567 435 11 12 785 374 8 281 520 163 144 516 343 513 536 509 511 532 542 565 524 83 76 18 16 10 9 518 402 546 561 786 522 555 550 527 409 286 702 0\n788 -18 -83 -52 -67 -51 -50 -34 0 719 129 197 17 787 517 544 557 554 549 785 374 343 173 81 552 521 186 227 381 435 11 12 8 281 255 60 103 96 83 52 13 9 187 400 525 704 0\n789 -83 -52 -67 -51 -50 -34 0 719 11 12 785 374 8 281 202 163 144 81 129 343 263 173 227 197 186 14 421 25 18 17 10 9 435 787 381 517 544 557 552 521 788 386 397 352 286 703 0\n790 -52 -67 -51 -50 -34 0 764 723 719 129 14 421 785 343 263 571 175 568 605 617 173 374 320 60 16 25 50 582 227 197 186 120 52 51 17 13 12 11 10 9 8 81 144 163 281 789 436 574 387 612 352 286 608 578 209 427 299 525 549 554 551 557 521 544 700 517 0\n791 -65 83 -67 -51 -50 -34 0 719 764 320 120 436 16 25 50 582 14 421 785 343 263 571 175 568 605 617 51 574 612 608 578 427 106 76 524 129 138 60 227 52 13 9 387 209 525 549 554 557 544 753 413 790 545 519 197 17 517 96 53 295 359 301 49 350 316 696 0\n792 83 -67 -51 -50 -34 0 764 723 719 106 96 53 295 13 790 359 129 14 421 785 343 263 571 175 568 605 617 173 374 320 60 16 25 50 582 524 227 197 138 120 76 52 51 17 9 436 574 387 612 608 578 209 427 525 549 554 551 557 544 545 753 517 519 413 791 376 366 521 705 0\n793 -72 65 -89 -67 -51 -50 -34 0 723 785 343 175 173 60 14 366 376 268 792 435 106 96 53 295 13 790 359 374 227 76 52 9 167 394 707 525 521 549 551 0\n794 65 -89 -67 -51 -50 -34 0 645 719 270 268 792 577 435 581 610 616 620 642 634 630 628 599 106 96 53 295 13 790 359 785 343 175 173 374 60 227 197 186 52 14 9 376 366 793 519 299 545 557 552 554 521 549 708 525 0\n795 72 -89 -67 -51 -50 -34 0 645 719 301 794 316 120 106 76 790 49 320 295 9 350 270 268 792 577 435 581 610 616 620 642 634 630 628 599 96 53 13 359 785 343 60 227 197 186 52 519 299 545 699 557 525 554 549 0\n796 -89 -67 -51 -50 -34 0 792 435 106 96 53 295 13 790 359 785 343 320 301 120 76 49 9 794 350 316 795 394 698 0\n797 -87 -149 38 -50 -34 0 227 52 13 9 258 260 525 0\n798 -67 -51 -50 -34 0 722 719 60 227 197 52 17 13 9 129 790 796 517 543 544 557 554 549 797 519 167 192 525 0\n799 -72 -51 -50 -34 0 566 14 421 768 798 510 531 539 563 560 554 549 60 227 52 13 9 167 192 525 0\n800 -51 -50 -34 0 566 296 227 197 186 138 120 106 53 52 51 50 14 421 768 17 13 12 11 9 8 60 785 343 374 173 798 510 328 531 539 563 558 560 544 545 552 554 549 797 799 519 774 81 90 144 358 281 525 299 521 517 387 411 686 0\n801 -71 72 -50 -34 0 720 718 566 800 217 197 120 106 54 51 50 783 14 421 768 25 18 17 12 11 10 8 152 247 258 386 387 411 331 335 508 529 530 510 538 539 129 534 752 563 512 558 560 174 344 544 545 552 517 519 81 281 521 660 0\n802 -38 176 60 35 0 26 115 772 376 0\n803 -155 -50 -34 0 800 295 54 50 49 783 14 421 768 12 11 10 9 8 539 541 530 534 512 168 531 279 510 508 126 0\n804 -38 -50 -34 0 718 800 54 783 12 11 26 34 38 115 508 376 530 512 538 534 0\n805 72 -50 -34 0 566 804 803 563 560 554 549 558 227 52 17 13 9 801 774 525 0\n806 -50 -34 0 566 13 9 52 227 803 563 560 554 549 804 805 167 192 525 0\n807 -45 85 -34 0 720 718 566 806 783 14 421 768 18 17 13 12 11 10 8 36 39 44 89 125 137 143 207 216 245 510 331 531 529 538 539 508 534 752 563 328 334 512 558 560 773 382 174 544 552 554 163 200 398 517 548 265 365 523 82 282 521 687 0\n808 -38 -34 0 718 783 14 421 768 12 11 26 34 38 60 115 376 512 534 538 530 531 508 510 128 0\n809 -55 149 -34 0 566 719 724 547 549 554 557 544 14 421 768 560 563 539 531 510 142 129 753 545 806 18 17 81 82 519 523 200 265 517 0\n810 -83 -20 -72 149 -34 0 723 719 724 566 18 14 421 768 549 554 560 563 539 531 510 142 547 806 557 544 129 17 200 517 265 523 166 163 13 365 551 783 10 541 752 12 11 534 512 174 809 521 175 303 530 126 128 25 130 425 323 293 292 168 9 8 127 16 294 422 279 508 435 695 0\n811 -72 149 85 -34 0 719 724 566 723 549 551 783 10 554 560 563 541 752 12 11 534 512 174 809 521 175 303 539 530 14 421 768 531 510 126 128 806 17 25 130 425 323 293 292 168 9 8 127 16 294 422 279 508 568 132 429 547 557 544 142 129 753 218 545 18 13 163 166 194 200 398 517 265 759 365 523 810 403 334 688 0\n812 85 76 71 -34 0 724 719 566 808 806 14 421 768 18 13 9 807 525 549 547 554 560 557 563 544 545 539 531 510 129 142 753 811 519 77 97 523 0\n813 72 76 71 -34 0 566 719 645 507 812 239 252 331 269 236 234 233 232 230 229 228 225 222 221 220 808 806 783 14 421 768 25 18 17 16 12 11 771 299 563 449 385 539 541 487 448 530 531 534 478 734 510 512 479 329 129 132 323 384 174 175 480 334 517 440 581 577 544 463 610 557 467 616 554 469 620 548 504 642 776 636 496 624 501 503 593 505 482 470 477 468 445 465 349 464 303 444 0\n814 54 -10 -67 -72 -85 -34 0 566 719 269 234 17 129 517 544 557 552 783 10 558 563 541 752 12 11 534 512 174 78 521 128 225 239 252 331 539 530 508 554 548 236 384 436 806 228 323 164 163 229 18 8 523 394 280 690 0\n815 -10 -67 -72 -85 76 -34 0 719 726 566 783 12 11 269 234 17 129 517 544 558 563 541 534 512 174 128 225 239 252 331 539 530 508 236 384 436 577 581 610 616 622 607 570 10 752 557 552 806 228 323 233 15 14 13 78 521 814 346 407 694 0\n816 -67 -72 -85 76 -34 0 719 566 726 239 252 331 269 236 234 229 228 225 808 806 783 18 17 14 12 11 10 8 128 129 323 384 517 436 581 544 577 610 557 558 616 554 563 622 548 539 541 607 530 534 752 570 508 512 301 174 815 316 282 356 376 366 523 394 709 0\n817 -51 -65 -54 -22 -58 -73 -72 -85 -34 0 644 226 14 421 768 225 221 121 377 74 16 25 162 582 611 230 238 770 233 235 602 239 232 252 598 626 629 224 228 165 590 424 222 164 586 623 633 640 263 571 175 568 605 619 614 574 237 410 174 11 10 8 282 223 806 17 15 319 684 0\n818 76 71 -34 0 644 720 718 566 806 783 14 421 768 25 18 17 16 12 11 10 8 812 221 222 224 225 226 228 229 230 232 233 234 235 237 238 239 252 269 424 602 770 331 598 626 629 813 162 164 165 259 582 586 590 611 623 633 640 816 510 531 529 538 539 534 752 563 512 558 560 174 175 263 544 552 554 568 571 517 548 605 99 363 619 523 614 74 82 121 282 410 574 521 377 817 508 344 658 0\n819 -76 -34 0 719 566 722 806 14 421 768 18 17 190 192 201 260 268 774 557 558 554 563 548 539 531 510 129 142 517 523 543 77 519 0\n820 -10 -78 -59 -34 0 719 566 783 12 11 819 818 167 258 97 519 545 558 563 541 534 512 174 806 17 104 14 421 768 539 531 510 323 219 247 331 152 530 734 329 10 752 557 552 122 108 411 94 95 387 231 203 415 155 154 8 78 280 521 691 0\n821 -59 89 58 -34 0 722 566 726 819 818 219 247 331 258 231 203 167 152 808 806 783 14 421 768 17 12 11 10 94 95 97 104 108 122 415 387 519 411 577 545 543 581 558 517 610 563 616 539 541 622 530 531 534 752 607 734 510 512 570 329 323 168 820 316 356 376 366 710 0\n822 68 89 58 -34 0 723 719 566 821 819 818 219 247 331 258 208 167 155 154 152 806 783 14 421 768 18 17 12 11 10 523 548 554 551 560 557 563 544 545 539 541 517 519 530 531 534 752 199 405 401 81 734 510 512 356 329 323 384 174 334 521 692 0\n823 -51 -78 -68 -34 0 718 566 14 421 768 142 510 531 539 563 560 552 783 10 538 752 12 11 534 512 174 819 818 167 258 558 545 519 81 521 8 281 135 136 387 193 247 214 418 203 416 152 149 15 379 153 151 806 25 17 319 685 0\n824 89 58 -34 0 720 718 566 819 818 219 247 331 258 214 203 193 167 152 149 783 14 421 768 17 15 12 11 10 8 822 135 136 142 379 416 418 387 510 531 529 538 539 534 752 563 512 558 560 174 544 545 552 517 519 81 281 521 823 508 344 659 0\n825 -89 -34 0 566 723 719 819 818 219 247 331 258 208 167 155 154 152 806 783 14 421 768 18 17 12 11 10 8 265 266 267 406 767 402 523 563 548 539 541 554 551 530 531 534 752 557 734 510 512 545 329 323 384 174 519 334 81 281 521 693 0\n826 -34 0 719 18 806 819 818 154 167 258 825 824 90 99 139 519 523 545 548 557 554 0\n827 -58 -71 0 566 156 768 258 167 90 129 519 510 545 531 558 539 563 0\n828 -155 -71 0 826 219 247 331 156 768 152 539 541 530 531 534 535 734 510 755 329 59 0\n829 -33 -141 -67 -71 0 826 721 566 828 563 560 552 167 258 558 545 519 71 81 183 146 64 152 128 754 514 533 219 247 331 508 58 512 174 521 356 304 208 384 436 544 827 231 203 151 150 148 7 196 289 396 517 652 0\n830 -141 -67 -71 0 566 721 826 247 208 384 436 142 128 167 258 828 563 558 545 519 97 81 71 64 560 554 548 552 544 827 219 331 203 191 183 154 152 150 148 147 146 754 508 514 58 533 512 174 304 356 521 829 523 48 197 291 397 517 653 0\n831 -153 -71 0 826 183 146 534 535 755 22 172 512 0\n832 -71 0 718 156 768 831 538 530 531 830 510 0\n833 -35 -151 0 531 530 145 768 510 126 128 754 0\n834 -50 -74 70 -67 -163 35 0 832 184 178 420 129 125 560 554 549 558 545 544 47 48 76 197 227 774 517 270 409 519 355 65 100 571 525 568 802 605 0\n835 -52 54 -74 70 -67 -163 35 0 832 834 178 420 142 129 125 560 554 549 548 558 544 65 97 100 523 432 568 7 188 196 571 605 517 802 269 525 0\n836 54 -74 70 -67 -163 35 0 834 184 142 129 560 554 548 558 545 544 835 519 257 270 523 7 196 517 0\n837 -74 70 -67 -163 35 0 558 545 184 836 77 256 519 0\n838 -26 -67 -141 0 128 126 32 58 508 0\n839 -27 68 -148 0 5 46 72 91 523 0\n840 -67 -143 73 -151 0 826 566 833 755 535 541 563 560 554 548 530 142 838 839 512 182 837 0\n841 -64 0 109 768 421 0\n842 143 35 0 721 826 566 533 534 514 541 64 157 253 563 519 558 545 0\n843 -33 89 -151 0 841 826 566 833 842 755 535 541 563 558 544 531 510 129 7 196 517 0\n844 -87 -151 0 841 826 566 833 842 755 535 541 563 560 554 548 558 544 531 510 142 129 256 257 270 843 523 48 197 517 0\n845 -10 -50 54 52 -151 0 826 566 841 832 833 531 510 842 840 175 176 263 571 171 568 605 802 755 535 541 563 558 545 844 519 288 192 125 560 554 549 227 525 241 205 384 218 530 126 128 162 161 168 170 515 287 49 279 508 334 129 200 544 48 517 394 164 552 304 174 173 838 78 280 521 650 0\n846 -50 54 52 -151 0 826 566 832 841 833 842 755 535 541 563 558 545 844 519 394 531 510 840 287 288 200 192 165 162 161 560 554 549 544 175 176 263 571 171 568 605 802 515 304 174 170 168 218 132 129 128 126 125 123 530 48 49 227 517 279 525 508 205 241 334 384 845 302 349 315 646 0\n847 -55 -59 -21 -72 -151 0 566 832 826 841 530 531 510 126 128 162 161 833 842 840 168 170 755 515 288 287 93 279 508 132 429 160 175 176 263 571 171 568 605 802 192 125 535 541 563 560 554 549 92 525 404 130 419 129 200 558 544 265 517 165 304 123 349 315 647 0\n848 54 52 -151 0 826 566 841 832 531 510 833 842 840 755 535 541 563 558 545 844 519 287 288 200 192 166 162 161 160 159 560 554 549 548 552 544 175 176 263 571 171 568 605 802 515 304 174 173 170 168 132 429 142 130 129 128 126 125 530 394 846 523 92 93 265 525 279 517 419 404 508 847 356 521 351 649 0\n849 -32 -83 52 -151 0 826 566 841 832 435 530 531 510 126 128 833 842 755 535 541 563 558 545 844 519 162 161 840 168 170 515 288 287 848 73 279 508 173 174 560 552 82 521 838 282 98 194 192 164 554 549 175 176 263 571 171 568 605 802 304 125 4 264 297 525 407 648 0\n850 -83 52 -151 0 826 566 841 832 530 531 510 126 128 833 842 755 535 541 563 558 545 844 519 162 161 840 168 170 515 288 287 848 73 279 508 173 174 560 552 82 521 838 282 76 130 160 425 200 192 554 549 544 175 176 263 571 171 568 605 802 304 129 125 435 849 517 323 269 406 525 651 0\n851 52 -151 0 841 826 566 832 844 833 842 755 535 541 563 560 554 549 558 545 531 510 840 175 176 263 571 171 568 605 802 132 429 127 125 519 160 192 194 288 848 75 76 850 404 525 398 211 241 403 0\n852 -151 0 841 832 507 826 531 833 510 124 142 842 840 755 170 176 185 263 304 515 438 456 457 851 65 66 81 84 107 163 352 356 452 393 444 492 448 464 494 478 465 479 466 480 471 500 505 506 501 472 495 496 458 493 486 487 455 489 490 484 449 437 454 453 451 300 291 417 362 406 0\n853 153 0 852 718 538 0\n854 -155 0 852 539 0\n855 143 0 853 534 0\n856 144 0 853 535 0\n857 163 0 854 566 563 0\n858 35 0 856 826 855 755 0\n859 157 0 857 558 0\n860 161 0 857 560 0\n861 -5 0 858 19 0\n862 -25 0 858 21 0\n863 -26 0 858 22 0\n864 -42 0 858 33 0\n865 -53 0 858 69 0\n866 -57 0 858 86 0\n867 -70 0 858 145 0\n868 -73 0 858 172 0\n869 -88 0 858 261 0\n870 19 0 858 342 0\n871 145 0 859 544 0\n872 146 0 859 545 0\n873 147 0 860 552 0\n874 159 0 860 554 0\n875 148 0 874 548 0\n876 149 0 874 549 0\n877 -76 -52 54 0 859 858 875 720 841 163 97 188 189 774 43 48 754 523 529 142 510 0\n878 -45 0 858 841 720 39 44 125 754 510 529 0\n879 -52 54 0 865 866 873 832 876 878 875 871 63 65 81 90 97 521 115 877 525 227 229 234 269 523 517 7 0\n880 -32 50 76 54 0 858 863 855 868 872 875 862 861 832 878 876 879 4 7 29 272 274 276 512 184 519 257 523 136 229 278 525 0\n881 -65 -28 -78 -68 54 0 841 720 872 864 867 862 868 855 863 861 858 870 136 135 133 512 177 134 181 204 426 178 27 277 205 278 210 312 879 184 519 211 141 414 142 510 529 37 754 195 379 140 316 350 682 0\n882 -68 32 76 54 0 855 868 871 720 872 832 878 876 841 862 861 864 863 869 867 865 866 873 858 870 879 133 134 135 136 139 141 142 229 267 512 510 517 177 178 181 184 529 195 204 278 519 426 525 27 37 205 210 211 379 277 754 414 312 881 338 373 521 678 0\n883 65 -58 -85 38 -87 -33 -74 0 841 720 869 867 865 866 873 858 870 225 129 510 529 754 40 119 221 377 35 24 404 102 419 338 373 521 677 0\n884 -33 32 76 54 0 875 868 855 863 872 862 832 878 876 871 841 720 861 858 870 882 839 512 879 6 24 28 30 35 40 102 105 119 159 196 273 275 519 278 254 270 525 517 221 225 419 404 129 377 510 529 754 883 316 350 681 0\n885 50 76 54 0 863 855 868 875 872 879 880 882 839 512 884 184 523 519 257 0\n886 76 54 0 863 855 868 862 861 872 832 878 876 871 879 885 46 48 50 51 197 227 512 177 178 184 278 519 525 270 88 517 0\n887 54 0 872 879 886 192 260 519 0\n888 -27 0 887 72 0\n889 -52 0 887 77 0\n890 -87 0 887 256 0\n891 74 0 888 868 855 863 512 0\n892 72 0 890 872 889 519 0\n893 0 891 892 184 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record009.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record009.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record009.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record009.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record009 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeafTable : ConcreteGrowth.Table (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record009.l) :=
(.branch 34
 (.branch 17
 (.branch 8
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
 (.leaf (⟨5, by decide⟩)))
 (.branch 7
 (.leaf (⟨6, by decide⟩))
 (.leaf (⟨7, by decide⟩)))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (⟨8, by decide⟩))
 (.leaf (⟨9, by decide⟩)))
 (.branch 11
 (.leaf (⟨10, by decide⟩))
 (.leaf (⟨11, by decide⟩))))
 (.branch 14
 (.branch 13
 (.leaf (⟨12, by decide⟩))
 (.leaf (⟨13, by decide⟩)))
 (.branch 15
 (.leaf (⟨14, by decide⟩))
 (.branch 16
 (.leaf (⟨15, by decide⟩))
 (.leaf (⟨16, by decide⟩)))))))
 (.branch 25
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf (⟨17, by decide⟩))
 (.leaf (⟨18, by decide⟩)))
 (.branch 20
 (.leaf (⟨19, by decide⟩))
 (.leaf (⟨20, by decide⟩))))
 (.branch 23
 (.branch 22
 (.leaf (⟨21, by decide⟩))
 (.leaf (⟨22, by decide⟩)))
 (.branch 24
 (.leaf (⟨23, by decide⟩))
 (.leaf (⟨24, by decide⟩)))))
 (.branch 29
 (.branch 27
 (.branch 26
 (.leaf (⟨25, by decide⟩))
 (.leaf (⟨26, by decide⟩)))
 (.branch 28
 (.leaf (⟨27, by decide⟩))
 (.leaf (⟨28, by decide⟩))))
 (.branch 31
 (.branch 30
 (.leaf (⟨29, by decide⟩))
 (.leaf (⟨30, by decide⟩)))
 (.branch 32
 (.leaf (⟨31, by decide⟩))
 (.branch 33
 (.leaf (⟨32, by decide⟩))
 (.leaf (⟨33, by decide⟩))))))))
 (.branch 51
 (.branch 42
 (.branch 38
 (.branch 36
 (.branch 35
 (.leaf (⟨34, by decide⟩))
 (.leaf (⟨35, by decide⟩)))
 (.branch 37
 (.leaf (⟨36, by decide⟩))
 (.leaf (⟨37, by decide⟩))))
 (.branch 40
 (.branch 39
 (.leaf (⟨38, by decide⟩))
 (.leaf (⟨39, by decide⟩)))
 (.branch 41
 (.leaf (⟨40, by decide⟩))
 (.leaf (⟨41, by decide⟩)))))
 (.branch 46
 (.branch 44
 (.branch 43
 (.leaf (⟨42, by decide⟩))
 (.leaf (⟨43, by decide⟩)))
 (.branch 45
 (.leaf (⟨44, by decide⟩))
 (.leaf (⟨45, by decide⟩))))
 (.branch 48
 (.branch 47
 (.leaf (⟨46, by decide⟩))
 (.leaf (⟨47, by decide⟩)))
 (.branch 49
 (.leaf (⟨48, by decide⟩))
 (.branch 50
 (.leaf (⟨49, by decide⟩))
 (.leaf (⟨50, by decide⟩)))))))
 (.branch 60
 (.branch 55
 (.branch 53
 (.branch 52
 (.leaf (⟨51, by decide⟩))
 (.leaf (⟨52, by decide⟩)))
 (.branch 54
 (.leaf (⟨53, by decide⟩))
 (.leaf (⟨54, by decide⟩))))
 (.branch 57
 (.branch 56
 (.leaf (⟨55, by decide⟩))
 (.leaf (⟨56, by decide⟩)))
 (.branch 58
 (.leaf (⟨57, by decide⟩))
 (.branch 59
 (.leaf (⟨58, by decide⟩))
 (.leaf (⟨59, by decide⟩))))))
 (.branch 64
 (.branch 62
 (.branch 61
 (.leaf (⟨60, by decide⟩))
 (.leaf (⟨61, by decide⟩)))
 (.branch 63
 (.leaf (⟨62, by decide⟩))
 (.leaf (⟨63, by decide⟩))))
 (.branch 66
 (.branch 65
 (.leaf (⟨64, by decide⟩))
 (.leaf (⟨65, by decide⟩)))
 (.branch 67
 (.leaf (⟨66, by decide⟩))
 (.branch 68
 (.leaf (⟨67, by decide⟩))
 (.leaf (⟨68, by decide⟩)))))))))
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record009.l := originalLeafTable.get j.val
def orbitWordTable : ConcreteGrowth.Table (List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record009.g)) :=
(.branch 34
 (.branch 17
 (.branch 8
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
 (.leaf ([])))
 (.branch 7
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ([]))
 (.leaf ([])))
 (.branch 11
 (.leaf ([]))
 (.leaf ([]))))
 (.branch 14
 (.branch 13
 (.leaf ([]))
 (.leaf ([])))
 (.branch 15
 (.leaf ([]))
 (.branch 16
 (.leaf ([]))
 (.leaf ([])))))))
 (.branch 25
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf ([]))
 (.leaf ([])))
 (.branch 20
 (.leaf ([]))
 (.leaf ([]))))
 (.branch 23
 (.branch 22
 (.leaf ([]))
 (.leaf ([])))
 (.branch 24
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 29
 (.branch 27
 (.branch 26
 (.leaf ([]))
 (.leaf ([])))
 (.branch 28
 (.leaf ([]))
 (.leaf ([]))))
 (.branch 31
 (.branch 30
 (.leaf ([]))
 (.leaf ([])))
 (.branch 32
 (.leaf ([]))
 (.branch 33
 (.leaf ([]))
 (.leaf ([]))))))))
 (.branch 51
 (.branch 42
 (.branch 38
 (.branch 36
 (.branch 35
 (.leaf ([]))
 (.leaf ([])))
 (.branch 37
 (.leaf ([]))
 (.leaf ([]))))
 (.branch 40
 (.branch 39
 (.leaf ([]))
 (.leaf ([])))
 (.branch 41
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 46
 (.branch 44
 (.branch 43
 (.leaf ([]))
 (.leaf ([])))
 (.branch 45
 (.leaf ([]))
 (.leaf ([]))))
 (.branch 48
 (.branch 47
 (.leaf ([]))
 (.leaf ([])))
 (.branch 49
 (.leaf ([]))
 (.branch 50
 (.leaf ([]))
 (.leaf ([])))))))
 (.branch 60
 (.branch 55
 (.branch 53
 (.branch 52
 (.leaf ([]))
 (.leaf ([])))
 (.branch 54
 (.leaf ([]))
 (.leaf ([]))))
 (.branch 57
 (.branch 56
 (.leaf ([]))
 (.leaf ([])))
 (.branch 58
 (.leaf ([]))
 (.branch 59
 (.leaf ([]))
 (.leaf ([]))))))
 (.branch 64
 (.branch 62
 (.branch 61
 (.leaf ([]))
 (.leaf ([])))
 (.branch 63
 (.leaf ([]))
 (.leaf ([]))))
 (.branch 66
 (.branch 65
 (.leaf ([]))
 (.leaf ([])))
 (.branch 67
 (.leaf ([]))
 (.branch 68
 (.leaf ([]))
 (.leaf ([])))))))))
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record009.g) := orbitWordTable.get j.val
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record009.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record009.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record009 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record009_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record009 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record009_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record009_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00114.record009

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00114.record000
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1b4c725cb49b26a8ea969a665a564d8b693a2e4ba1e4785e745b1725a93a659565a5656554d4b59361d4745d68ce364e534ccb362e4b32d2b2ac6b86d1b16d8791d2729e1745c9715c3783d0f13c1f4b25234a4a85a0e0b9a1644d14a5254550d0b4c328c9314c4b0ac2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db4db4da6d249b49a6da4d36d349269a4926d3692492492249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record000 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record000 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record000.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record000.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record000.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 45), (facetIndex 63), (facetIndex 65)]))
 (.leaf ([(facetIndex 80), (facetIndex 81)])))
 (.branch 3
 (.leaf ([(facetIndex 35), (facetIndex 39), (facetIndex 52)]))
 (.branch 4
 (.leaf ([(facetIndex 54), (facetIndex 55), (facetIndex 68)]))
 (.leaf ([(facetIndex 36), (facetIndex 47), (facetIndex 56)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 58), (facetIndex 62), (facetIndex 84)]))
 (.leaf ([(facetIndex 74), (facetIndex 75), (facetIndex 77)])))
 (.branch 8
 (.leaf ([(facetIndex 78), (facetIndex 82), (facetIndex 86)]))
 (.branch 9
 (.leaf ([(facetIndex 38), (facetIndex 61), (facetIndex 85)]))
 (.leaf ([(facetIndex 69)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "7850711076066000093000005800504330200004000000028042z23;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [2, 3, 4]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [3, 4]
def grouped3_0009 : List Nat := [4]
def grouped3_0010 : List Nat := [5]
def grouped3_0011 : List Nat := [5, 6]
def grouped3_0012 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0013 : List Nat := [6]
def grouped3_0014 : List Nat := [7]
def grouped3_0015 : List Nat := [7, 8, 9]
def grouped3_0016 : List Nat := [8]
def grouped3_0017 : List Nat := [8, 9]
def grouped3_0018 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record000 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record000_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00114.record000" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00114.record000" 61

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00114.record000" "{\"ridges\":[[11,276],[15,400],[18,524],[19,532],[20,584],[22,592],[27,524],[31,276],[32,532],[35,581],[44,73],[44,584],[47,306],[48,592],[49,400],[53,276],[57,276],[59,276],[59,400],[61,344],[62,537],[65,456],[66,400],[67,400],[70,524],[70,532],[72,524],[73,524],[73,584],[76,592],[79,584],[79,592],[83,592],[84,92],[85,792]],\"owners\":[[44,73,[52,61,63,65],[4,25,37,40,43,55,62]],[11,276,[69,75,77,85,86],[31,53,57,59]],[31,276,[85,86],[11,53,57,59,69,75,77]],[53,276,[75,77,86],[11,31,57,59,69,85]],[57,276,[69,77,85],[11,31,53,59,75,86]],[59,276,[69,75,85],[11,31,53,57,77,86]],[15,400,[77,82,86],[49,59,66,67]],[49,400,[86],[15,59,66,67,77,82]],[59,400,[82],[15,49,66,67,77,86]],[66,400,[77],[15,49,59,67,82,86]],[67,400,[77,82,86],[15,49,59,66]],[18,524,[54,55,84,85],[27,70,72,73]],[27,524,[84,85],[18,54,55,70,72,73]],[70,524,[55],[18,27,54,72,73,84,85]],[72,524,[54,55,84,85],[18,27,70,73]],[73,524,[54,85],[18,27,55,70,72,84]],[19,532,[54,58,84,85],[32,70,76]],[32,532,[84,85],[19,54,58,70,76]],[70,532,[58],[19,32,54,76,84,85]],[20,584,[55,62,84],[44,73,79]],[44,584,[84],[20,55,62,73,79]],[73,584,[62],[20,44,55,79,84]],[79,584,[55],[20,44,62,73,84]],[22,592,[58,62,84],[48,76,79,83]],[48,592,[84],[22,58,62,76,79,83]],[76,592,[62],[22,48,58,79,83,84]],[79,592,[58],[22,48,62,76,83,84]],[83,592,[58,62,84],[22,48,76,79]],[35,581,[55,58],[]],[62,537,[39,54],[]],[47,306,[75,82],[]],[84,92,[52,68],[]],[61,344,[],[]],[65,456,[],[]],[85,792,[],[]]],\"edges\":[[29,[18,20,27,39,44,54,55,62,70,72,73,79,84,85]],[33,[11,15,31,38,47,49,53,57,59,61,66,67,69,75,77,82,85,86]],[34,[19,22,32,39,48,54,58,62,70,76,79,83,84,85]],[41,[20,22,35,44,48,55,58,62,73,76,79,83,84]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00114.record000" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00114.record000\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-20,-12],[-20,-19],[-22,-8],[-25,-11],[-25,-18],[-25,-20],[-31,-25],[-36,-20],[-41,-11],[-41,-18],[-41,-31],[-13,17,24,26,27],[-1,31,35,37,42,43],[-8,42,43],[-18,35,37,43],[-21,31,37,42],[-23,31,35,42],[-2,37,39,43],[-16,43],[-23,39],[-28,37],[-29,37,39,43],[-3,19,20,41,42],[-7,41,42],[-32,20],[-33,19,20,41,42],[-34,19,42],[-4,19,22,41,42],[-9,41,42],[-32,22],[-5,20,25,41],[-13,41],[-34,25],[-38,20],[-6,22,25,41],[-15,41],[-36,25],[-38,22],[-40,22,25,41],[-10,20,22],[-25,12,19],[-14,35,39],[-41,17,30],[-24],[-27],[-42],[-26,44],[-12,45],[-17,45],[-19,46],[-20,46],[-30,46],[-22,47],[-25,47],[-41,47],[-35,48],[-37,48],[-39,49],[-43,49],[-11,50],[-31,51],[-44,52],[-46,53],[-53,54],[-45,54],[-54,55],[-52,55],[-47,56],[-47,-48,57],[-51,58],[-50,58],[-58,59],[-49,59],[-56,-59,60],[-57,60],[-55,-60,61],[-61],[3,5,7,12,13,19,20,25,32,33,34,38,41,42],[1,2,8,11,14,16,18,21,23,24,28,29,31,35,37,39,42,43],[4,6,9,12,15,19,22,25,32,36,38,40,41,42],[5,6,10,13,15,20,22,25,34,36,38,40,41]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":55,\"b\":39},{\"tag\":\"incompatible\",\"a\":55,\"b\":54},{\"tag\":\"incompatible\",\"a\":58,\"b\":31},{\"tag\":\"incompatible\",\"a\":62,\"b\":38},{\"tag\":\"incompatible\",\"a\":62,\"b\":53},{\"tag\":\"incompatible\",\"a\":62,\"b\":55},{\"tag\":\"incompatible\",\"a\":69,\"b\":62},{\"tag\":\"incompatible\",\"a\":76,\"b\":55},{\"tag\":\"incompatible\",\"a\":84,\"b\":38},{\"tag\":\"incompatible\",\"a\":84,\"b\":53},{\"tag\":\"incompatible\",\"a\":84,\"b\":69},{\"tag\":\"mate\",\"ridge\":73,\"a\":44,\"owners\":[52,61,63,65]},{\"tag\":\"mate\",\"ridge\":276,\"a\":11,\"owners\":[69,75,77,85,86]},{\"tag\":\"mate\",\"ridge\":276,\"a\":31,\"owners\":[85,86]},{\"tag\":\"mate\",\"ridge\":276,\"a\":53,\"owners\":[75,77,86]},{\"tag\":\"mate\",\"ridge\":276,\"a\":57,\"owners\":[69,77,85]},{\"tag\":\"mate\",\"ridge\":276,\"a\":59,\"owners\":[69,75,85]},{\"tag\":\"mate\",\"ridge\":400,\"a\":15,\"owners\":[77,82,86]},{\"tag\":\"mate\",\"ridge\":400,\"a\":49,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":400,\"a\":59,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":400,\"a\":66,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":400,\"a\":67,\"owners\":[77,82,86]},{\"tag\":\"mate\",\"ridge\":524,\"a\":18,\"owners\":[54,55,84,85]},{\"tag\":\"mate\",\"ridge\":524,\"a\":27,\"owners\":[84,85]},{\"tag\":\"mate\",\"ridge\":524,\"a\":70,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":524,\"a\":72,\"owners\":[54,55,84,85]},{\"tag\":\"mate\",\"ridge\":524,\"a\":73,\"owners\":[54,85]},{\"tag\":\"mate\",\"ridge\":532,\"a\":19,\"owners\":[54,58,84,85]},{\"tag\":\"mate\",\"ridge\":532,\"a\":32,\"owners\":[84,85]},{\"tag\":\"mate\",\"ridge\":532,\"a\":70,\"owners\":[58]},{\"tag\":\"mate\",\"ridge\":584,\"a\":20,\"owners\":[55,62,84]},{\"tag\":\"mate\",\"ridge\":584,\"a\":44,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":584,\"a\":73,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":584,\"a\":79,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":592,\"a\":22,\"owners\":[58,62,84]},{\"tag\":\"mate\",\"ridge\":592,\"a\":48,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":592,\"a\":76,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":592,\"a\":79,\"owners\":[58]},{\"tag\":\"mate\",\"ridge\":592,\"a\":83,\"owners\":[58,62,84]},{\"tag\":\"mate\",\"ridge\":581,\"a\":35,\"owners\":[55,58]},{\"tag\":\"mate\",\"ridge\":537,\"a\":62,\"owners\":[39,54]},{\"tag\":\"mate\",\"ridge\":306,\"a\":47,\"owners\":[75,82]},{\"tag\":\"mate\",\"ridge\":92,\"a\":84,\"owners\":[52,68]},{\"tag\":\"mate\",\"ridge\":344,\"a\":61,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":456,\"a\":65,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":792,\"a\":85,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":63,\"full_literals\":[-26,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":39,\"full_literals\":[-12,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":52,\"full_literals\":[-17,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":54,\"full_literals\":[-19,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":55,\"full_literals\":[-20,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":68,\"full_literals\":[-30,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":58,\"full_literals\":[-22,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":62,\"full_literals\":[-25,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":84,\"full_literals\":[-41,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":75,\"full_literals\":[-35,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":77,\"full_literals\":[-37,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":82,\"full_literals\":[-39,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":86,\"full_literals\":[-43,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":38,\"full_literals\":[-11,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":69,\"full_literals\":[-31,51]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-53,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-45,false,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-54,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-52,false,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-47,false,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-47,-48,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-51,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-50,false,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-58,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-49,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-56,-59,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-57,false,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-55,-60,61],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":29,\"owners\":[18,20,27,39,44,54,55,62,70,72,73,79,84,85]},{\"tag\":\"edge\",\"edge\":33,\"owners\":[11,15,31,38,47,49,53,57,59,61,66,67,69,75,77,82,85,86]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[19,22,32,39,48,54,58,62,70,76,79,83,84,85]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[20,22,35,44,48,55,58,62,73,76,79,83,84]}]}"
  "p cnf 61 81\n-20 -12 0\n-20 -19 0\n-22 -8 0\n-25 -11 0\n-25 -18 0\n-25 -20 0\n-31 -25 0\n-36 -20 0\n-41 -11 0\n-41 -18 0\n-41 -31 0\n-13 17 24 26 27 0\n-1 31 35 37 42 43 0\n-8 42 43 0\n-18 35 37 43 0\n-21 31 37 42 0\n-23 31 35 42 0\n-2 37 39 43 0\n-16 43 0\n-23 39 0\n-28 37 0\n-29 37 39 43 0\n-3 19 20 41 42 0\n-7 41 42 0\n-32 20 0\n-33 19 20 41 42 0\n-34 19 42 0\n-4 19 22 41 42 0\n-9 41 42 0\n-32 22 0\n-5 20 25 41 0\n-13 41 0\n-34 25 0\n-38 20 0\n-6 22 25 41 0\n-15 41 0\n-36 25 0\n-38 22 0\n-40 22 25 41 0\n-10 20 22 0\n-25 12 19 0\n-14 35 39 0\n-41 17 30 0\n-24 0\n-27 0\n-42 0\n-26 44 0\n-12 45 0\n-17 45 0\n-19 46 0\n-20 46 0\n-30 46 0\n-22 47 0\n-25 47 0\n-41 47 0\n-35 48 0\n-37 48 0\n-39 49 0\n-43 49 0\n-11 50 0\n-31 51 0\n-44 52 0\n-46 53 0\n-53 54 0\n-45 54 0\n-54 55 0\n-52 55 0\n-47 56 0\n-47 -48 57 0\n-51 58 0\n-50 58 0\n-58 59 0\n-49 59 0\n-56 -59 60 0\n-57 60 0\n-55 -60 61 0\n-61 0\n3 5 7 12 13 19 20 25 32 33 34 38 41 42 0\n1 2 8 11 14 16 18 21 23 24 28 29 31 35 37 39 42 43 0\n4 6 9 12 15 19 22 25 32 36 38 40 41 42 0\n5 6 10 13 15 20 22 25 34 36 38 40 41 0\n"
  "82 3 5 7 12 13 19 20 25 32 33 34 38 41 0 46 78 0\n83 1 2 8 11 14 16 18 21 23 28 29 31 35 37 39 43 0 44 46 79 0\n84 4 6 9 12 15 19 22 25 32 36 38 40 41 0 46 80 0\n85 3 41 7 12 13 19 20 25 32 33 34 38 0 82 31 0\n86 55 0 45 44 46 66 67 64 65 62 63 48 49 47 50 51 52 12 43 23 27 41 25 34 24 26 85 0\n87 -60 0 86 77 76 0\n88 -57 0 87 75 0\n89 -22 0 88 87 46 3 53 68 69 74 56 57 72 73 21 70 71 58 59 61 60 20 42 19 22 15 13 18 16 83 0\n90 -32 0 89 30 0\n91 -38 0 89 38 0\n92 -20 41 0 46 91 90 89 36 29 1 2 6 8 28 35 39 84 0\n93 -25 0 88 87 46 4 5 7 54 68 69 74 56 57 73 17 21 16 58 59 42 19 14 22 13 18 83 0\n94 -34 0 93 33 0\n95 -36 0 93 37 0\n96 41 0 91 95 94 93 89 32 36 92 40 35 39 31 81 0\n97 -11 0 96 9 0\n98 -18 0 96 10 0\n99 -31 0 96 11 0\n100 47 0 96 55 0\n101 56 0 100 68 0\n102 -48 0 100 88 69 0\n103 -59 0 101 87 74 0\n104 -35 0 102 56 0\n105 -37 0 102 57 0\n106 -49 0 103 73 0\n107 -23 0 104 99 46 17 0\n108 -28 0 105 21 0\n109 -21 0 105 99 46 16 0\n110 -39 0 106 58 0\n111 -43 0 106 59 0\n112 -14 0 110 104 42 0\n113 -16 0 111 19 0\n114 -8 0 111 46 14 0\n115 -29 0 111 110 105 22 0\n116 -1 0 111 99 105 46 104 13 0\n117 -2 0 111 110 105 18 0\n118 0 117 112 116 114 97 113 98 109 107 108 115 99 104 105 110 111 83 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record000.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record000.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record000.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record000.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record000 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record000.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record000.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record000.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record000.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record000 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record000_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record000 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record000_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record000_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00114.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00114.record004
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "751b46b25c4f1aac6a5a8e93a719a6959564d98e9392e2ba1e4785e0f9b13c5a9966394e5a565655355352d58d9352d2b61d4745d0f6c368ce394e334cc7362e4b8ad2b2ae1b46c5b0ed8791d2729e1745c570de0f43c8f13c2f07d38471a24a9863190e946190e4c51541d90cc328e0b0ac8711c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6d26da49b69a6d36db4936936db6924924db69249b4934da692491249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record004 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record004 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record004.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record004.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record004.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 30), (facetIndex 36), (facetIndex 57)]))
 (.leaf ([(facetIndex 59), (facetIndex 63), (facetIndex 69), (facetIndex 93)])))
 (.branch 3
 (.leaf ([(facetIndex 72), (facetIndex 74), (facetIndex 77)]))
 (.branch 4
 (.leaf ([(facetIndex 81), (facetIndex 86), (facetIndex 90)]))
 (.leaf ([(facetIndex 32), (facetIndex 43), (facetIndex 55)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 56), (facetIndex 58), (facetIndex 75)]))
 (.branch 7
 (.leaf ([(facetIndex 60), (facetIndex 68), (facetIndex 91)]))
 (.leaf ([(facetIndex 27), (facetIndex 29), (facetIndex 44), (facetIndex 46), (facetIndex 80), (facetIndex 87)]))))
 (.branch 9
 (.leaf ([(facetIndex 37), (facetIndex 71), (facetIndex 85)]))
 (.branch 10
 (.leaf ([(facetIndex 64), (facetIndex 79), (facetIndex 92)]))
 (.leaf ([(facetIndex 45), (facetIndex 70)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "19630073800037902052028a160009100615054000000007a740000080000400707z1b;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 11
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [2, 3, 4]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [3, 4]
def grouped3_0009 : List Nat := [4]
def grouped3_0010 : List Nat := [5]
def grouped3_0011 : List Nat := [5, 6, 7]
def grouped3_0012 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped3_0013 : List Nat := [6]
def grouped3_0014 : List Nat := [6, 7]
def grouped3_0015 : List Nat := [7]
def grouped3_0016 : List Nat := [8]
def grouped3_0017 : List Nat := [8, 9, 10]
def grouped3_0018 : List Nat := [9]
def grouped3_0019 : List Nat := [9, 10]
def grouped3_0020 : List Nat := [10]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record004 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record004_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00114.record004" "{\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":10},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00114.record004" 83

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00114.record004" "{\"ridges\":[[5,161],[7,578],[12,536],[13,592],[18,416],[19,276],[20,304],[27,54],[29,275],[30,534],[33,578],[37,275],[38,522],[39,161],[42,578],[44,114],[45,275],[47,578],[48,161],[50,578],[53,276],[54,536],[59,180],[62,84],[63,401],[65,49],[65,304],[66,536],[67,536],[67,592],[69,240],[70,401],[71,54],[73,276],[79,54],[80,338],[82,388],[84,304],[85,562],[87,786],[88,416],[89,276],[92,180],[93,464]],\"owners\":[[38,522,[77],[4,26,41,42,74,85,86,87]],[5,161,[55,59,64,68,69,70],[31,39,48,49]],[39,161,[59,64,69,70],[5,31,48,49,55,68]],[48,161,[55,59,64,68,70],[5,31,39,49,69]],[7,578,[77,81,86],[33,42,47,50]],[33,578,[86],[7,42,47,50,77,81]],[42,578,[81],[7,33,47,50,77,86]],[47,578,[77],[7,33,42,50,81,86]],[50,578,[77,81,86],[7,33,42,47]],[62,84,[72,80,93],[9,28,52,61,81,90]],[65,49,[27,44,46,59,69],[11,35,45,51,60,66,70]],[12,536,[74,85,86,87,90],[38,54,66,67]],[54,536,[85,86,87],[12,38,66,67,74,90]],[66,536,[74,86,87,90],[12,38,54,67,85]],[67,536,[74,85,87],[12,38,54,66,86,90]],[13,592,[81,86,90],[47,62,67]],[67,592,[81],[13,47,62,86,90]],[82,388,[58,63,93],[16,34,64,78,83,91,92]],[18,416,[64,68,70,91,92],[49,82,88]],[88,416,[64,70,92],[18,49,68,82,91]],[19,276,[29,60,63,79,80,92,93],[53,73,89]],[53,276,[79,80,92,93],[19,29,60,63,73,89]],[73,276,[60,63,92,93],[19,29,53,79,80,89]],[89,276,[29,63,80,93],[19,53,60,73,79,92]],[20,304,[45,60,70,79,92],[65,84,89]],[65,304,[79,92],[20,45,60,70,84,89]],[84,304,[60,70,92],[20,45,65,79,89]],[27,54,[71,79],[]],[71,54,[27,79],[]],[79,54,[27,71],[]],[29,275,[37,45],[]],[37,275,[29,45],[]],[45,275,[29,37],[]],[30,534,[74,81],[]],[44,114,[],[]],[85,562,[46],[]],[59,180,[92],[]],[92,180,[59],[]],[63,401,[70],[]],[70,401,[63],[]],[69,240,[],[]],[80,338,[],[]],[87,786,[],[]],[93,464,[],[]]],\"edges\":[[33,[19,20,29,37,45,53,60,63,65,70,73,79,80,84,87,89,92,93]],[34,[12,13,30,38,46,47,54,62,66,67,74,81,85,86,87,90]],[36,[5,18,31,39,48,49,55,59,64,68,69,70,75,82,88,91,92]],[41,[7,13,33,42,47,50,57,62,67,77,81,86,90]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00114.record004" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00114.record004\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-30,-11],[-30,-22],[-30,-26],[-37,-30],[-57,-30],[-14,45],[-1,26,29,33,37,38,39],[-15,29,33,38,39],[-21,26,29,33,37,39],[-2,45,48,52],[-12,52],[-16,48],[-20,45],[-23,45,48,52],[-31,41,47,59],[-34,8,17,19,29,38],[-3,43,51,52,53,56],[-25,51,52,53],[-35,43,52,53,56],[-36,43,51,53],[-4,48,52,56],[-36,48],[-49,28,32,59],[-5,33,37,39,57,58],[-54,33,39,58],[-6,9,30,32,46,47,58,59],[-24,46,47,58,59],[-42,30,32,58,59],[-55,9,32,47,59],[-7,18,30,39,46,58],[-34,46,58],[-50,30,39,58],[-8,40,46],[-40,8,46],[-46,8,40],[-9,13,18],[-13,9,18],[-18,9,13],[-10,43,48],[-17],[-51,19],[-29,58],[-58,29],[-32,39],[-39,32],[-38],[-47],[-53],[-59],[-27,60],[-29,61],[-32,61],[-41,62],[-43,62],[-45,62],[-48,63],[-52,63],[-56,63],[-28,64],[-44,64],[-30,65],[-8,66],[-9,66],[-19,66],[-67,13,40,51],[-13,67],[-40,67],[-33,68],[-46,68],[-58,68],[-18,69],[-39,69],[-61,70],[-60,70],[-63,71],[-71,72],[-62,72],[-72,73],[-70,73],[-70,-72,74],[-66,75],[-65,75],[-75,76],[-64,-75,77],[-69,78],[-68,78],[-78,79],[-67,79],[-67,-78,80],[-79,81],[-80,82],[-76,-79,82],[-77,82],[-73,-82,83],[-74,-81,83],[-83],[6,7,9,13,18,24,30,32,34,39,42,46,47,50,53,55,58,59],[3,4,10,14,19,20,25,31,35,36,43,48,51,52,53,56],[1,5,11,15,21,22,26,29,33,37,38,39,44,49,54,57,58],[2,4,12,16,20,23,27,31,36,45,48,52,56]],\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":10,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":60,\"b\":31},{\"tag\":\"incompatible\",\"a\":60,\"b\":49},{\"tag\":\"incompatible\",\"a\":60,\"b\":55},{\"tag\":\"incompatible\",\"a\":68,\"b\":60},{\"tag\":\"incompatible\",\"a\":91,\"b\":60},{\"tag\":\"mate\",\"ridge\":522,\"a\":38,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":161,\"a\":5,\"owners\":[55,59,64,68,69,70]},{\"tag\":\"mate\",\"ridge\":161,\"a\":39,\"owners\":[59,64,69,70]},{\"tag\":\"mate\",\"ridge\":161,\"a\":48,\"owners\":[55,59,64,68,70]},{\"tag\":\"mate\",\"ridge\":578,\"a\":7,\"owners\":[77,81,86]},{\"tag\":\"mate\",\"ridge\":578,\"a\":33,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":578,\"a\":42,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":578,\"a\":47,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":578,\"a\":50,\"owners\":[77,81,86]},{\"tag\":\"mate\",\"ridge\":84,\"a\":62,\"owners\":[72,80,93]},{\"tag\":\"mate\",\"ridge\":49,\"a\":65,\"owners\":[27,44,46,59,69]},{\"tag\":\"mate\",\"ridge\":536,\"a\":12,\"owners\":[74,85,86,87,90]},{\"tag\":\"mate\",\"ridge\":536,\"a\":54,\"owners\":[85,86,87]},{\"tag\":\"mate\",\"ridge\":536,\"a\":66,\"owners\":[74,86,87,90]},{\"tag\":\"mate\",\"ridge\":536,\"a\":67,\"owners\":[74,85,87]},{\"tag\":\"mate\",\"ridge\":592,\"a\":13,\"owners\":[81,86,90]},{\"tag\":\"mate\",\"ridge\":592,\"a\":67,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":388,\"a\":82,\"owners\":[58,63,93]},{\"tag\":\"mate\",\"ridge\":416,\"a\":18,\"owners\":[64,68,70,91,92]},{\"tag\":\"mate\",\"ridge\":416,\"a\":88,\"owners\":[64,70,92]},{\"tag\":\"mate\",\"ridge\":276,\"a\":19,\"owners\":[29,60,63,79,80,92,93]},{\"tag\":\"mate\",\"ridge\":276,\"a\":53,\"owners\":[79,80,92,93]},{\"tag\":\"mate\",\"ridge\":276,\"a\":73,\"owners\":[60,63,92,93]},{\"tag\":\"mate\",\"ridge\":276,\"a\":89,\"owners\":[29,63,80,93]},{\"tag\":\"mate\",\"ridge\":304,\"a\":20,\"owners\":[45,60,70,79,92]},{\"tag\":\"mate\",\"ridge\":304,\"a\":65,\"owners\":[79,92]},{\"tag\":\"mate\",\"ridge\":304,\"a\":84,\"owners\":[60,70,92]},{\"tag\":\"mate\",\"ridge\":54,\"a\":27,\"owners\":[71,79]},{\"tag\":\"mate\",\"ridge\":54,\"a\":71,\"owners\":[27,79]},{\"tag\":\"mate\",\"ridge\":54,\"a\":79,\"owners\":[27,71]},{\"tag\":\"mate\",\"ridge\":275,\"a\":29,\"owners\":[37,45]},{\"tag\":\"mate\",\"ridge\":275,\"a\":37,\"owners\":[29,45]},{\"tag\":\"mate\",\"ridge\":275,\"a\":45,\"owners\":[29,37]},{\"tag\":\"mate\",\"ridge\":534,\"a\":30,\"owners\":[74,81]},{\"tag\":\"mate\",\"ridge\":114,\"a\":44,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":562,\"a\":85,\"owners\":[46]},{\"tag\":\"mate\",\"ridge\":180,\"a\":59,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":180,\"a\":92,\"owners\":[59]},{\"tag\":\"mate\",\"ridge\":401,\"a\":63,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":401,\"a\":70,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":240,\"a\":69,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":338,\"a\":80,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":786,\"a\":87,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":464,\"a\":93,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":57,\"full_literals\":[-27,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":59,\"full_literals\":[-29,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":63,\"full_literals\":[-32,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":72,\"full_literals\":[-41,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":74,\"full_literals\":[-43,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":77,\"full_literals\":[-45,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":81,\"full_literals\":[-48,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":86,\"full_literals\":[-52,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":90,\"full_literals\":[-56,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":58,\"full_literals\":[-28,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":75,\"full_literals\":[-44,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":60,\"full_literals\":[-30,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":27,\"full_literals\":[-8,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":29,\"full_literals\":[-9,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":46,\"full_literals\":[-19,66]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[37,71,85],\"full_literals\":[-67,13,40,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":37,\"full_literals\":[-13,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":71,\"full_literals\":[-40,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":64,\"full_literals\":[-33,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":79,\"full_literals\":[-46,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":92,\"full_literals\":[-58,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":45,\"full_literals\":[-18,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":70,\"full_literals\":[-39,69]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-61,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-60,false,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-71,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-62,false,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-72,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-70,false,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-70,-72,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-66,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-65,false,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-75,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-64,-75,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-69,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-68,false,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-78,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-67,false,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-67,-78,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-79,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-80,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-76,-79,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0012\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-77,false,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-73,-82,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-74,-81,83],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":33,\"owners\":[19,20,29,37,45,53,60,63,65,70,73,79,80,84,87,89,92,93]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[12,13,30,38,46,47,54,62,66,67,74,81,85,86,87,90]},{\"tag\":\"edge\",\"edge\":36,\"owners\":[5,18,31,39,48,49,55,59,64,68,69,70,75,82,88,91,92]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[7,13,33,42,47,50,57,62,67,77,81,86,90]}]}"
  "p cnf 83 100\n-30 -11 0\n-30 -22 0\n-30 -26 0\n-37 -30 0\n-57 -30 0\n-14 45 0\n-1 26 29 33 37 38 39 0\n-15 29 33 38 39 0\n-21 26 29 33 37 39 0\n-2 45 48 52 0\n-12 52 0\n-16 48 0\n-20 45 0\n-23 45 48 52 0\n-31 41 47 59 0\n-34 8 17 19 29 38 0\n-3 43 51 52 53 56 0\n-25 51 52 53 0\n-35 43 52 53 56 0\n-36 43 51 53 0\n-4 48 52 56 0\n-36 48 0\n-49 28 32 59 0\n-5 33 37 39 57 58 0\n-54 33 39 58 0\n-6 9 30 32 46 47 58 59 0\n-24 46 47 58 59 0\n-42 30 32 58 59 0\n-55 9 32 47 59 0\n-7 18 30 39 46 58 0\n-34 46 58 0\n-50 30 39 58 0\n-8 40 46 0\n-40 8 46 0\n-46 8 40 0\n-9 13 18 0\n-13 9 18 0\n-18 9 13 0\n-10 43 48 0\n-17 0\n-51 19 0\n-29 58 0\n-58 29 0\n-32 39 0\n-39 32 0\n-38 0\n-47 0\n-53 0\n-59 0\n-27 60 0\n-29 61 0\n-32 61 0\n-41 62 0\n-43 62 0\n-45 62 0\n-48 63 0\n-52 63 0\n-56 63 0\n-28 64 0\n-44 64 0\n-30 65 0\n-8 66 0\n-9 66 0\n-19 66 0\n-67 13 40 51 0\n-13 67 0\n-40 67 0\n-33 68 0\n-46 68 0\n-58 68 0\n-18 69 0\n-39 69 0\n-61 70 0\n-60 70 0\n-63 71 0\n-71 72 0\n-62 72 0\n-72 73 0\n-70 73 0\n-70 -72 74 0\n-66 75 0\n-65 75 0\n-75 76 0\n-64 -75 77 0\n-69 78 0\n-68 78 0\n-78 79 0\n-67 79 0\n-67 -78 80 0\n-79 81 0\n-80 82 0\n-76 -79 82 0\n-77 82 0\n-73 -82 83 0\n-74 -81 83 0\n-83 0\n6 7 9 13 18 24 30 32 34 39 42 46 47 50 53 55 58 59 0\n3 4 10 14 19 20 25 31 35 36 43 48 51 52 53 56 0\n1 5 11 15 21 22 26 29 33 37 38 39 44 49 54 57 58 0\n2 4 12 16 20 23 27 31 36 45 48 52 56 0\n"
  "101 6 7 9 13 18 24 30 32 34 39 42 46 50 55 58 0 47 48 49 97 0\n102 3 4 10 14 19 20 25 31 35 36 43 48 51 52 56 0 48 98 0\n103 1 5 11 15 21 22 26 29 33 37 39 44 49 54 57 58 0 46 99 0\n104 73 0 49 47 78 79 76 77 74 75 53 55 50 56 57 58 15 10 13 14 12 22 11 21 100 0\n105 -82 0 104 96 94 0\n106 -80 0 105 91 0\n107 -77 0 105 93 0\n108 72 19 0 49 47 48 41 76 77 75 53 54 55 56 57 58 15 19 39 20 6 13 18 21 17 102 0\n109 67 34 58 32 30 9 8 0 49 47 45 32 28 29 66 67 38 35 27 26 30 101 0\n110 75 74 0 46 40 106 81 82 62 63 64 61 41 108 80 73 51 52 43 16 109 89 85 86 71 69 37 34 65 0\n111 -75 0 107 105 49 46 83 84 92 59 60 87 88 85 86 66 67 71 72 68 69 70 36 33 44 25 42 31 23 8 109 1 2 3 4 5 24 7 9 103 0\n112 -66 0 111 81 0\n113 -65 0 111 82 0\n114 74 0 111 110 0\n115 -8 0 112 62 0\n116 -9 0 112 63 0\n117 -30 0 113 61 0\n118 -81 0 114 96 95 0\n119 -79 0 118 90 0\n120 -78 0 119 87 0\n121 -67 0 119 88 0\n122 -69 0 120 85 0\n123 -68 0 120 86 0\n124 -39 0 122 72 0\n125 -46 0 123 69 0\n126 -58 0 123 70 0\n127 -32 0 124 44 0\n128 -34 0 126 125 31 0\n129 0 128 126 121 127 117 116 115 109 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record004.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record004.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record004.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record004.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record004 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record004.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record004.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record004.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record004.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record004 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record004_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record004 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record004_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record004_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00114.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00114.record008
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "6b25cb29aa968da719a639a5663a4e3392e2ba1e1783eb25a9964d9715a5396556364d3352d2b61d1743db0dc338cd3a2d8b92ccb8ad2b26c5b0ed8791d4731ca719e1745c3783d0f23c4f68a522aa1a498560b81e686512a619494550b41d60e4330d2328e1314e0b22c2b06d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6da4da69b69249a4da69b692492492492492492492492249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record008 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record008 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record008.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record008.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record008.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 38), (facetIndex 46), (facetIndex 59), (facetIndex 60), (facetIndex 66), (facetIndex 71)]))
 (.leaf ([(facetIndex 40), (facetIndex 48), (facetIndex 61), (facetIndex 62), (facetIndex 68), (facetIndex 72)])))
 (.branch 3
 (.leaf ([(facetIndex 75), (facetIndex 76), (facetIndex 82), (facetIndex 87)]))
 (.leaf ([(facetIndex 77), (facetIndex 78), (facetIndex 84), (facetIndex 88)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 32), (facetIndex 33), (facetIndex 34), (facetIndex 35), (facetIndex 36), (facetIndex 45), (facetIndex 58), (facetIndex 74)]))
 (.leaf ([(facetIndex 41), (facetIndex 43), (facetIndex 50), (facetIndex 54), (facetIndex 55), (facetIndex 56), (facetIndex 57)])))
 (.branch 7
 (.leaf ([(facetIndex 37), (facetIndex 39), (facetIndex 42), (facetIndex 44)]))
 (.branch 8
 (.leaf ([(facetIndex 47), (facetIndex 49), (facetIndex 51), (facetIndex 53)]))
 (.leaf ([(facetIndex 52)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "320030200033224010001000001100455557875717046565160644444z20;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 63), (facetIndex 64), (facetIndex 70), (facetIndex 73)]))
 (.branch 2
 (.leaf ([(facetIndex 65), (facetIndex 67), (facetIndex 69), (facetIndex 79)]))
 (.leaf ([(facetIndex 80), (facetIndex 86), (facetIndex 89)]))))
 (.branch 4
 (.leaf ([(facetIndex 81), (facetIndex 83), (facetIndex 85)]))
 (.branch 5
 (.leaf ([(facetIndex 90)]))
 (.leaf ([(facetIndex 91)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "b1009861a200000008208z30;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
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
def grouped3_0018 : List Nat := [0, 1, 2]
def grouped3_0020 : List Nat := [1]
def grouped3_0021 : List Nat := [1, 2]
def grouped3_0022 : List Nat := [2]
def grouped3_0023 : List Nat := [3]
def grouped3_0024 : List Nat := [3, 4, 5]
def grouped3_0025 : List Nat := [4]
def grouped3_0026 : List Nat := [4, 5]
def grouped3_0027 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record008 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record008_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00114.record008" "{\"atoms\":[{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00114.record008" 116

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00114.record008" "{\"ridges\":[[10,19],[13,193],[13,194],[16,13],[17,13],[17,37],[18,21],[18,84],[19,37],[19,261],[20,521],[21,137],[22,577],[25,38],[26,22],[26,84],[27,262],[29,138],[30,578],[37,19],[37,21],[37,22],[37,261],[37,262],[39,37],[39,38],[39,67],[41,193],[41,194],[42,259],[45,19],[45,25],[50,193],[50,194],[51,67],[54,193],[54,194],[55,193],[55,194],[56,67],[56,193],[56,194],[57,193],[57,194],[58,21],[58,37],[59,69],[62,261],[63,13],[63,193],[63,204],[64,588],[65,396],[66,69],[66,529],[67,228],[68,37],[68,385],[69,193],[69,261],[69,452],[70,193],[70,216],[71,577],[73,193],[73,712],[74,22],[74,38],[74,44],[75,70],[78,262],[79,194],[79,204],[80,588],[82,70],[83,228],[84,38],[84,262],[85,262],[85,452],[86,194],[86,216],[87,578],[89,194],[89,712]],\"owners\":[[17,37,[2,19,36,39,40,67,68],[58,61]],[19,37,[2,17,36,39,40,58,61,67],[68]],[58,37,[2,19,39,40,67,68],[17,36,61]],[25,38,[2,27,36,39,40,83,84],[74,77]],[74,38,[2,27,39,40,83,84],[25,36,77]],[59,69,[3,39,41,42,43,67,69],[18,32,63,64,66]],[66,69,[3,32,39,41,42,63,67,69],[18,43,59,64]],[75,70,[3,39,41,42,43,83,85],[26,32,79,80,82]],[82,70,[3,32,39,41,42,79,83,85],[26,43,75,80]],[42,259,[12,15,48,52],[4,34,37,56]],[37,261,[19,62,65,68,69],[4,34,42,44]],[27,262,[4,34,37,42,44,81,85],[78,84]],[84,262,[4,34,37,42],[27,44,78,81,85]],[45,25,[16,20,59,70,71],[5,46,47,58]],[21,137,[7,33,47,50,52,53,63,65,70,73],[61,72]],[29,138,[7,33,47,50,52,53,79,81,86,89],[77,88]],[20,521,[8,35,49,51,53,64,73],[60,71]],[66,529,[10,20],[22,38,60]],[13,193,[63,67,69,70,73],[41,50,54,55,56,57]],[41,193,[70,73],[13,50,54,55,56,57,63,67,69]],[50,193,[67,69],[13,41,54,55,56,57,63,70,73]],[54,193,[63,67,69,73],[13,41,50,55,56,57,70]],[55,193,[63,69,70,73],[13,41,50,54,56,57,67]],[56,193,[63,67,70,73],[13,41,50,54,55,57,69]],[57,193,[63,67,69,70],[13,41,50,54,55,56,73]],[63,193,[13,54,55,56,57],[41,50,67,69,70,73]],[69,193,[13,50,54,55,57,70,73],[41,56,63,67]],[70,193,[13,41,55,56,57,67,69],[50,54,63,73]],[73,193,[13,41,54,55,56,67,69],[50,57,63,70]],[13,194,[79,83,85,86,89],[41,50,54,55,56,57]],[41,194,[86,89],[13,50,54,55,56,57,79,83,85]],[50,194,[83,85],[13,41,54,55,56,57,79,86,89]],[54,194,[79,83,85,89],[13,41,50,55,56,57,86]],[55,194,[79,85,86,89],[13,41,50,54,56,57,83]],[56,194,[79,83,86,89],[13,41,50,54,55,57,85]],[57,194,[79,83,85,86],[13,41,50,54,55,56,89]],[79,194,[13,54,55,56,57],[41,50,83,85,86,89]],[86,194,[13,41,55,56,57,83,85],[50,54,79,89]],[89,194,[13,41,54,55,56,83,85],[50,57,79,86]],[22,577,[14,43,51,57,64,73],[66,71]],[71,577,[14,43,57],[22,51,64,66,73]],[30,578,[14,43,51,57,80,89],[82,87]],[87,578,[14,43,57],[30,51,80,82,89]],[68,385,[15,52,56],[23,44,65,69,72]],[74,44,[17,61,62,91],[25,58,77,78]],[18,84,[26,75,82,90],[59,66]],[26,84,[18,59,66,90],[75,82]],[63,204,[79],[]],[79,204,[63],[]],[64,588,[80,90],[]],[80,588,[64,90],[]],[65,396,[81,91],[]],[67,228,[83],[]],[83,228,[67],[]],[69,452,[85],[]],[85,452,[69],[]],[70,216,[86],[]],[86,216,[70],[]],[73,712,[89],[]],[89,712,[73],[]]],\"edges\":[[19,[2,17,19,25,27,36,39,40,58,61,62,67,68,74,77,78,83,84,91]],[20,[3,18,26,32,39,41,42,43,59,63,64,66,67,69,75,79,80,82,83,85,90]],[22,[4,19,27,34,37,42,44,62,65,68,69,78,81,84,85,91]],[27,[7,21,29,33,47,50,52,53,61,63,65,70,72,73,77,79,81,86,88,89,91]],[39,[13,41,50,54,55,56,57,63,67,69,70,73,79,83,85,86,89]],[41,[14,22,30,43,51,57,64,66,71,73,80,82,87,89,90]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00114.record008" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00114.record008\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-28,-1],[-28,-2],[-28,-23],[-28,-24],[-28,-25],[-28,-26],[-28,-27],[-29,-28],[-30,-3],[-30,-23],[-30,-24],[-30,-25],[-30,-27],[-30,-28],[-31,-28],[-31,-30],[-32,-28],[-33,-23],[-33,-24],[-33,-25],[-33,-27],[-33,-28],[-33,-31],[-33,-32],[-34,-8],[-34,-28],[-34,-30],[-34,-33],[-35,-23],[-35,-24],[-35,-25],[-35,-27],[-35,-31],[-36,-5],[-37,-28],[-38,-26],[-38,-36],[-39,-35],[-40,-26],[-40,-36],[-41,-38],[-41,-40],[-42,-26],[-42,-36],[-42,-41],[-43,-8],[-43,-32],[-43,-36],[-43,-39],[-43,-41],[-44,-26],[-44,-36],[-44,-41],[-45,-9],[-45,-30],[-45,-33],[-45,-34],[-45,-42],[-45,-43],[-46,-4],[-46,-10],[-46,-38],[-46,-39],[-46,-43],[-46,-44],[-47,-33],[-47,-38],[-47,-43],[-47,-44],[-48,-2],[-48,-23],[-48,-30],[-48,-32],[-48,-33],[-48,-34],[-48,-37],[-48,-42],[-48,-43],[-48,-44],[-50,-28],[-51,-36],[-52,-32],[-52,-35],[-52,-40],[-52,-49],[-53,-30],[-53,-49],[-54,-35],[-54,-42],[-54,-49],[-54,-52],[-55,-49],[-55,-54],[-57,-45],[-58,-53],[-59,-32],[-59,-35],[-59,-54],[-61,-51],[-61,-57],[-62,-54],[-62,-61],[-63,-46],[-63,-58],[-64,-48],[-64,-54],[-66,-28],[-68,-35],[-68,-54],[-68,-65],[-69,-30],[-69,-53],[-69,-63],[-69,-65],[-70,-35],[-70,-65],[-71,-65],[-73,-45],[-74,-31],[-74,-52],[-74,-59],[-74,-68],[-74,-69],[-75,-7],[-75,-32],[-75,-35],[-75,-39],[-75,-52],[-75,-54],[-75,-59],[-75,-74],[-76,-24],[-76,-31],[-76,-33],[-76,-35],[-76,-52],[-76,-56],[-76,-59],[-76,-68],[-76,-72],[-76,-75],[-77,-67],[-78,-61],[-79,-39],[-79,-46],[-79,-53],[-79,-63],[-79,-74],[-11,-12,-54],[-6,-28,-36],[-13,-28,-49],[-19,-28,-65],[-12,1,14,27,30,31,58,59],[-14,1,12,27,30,31,49,52,58],[-49,1,14,30,31,58,59],[-12,-30,-59],[-14,-30,-49],[-30,-49,-59],[-18,1,20,27,30,31,74,75],[-65,1,20,30,31,74,75],[-30,-65,-75],[-30,-42,-47],[-50,2,30,32,33,34,58,60],[-57,2,23,30,32,33,54,58,60],[-66,2,30,32,33,34,74,76],[-73,2,23,30,32,33,70,74,76],[-33,7,10,39,43],[-28,14,53,56,59,60],[-14,-28,-60],[-28,-53,-60],[-20,3,25,28,33,35,72,76],[-75,3,25,28,33],[-20,-28,-76],[-28,-69,-76],[-36,11,15,50,61,62],[-16,4,24,38,41,43,44,54,56,61,64],[-21,4,24,38,41,43,44,70,72,77,80],[-15,5,26,40,42,44,55,64],[-57,6,15],[-8,54,58,60,61,64],[-32,61,64],[-41,58,60],[-45,54,58,60,64],[-46,54,60,61,64],[-47,54,58,61,64],[-48,54,58,60,61],[-54,8,45,46,47,48],[-60,8,41,45,46,48,61,64],[-61,8,32,46,47,48,58,60],[-64,8,32,45,46,47,58,60],[-8,70,74,76,77,80],[-32,77,80],[-41,74,76],[-45,70,74,76,80],[-46,70,76,77,80],[-47,70,74,77,80],[-48,70,74,76,77],[-70,8,45,46,47,48],[-77,8,32,46,47,48,74,76],[-80,8,32,45,46,47,74,76],[-17,9,34,42,48,55,64],[-62,9,34,48],[-22,9,34,42,48,71,80],[-78,9,34,48],[-59,10,43,47],[-65,12,52,53,82],[-13,19,66,73,81],[-19,13,50,57,81],[-54,70],[-70,54],[-55,71,81],[-71,55,81],[-56,72,82],[-58,74],[-74,58],[-60,76],[-76,60],[-61,77],[-77,61],[-64,80],[-80,64],[-83,29,37,50,51,57,62],[-84,31,39,52,53,59,63],[-85,66,67,73,78],[-86,68,69,75,79],[-87,23,24,25,26,27,36,49,65],[-88,32,34,41,45,46,47,48],[-89,28,30,33,35],[-90,38,40,42,44],[-91,43],[-92,83],[-92,84],[-93,85],[-93,86],[-94,92,93],[-95,92],[-95,93],[-96,87],[-96,88],[-97,90,91],[-98,91],[-99,89,98],[-99,97],[-100,98],[-101,96,100],[-102,96],[-101,99],[-102,100],[-103,94],[-103,95,102],[-103,101],[103],[-104,54,55,61,64],[-54,104],[-55,104],[-61,104],[-64,104],[-58,105],[-60,105],[-70,105],[-71,106],[-77,106],[-80,106],[-72,107],[-74,107],[-76,107],[-81,108],[-82,109],[-106,110],[-105,110],[-110,111],[-104,111],[-104,-110,112],[-109,113],[-108,113],[-113,114],[-107,114],[-107,-113,115],[-111,-115,116],[-112,-114,116],[-116],[1,12,14,18,20,27,30,31,49,52,53,58,59,65,68,69,74,75,82],[2,13,19,23,30,32,33,34,50,54,55,57,58,60,66,70,71,73,74,76,81],[3,14,20,25,28,33,35,53,56,59,60,69,72,75,76,82],[4,16,21,24,38,41,43,44,52,54,56,61,63,64,68,70,72,77,79,80,82],[8,32,41,45,46,47,48,54,58,60,61,64,70,74,76,77,80],[9,17,22,34,42,48,55,57,62,64,71,73,78,80,81]],\"atoms\":[{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":37,\"b\":2},{\"tag\":\"incompatible\",\"a\":37,\"b\":3},{\"tag\":\"incompatible\",\"a\":37,\"b\":32},{\"tag\":\"incompatible\",\"a\":37,\"b\":33},{\"tag\":\"incompatible\",\"a\":37,\"b\":34},{\"tag\":\"incompatible\",\"a\":37,\"b\":35},{\"tag\":\"incompatible\",\"a\":37,\"b\":36},{\"tag\":\"incompatible\",\"a\":38,\"b\":37},{\"tag\":\"incompatible\",\"a\":39,\"b\":4},{\"tag\":\"incompatible\",\"a\":39,\"b\":32},{\"tag\":\"incompatible\",\"a\":39,\"b\":33},{\"tag\":\"incompatible\",\"a\":39,\"b\":34},{\"tag\":\"incompatible\",\"a\":39,\"b\":36},{\"tag\":\"incompatible\",\"a\":39,\"b\":37},{\"tag\":\"incompatible\",\"a\":40,\"b\":37},{\"tag\":\"incompatible\",\"a\":40,\"b\":39},{\"tag\":\"incompatible\",\"a\":41,\"b\":37},{\"tag\":\"incompatible\",\"a\":42,\"b\":32},{\"tag\":\"incompatible\",\"a\":42,\"b\":33},{\"tag\":\"incompatible\",\"a\":42,\"b\":34},{\"tag\":\"incompatible\",\"a\":42,\"b\":36},{\"tag\":\"incompatible\",\"a\":42,\"b\":37},{\"tag\":\"incompatible\",\"a\":42,\"b\":40},{\"tag\":\"incompatible\",\"a\":42,\"b\":41},{\"tag\":\"incompatible\",\"a\":43,\"b\":13},{\"tag\":\"incompatible\",\"a\":43,\"b\":37},{\"tag\":\"incompatible\",\"a\":43,\"b\":39},{\"tag\":\"incompatible\",\"a\":43,\"b\":42},{\"tag\":\"incompatible\",\"a\":44,\"b\":32},{\"tag\":\"incompatible\",\"a\":44,\"b\":33},{\"tag\":\"incompatible\",\"a\":44,\"b\":34},{\"tag\":\"incompatible\",\"a\":44,\"b\":36},{\"tag\":\"incompatible\",\"a\":44,\"b\":40},{\"tag\":\"incompatible\",\"a\":45,\"b\":8},{\"tag\":\"incompatible\",\"a\":46,\"b\":37},{\"tag\":\"incompatible\",\"a\":47,\"b\":35},{\"tag\":\"incompatible\",\"a\":47,\"b\":45},{\"tag\":\"incompatible\",\"a\":48,\"b\":44},{\"tag\":\"incompatible\",\"a\":49,\"b\":35},{\"tag\":\"incompatible\",\"a\":49,\"b\":45},{\"tag\":\"incompatible\",\"a\":50,\"b\":47},{\"tag\":\"incompatible\",\"a\":50,\"b\":49},{\"tag\":\"incompatible\",\"a\":51,\"b\":35},{\"tag\":\"incompatible\",\"a\":51,\"b\":45},{\"tag\":\"incompatible\",\"a\":51,\"b\":50},{\"tag\":\"incompatible\",\"a\":52,\"b\":13},{\"tag\":\"incompatible\",\"a\":52,\"b\":41},{\"tag\":\"incompatible\",\"a\":52,\"b\":45},{\"tag\":\"incompatible\",\"a\":52,\"b\":48},{\"tag\":\"incompatible\",\"a\":52,\"b\":50},{\"tag\":\"incompatible\",\"a\":53,\"b\":35},{\"tag\":\"incompatible\",\"a\":53,\"b\":45},{\"tag\":\"incompatible\",\"a\":53,\"b\":50},{\"tag\":\"incompatible\",\"a\":54,\"b\":14},{\"tag\":\"incompatible\",\"a\":54,\"b\":39},{\"tag\":\"incompatible\",\"a\":54,\"b\":42},{\"tag\":\"incompatible\",\"a\":54,\"b\":43},{\"tag\":\"incompatible\",\"a\":54,\"b\":51},{\"tag\":\"incompatible\",\"a\":54,\"b\":52},{\"tag\":\"incompatible\",\"a\":55,\"b\":7},{\"tag\":\"incompatible\",\"a\":55,\"b\":15},{\"tag\":\"incompatible\",\"a\":55,\"b\":47},{\"tag\":\"incompatible\",\"a\":55,\"b\":48},{\"tag\":\"incompatible\",\"a\":55,\"b\":52},{\"tag\":\"incompatible\",\"a\":55,\"b\":53},{\"tag\":\"incompatible\",\"a\":56,\"b\":42},{\"tag\":\"incompatible\",\"a\":56,\"b\":47},{\"tag\":\"incompatible\",\"a\":56,\"b\":52},{\"tag\":\"incompatible\",\"a\":56,\"b\":53},{\"tag\":\"incompatible\",\"a\":57,\"b\":3},{\"tag\":\"incompatible\",\"a\":57,\"b\":32},{\"tag\":\"incompatible\",\"a\":57,\"b\":39},{\"tag\":\"incompatible\",\"a\":57,\"b\":41},{\"tag\":\"incompatible\",\"a\":57,\"b\":42},{\"tag\":\"incompatible\",\"a\":57,\"b\":43},{\"tag\":\"incompatible\",\"a\":57,\"b\":46},{\"tag\":\"incompatible\",\"a\":57,\"b\":51},{\"tag\":\"incompatible\",\"a\":57,\"b\":52},{\"tag\":\"incompatible\",\"a\":57,\"b\":53},{\"tag\":\"incompatible\",\"a\":59,\"b\":37},{\"tag\":\"incompatible\",\"a\":60,\"b\":45},{\"tag\":\"incompatible\",\"a\":61,\"b\":41},{\"tag\":\"incompatible\",\"a\":61,\"b\":44},{\"tag\":\"incompatible\",\"a\":61,\"b\":49},{\"tag\":\"incompatible\",\"a\":61,\"b\":58},{\"tag\":\"incompatible\",\"a\":62,\"b\":39},{\"tag\":\"incompatible\",\"a\":62,\"b\":58},{\"tag\":\"incompatible\",\"a\":63,\"b\":44},{\"tag\":\"incompatible\",\"a\":63,\"b\":51},{\"tag\":\"incompatible\",\"a\":63,\"b\":58},{\"tag\":\"incompatible\",\"a\":63,\"b\":61},{\"tag\":\"incompatible\",\"a\":64,\"b\":58},{\"tag\":\"incompatible\",\"a\":64,\"b\":63},{\"tag\":\"incompatible\",\"a\":66,\"b\":54},{\"tag\":\"incompatible\",\"a\":67,\"b\":62},{\"tag\":\"incompatible\",\"a\":68,\"b\":41},{\"tag\":\"incompatible\",\"a\":68,\"b\":44},{\"tag\":\"incompatible\",\"a\":68,\"b\":63},{\"tag\":\"incompatible\",\"a\":70,\"b\":60},{\"tag\":\"incompatible\",\"a\":70,\"b\":66},{\"tag\":\"incompatible\",\"a\":71,\"b\":63},{\"tag\":\"incompatible\",\"a\":71,\"b\":70},{\"tag\":\"incompatible\",\"a\":72,\"b\":55},{\"tag\":\"incompatible\",\"a\":72,\"b\":67},{\"tag\":\"incompatible\",\"a\":73,\"b\":57},{\"tag\":\"incompatible\",\"a\":73,\"b\":63},{\"tag\":\"incompatible\",\"a\":75,\"b\":37},{\"tag\":\"incompatible\",\"a\":77,\"b\":44},{\"tag\":\"incompatible\",\"a\":77,\"b\":63},{\"tag\":\"incompatible\",\"a\":77,\"b\":74},{\"tag\":\"incompatible\",\"a\":78,\"b\":39},{\"tag\":\"incompatible\",\"a\":78,\"b\":62},{\"tag\":\"incompatible\",\"a\":78,\"b\":72},{\"tag\":\"incompatible\",\"a\":78,\"b\":74},{\"tag\":\"incompatible\",\"a\":79,\"b\":44},{\"tag\":\"incompatible\",\"a\":79,\"b\":74},{\"tag\":\"incompatible\",\"a\":80,\"b\":74},{\"tag\":\"incompatible\",\"a\":82,\"b\":54},{\"tag\":\"incompatible\",\"a\":83,\"b\":40},{\"tag\":\"incompatible\",\"a\":83,\"b\":61},{\"tag\":\"incompatible\",\"a\":83,\"b\":68},{\"tag\":\"incompatible\",\"a\":83,\"b\":77},{\"tag\":\"incompatible\",\"a\":83,\"b\":78},{\"tag\":\"incompatible\",\"a\":84,\"b\":12},{\"tag\":\"incompatible\",\"a\":84,\"b\":41},{\"tag\":\"incompatible\",\"a\":84,\"b\":44},{\"tag\":\"incompatible\",\"a\":84,\"b\":48},{\"tag\":\"incompatible\",\"a\":84,\"b\":61},{\"tag\":\"incompatible\",\"a\":84,\"b\":63},{\"tag\":\"incompatible\",\"a\":84,\"b\":68},{\"tag\":\"incompatible\",\"a\":84,\"b\":83},{\"tag\":\"incompatible\",\"a\":85,\"b\":33},{\"tag\":\"incompatible\",\"a\":85,\"b\":40},{\"tag\":\"incompatible\",\"a\":85,\"b\":42},{\"tag\":\"incompatible\",\"a\":85,\"b\":44},{\"tag\":\"incompatible\",\"a\":85,\"b\":61},{\"tag\":\"incompatible\",\"a\":85,\"b\":65},{\"tag\":\"incompatible\",\"a\":85,\"b\":68},{\"tag\":\"incompatible\",\"a\":85,\"b\":77},{\"tag\":\"incompatible\",\"a\":85,\"b\":81},{\"tag\":\"incompatible\",\"a\":85,\"b\":84},{\"tag\":\"incompatible\",\"a\":86,\"b\":76},{\"tag\":\"incompatible\",\"a\":87,\"b\":70},{\"tag\":\"incompatible\",\"a\":88,\"b\":48},{\"tag\":\"incompatible\",\"a\":88,\"b\":55},{\"tag\":\"incompatible\",\"a\":88,\"b\":62},{\"tag\":\"incompatible\",\"a\":88,\"b\":72},{\"tag\":\"incompatible\",\"a\":88,\"b\":83},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[16,17,63]},{\"tag\":\"three\",\"ridge\":19,\"vertices\":[10,37,45]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[18,37,58]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[26,37,74]},{\"tag\":\"mate\",\"ridge\":37,\"a\":17,\"owners\":[2,19,36,39,40,67,68]},{\"tag\":\"mate\",\"ridge\":37,\"a\":19,\"owners\":[2,17,36,39,40,58,61,67]},{\"tag\":\"mate\",\"ridge\":37,\"a\":58,\"owners\":[2,19,39,40,67,68]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[17,39,68]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[19,39,58]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[39,58,68]},{\"tag\":\"mate\",\"ridge\":38,\"a\":25,\"owners\":[2,27,36,39,40,83,84]},{\"tag\":\"mate\",\"ridge\":38,\"a\":74,\"owners\":[2,27,39,40,83,84]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[39,74,84]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[39,51,56]},{\"tag\":\"mate\",\"ridge\":69,\"a\":59,\"owners\":[3,39,41,42,43,67,69]},{\"tag\":\"mate\",\"ridge\":69,\"a\":66,\"owners\":[3,32,39,41,42,63,67,69]},{\"tag\":\"mate\",\"ridge\":70,\"a\":75,\"owners\":[3,39,41,42,43,83,85]},{\"tag\":\"mate\",\"ridge\":70,\"a\":82,\"owners\":[3,32,39,41,42,79,83,85]},{\"tag\":\"mate\",\"ridge\":259,\"a\":42,\"owners\":[12,15,48,52]},{\"tag\":\"mate\",\"ridge\":261,\"a\":37,\"owners\":[19,62,65,68,69]},{\"tag\":\"three\",\"ridge\":261,\"vertices\":[19,37,69]},{\"tag\":\"three\",\"ridge\":261,\"vertices\":[37,62,69]},{\"tag\":\"mate\",\"ridge\":262,\"a\":27,\"owners\":[4,34,37,42,44,81,85]},{\"tag\":\"mate\",\"ridge\":262,\"a\":84,\"owners\":[4,34,37,42]},{\"tag\":\"three\",\"ridge\":262,\"vertices\":[27,37,85]},{\"tag\":\"three\",\"ridge\":262,\"vertices\":[37,78,85]},{\"tag\":\"mate\",\"ridge\":25,\"a\":45,\"owners\":[16,20,59,70,71]},{\"tag\":\"mate\",\"ridge\":137,\"a\":21,\"owners\":[7,33,47,50,52,53,63,65,70,73]},{\"tag\":\"mate\",\"ridge\":138,\"a\":29,\"owners\":[7,33,47,50,52,53,79,81,86,89]},{\"tag\":\"mate\",\"ridge\":521,\"a\":20,\"owners\":[8,35,49,51,53,64,73]},{\"tag\":\"mate\",\"ridge\":529,\"a\":66,\"owners\":[10,20]},{\"tag\":\"mate\",\"ridge\":193,\"a\":13,\"owners\":[63,67,69,70,73]},{\"tag\":\"mate\",\"ridge\":193,\"a\":41,\"owners\":[70,73]},{\"tag\":\"mate\",\"ridge\":193,\"a\":50,\"owners\":[67,69]},{\"tag\":\"mate\",\"ridge\":193,\"a\":54,\"owners\":[63,67,69,73]},{\"tag\":\"mate\",\"ridge\":193,\"a\":55,\"owners\":[63,69,70,73]},{\"tag\":\"mate\",\"ridge\":193,\"a\":56,\"owners\":[63,67,70,73]},{\"tag\":\"mate\",\"ridge\":193,\"a\":57,\"owners\":[63,67,69,70]},{\"tag\":\"mate\",\"ridge\":193,\"a\":63,\"owners\":[13,54,55,56,57]},{\"tag\":\"mate\",\"ridge\":193,\"a\":69,\"owners\":[13,50,54,55,57,70,73]},{\"tag\":\"mate\",\"ridge\":193,\"a\":70,\"owners\":[13,41,55,56,57,67,69]},{\"tag\":\"mate\",\"ridge\":193,\"a\":73,\"owners\":[13,41,54,55,56,67,69]},{\"tag\":\"mate\",\"ridge\":194,\"a\":13,\"owners\":[79,83,85,86,89]},{\"tag\":\"mate\",\"ridge\":194,\"a\":41,\"owners\":[86,89]},{\"tag\":\"mate\",\"ridge\":194,\"a\":50,\"owners\":[83,85]},{\"tag\":\"mate\",\"ridge\":194,\"a\":54,\"owners\":[79,83,85,89]},{\"tag\":\"mate\",\"ridge\":194,\"a\":55,\"owners\":[79,85,86,89]},{\"tag\":\"mate\",\"ridge\":194,\"a\":56,\"owners\":[79,83,86,89]},{\"tag\":\"mate\",\"ridge\":194,\"a\":57,\"owners\":[79,83,85,86]},{\"tag\":\"mate\",\"ridge\":194,\"a\":79,\"owners\":[13,54,55,56,57]},{\"tag\":\"mate\",\"ridge\":194,\"a\":86,\"owners\":[13,41,55,56,57,83,85]},{\"tag\":\"mate\",\"ridge\":194,\"a\":89,\"owners\":[13,41,54,55,56,83,85]},{\"tag\":\"mate\",\"ridge\":577,\"a\":22,\"owners\":[14,43,51,57,64,73]},{\"tag\":\"mate\",\"ridge\":577,\"a\":71,\"owners\":[14,43,57]},{\"tag\":\"mate\",\"ridge\":578,\"a\":30,\"owners\":[14,43,51,57,80,89]},{\"tag\":\"mate\",\"ridge\":578,\"a\":87,\"owners\":[14,43,57]},{\"tag\":\"mate\",\"ridge\":385,\"a\":68,\"owners\":[15,52,56]},{\"tag\":\"mate\",\"ridge\":44,\"a\":74,\"owners\":[17,61,62,91]},{\"tag\":\"mate\",\"ridge\":84,\"a\":18,\"owners\":[26,75,82,90]},{\"tag\":\"mate\",\"ridge\":84,\"a\":26,\"owners\":[18,59,66,90]},{\"tag\":\"mate\",\"ridge\":204,\"a\":63,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":204,\"a\":79,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":588,\"a\":64,\"owners\":[80,90]},{\"tag\":\"mate\",\"ridge\":588,\"a\":80,\"owners\":[64,90]},{\"tag\":\"mate\",\"ridge\":396,\"a\":65,\"owners\":[81,91]},{\"tag\":\"mate\",\"ridge\":228,\"a\":67,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":228,\"a\":83,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":452,\"a\":69,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":452,\"a\":85,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":216,\"a\":70,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":216,\"a\":86,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":712,\"a\":73,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":712,\"a\":89,\"owners\":[73]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[38,46,59,60,66,71],\"full_literals\":[-83,29,37,50,51,57,62]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[40,48,61,62,68,72],\"full_literals\":[-84,31,39,52,53,59,63]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[75,76,82,87],\"full_literals\":[-85,66,67,73,78]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[77,78,84,88],\"full_literals\":[-86,68,69,75,79]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[32,33,34,35,36,45,58,74],\"full_literals\":[-87,23,24,25,26,27,36,49,65]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[41,43,50,54,55,56,57],\"full_literals\":[-88,32,34,41,45,46,47,48]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[37,39,42,44],\"full_literals\":[-89,28,30,33,35]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[47,49,51,53],\"full_literals\":[-90,38,40,42,44]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[52],\"full_literals\":[-91,43]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-92,83,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-92,false,84],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-93,85,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-93,false,86],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-94,92,93],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-95,92,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-95,false,93],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-96,87,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-96,false,88],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-97,90,91],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-98,false,91],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-99,89,98],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-99,false,97],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-100,false,98],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-101,96,100],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-102,96,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-101,false,99],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-102,false,100],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-103,94,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-103,95,102],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-103,false,101],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[63,64,70,73],\"full_literals\":[-104,54,55,61,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":63,\"full_literals\":[-54,104]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":64,\"full_literals\":[-55,104]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":70,\"full_literals\":[-61,104]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":73,\"full_literals\":[-64,104]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":67,\"full_literals\":[-58,105]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":69,\"full_literals\":[-60,105]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":79,\"full_literals\":[-70,105]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":80,\"full_literals\":[-71,106]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":86,\"full_literals\":[-77,106]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":89,\"full_literals\":[-80,106]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":81,\"full_literals\":[-72,107]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":83,\"full_literals\":[-74,107]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":85,\"full_literals\":[-76,107]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":90,\"full_literals\":[-81,108]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":91,\"full_literals\":[-82,109]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-106,110],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-105,false,110],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-110,111],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-104,false,111],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-104,-110,112],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-109,113],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-108,false,113],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-113,114],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-107,false,114],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-107,-113,115],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-111,-115,116],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-112,-114,116],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":19,\"owners\":[2,17,19,25,27,36,39,40,58,61,62,67,68,74,77,78,83,84,91]},{\"tag\":\"edge\",\"edge\":20,\"owners\":[3,18,26,32,39,41,42,43,59,63,64,66,67,69,75,79,80,82,83,85,90]},{\"tag\":\"edge\",\"edge\":22,\"owners\":[4,19,27,34,37,42,44,62,65,68,69,78,81,84,85,91]},{\"tag\":\"edge\",\"edge\":27,\"owners\":[7,21,29,33,47,50,52,53,61,63,65,70,72,73,77,79,81,86,88,89,91]},{\"tag\":\"edge\",\"edge\":39,\"owners\":[13,41,50,54,55,56,57,63,67,69,70,73,79,83,85,86,89]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[14,22,30,43,51,57,64,66,71,73,80,82,87,89,90]}]}"
  "p cnf 116 287\n-28 -1 0\n-28 -2 0\n-28 -23 0\n-28 -24 0\n-28 -25 0\n-28 -26 0\n-28 -27 0\n-29 -28 0\n-30 -3 0\n-30 -23 0\n-30 -24 0\n-30 -25 0\n-30 -27 0\n-30 -28 0\n-31 -28 0\n-31 -30 0\n-32 -28 0\n-33 -23 0\n-33 -24 0\n-33 -25 0\n-33 -27 0\n-33 -28 0\n-33 -31 0\n-33 -32 0\n-34 -8 0\n-34 -28 0\n-34 -30 0\n-34 -33 0\n-35 -23 0\n-35 -24 0\n-35 -25 0\n-35 -27 0\n-35 -31 0\n-36 -5 0\n-37 -28 0\n-38 -26 0\n-38 -36 0\n-39 -35 0\n-40 -26 0\n-40 -36 0\n-41 -38 0\n-41 -40 0\n-42 -26 0\n-42 -36 0\n-42 -41 0\n-43 -8 0\n-43 -32 0\n-43 -36 0\n-43 -39 0\n-43 -41 0\n-44 -26 0\n-44 -36 0\n-44 -41 0\n-45 -9 0\n-45 -30 0\n-45 -33 0\n-45 -34 0\n-45 -42 0\n-45 -43 0\n-46 -4 0\n-46 -10 0\n-46 -38 0\n-46 -39 0\n-46 -43 0\n-46 -44 0\n-47 -33 0\n-47 -38 0\n-47 -43 0\n-47 -44 0\n-48 -2 0\n-48 -23 0\n-48 -30 0\n-48 -32 0\n-48 -33 0\n-48 -34 0\n-48 -37 0\n-48 -42 0\n-48 -43 0\n-48 -44 0\n-50 -28 0\n-51 -36 0\n-52 -32 0\n-52 -35 0\n-52 -40 0\n-52 -49 0\n-53 -30 0\n-53 -49 0\n-54 -35 0\n-54 -42 0\n-54 -49 0\n-54 -52 0\n-55 -49 0\n-55 -54 0\n-57 -45 0\n-58 -53 0\n-59 -32 0\n-59 -35 0\n-59 -54 0\n-61 -51 0\n-61 -57 0\n-62 -54 0\n-62 -61 0\n-63 -46 0\n-63 -58 0\n-64 -48 0\n-64 -54 0\n-66 -28 0\n-68 -35 0\n-68 -54 0\n-68 -65 0\n-69 -30 0\n-69 -53 0\n-69 -63 0\n-69 -65 0\n-70 -35 0\n-70 -65 0\n-71 -65 0\n-73 -45 0\n-74 -31 0\n-74 -52 0\n-74 -59 0\n-74 -68 0\n-74 -69 0\n-75 -7 0\n-75 -32 0\n-75 -35 0\n-75 -39 0\n-75 -52 0\n-75 -54 0\n-75 -59 0\n-75 -74 0\n-76 -24 0\n-76 -31 0\n-76 -33 0\n-76 -35 0\n-76 -52 0\n-76 -56 0\n-76 -59 0\n-76 -68 0\n-76 -72 0\n-76 -75 0\n-77 -67 0\n-78 -61 0\n-79 -39 0\n-79 -46 0\n-79 -53 0\n-79 -63 0\n-79 -74 0\n-11 -12 -54 0\n-6 -28 -36 0\n-13 -28 -49 0\n-19 -28 -65 0\n-12 1 14 27 30 31 58 59 0\n-14 1 12 27 30 31 49 52 58 0\n-49 1 14 30 31 58 59 0\n-12 -30 -59 0\n-14 -30 -49 0\n-30 -49 -59 0\n-18 1 20 27 30 31 74 75 0\n-65 1 20 30 31 74 75 0\n-30 -65 -75 0\n-30 -42 -47 0\n-50 2 30 32 33 34 58 60 0\n-57 2 23 30 32 33 54 58 60 0\n-66 2 30 32 33 34 74 76 0\n-73 2 23 30 32 33 70 74 76 0\n-33 7 10 39 43 0\n-28 14 53 56 59 60 0\n-14 -28 -60 0\n-28 -53 -60 0\n-20 3 25 28 33 35 72 76 0\n-75 3 25 28 33 0\n-20 -28 -76 0\n-28 -69 -76 0\n-36 11 15 50 61 62 0\n-16 4 24 38 41 43 44 54 56 61 64 0\n-21 4 24 38 41 43 44 70 72 77 80 0\n-15 5 26 40 42 44 55 64 0\n-57 6 15 0\n-8 54 58 60 61 64 0\n-32 61 64 0\n-41 58 60 0\n-45 54 58 60 64 0\n-46 54 60 61 64 0\n-47 54 58 61 64 0\n-48 54 58 60 61 0\n-54 8 45 46 47 48 0\n-60 8 41 45 46 48 61 64 0\n-61 8 32 46 47 48 58 60 0\n-64 8 32 45 46 47 58 60 0\n-8 70 74 76 77 80 0\n-32 77 80 0\n-41 74 76 0\n-45 70 74 76 80 0\n-46 70 76 77 80 0\n-47 70 74 77 80 0\n-48 70 74 76 77 0\n-70 8 45 46 47 48 0\n-77 8 32 46 47 48 74 76 0\n-80 8 32 45 46 47 74 76 0\n-17 9 34 42 48 55 64 0\n-62 9 34 48 0\n-22 9 34 42 48 71 80 0\n-78 9 34 48 0\n-59 10 43 47 0\n-65 12 52 53 82 0\n-13 19 66 73 81 0\n-19 13 50 57 81 0\n-54 70 0\n-70 54 0\n-55 71 81 0\n-71 55 81 0\n-56 72 82 0\n-58 74 0\n-74 58 0\n-60 76 0\n-76 60 0\n-61 77 0\n-77 61 0\n-64 80 0\n-80 64 0\n-83 29 37 50 51 57 62 0\n-84 31 39 52 53 59 63 0\n-85 66 67 73 78 0\n-86 68 69 75 79 0\n-87 23 24 25 26 27 36 49 65 0\n-88 32 34 41 45 46 47 48 0\n-89 28 30 33 35 0\n-90 38 40 42 44 0\n-91 43 0\n-92 83 0\n-92 84 0\n-93 85 0\n-93 86 0\n-94 92 93 0\n-95 92 0\n-95 93 0\n-96 87 0\n-96 88 0\n-97 90 91 0\n-98 91 0\n-99 89 98 0\n-99 97 0\n-100 98 0\n-101 96 100 0\n-102 96 0\n-101 99 0\n-102 100 0\n-103 94 0\n-103 95 102 0\n-103 101 0\n103 0\n-104 54 55 61 64 0\n-54 104 0\n-55 104 0\n-61 104 0\n-64 104 0\n-58 105 0\n-60 105 0\n-70 105 0\n-71 106 0\n-77 106 0\n-80 106 0\n-72 107 0\n-74 107 0\n-76 107 0\n-81 108 0\n-82 109 0\n-106 110 0\n-105 110 0\n-110 111 0\n-104 111 0\n-104 -110 112 0\n-109 113 0\n-108 113 0\n-113 114 0\n-107 114 0\n-107 -113 115 0\n-111 -115 116 0\n-112 -114 116 0\n-116 0\n1 12 14 18 20 27 30 31 49 52 53 58 59 65 68 69 74 75 82 0\n2 13 19 23 30 32 33 34 50 54 55 57 58 60 66 70 71 73 74 76 81 0\n3 14 20 25 28 33 35 53 56 59 60 69 72 75 76 82 0\n4 16 21 24 38 41 43 44 52 54 56 61 63 64 68 70 72 77 79 80 82 0\n8 32 41 45 46 47 48 54 58 60 61 64 70 74 76 77 80 0\n9 17 22 34 42 48 55 57 62 64 71 73 78 80 81 0\n"
  "288 94 0 252 249 0\n289 101 0 252 251 0\n290 99 0 289 247 0\n291 97 0 290 243 0\n292 111 0 271 272 269 270 254 256 257 262 263 258 259 260 180 183 184 185 186 181 215 217 182 286 0\n293 -115 0 292 281 279 0\n294 110 107 0 265 266 193 216 214 269 270 262 263 260 218 220 192 191 194 195 196 197 209 286 0\n295 107 112 0 265 266 214 216 193 294 273 254 256 257 180 183 184 185 186 210 219 221 181 286 0\n296 74 76 104 0 257 221 256 219 254 210 195 216 181 214 191 194 196 197 193 286 0\n297 -74 0 288 252 119 120 121 122 123 131 148 215 225 95 104 234 237 235 250 232 248 223 244 49 241 230 0\n298 -58 0 297 214 0\n299 41 45 46 48 104 0 297 289 296 217 257 221 256 219 254 210 196 181 188 25 46 227 230 239 241 245 244 0\n300 -41 0 291 41 42 45 50 53 229 230 240 0\n301 -45 48 104 81 0 257 221 255 212 54 57 58 94 118 201 204 202 203 287 0\n302 -46 104 82 0 297 300 296 140 139 137 136 132 257 221 256 219 254 210 60 62 64 65 103 145 176 177 285 0\n303 48 46 104 81 0 300 301 299 0\n304 104 113 0 290 297 298 275 267 274 268 296 133 134 135 136 138 139 141 217 302 303 72 78 230 241 242 228 1 7 169 170 173 174 153 155 159 160 282 0\n305 112 0 293 295 278 275 267 304 273 269 270 261 262 263 260 211 218 220 209 253 0\n306 -114 0 305 281 280 0\n307 -113 0 306 276 0\n308 -107 0 306 277 0\n309 -109 0 307 274 0\n310 -108 0 307 275 0\n311 -72 0 308 264 0\n312 -76 0 308 266 0\n313 -82 0 309 268 0\n314 -81 0 310 267 0\n315 -56 0 311 313 213 0\n316 -60 0 312 216 0\n317 -59 -48 0 290 252 316 298 78 230 241 244 248 250 236 231 242 75 74 73 72 70 163 76 71 97 98 228 186 164 8 99 102 222 0\n318 -61 29 -48 0 298 316 252 78 230 241 244 248 250 236 231 75 74 73 72 70 163 76 99 100 102 222 0\n319 -28 53 52 -48 0 289 315 316 312 297 298 317 78 230 241 244 245 238 75 74 73 72 70 163 105 79 77 71 1 4 5 6 7 8 15 168 318 219 186 197 90 93 101 116 154 226 149 34 40 175 178 0\n320 -35 -48 0 252 298 316 312 297 78 230 241 244 248 250 237 233 75 74 73 72 70 165 71 88 115 186 197 166 143 142 224 0\n321 -48 0 290 252 298 316 72 74 78 230 241 244 242 248 250 237 234 320 228 8 318 186 129 91 319 112 146 225 109 0\n322 -102 -54 -28 0 209 116 90 7 6 5 4 3 246 248 238 244 226 241 48 230 0\n323 -36 -54 -28 0 252 322 250 236 231 106 101 93 89 80 35 8 6 34 40 52 81 150 178 222 179 0\n324 -54 -28 0 289 321 7 6 5 4 3 90 209 116 323 226 238 245 244 241 230 46 59 64 68 187 0\n325 -43 61 -28 0 312 297 316 298 321 300 219 324 210 17 46 59 64 68 190 200 286 0\n326 -36 -90 0 37 40 44 52 229 0\n327 -49 -28 0 314 312 297 316 298 2 22 17 14 3 324 210 166 164 107 80 26 92 151 212 208 283 0\n328 -65 -28 0 314 312 297 316 298 2 22 17 14 3 324 210 166 164 107 80 26 117 152 211 207 283 0\n329 -36 0 291 48 326 230 240 0\n330 -28 0 329 289 316 298 321 3 4 5 6 7 17 327 328 226 238 245 244 241 230 46 64 68 325 189 0\n331 -43 0 312 297 316 298 321 300 46 47 59 64 68 189 190 199 200 187 198 286 0\n332 -91 0 331 230 0\n333 -98 0 332 241 0\n334 90 0 332 291 240 0\n335 -100 0 333 244 0\n336 89 0 333 290 242 0\n337 -102 0 335 248 0\n338 96 0 335 289 245 0\n339 95 0 337 252 250 0\n340 87 0 338 238 0\n341 88 0 338 239 0\n342 92 0 339 236 0\n343 93 0 339 237 0\n344 84 0 342 232 0\n345 86 0 343 234 0\n346 -25 0 330 336 12 20 31 228 0\n347 -26 0 334 36 39 43 51 229 0\n348 -24 0 330 336 11 19 30 228 0\n349 -27 0 330 336 13 21 32 228 0\n350 -35 -49 0 344 345 87 85 33 38 97 108 126 223 113 147 225 0\n351 33 -49 0 336 313 312 311 316 315 330 346 350 87 228 9 111 157 158 171 172 284 0\n352 -46 -49 0 331 344 351 66 23 87 85 61 63 103 205 223 0\n353 -49 0 321 341 300 351 28 56 66 352 24 227 0\n354 -39 -65 0 345 114 110 127 144 225 0\n355 -63 -65 0 345 330 336 321 341 300 114 110 103 147 225 125 126 161 228 28 56 66 227 0\n356 -31 0 330 336 16 23 33 228 0\n357 -47 -52 0 330 336 334 84 83 66 67 69 228 229 162 0\n358 -45 35 0 330 336 55 56 228 0\n359 -52 -65 0 345 321 341 300 330 336 114 110 82 83 128 225 145 357 358 227 27 28 228 0\n360 -53 -65 0 345 330 336 331 321 341 300 354 114 110 86 146 225 124 125 126 358 228 28 66 167 227 61 0\n361 -65 0 356 344 313 330 336 345 321 341 300 110 114 354 355 359 360 223 206 96 97 130 156 358 228 225 28 66 145 227 0\n362 23 0 361 353 349 340 346 347 348 329 226 0\n363 -30 0 362 10 0\n364 -33 0 362 18 0\n365 -35 0 362 29 0\n366 0 364 365 336 363 330 228 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record008.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record008.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record008.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record008.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record008 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record008.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record008.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record008.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record008.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record008 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record008_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record008 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record008_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record008_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00114.record008
