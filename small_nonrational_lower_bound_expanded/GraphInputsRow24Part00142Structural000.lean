module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00142Data
public import GraphInputsRow24Part00142Frames
public import GraphInputsRow24Part00142Leaves
public import GraphInputsRow24Part00142Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00142.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record002
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨80, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 5630049290027008, 442005821849600, (certNat% 3), 9367487224930631680, 68719476736]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 4), 903016873984, 5910974510923776, (certNat% 3), 648518346341351424, 17592186044416]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), 10141938204278784, 2882303761517117440, (certNat% 6), 439806798594048, 963146416128]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), 14645529241714688, (certNat% 9), 1040455827456, 512374566027264, 792633538712174592]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record002_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00142.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00142.record000
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2f03b19c4f0bcb8ad2aca723ca6a3a99a2e8e665a362d98e338ae1b91e2783e9c4f19a4e94e4b9396354d4b53352d2b46d4749d0f66338f1394cd38ccb31ce4b52ccb8acab1ad1b26c3b31e2729c6785c970dc8f13c2f07ce82d0ac329162590e23a618c469454354342d90e1344d0b12d0705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "34da6db6d36d34926934d26da49a49349a4d36926d26db6d2492449249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record000 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record000 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record000.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record000.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record000.data.quota

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
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 50), (facetIndex 65), (facetIndex 67)]))
 (.leaf ([(facetIndex 25), (facetIndex 37), (facetIndex 40), (facetIndex 41), (facetIndex 42)])))
 (.branch 3
 (.leaf ([(facetIndex 29), (facetIndex 45), (facetIndex 47), (facetIndex 48)]))
 (.branch 4
 (.leaf ([(facetIndex 23), (facetIndex 69), (facetIndex 70), (facetIndex 74), (facetIndex 77)]))
 (.leaf ([(facetIndex 54), (facetIndex 73), (facetIndex 91)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 51), (facetIndex 53), (facetIndex 56), (facetIndex 59)]))
 (.leaf ([(facetIndex 27), (facetIndex 58), (facetIndex 60)])))
 (.branch 8
 (.leaf ([(facetIndex 36), (facetIndex 88)]))
 (.branch 9
 (.leaf ([(facetIndex 26), (facetIndex 28), (facetIndex 55), (facetIndex 64)]))
 (.leaf ([(facetIndex 24), (facetIndex 72), (facetIndex 75), (facetIndex 81)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "400700000090003093490330000800065605845050022020011100170000002868193z17;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 43), (facetIndex 85), (facetIndex 86)]))
 (.leaf ([(facetIndex 83), (facetIndex 87), (facetIndex 92)])))
 (.branch 3
 (.leaf ([(facetIndex 34), (facetIndex 35), (facetIndex 63), (facetIndex 80)]))
 (.leaf ([(facetIndex 52), (facetIndex 68), (facetIndex 89), (facetIndex 90)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 31), (facetIndex 33), (facetIndex 46), (facetIndex 62)]))
 (.leaf ([(facetIndex 38), (facetIndex 57), (facetIndex 66)])))
 (.branch 7
 (.leaf ([(facetIndex 30), (facetIndex 44), (facetIndex 61)]))
 (.branch 8
 (.leaf ([(facetIndex 32), (facetIndex 39), (facetIndex 49), (facetIndex 71), (facetIndex 79), (facetIndex 84)]))
 (.leaf ([(facetIndex 76), (facetIndex 78), (facetIndex 82)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "103301007180278080000700305002460005000030070040600007500224746z1e;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped1_0000 : List Nat := [0, 1]
def grouped1_0001 : List Nat := [0, 1, 2, 3, 4]
def grouped1_0002 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
def grouped1_0004 : List Nat := [2]
def grouped1_0005 : List Nat := [2, 3, 4]
def grouped1_0006 : List Nat := [3]
def grouped1_0007 : List Nat := [3, 4]
def grouped1_0008 : List Nat := [4]
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
def grouped2_0045 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0047 : List Nat := [1]
def grouped2_0048 : List Nat := [2]
def grouped2_0049 : List Nat := [2, 3, 4]
def grouped2_0050 : List Nat := [3]
def grouped2_0051 : List Nat := [3, 4]
def grouped2_0052 : List Nat := [4]
def grouped2_0053 : List Nat := [5]
def grouped2_0054 : List Nat := [5, 6]
def grouped2_0055 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0056 : List Nat := [6]
def grouped2_0057 : List Nat := [7]
def grouped2_0058 : List Nat := [7, 8, 9]
def grouped2_0059 : List Nat := [8]
def grouped2_0060 : List Nat := [8, 9]
def grouped2_0061 : List Nat := [9]
def grouped3_0062 : List Nat := [0]
def grouped3_0063 : List Nat := [0, 1]
def grouped3_0064 : List Nat := [0, 1, 2, 3]
def grouped3_0066 : List Nat := [1]
def grouped3_0067 : List Nat := [2]
def grouped3_0068 : List Nat := [2, 3]
def grouped3_0069 : List Nat := [3]
def grouped3_0070 : List Nat := [4]
def grouped3_0071 : List Nat := [4, 5]
def grouped3_0072 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0073 : List Nat := [5]
def grouped3_0074 : List Nat := [6]
def grouped3_0075 : List Nat := [6, 7, 8]
def grouped3_0076 : List Nat := [7]
def grouped3_0077 : List Nat := [7, 8]
def grouped3_0078 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record000 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record000_matrix_checked

def leafCount : Nat := 52
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaf0000 : List (Fin data.count) := [(facetIndex 4), (facetIndex 11), (facetIndex 14), (facetIndex 16), (facetIndex 42), (facetIndex 48), (facetIndex 56), (facetIndex 60), (facetIndex 64), (facetIndex 73), (facetIndex 77), (facetIndex 83), (facetIndex 84), (facetIndex 88)]
theorem leaf0000_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0000 = true := by
  decide +kernel
theorem leaf0000_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0000 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0000_counts_checked
def leaf0001 : List (Fin data.count) := [(facetIndex 4), (facetIndex 11), (facetIndex 14), (facetIndex 16), (facetIndex 42), (facetIndex 48), (facetIndex 56), (facetIndex 60), (facetIndex 64), (facetIndex 73), (facetIndex 77), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0001_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0001 = true := by
  decide +kernel
theorem leaf0001_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0001 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0001_counts_checked
def leaf0002 : List (Fin data.count) := [(facetIndex 4), (facetIndex 7), (facetIndex 11), (facetIndex 18), (facetIndex 40), (facetIndex 48), (facetIndex 56), (facetIndex 60), (facetIndex 65), (facetIndex 74), (facetIndex 75), (facetIndex 86), (facetIndex 91), (facetIndex 92)]
theorem leaf0002_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0002 = true := by
  decide +kernel
theorem leaf0002_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0002 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0002_counts_checked
def leaf0003 : List (Fin data.count) := [(facetIndex 4), (facetIndex 7), (facetIndex 11), (facetIndex 15), (facetIndex 40), (facetIndex 48), (facetIndex 56), (facetIndex 60), (facetIndex 65), (facetIndex 70), (facetIndex 75), (facetIndex 86), (facetIndex 91), (facetIndex 92)]
theorem leaf0003_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0003 = true := by
  decide +kernel
theorem leaf0003_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0003 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0003_counts_checked
def leaf0004 : List (Fin data.count) := [(facetIndex 4), (facetIndex 11), (facetIndex 14), (facetIndex 20), (facetIndex 42), (facetIndex 48), (facetIndex 56), (facetIndex 60), (facetIndex 64), (facetIndex 70), (facetIndex 73), (facetIndex 75), (facetIndex 86), (facetIndex 92)]
theorem leaf0004_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0004 = true := by
  decide +kernel
theorem leaf0004_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0004 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0004_counts_checked
def leaf0005 : List (Fin data.count) := [(facetIndex 3), (facetIndex 4), (facetIndex 11), (facetIndex 16), (facetIndex 48), (facetIndex 50), (facetIndex 56), (facetIndex 60), (facetIndex 64), (facetIndex 73), (facetIndex 77), (facetIndex 86), (facetIndex 88), (facetIndex 92)]
theorem leaf0005_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0005 = true := by
  decide +kernel
theorem leaf0005_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0005 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0005_counts_checked
def leaf0006 : List (Fin data.count) := [(facetIndex 4), (facetIndex 11), (facetIndex 14), (facetIndex 16), (facetIndex 42), (facetIndex 48), (facetIndex 56), (facetIndex 60), (facetIndex 64), (facetIndex 73), (facetIndex 77), (facetIndex 86), (facetIndex 88), (facetIndex 92)]
theorem leaf0006_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0006 = true := by
  decide +kernel
theorem leaf0006_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0006 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0006_counts_checked
def leaf0007 : List (Fin data.count) := [(facetIndex 4), (facetIndex 7), (facetIndex 8), (facetIndex 18), (facetIndex 40), (facetIndex 48), (facetIndex 53), (facetIndex 60), (facetIndex 65), (facetIndex 74), (facetIndex 75), (facetIndex 86), (facetIndex 91), (facetIndex 92)]
theorem leaf0007_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0007 = true := by
  decide +kernel
theorem leaf0007_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0007 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0007_counts_checked
def leaf0008 : List (Fin data.count) := [(facetIndex 4), (facetIndex 10), (facetIndex 11), (facetIndex 16), (facetIndex 42), (facetIndex 48), (facetIndex 56), (facetIndex 64), (facetIndex 67), (facetIndex 73), (facetIndex 77), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0008_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0008 = true := by
  decide +kernel
theorem leaf0008_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0008 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0008_counts_checked
def leaf0009 : List (Fin data.count) := [(facetIndex 4), (facetIndex 8), (facetIndex 9), (facetIndex 16), (facetIndex 42), (facetIndex 48), (facetIndex 59), (facetIndex 64), (facetIndex 67), (facetIndex 73), (facetIndex 77), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0009_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0009 = true := by
  decide +kernel
theorem leaf0009_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0009 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0009_counts_checked
def leaf0010 : List (Fin data.count) := [(facetIndex 5), (facetIndex 11), (facetIndex 16), (facetIndex 22), (facetIndex 41), (facetIndex 47), (facetIndex 56), (facetIndex 60), (facetIndex 65), (facetIndex 73), (facetIndex 77), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0010_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0010 = true := by
  decide +kernel
theorem leaf0010_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0010 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0010_counts_checked
def leaf0011 : List (Fin data.count) := [(facetIndex 5), (facetIndex 16), (facetIndex 21), (facetIndex 22), (facetIndex 41), (facetIndex 47), (facetIndex 53), (facetIndex 55), (facetIndex 60), (facetIndex 65), (facetIndex 73), (facetIndex 77), (facetIndex 85), (facetIndex 87)]
theorem leaf0011_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0011 = true := by
  decide +kernel
theorem leaf0011_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0011 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0011_counts_checked
def leaf0012 : List (Fin data.count) := [(facetIndex 5), (facetIndex 6), (facetIndex 11), (facetIndex 16), (facetIndex 41), (facetIndex 50), (facetIndex 56), (facetIndex 60), (facetIndex 64), (facetIndex 73), (facetIndex 77), (facetIndex 86), (facetIndex 88), (facetIndex 92)]
theorem leaf0012_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0012 = true := by
  decide +kernel
theorem leaf0012_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0012 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0012_counts_checked
def leaf0013 : List (Fin data.count) := [(facetIndex 5), (facetIndex 11), (facetIndex 14), (facetIndex 16), (facetIndex 41), (facetIndex 47), (facetIndex 56), (facetIndex 60), (facetIndex 64), (facetIndex 73), (facetIndex 77), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0013_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0013 = true := by
  decide +kernel
theorem leaf0013_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0013 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0013_counts_checked
def leaf0014 : List (Fin data.count) := [(facetIndex 7), (facetIndex 9), (facetIndex 11), (facetIndex 22), (facetIndex 41), (facetIndex 48), (facetIndex 55), (facetIndex 60), (facetIndex 65), (facetIndex 70), (facetIndex 73), (facetIndex 75), (facetIndex 86), (facetIndex 92)]
theorem leaf0014_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0014 = true := by
  decide +kernel
theorem leaf0014_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0014 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0014_counts_checked
def leaf0015 : List (Fin data.count) := [(facetIndex 8), (facetIndex 9), (facetIndex 11), (facetIndex 16), (facetIndex 41), (facetIndex 48), (facetIndex 50), (facetIndex 60), (facetIndex 64), (facetIndex 73), (facetIndex 77), (facetIndex 86), (facetIndex 88), (facetIndex 92)]
theorem leaf0015_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0015 = true := by
  decide +kernel
theorem leaf0015_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0015 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0015_counts_checked
def leaf0016 : List (Fin data.count) := [(facetIndex 7), (facetIndex 9), (facetIndex 13), (facetIndex 22), (facetIndex 41), (facetIndex 48), (facetIndex 55), (facetIndex 59), (facetIndex 65), (facetIndex 70), (facetIndex 73), (facetIndex 75), (facetIndex 86), (facetIndex 92)]
theorem leaf0016_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0016 = true := by
  decide +kernel
theorem leaf0016_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0016 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0016_counts_checked
def leaf0017 : List (Fin data.count) := [(facetIndex 8), (facetIndex 9), (facetIndex 13), (facetIndex 16), (facetIndex 41), (facetIndex 48), (facetIndex 50), (facetIndex 59), (facetIndex 64), (facetIndex 73), (facetIndex 77), (facetIndex 86), (facetIndex 88), (facetIndex 92)]
theorem leaf0017_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0017 = true := by
  decide +kernel
theorem leaf0017_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0017 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0017_counts_checked
def leaf0018 : List (Fin data.count) := [(facetIndex 7), (facetIndex 8), (facetIndex 9), (facetIndex 16), (facetIndex 41), (facetIndex 48), (facetIndex 59), (facetIndex 64), (facetIndex 67), (facetIndex 73), (facetIndex 77), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0018_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0018 = true := by
  decide +kernel
theorem leaf0018_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0018 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0018_counts_checked
def leaf0019 : List (Fin data.count) := [(facetIndex 6), (facetIndex 7), (facetIndex 11), (facetIndex 18), (facetIndex 36), (facetIndex 40), (facetIndex 56), (facetIndex 60), (facetIndex 65), (facetIndex 74), (facetIndex 75), (facetIndex 86), (facetIndex 91), (facetIndex 92)]
theorem leaf0019_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0019 = true := by
  decide +kernel
theorem leaf0019_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0019 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0019_counts_checked
def leaf0020 : List (Fin data.count) := [(facetIndex 11), (facetIndex 17), (facetIndex 18), (facetIndex 21), (facetIndex 36), (facetIndex 40), (facetIndex 47), (facetIndex 56), (facetIndex 60), (facetIndex 65), (facetIndex 74), (facetIndex 85), (facetIndex 87), (facetIndex 91)]
theorem leaf0020_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0020 = true := by
  decide +kernel
theorem leaf0020_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0020 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0020_counts_checked
def leaf0021 : List (Fin data.count) := [(facetIndex 11), (facetIndex 15), (facetIndex 16), (facetIndex 21), (facetIndex 36), (facetIndex 40), (facetIndex 47), (facetIndex 56), (facetIndex 60), (facetIndex 65), (facetIndex 77), (facetIndex 85), (facetIndex 87), (facetIndex 91)]
theorem leaf0021_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0021 = true := by
  decide +kernel
theorem leaf0021_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0021 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0021_counts_checked
def leaf0022 : List (Fin data.count) := [(facetIndex 10), (facetIndex 11), (facetIndex 13), (facetIndex 16), (facetIndex 41), (facetIndex 48), (facetIndex 50), (facetIndex 56), (facetIndex 64), (facetIndex 73), (facetIndex 77), (facetIndex 86), (facetIndex 88), (facetIndex 92)]
theorem leaf0022_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0022 = true := by
  decide +kernel
theorem leaf0022_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0022 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0022_counts_checked
def leaf0023 : List (Fin data.count) := [(facetIndex 7), (facetIndex 10), (facetIndex 11), (facetIndex 16), (facetIndex 41), (facetIndex 48), (facetIndex 56), (facetIndex 64), (facetIndex 67), (facetIndex 73), (facetIndex 77), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0023_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0023 = true := by
  decide +kernel
theorem leaf0023_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0023 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0023_counts_checked
def leaf0024 : List (Fin data.count) := [(facetIndex 7), (facetIndex 11), (facetIndex 14), (facetIndex 16), (facetIndex 41), (facetIndex 48), (facetIndex 56), (facetIndex 60), (facetIndex 64), (facetIndex 73), (facetIndex 77), (facetIndex 83), (facetIndex 84), (facetIndex 88)]
theorem leaf0024_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0024 = true := by
  decide +kernel
theorem leaf0024_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0024 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0024_counts_checked
def leaf0025 : List (Fin data.count) := [(facetIndex 7), (facetIndex 11), (facetIndex 14), (facetIndex 16), (facetIndex 41), (facetIndex 48), (facetIndex 56), (facetIndex 60), (facetIndex 64), (facetIndex 73), (facetIndex 77), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0025_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0025 = true := by
  decide +kernel
theorem leaf0025_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0025 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0025_counts_checked
def leaf0026 : List (Fin data.count) := [(facetIndex 7), (facetIndex 11), (facetIndex 14), (facetIndex 16), (facetIndex 41), (facetIndex 48), (facetIndex 56), (facetIndex 60), (facetIndex 64), (facetIndex 73), (facetIndex 77), (facetIndex 86), (facetIndex 88), (facetIndex 92)]
theorem leaf0026_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0026 = true := by
  decide +kernel
theorem leaf0026_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0026 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0026_counts_checked
def leaf0027 : List (Fin data.count) := [(facetIndex 7), (facetIndex 11), (facetIndex 14), (facetIndex 20), (facetIndex 41), (facetIndex 48), (facetIndex 56), (facetIndex 60), (facetIndex 64), (facetIndex 70), (facetIndex 73), (facetIndex 75), (facetIndex 86), (facetIndex 92)]
theorem leaf0027_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0027 = true := by
  decide +kernel
theorem leaf0027_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0027 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0027_counts_checked
def leaf0028 : List (Fin data.count) := [(facetIndex 7), (facetIndex 11), (facetIndex 16), (facetIndex 22), (facetIndex 41), (facetIndex 48), (facetIndex 56), (facetIndex 60), (facetIndex 65), (facetIndex 73), (facetIndex 77), (facetIndex 83), (facetIndex 84), (facetIndex 88)]
theorem leaf0028_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0028 = true := by
  decide +kernel
theorem leaf0028_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0028 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0028_counts_checked
def leaf0029 : List (Fin data.count) := [(facetIndex 7), (facetIndex 11), (facetIndex 16), (facetIndex 22), (facetIndex 41), (facetIndex 48), (facetIndex 56), (facetIndex 60), (facetIndex 65), (facetIndex 73), (facetIndex 77), (facetIndex 85), (facetIndex 87), (facetIndex 88)]
theorem leaf0029_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0029 = true := by
  decide +kernel
theorem leaf0029_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0029 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0029_counts_checked
def leaf0030 : List (Fin data.count) := [(facetIndex 7), (facetIndex 11), (facetIndex 18), (facetIndex 19), (facetIndex 41), (facetIndex 48), (facetIndex 56), (facetIndex 60), (facetIndex 65), (facetIndex 74), (facetIndex 75), (facetIndex 86), (facetIndex 91), (facetIndex 92)]
theorem leaf0030_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0030 = true := by
  decide +kernel
theorem leaf0030_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0030 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0030_counts_checked
def leaf0031 : List (Fin data.count) := [(facetIndex 7), (facetIndex 11), (facetIndex 20), (facetIndex 22), (facetIndex 41), (facetIndex 48), (facetIndex 56), (facetIndex 60), (facetIndex 65), (facetIndex 70), (facetIndex 73), (facetIndex 75), (facetIndex 86), (facetIndex 92)]
theorem leaf0031_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0031 = true := by
  decide +kernel
theorem leaf0031_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0031 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0031_counts_checked
def leaf0032 : List (Fin data.count) := [(facetIndex 7), (facetIndex 11), (facetIndex 15), (facetIndex 19), (facetIndex 41), (facetIndex 48), (facetIndex 56), (facetIndex 60), (facetIndex 65), (facetIndex 70), (facetIndex 75), (facetIndex 86), (facetIndex 91), (facetIndex 92)]
theorem leaf0032_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0032 = true := by
  decide +kernel
theorem leaf0032_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0032 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0032_counts_checked
def leaf0033 : List (Fin data.count) := [(facetIndex 7), (facetIndex 11), (facetIndex 16), (facetIndex 22), (facetIndex 41), (facetIndex 48), (facetIndex 56), (facetIndex 60), (facetIndex 65), (facetIndex 73), (facetIndex 77), (facetIndex 86), (facetIndex 88), (facetIndex 92)]
theorem leaf0033_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0033 = true := by
  decide +kernel
theorem leaf0033_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0033 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0033_counts_checked
def leaf0034 : List (Fin data.count) := [(facetIndex 7), (facetIndex 11), (facetIndex 17), (facetIndex 18), (facetIndex 41), (facetIndex 48), (facetIndex 56), (facetIndex 60), (facetIndex 65), (facetIndex 74), (facetIndex 81), (facetIndex 86), (facetIndex 88), (facetIndex 92)]
theorem leaf0034_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0034 = true := by
  decide +kernel
theorem leaf0034_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0034 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0034_counts_checked
def leaf0035 : List (Fin data.count) := [(facetIndex 7), (facetIndex 11), (facetIndex 15), (facetIndex 16), (facetIndex 41), (facetIndex 48), (facetIndex 56), (facetIndex 60), (facetIndex 65), (facetIndex 77), (facetIndex 81), (facetIndex 86), (facetIndex 88), (facetIndex 92)]
theorem leaf0035_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0035 = true := by
  decide +kernel
theorem leaf0035_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0035 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0035_counts_checked
def leaf0036 : List (Fin data.count) := [(facetIndex 11), (facetIndex 12), (facetIndex 16), (facetIndex 22), (facetIndex 41), (facetIndex 48), (facetIndex 50), (facetIndex 56), (facetIndex 60), (facetIndex 73), (facetIndex 77), (facetIndex 86), (facetIndex 88), (facetIndex 92)]
theorem leaf0036_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0036 = true := by
  decide +kernel
theorem leaf0036_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0036 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0036_counts_checked
def leaf0037 : List (Fin data.count) := [(facetIndex 11), (facetIndex 16), (facetIndex 20), (facetIndex 21), (facetIndex 41), (facetIndex 48), (facetIndex 50), (facetIndex 56), (facetIndex 60), (facetIndex 64), (facetIndex 73), (facetIndex 77), (facetIndex 86), (facetIndex 92)]
theorem leaf0037_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0037 = true := by
  decide +kernel
theorem leaf0037_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0037 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0037_counts_checked
def leaf0038 : List (Fin data.count) := [(facetIndex 11), (facetIndex 17), (facetIndex 20), (facetIndex 21), (facetIndex 41), (facetIndex 48), (facetIndex 50), (facetIndex 56), (facetIndex 60), (facetIndex 64), (facetIndex 70), (facetIndex 73), (facetIndex 86), (facetIndex 92)]
theorem leaf0038_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0038 = true := by
  decide +kernel
theorem leaf0038_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0038 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0038_counts_checked
def leaf0039 : List (Fin data.count) := [(facetIndex 11), (facetIndex 17), (facetIndex 18), (facetIndex 19), (facetIndex 41), (facetIndex 48), (facetIndex 50), (facetIndex 56), (facetIndex 60), (facetIndex 64), (facetIndex 74), (facetIndex 86), (facetIndex 88), (facetIndex 92)]
theorem leaf0039_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0039 = true := by
  decide +kernel
theorem leaf0039_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0039 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0039_counts_checked
def leaf0040 : List (Fin data.count) := [(facetIndex 11), (facetIndex 15), (facetIndex 16), (facetIndex 19), (facetIndex 41), (facetIndex 48), (facetIndex 50), (facetIndex 56), (facetIndex 60), (facetIndex 64), (facetIndex 77), (facetIndex 86), (facetIndex 88), (facetIndex 92)]
theorem leaf0040_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0040 = true := by
  decide +kernel
theorem leaf0040_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0040 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0040_counts_checked
def leaf0041 : List (Fin data.count) := [(facetIndex 11), (facetIndex 16), (facetIndex 17), (facetIndex 18), (facetIndex 41), (facetIndex 48), (facetIndex 50), (facetIndex 56), (facetIndex 60), (facetIndex 64), (facetIndex 73), (facetIndex 86), (facetIndex 88), (facetIndex 92)]
theorem leaf0041_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0041 = true := by
  decide +kernel
theorem leaf0041_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0041 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0041_counts_checked
def leaf0042 : List (Fin data.count) := [(facetIndex 7), (facetIndex 17), (facetIndex 18), (facetIndex 21), (facetIndex 41), (facetIndex 48), (facetIndex 53), (facetIndex 55), (facetIndex 60), (facetIndex 65), (facetIndex 74), (facetIndex 81), (facetIndex 86), (facetIndex 92)]
theorem leaf0042_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0042 = true := by
  decide +kernel
theorem leaf0042_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0042 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0042_counts_checked
def leaf0043 : List (Fin data.count) := [(facetIndex 7), (facetIndex 15), (facetIndex 16), (facetIndex 21), (facetIndex 41), (facetIndex 48), (facetIndex 53), (facetIndex 55), (facetIndex 60), (facetIndex 65), (facetIndex 77), (facetIndex 81), (facetIndex 86), (facetIndex 92)]
theorem leaf0043_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0043 = true := by
  decide +kernel
theorem leaf0043_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0043 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0043_counts_checked
def leaf0044 : List (Fin data.count) := [(facetIndex 7), (facetIndex 16), (facetIndex 21), (facetIndex 22), (facetIndex 41), (facetIndex 48), (facetIndex 53), (facetIndex 55), (facetIndex 60), (facetIndex 65), (facetIndex 73), (facetIndex 77), (facetIndex 83), (facetIndex 84)]
theorem leaf0044_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0044 = true := by
  decide +kernel
theorem leaf0044_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0044 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0044_counts_checked
def leaf0045 : List (Fin data.count) := [(facetIndex 7), (facetIndex 16), (facetIndex 21), (facetIndex 22), (facetIndex 41), (facetIndex 48), (facetIndex 53), (facetIndex 55), (facetIndex 60), (facetIndex 65), (facetIndex 73), (facetIndex 77), (facetIndex 85), (facetIndex 87)]
theorem leaf0045_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0045 = true := by
  decide +kernel
theorem leaf0045_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0045 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0045_counts_checked
def leaf0046 : List (Fin data.count) := [(facetIndex 7), (facetIndex 16), (facetIndex 21), (facetIndex 22), (facetIndex 41), (facetIndex 48), (facetIndex 53), (facetIndex 55), (facetIndex 60), (facetIndex 65), (facetIndex 73), (facetIndex 77), (facetIndex 86), (facetIndex 92)]
theorem leaf0046_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0046 = true := by
  decide +kernel
theorem leaf0046_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0046 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0046_counts_checked
def leaf0047 : List (Fin data.count) := [(facetIndex 7), (facetIndex 8), (facetIndex 18), (facetIndex 19), (facetIndex 41), (facetIndex 48), (facetIndex 53), (facetIndex 60), (facetIndex 65), (facetIndex 74), (facetIndex 75), (facetIndex 86), (facetIndex 91), (facetIndex 92)]
theorem leaf0047_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0047 = true := by
  decide +kernel
theorem leaf0047_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0047 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0047_counts_checked
def leaf0048 : List (Fin data.count) := [(facetIndex 7), (facetIndex 18), (facetIndex 19), (facetIndex 22), (facetIndex 41), (facetIndex 48), (facetIndex 53), (facetIndex 55), (facetIndex 60), (facetIndex 65), (facetIndex 74), (facetIndex 75), (facetIndex 86), (facetIndex 92)]
theorem leaf0048_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0048 = true := by
  decide +kernel
theorem leaf0048_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0048 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0048_counts_checked
def leaf0049 : List (Fin data.count) := [(facetIndex 7), (facetIndex 16), (facetIndex 18), (facetIndex 22), (facetIndex 41), (facetIndex 48), (facetIndex 53), (facetIndex 55), (facetIndex 60), (facetIndex 65), (facetIndex 73), (facetIndex 75), (facetIndex 86), (facetIndex 92)]
theorem leaf0049_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0049 = true := by
  decide +kernel
theorem leaf0049_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0049 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0049_counts_checked
def leaf0050 : List (Fin data.count) := [(facetIndex 12), (facetIndex 16), (facetIndex 21), (facetIndex 22), (facetIndex 41), (facetIndex 48), (facetIndex 50), (facetIndex 53), (facetIndex 55), (facetIndex 60), (facetIndex 73), (facetIndex 77), (facetIndex 86), (facetIndex 92)]
theorem leaf0050_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0050 = true := by
  decide +kernel
theorem leaf0050_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0050 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0050_counts_checked
def leaf0051 : List (Fin data.count) := [(facetIndex 8), (facetIndex 16), (facetIndex 20), (facetIndex 21), (facetIndex 41), (facetIndex 48), (facetIndex 50), (facetIndex 53), (facetIndex 60), (facetIndex 64), (facetIndex 73), (facetIndex 77), (facetIndex 86), (facetIndex 92)]
theorem leaf0051_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0051 = true := by
  decide +kernel
theorem leaf0051_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0051 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0051_counts_checked
def leavesTable : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 26
 (.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (leaf0000))
 (.branch 2
 (.leaf (leaf0001))
 (.leaf (leaf0002))))
 (.branch 4
 (.leaf (leaf0003))
 (.branch 5
 (.leaf (leaf0004))
 (.leaf (leaf0005)))))
 (.branch 9
 (.branch 7
 (.leaf (leaf0006))
 (.branch 8
 (.leaf (leaf0007))
 (.leaf (leaf0008))))
 (.branch 11
 (.branch 10
 (.leaf (leaf0009))
 (.leaf (leaf0010)))
 (.branch 12
 (.leaf (leaf0011))
 (.leaf (leaf0012))))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf (leaf0013))
 (.branch 15
 (.leaf (leaf0014))
 (.leaf (leaf0015))))
 (.branch 17
 (.leaf (leaf0016))
 (.branch 18
 (.leaf (leaf0017))
 (.leaf (leaf0018)))))
 (.branch 22
 (.branch 20
 (.leaf (leaf0019))
 (.branch 21
 (.leaf (leaf0020))
 (.leaf (leaf0021))))
 (.branch 24
 (.branch 23
 (.leaf (leaf0022))
 (.leaf (leaf0023)))
 (.branch 25
 (.leaf (leaf0024))
 (.leaf (leaf0025)))))))
 (.branch 39
 (.branch 32
 (.branch 29
 (.branch 27
 (.leaf (leaf0026))
 (.branch 28
 (.leaf (leaf0027))
 (.leaf (leaf0028))))
 (.branch 30
 (.leaf (leaf0029))
 (.branch 31
 (.leaf (leaf0030))
 (.leaf (leaf0031)))))
 (.branch 35
 (.branch 33
 (.leaf (leaf0032))
 (.branch 34
 (.leaf (leaf0033))
 (.leaf (leaf0034))))
 (.branch 37
 (.branch 36
 (.leaf (leaf0035))
 (.leaf (leaf0036)))
 (.branch 38
 (.leaf (leaf0037))
 (.leaf (leaf0038))))))
 (.branch 45
 (.branch 42
 (.branch 40
 (.leaf (leaf0039))
 (.branch 41
 (.leaf (leaf0040))
 (.leaf (leaf0041))))
 (.branch 43
 (.leaf (leaf0042))
 (.branch 44
 (.leaf (leaf0043))
 (.leaf (leaf0044)))))
 (.branch 48
 (.branch 46
 (.leaf (leaf0045))
 (.branch 47
 (.leaf (leaf0046))
 (.leaf (leaf0047))))
 (.branch 50
 (.branch 49
 (.leaf (leaf0048))
 (.leaf (leaf0049)))
 (.branch 51
 (.leaf (leaf0050))
 (.leaf (leaf0051))))))))
def leaves (j : Fin leafCount) : List (Fin data.count) := leavesTable.get j.val

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00142.record000" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"group\",\"kind\":1,\"index\":3},{\"tag\":\"group\",\"kind\":1,\"index\":4},{\"tag\":\"group\",\"kind\":1,\"index\":6},{\"tag\":\"group\",\"kind\":1,\"index\":7},{\"tag\":\"group\",\"kind\":1,\"index\":8},{\"tag\":\"group\",\"kind\":1,\"index\":9},{\"tag\":\"group\",\"kind\":1,\"index\":11},{\"tag\":\"group\",\"kind\":1,\"index\":12},{\"tag\":\"group\",\"kind\":1,\"index\":13},{\"tag\":\"group\",\"kind\":1,\"index\":14},{\"tag\":\"group\",\"kind\":1,\"index\":16},{\"tag\":\"group\",\"kind\":1,\"index\":17},{\"tag\":\"group\",\"kind\":1,\"index\":18},{\"tag\":\"group\",\"kind\":1,\"index\":19},{\"tag\":\"group\",\"kind\":1,\"index\":20},{\"tag\":\"group\",\"kind\":1,\"index\":21},{\"tag\":\"group\",\"kind\":1,\"index\":22},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0007\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0007\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0005\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0005\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0013\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0010\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0018\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0016\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0016\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0011\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0011\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0002\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0002\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0002\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0025\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0025\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0021\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0021\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0030\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0028\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0028\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0022\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0022\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0022\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0036\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0033\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0033\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0041\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0039\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0039\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0034\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0034\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0034\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":4,\"list_name\":\"grouped1_0034\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":4,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":5,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":5,\"list_name\":\"groupKind1\"},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0044\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0044\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0051\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0051\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0049\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0049\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0049\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0045\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0045\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0045\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0054\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0054\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0060\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0060\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0058\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0058\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0058\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0055\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0055\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0055\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":9,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0063\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0063\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0068\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0064\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0064\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0064\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0071\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0077\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0077\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0075\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0075\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0072\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0072\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0072\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00142.record000" 206

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00142.record000" "{\"ridges\":[[0,7],[0,13],[0,14],[1,19],[1,21],[2,7],[2,259],[4,11],[4,259],[4,265],[4,266],[5,19],[5,273],[5,274],[6,19],[7,578],[8,44],[9,265],[9,268],[10,21],[11,21],[11,273],[11,276],[13,560],[14,608],[16,14],[16,266],[16,268],[17,146],[18,274],[18,276],[19,138],[20,164],[21,148],[21,176],[24,11],[24,14],[25,7],[25,13],[26,7],[27,7],[28,19],[28,21],[28,146],[32,7],[32,550],[33,197],[35,153],[36,19],[36,265],[36,266],[36,273],[36,274],[37,97],[39,554],[40,138],[41,74],[41,259],[41,265],[41,266],[42,11],[42,73],[42,515],[42,577],[42,578],[45,49],[45,545],[45,560],[46,209],[47,19],[47,530],[47,577],[47,578],[48,259],[48,273],[48,274],[48,515],[48,530],[50,545],[50,578],[50,608],[53,13],[53,21],[53,268],[53,273],[53,276],[55,13],[55,41],[55,140],[55,164],[55,168],[56,37],[56,41],[56,261],[56,265],[56,268],[58,176],[59,37],[59,49],[59,261],[60,21],[60,37],[60,52],[60,529],[60,560],[62,41],[62,153],[64,41],[64,73],[64,97],[64,200],[64,224],[65,41],[65,104],[65,577],[65,608],[66,209],[67,560],[67,608],[69,146],[70,14],[70,266],[70,274],[70,276],[73,14],[73,134],[73,140],[73,200],[74,134],[74,138],[74,262],[74,266],[75,22],[75,146],[75,176],[76,530],[77,134],[77,146],[77,262],[77,274],[77,276],[78,224],[79,58],[80,146],[80,274],[81,138],[81,224],[82,554],[84,114],[84,578],[84,608],[86,146],[86,530],[86,578],[86,720],[87,578],[87,674],[88,44],[88,52],[88,140],[88,168],[88,176],[89,312],[90,276],[90,408],[92,176],[92,224],[92,608],[92,720]],\"owners\":[[0,7,[1,2,27,28,29,30,31,32,33],[24,25,26]],[2,7,[0,1,24,25,26,27,28,29,30,31,32,33],[]],[25,7,[1,2,27,28,29,31,32],[0,24,26,30,33]],[26,7,[1,2,27,29,30,32],[0,24,25,28,31,33]],[27,7,[0,2,25,26,33],[1,24,28,29,30,31,32]],[32,7,[0,1,2,25,26,28,33],[24,27,29,30,31]],[4,11,[0,3,23,24,26,34,35,37,38,39,40,42],[36]],[42,11,[0,4,23,24,26,34,35,36,38],[3,37,39,40]],[73,14,[0,16,23,24,68,70],[15,25,69,71,72]],[47,19,[1,5,23,27,28,34,35,36,44],[6,43,45,46]],[60,21,[1,11,23,28,52,53],[10,29,51,58]],[75,22,[1,18,23,29,70],[17,27,68,69,76]],[56,261,[2,11],[9,59]],[59,261,[2,9],[11,56]],[74,262,[2,18],[16,77]],[77,262,[2,16],[18,74]],[42,73,[12,54,57,64],[3,25,40,41,65]],[64,73,[3,25,41,42],[12,40,54,57,65]],[41,74,[19,71,73,81,82],[3,25,37,42]],[4,265,[9,53,56,63],[36,41]],[9,265,[4,36,41,63],[53,56]],[36,265,[9,56],[4,41,53,63]],[41,265,[9,53,56,63],[4,36]],[56,265,[4,36,41],[9,53,63]],[4,266,[16,70,74,80],[36,41]],[16,266,[4,36,41,80],[70,74]],[36,266,[16,74],[4,41,70,80]],[41,266,[16,70,74,80],[4,36]],[70,266,[4,41],[16,36,74,80]],[74,266,[4,36,41],[16,70,80]],[5,273,[11,53,59,63],[36,48]],[11,273,[5,36,48,63],[53,59]],[36,273,[11,59],[5,48,53,63]],[48,273,[11,53,59,63],[5,36]],[53,273,[5,48],[11,36,59,63]],[5,274,[18,70,77,80],[36,48]],[18,274,[5,36,48,80],[70,77]],[36,274,[18,77],[5,48,70,80]],[48,274,[18,70,77,80],[5,36]],[70,274,[5,48],[18,36,77,80]],[77,274,[5,36,48],[18,70,80]],[80,274,[5,18,48],[36,70,77]],[42,515,[6,29,32,45,48],[7,39,50]],[48,515,[7,32,39,42,50],[6,29,45]],[60,529,[6,47,48],[13,29,67]],[47,530,[76,85],[6,29,45,48,84,86]],[86,530,[6,29,45,48,76],[47,84,85]],[42,577,[14,67],[7,47,65]],[47,577,[14,65],[7,42,67]],[65,577,[7,47],[14,42,67]],[7,578,[82,84,86,87],[42,47,50]],[42,578,[84,86,87],[7,47,50,82]],[47,578,[82,87],[7,42,50,84,86]],[50,578,[86],[7,42,47,82,84,87]],[84,578,[7,42],[47,50,82,86,87]],[86,578,[7,42,50,82],[47,84,87]],[87,578,[7,42,47],[50,82,84,86]],[56,37,[10,27,30,31,32,58,60,61],[8,24,54,55,59]],[59,37,[8,24,30,31,32,54,55,61],[10,27,56,58,60]],[60,37,[8,24,30,31,54,55,56,61],[10,27,32,58,59]],[55,41,[12,34,37,39,63,65],[8,24,38,51,56,62,64]],[56,41,[12,34,37,38,39,62,64,65],[8,24,51,55,63]],[64,41,[8,24,34,39,51,56,63],[12,37,38,55,62,65]],[65,41,[8,24,34,38,51,55,56,62,63],[12,37,39,64]],[8,44,[20,68,71,72,88,89,91],[24,51,54,56]],[88,44,[8,24,54,56,71],[20,51,68,72,89,91]],[9,268,[16,70,74,89,90],[53,56]],[16,268,[9,53,56,89,90],[70,74]],[53,268,[16,74],[9,56,70,89,90]],[56,268,[16,70,74,90],[9,53,89]],[45,49,[10,51,58,59,62,63,66],[13,27,34,43,44,67]],[59,49,[13,34,43,44,45,62,66,67],[10,27,51,58,63]],[60,52,[21,68,75,88,89],[10,27,51,59,76]],[88,52,[10,27,59,60,76],[21,51,68,75,89]],[11,276,[18,70,77,89,90],[53,59]],[18,276,[11,53,59,89,90],[70,77]],[53,276,[18,77],[11,59,70,89,90]],[70,276,[11,59],[18,53,77,89,90]],[77,276,[11,53,59,89],[18,70,90]],[90,276,[11,18,59],[53,70,77,89]],[37,97,[14,61,66,67],[12,30,43,49,50,54,64]],[64,97,[14,30,43,50,67],[12,37,49,54,61,66]],[65,104,[22,71,81,91],[12,37,54,82]],[45,545,[14,65],[13,32,39,50,60]],[50,545,[13,60],[14,32,39,45,65]],[13,560,[76,84,85,92],[45,60,67]],[45,560,[92],[13,60,67,76,84,85]],[60,560,[84,85,92],[13,45,67,76]],[67,560,[76,85],[13,45,60,84,92]],[14,608,[82,84,87,92],[50,65,67]],[50,608,[92],[14,65,67,82,84,87]],[65,608,[84,87,92],[14,50,67,82]],[67,608,[82,87],[14,50,65,84,92]],[84,608,[14,65],[50,67,82,87,92]],[92,608,[14,50,65,82],[67,84,87]],[73,134,[17,28,31,75,77],[15,26,33,72,74,78]],[74,134,[17,28,31,33,75,78],[15,26,72,73,77]],[77,134,[15,26,31,33,72,73,78],[17,28,74,75]],[19,138,[15,26,35,38,69,72,74,79,80],[40,81]],[40,138,[15,69,72,74,79,80],[19,26,35,38,81]],[74,138,[19,35,38,40,79,81],[15,26,69,72,80]],[81,138,[15,26,35,69,74,80],[19,38,40,72,79]],[55,140,[15,69,73,74,90],[20,26,52,57,88,91]],[73,140,[20,52,55,88,90],[15,26,57,69,74,91]],[88,140,[15,26,57,73,74],[20,52,55,69,90,91]],[17,146,[35,44,46,79,80,83,85,86],[28,69,75,77]],[28,146,[79,80,83,85,86],[17,35,44,46,69,75,77]],[69,146,[44,46,83,85,86],[17,28,35,75,77,79,80]],[75,146,[35,46,80,86],[17,28,44,69,77,79,83,85]],[77,146,[35,44,46,79,83,85,86],[17,28,69,75,80]],[21,148,[17,28,52,69,77,90],[58,88]],[64,200,[19,73],[22,40,57,91]],[73,200,[22,64],[19,40,57,91]],[20,164,[21,31,58,61,75,78],[55,72,91]],[55,164,[21,75,78],[20,31,58,61,72,91]],[55,168,[22,79,81],[20,38,62,64,72,88]],[88,168,[22,38,64,81],[20,55,62,72,79]],[21,176,[44,62,66,79,83,85,92],[58,75,88]],[58,176,[79,83,85,92],[21,44,62,66,75,88]],[75,176,[62,66,92],[21,44,58,79,83,85,88]],[88,176,[44,66,83,85,92],[21,58,62,75,79]],[92,176,[21,44,58,62,75,79,88],[66,83,85]],[81,224,[61,66,92],[22,49,64,78,83,87,91]],[32,550,[76],[]],[33,197,[57,61],[]],[79,58,[34,68],[]],[35,153,[52,62],[]],[62,153,[35,52],[]],[39,554,[82],[]],[82,554,[39],[]],[84,114,[43,83],[]],[46,209,[66],[]],[66,209,[46],[]],[89,312,[63],[]],[90,408,[80],[]],[87,674,[85],[]],[86,720,[92],[]],[92,720,[86],[]]],\"edges\":[[28,[4,9,16,36,41,53,56,63,70,74,80,89,90]],[32,[17,21,28,35,44,46,52,58,62,66,69,75,77,79,80,83,85,86,88,90,92]],[33,[5,11,18,36,48,53,59,63,70,77,80,89,90]],[38,[13,14,32,39,45,50,60,65,67,76,82,84,85,87,92]],[41,[7,14,42,47,50,65,67,82,84,86,87,92]]],\"groupings\":[1,2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00142.record000" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00142.record000\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-25,-10],[-26,-5],[-26,-25],[-27,-17],[-28,-12],[-29,-19],[-30,-6],[-30,-28],[-37,-3],[-37,-24],[-37,-26],[-37,-30],[-37,-35],[-37,-36],[-41,-29],[-42,-1],[-42,-24],[-42,-25],[-42,-27],[-42,-37],[-42,-38],[-42,-41],[-43,-26],[-43,-42],[-45,-33],[-45,-40],[-46,-25],[-46,-28],[-48,-33],[-48,-43],[-49,-2],[-49,-24],[-49,-28],[-49,-29],[-49,-30],[-49,-35],[-49,-36],[-49,-37],[-49,-44],[-49,-45],[-49,-46],[-49,-47],[-49,-48],[-50,-25],[-50,-28],[-50,-33],[-50,-38],[-50,-43],[-50,-46],[-50,-48],[-51,-37],[-52,-37],[-53,-3],[-53,-24],[-53,-25],[-53,-37],[-53,-51],[-54,-51],[-55,-25],[-55,-41],[-55,-51],[-55,-54],[-56,-1],[-56,-24],[-56,-25],[-56,-26],[-56,-27],[-56,-51],[-56,-52],[-56,-53],[-56,-54],[-56,-55],[-57,-56],[-58,-27],[-58,-29],[-58,-41],[-58,-55],[-59,-24],[-59,-28],[-59,-29],[-59,-30],[-59,-53],[-59,-56],[-59,-58],[-60,-30],[-60,-44],[-60,-46],[-60,-51],[-60,-58],[-60,-59],[-63,-37],[-63,-56],[-63,-59],[-63,-60],[-64,-27],[-64,-29],[-64,-32],[-64,-34],[-64,-38],[-64,-41],[-64,-45],[-64,-52],[-64,-54],[-64,-55],[-64,-57],[-64,-58],[-64,-61],[-64,-62],[-65,-31],[-65,-38],[-65,-43],[-65,-44],[-65,-50],[-65,-54],[-65,-61],[-65,-64],[-66,-65],[-67,-48],[-67,-60],[-68,-37],[-69,-37],[-69,-53],[-70,-3],[-70,-27],[-70,-29],[-70,-37],[-70,-51],[-70,-53],[-71,-64],[-72,-46],[-72,-50],[-72,-55],[-73,-20],[-73,-26],[-73,-31],[-73,-41],[-73,-69],[-73,-72],[-74,-25],[-74,-26],[-74,-27],[-74,-70],[-74,-72],[-74,-73],[-75,-28],[-75,-29],[-75,-38],[-75,-46],[-75,-50],[-75,-58],[-75,-69],[-75,-72],[-76,-25],[-76,-45],[-76,-75],[-77,-2],[-77,-28],[-77,-29],[-77,-30],[-77,-70],[-77,-74],[-77,-75],[-77,-76],[-78,-73],[-79,-73],[-80,-37],[-80,-73],[-81,-38],[-81,-41],[-81,-46],[-81,-50],[-81,-64],[-81,-73],[-81,-75],[-82,-45],[-84,-25],[-84,-28],[-84,-35],[-84,-38],[-84,-39],[-84,-48],[-84,-68],[-84,-72],[-84,-75],[-84,-78],[-84,-79],[-84,-81],[-85,-25],[-85,-72],[-85,-75],[-87,-25],[-87,-28],[-87,-31],[-87,-32],[-87,-33],[-87,-35],[-87,-38],[-87,-39],[-87,-44],[-87,-45],[-87,-46],[-87,-50],[-87,-68],[-87,-72],[-87,-75],[-87,-76],[-87,-78],[-87,-79],[-87,-81],[-88,-24],[-88,-37],[-88,-51],[-88,-53],[-88,-55],[-88,-58],[-88,-69],[-88,-70],[-88,-72],[-88,-75],[-89,-37],[-89,-56],[-90,-37],[-91,-55],[-91,-64],[-91,-72],[-91,-81],[-91,-88],[-92,-48],[-92,-67],[-92,-87],[-1,2,3,28,29,30,31,32,33,34],[-3,1,2,25,26,27,28,29,30,31,32,33,34],[-26,2,3,28,29,30,32,33],[-27,2,3,28,30,31,33],[-28,1,3,26,27,34],[-33,1,2,3,26,27,29,34],[-5,1,4,24,25,27,35,36,38,39,40,41,43],[-43,1,5,24,25,27,35,36,37,39],[-5,-25,-43],[-1,-53,-55],[-26,-53,-55],[-73,1,17,24,25,68,70],[-1,-70,-73],[-17,-25,-73],[-48,2,6,24,28,29,35,36,37,45],[-2,-37,-48],[-6,-7,-29],[-6,-29,-48],[-7,-29,-37],[-29,-37,-48],[-60,2,12,24,29,52,53],[-2,-12,-60],[-11,-12,-29],[-12,-29,-60],[-29,-53,-60],[-75,2,19,24,30,70],[-3,-5,-49],[-3,-42,-49],[-56,3,12],[-59,3,10],[-74,3,19],[-77,3,17],[-43,13,54,57,64],[-64,4,26,42,43],[-42,20,71,73,81,82],[-5,10,53,56,63],[-10,5,37,42,63],[-37,10,56],[-42,10,53,56,63],[-56,5,37,42],[-5,17,70,74,80],[-17,5,37,42,80],[-37,17,74],[-42,17,70,74,80],[-70,5,42],[-74,5,37,42],[-6,12,53,59,63],[-12,6,37,49,63],[-37,12,59],[-49,12,53,59,63],[-53,6,49],[-6,19,70,77,80],[-19,6,37,49,80],[-37,19,77],[-49,19,70,77,80],[-70,6,49],[-77,6,37,49],[-80,6,19,49],[-43,7,30,33,46,49],[-49,8,33,40,43,50],[-60,7,48,49],[-48,76,85],[-86,7,30,46,49,76],[-49,-76,-86],[-43,15,67],[-48,15,65],[-65,8,48],[-8,82,84,86,87],[-43,84,86,87],[-48,82,87],[-50,86],[-84,8,43],[-86,8,43,50,82],[-87,8,43,48],[-56,11,28,31,32,33,58,60,61],[-59,9,25,31,32,33,54,55,61],[-60,9,25,31,32,54,55,56,61],[-55,13,35,38,40,63,65],[-56,13,35,38,39,40,62,64,65],[-64,9,25,35,40,51,56,63],[-65,9,25,35,39,51,55,56,62,63],[-56,-62,-65],[-9,21,68,71,72,88,89,91],[-88,9,25,54,56,71],[-10,17,70,74,89,90],[-17,10,53,56,89,90],[-53,17,74],[-56,17,70,74,90],[-46,11,51,58,59,62,63,66],[-59,14,35,44,45,46,62,66,67],[-60,22,68,75,88,89],[-88,11,28,59,60,76],[-12,19,70,77,89,90],[-19,12,53,59,89,90],[-53,19,77],[-70,12,59],[-77,12,53,59,89],[-90,12,19,59],[-38,15,61,66,67],[-64,15,31,44,50,67],[-65,23,71,81,91],[-46,15,65],[-50,14,60],[-14,76,84,85,92],[-46,92],[-60,84,85,92],[-67,76,85],[-15,82,84,87,92],[-50,92],[-65,84,87,92],[-67,82,87],[-84,15,65],[-92,15,50,65,82],[-73,18,29,32,75,77],[-74,18,29,32,34,75,78],[-77,16,27,32,34,72,73,78],[-20,16,27,36,39,69,72,74,79,80],[-41,16,69,72,74,79,80],[-74,20,36,39,41,79,81],[-81,16,27,36,69,74,80],[-55,16,69,73,74,90],[-73,21,52,55,88,90],[-88,16,27,57,73,74],[-18,36,45,47,79,80,83,85,86],[-29,79,80,83,85,86],[-69,45,47,83,85,86],[-75,36,47,80,86],[-77,36,45,47,79,83,85,86],[-29,-80,-86],[-22,18,29,52,69,77,90],[-64,20,73],[-73,23,64],[-21,22,32,58,61,75,78],[-55,22,75,78],[-55,23,79,81],[-88,23,39,64,81],[-22,45,62,66,79,83,85,92],[-58,79,83,85,92],[-75,62,66,92],[-88,45,66,83,85,92],[-92,22,45,58,62,75,79,88],[-81,61,66,92],[-64,-78,-92],[-33,76],[-34,57,61],[-79,35,68],[-36,52,62],[-62,36,52],[-40,82],[-82,40],[-84,44,83],[-47,66],[-66,47],[-89,63],[-90,80],[-87,85],[-86,92],[-92,86],[-4,93],[-5,94],[-7,95],[-8,96],[-9,97],[-10,98],[-12,99],[-13,100],[-14,101],[-15,102],[-17,103],[-18,104],[-19,105],[-20,106],[-21,107],[-22,108],[-23,109],[-94,110],[-93,-94,111],[-110,112],[-111,113],[-112,114],[-113,115],[-96,116],[-95,116],[-116,117],[-98,118],[-118,119],[-97,119],[-97,-118,120],[-119,121],[-120,122],[-117,121],[-117,-119,122],[-121,123],[-122,124],[-114,123],[-114,-121,124],[-115,-121,125],[-100,126],[-100,-101,127],[-127,129],[-99,128],[-99,-126,129],[-103,130],[-130,131],[-102,-130,132],[-128,133],[-128,-131,134],[-128,-132,135],[-129,134],[-105,-106,136],[-136,138],[-104,137],[-109,139],[-108,139],[-139,140],[-107,140],[-107,-139,141],[-140,142],[-141,143],[-137,-141,144],[-138,143],[-138,-140,144],[-138,-141,145],[-143,146],[-145,148],[-133,-143,147],[-133,-144,148],[-134,-142,147],[-134,-143,148],[-134,-144,149],[-135,-142,148],[-135,-143,149],[-149,150],[-123,-148,150],[-124,-147,150],[-125,-146,150],[-150],[-151,50,65,67],[-50,151],[-152,26,38,41,42,43],[-42,152],[-153,30,46,48,49],[-46,153],[-49,153],[-154,24,69,70,74,77],[-77,154],[-155,54,73,91],[-73,155],[-156,51,53,56,59],[-56,156],[-157,28,58,60],[-60,157],[-158,37,88],[-88,158],[-159,27,29,55,64],[-29,159],[-64,159],[-160,25,72,75,81],[-25,160],[-75,160],[-81,160],[-161,151,152],[-162,151],[-162,152],[-151,-152,162],[-163,154,155],[-164,154],[-164,155],[-154,-155,164],[-165,153,163],[-166,153,164],[-167,153],[-166,163],[-167,164],[-153,-164,167],[-168,161,167],[-169,161],[-168,162,166],[-169,162,167],[-170,162],[-168,165],[-169,166],[-170,167],[-162,-167,170],[-171,156,157],[-172,156],[-172,157],[-156,-157,172],[-173,159,160],[-174,159],[-159,173],[-174,160],[-159,-160,174],[-175,158,173],[-176,158,174],[-177,158],[-176,173],[-158,-173,176],[-177,174],[-158,-174,177],[-178,171,177],[-178,172,176],[-179,172,177],[-180,172],[-178,175],[-179,176],[-172,-176,179],[-180,177],[-181,168],[-181,169,180],[-181,170,179],[-181,178],[-170,-179,182],[181],[-182],[-44,183],[-85,183],[-86,183],[-83,184],[-87,184],[-92,184],[-185,35,36,63,80],[-35,185],[-36,185],[-63,185],[-80,185],[-186,52,68,89,90],[-52,186],[-68,186],[-89,186],[-90,186],[-32,187],[-34,187],[-47,187],[-39,188],[-57,188],[-66,188],[-31,189],[-45,189],[-61,189],[-33,190],[-40,190],[-71,190],[-84,190],[-76,191],[-78,191],[-82,191],[-184,192],[-183,192],[-183,-184,193],[-194,185,186],[-186,194],[-185,194],[-194,195],[-192,195],[-192,-194,196],[-193,196],[-193,-194,197],[-188,198],[-187,198],[-191,199],[-190,199],[-190,-191,200],[-199,201],[-200,202],[-189,201],[-201,203],[-202,204],[-198,203],[-198,-202,205],[-205,206],[-195,-204,206],[-196,-203,206],[-197,206],[-206],[-5,-12,-15,-17,-43,-49,-56,-60,-64,-73,-77,-83,-84,-88],[-5,-12,-15,-17,-43,-49,-56,-60,-64,-73,-77,-85,-87,-88],[-5,-8,-12,-19,-41,-49,-56,-60,-65,-74,-75,-86,-91,-92],[-5,-8,-12,-16,-41,-49,-56,-60,-65,-70,-75,-86,-91,-92],[-5,-12,-15,-21,-43,-49,-56,-60,-64,-70,-73,-75,-86,-92],[-4,-5,-12,-17,-49,-50,-56,-60,-64,-73,-77,-86,-88,-92],[-5,-12,-15,-17,-43,-49,-56,-60,-64,-73,-77,-86,-88,-92],[-5,-8,-9,-19,-41,-49,-53,-60,-65,-74,-75,-86,-91,-92],[-5,-11,-12,-17,-43,-49,-56,-64,-67,-73,-77,-85,-87,-88],[-5,-9,-10,-17,-43,-49,-59,-64,-67,-73,-77,-85,-87,-88],[-6,-12,-17,-23,-42,-48,-56,-60,-65,-73,-77,-85,-87,-88],[-6,-17,-22,-23,-42,-48,-53,-55,-60,-65,-73,-77,-85,-87],[-6,-7,-12,-17,-42,-50,-56,-60,-64,-73,-77,-86,-88,-92],[-6,-12,-15,-17,-42,-48,-56,-60,-64,-73,-77,-85,-87,-88],[-8,-10,-12,-23,-42,-49,-55,-60,-65,-70,-73,-75,-86,-92],[-9,-10,-12,-17,-42,-49,-50,-60,-64,-73,-77,-86,-88,-92],[-8,-10,-14,-23,-42,-49,-55,-59,-65,-70,-73,-75,-86,-92],[-9,-10,-14,-17,-42,-49,-50,-59,-64,-73,-77,-86,-88,-92],[-8,-9,-10,-17,-42,-49,-59,-64,-67,-73,-77,-85,-87,-88],[-7,-8,-12,-19,-37,-41,-56,-60,-65,-74,-75,-86,-91,-92],[-12,-18,-19,-22,-37,-41,-48,-56,-60,-65,-74,-85,-87,-91],[-12,-16,-17,-22,-37,-41,-48,-56,-60,-65,-77,-85,-87,-91],[-11,-12,-14,-17,-42,-49,-50,-56,-64,-73,-77,-86,-88,-92],[-8,-11,-12,-17,-42,-49,-56,-64,-67,-73,-77,-85,-87,-88],[-8,-12,-15,-17,-42,-49,-56,-60,-64,-73,-77,-83,-84,-88],[-8,-12,-15,-17,-42,-49,-56,-60,-64,-73,-77,-85,-87,-88],[-8,-12,-15,-17,-42,-49,-56,-60,-64,-73,-77,-86,-88,-92],[-8,-12,-15,-21,-42,-49,-56,-60,-64,-70,-73,-75,-86,-92],[-8,-12,-17,-23,-42,-49,-56,-60,-65,-73,-77,-83,-84,-88],[-8,-12,-17,-23,-42,-49,-56,-60,-65,-73,-77,-85,-87,-88],[-8,-12,-19,-20,-42,-49,-56,-60,-65,-74,-75,-86,-91,-92],[-8,-12,-21,-23,-42,-49,-56,-60,-65,-70,-73,-75,-86,-92],[-8,-12,-16,-20,-42,-49,-56,-60,-65,-70,-75,-86,-91,-92],[-8,-12,-17,-23,-42,-49,-56,-60,-65,-73,-77,-86,-88,-92],[-8,-12,-18,-19,-42,-49,-56,-60,-65,-74,-81,-86,-88,-92],[-8,-12,-16,-17,-42,-49,-56,-60,-65,-77,-81,-86,-88,-92],[-12,-13,-17,-23,-42,-49,-50,-56,-60,-73,-77,-86,-88,-92],[-12,-17,-21,-22,-42,-49,-50,-56,-60,-64,-73,-77,-86,-92],[-12,-18,-21,-22,-42,-49,-50,-56,-60,-64,-70,-73,-86,-92],[-12,-18,-19,-20,-42,-49,-50,-56,-60,-64,-74,-86,-88,-92],[-12,-16,-17,-20,-42,-49,-50,-56,-60,-64,-77,-86,-88,-92],[-12,-17,-18,-19,-42,-49,-50,-56,-60,-64,-73,-86,-88,-92],[-8,-18,-19,-22,-42,-49,-53,-55,-60,-65,-74,-81,-86,-92],[-8,-16,-17,-22,-42,-49,-53,-55,-60,-65,-77,-81,-86,-92],[-8,-17,-22,-23,-42,-49,-53,-55,-60,-65,-73,-77,-83,-84],[-8,-17,-22,-23,-42,-49,-53,-55,-60,-65,-73,-77,-85,-87],[-8,-17,-22,-23,-42,-49,-53,-55,-60,-65,-73,-77,-86,-92],[-8,-9,-19,-20,-42,-49,-53,-60,-65,-74,-75,-86,-91,-92],[-8,-19,-20,-23,-42,-49,-53,-55,-60,-65,-74,-75,-86,-92],[-8,-17,-19,-23,-42,-49,-53,-55,-60,-65,-73,-75,-86,-92],[-13,-17,-22,-23,-42,-49,-50,-53,-55,-60,-73,-77,-86,-92],[-9,-17,-21,-22,-42,-49,-50,-53,-60,-64,-73,-77,-86,-92],[5,10,17,37,42,53,56,63,70,74,80,89,90],[18,22,29,36,45,47,52,58,62,66,69,75,77,79,80,83,85,86,88,90,92],[6,12,19,37,49,53,59,63,70,77,80,89,90],[14,15,33,40,46,50,60,65,67,76,82,84,85,87,92],[8,15,43,48,50,65,67,82,84,86,87,92]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"group\",\"index\":3,\"kind\":1},{\"tag\":\"group\",\"index\":4,\"kind\":1},{\"tag\":\"group\",\"index\":6,\"kind\":1},{\"tag\":\"group\",\"index\":7,\"kind\":1},{\"tag\":\"group\",\"index\":8,\"kind\":1},{\"tag\":\"group\",\"index\":9,\"kind\":1},{\"tag\":\"group\",\"index\":11,\"kind\":1},{\"tag\":\"group\",\"index\":12,\"kind\":1},{\"tag\":\"group\",\"index\":13,\"kind\":1},{\"tag\":\"group\",\"index\":14,\"kind\":1},{\"tag\":\"group\",\"index\":16,\"kind\":1},{\"tag\":\"group\",\"index\":17,\"kind\":1},{\"tag\":\"group\",\"index\":18,\"kind\":1},{\"tag\":\"group\",\"index\":19,\"kind\":1},{\"tag\":\"group\",\"index\":20,\"kind\":1},{\"tag\":\"group\",\"index\":21,\"kind\":1},{\"tag\":\"group\",\"index\":22,\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":24,\"b\":9},{\"tag\":\"incompatible\",\"a\":25,\"b\":4},{\"tag\":\"incompatible\",\"a\":25,\"b\":24},{\"tag\":\"incompatible\",\"a\":26,\"b\":16},{\"tag\":\"incompatible\",\"a\":27,\"b\":11},{\"tag\":\"incompatible\",\"a\":28,\"b\":18},{\"tag\":\"incompatible\",\"a\":29,\"b\":5},{\"tag\":\"incompatible\",\"a\":29,\"b\":27},{\"tag\":\"incompatible\",\"a\":36,\"b\":2},{\"tag\":\"incompatible\",\"a\":36,\"b\":23},{\"tag\":\"incompatible\",\"a\":36,\"b\":25},{\"tag\":\"incompatible\",\"a\":36,\"b\":29},{\"tag\":\"incompatible\",\"a\":36,\"b\":34},{\"tag\":\"incompatible\",\"a\":36,\"b\":35},{\"tag\":\"incompatible\",\"a\":40,\"b\":28},{\"tag\":\"incompatible\",\"a\":41,\"b\":0},{\"tag\":\"incompatible\",\"a\":41,\"b\":23},{\"tag\":\"incompatible\",\"a\":41,\"b\":24},{\"tag\":\"incompatible\",\"a\":41,\"b\":26},{\"tag\":\"incompatible\",\"a\":41,\"b\":36},{\"tag\":\"incompatible\",\"a\":41,\"b\":37},{\"tag\":\"incompatible\",\"a\":41,\"b\":40},{\"tag\":\"incompatible\",\"a\":42,\"b\":25},{\"tag\":\"incompatible\",\"a\":42,\"b\":41},{\"tag\":\"incompatible\",\"a\":44,\"b\":32},{\"tag\":\"incompatible\",\"a\":44,\"b\":39},{\"tag\":\"incompatible\",\"a\":45,\"b\":24},{\"tag\":\"incompatible\",\"a\":45,\"b\":27},{\"tag\":\"incompatible\",\"a\":47,\"b\":32},{\"tag\":\"incompatible\",\"a\":47,\"b\":42},{\"tag\":\"incompatible\",\"a\":48,\"b\":1},{\"tag\":\"incompatible\",\"a\":48,\"b\":23},{\"tag\":\"incompatible\",\"a\":48,\"b\":27},{\"tag\":\"incompatible\",\"a\":48,\"b\":28},{\"tag\":\"incompatible\",\"a\":48,\"b\":29},{\"tag\":\"incompatible\",\"a\":48,\"b\":34},{\"tag\":\"incompatible\",\"a\":48,\"b\":35},{\"tag\":\"incompatible\",\"a\":48,\"b\":36},{\"tag\":\"incompatible\",\"a\":48,\"b\":43},{\"tag\":\"incompatible\",\"a\":48,\"b\":44},{\"tag\":\"incompatible\",\"a\":48,\"b\":45},{\"tag\":\"incompatible\",\"a\":48,\"b\":46},{\"tag\":\"incompatible\",\"a\":48,\"b\":47},{\"tag\":\"incompatible\",\"a\":50,\"b\":24},{\"tag\":\"incompatible\",\"a\":50,\"b\":27},{\"tag\":\"incompatible\",\"a\":50,\"b\":32},{\"tag\":\"incompatible\",\"a\":50,\"b\":37},{\"tag\":\"incompatible\",\"a\":50,\"b\":42},{\"tag\":\"incompatible\",\"a\":50,\"b\":45},{\"tag\":\"incompatible\",\"a\":50,\"b\":47},{\"tag\":\"incompatible\",\"a\":51,\"b\":36},{\"tag\":\"incompatible\",\"a\":52,\"b\":36},{\"tag\":\"incompatible\",\"a\":53,\"b\":2},{\"tag\":\"incompatible\",\"a\":53,\"b\":23},{\"tag\":\"incompatible\",\"a\":53,\"b\":24},{\"tag\":\"incompatible\",\"a\":53,\"b\":36},{\"tag\":\"incompatible\",\"a\":53,\"b\":51},{\"tag\":\"incompatible\",\"a\":54,\"b\":51},{\"tag\":\"incompatible\",\"a\":55,\"b\":24},{\"tag\":\"incompatible\",\"a\":55,\"b\":40},{\"tag\":\"incompatible\",\"a\":55,\"b\":51},{\"tag\":\"incompatible\",\"a\":55,\"b\":54},{\"tag\":\"incompatible\",\"a\":56,\"b\":0},{\"tag\":\"incompatible\",\"a\":56,\"b\":23},{\"tag\":\"incompatible\",\"a\":56,\"b\":24},{\"tag\":\"incompatible\",\"a\":56,\"b\":25},{\"tag\":\"incompatible\",\"a\":56,\"b\":26},{\"tag\":\"incompatible\",\"a\":56,\"b\":51},{\"tag\":\"incompatible\",\"a\":56,\"b\":52},{\"tag\":\"incompatible\",\"a\":56,\"b\":53},{\"tag\":\"incompatible\",\"a\":56,\"b\":54},{\"tag\":\"incompatible\",\"a\":56,\"b\":55},{\"tag\":\"incompatible\",\"a\":57,\"b\":56},{\"tag\":\"incompatible\",\"a\":58,\"b\":26},{\"tag\":\"incompatible\",\"a\":58,\"b\":28},{\"tag\":\"incompatible\",\"a\":58,\"b\":40},{\"tag\":\"incompatible\",\"a\":58,\"b\":55},{\"tag\":\"incompatible\",\"a\":59,\"b\":23},{\"tag\":\"incompatible\",\"a\":59,\"b\":27},{\"tag\":\"incompatible\",\"a\":59,\"b\":28},{\"tag\":\"incompatible\",\"a\":59,\"b\":29},{\"tag\":\"incompatible\",\"a\":59,\"b\":53},{\"tag\":\"incompatible\",\"a\":59,\"b\":56},{\"tag\":\"incompatible\",\"a\":59,\"b\":58},{\"tag\":\"incompatible\",\"a\":60,\"b\":29},{\"tag\":\"incompatible\",\"a\":60,\"b\":43},{\"tag\":\"incompatible\",\"a\":60,\"b\":45},{\"tag\":\"incompatible\",\"a\":60,\"b\":51},{\"tag\":\"incompatible\",\"a\":60,\"b\":58},{\"tag\":\"incompatible\",\"a\":60,\"b\":59},{\"tag\":\"incompatible\",\"a\":63,\"b\":36},{\"tag\":\"incompatible\",\"a\":63,\"b\":56},{\"tag\":\"incompatible\",\"a\":63,\"b\":59},{\"tag\":\"incompatible\",\"a\":63,\"b\":60},{\"tag\":\"incompatible\",\"a\":64,\"b\":26},{\"tag\":\"incompatible\",\"a\":64,\"b\":28},{\"tag\":\"incompatible\",\"a\":64,\"b\":31},{\"tag\":\"incompatible\",\"a\":64,\"b\":33},{\"tag\":\"incompatible\",\"a\":64,\"b\":37},{\"tag\":\"incompatible\",\"a\":64,\"b\":40},{\"tag\":\"incompatible\",\"a\":64,\"b\":44},{\"tag\":\"incompatible\",\"a\":64,\"b\":52},{\"tag\":\"incompatible\",\"a\":64,\"b\":54},{\"tag\":\"incompatible\",\"a\":64,\"b\":55},{\"tag\":\"incompatible\",\"a\":64,\"b\":57},{\"tag\":\"incompatible\",\"a\":64,\"b\":58},{\"tag\":\"incompatible\",\"a\":64,\"b\":61},{\"tag\":\"incompatible\",\"a\":64,\"b\":62},{\"tag\":\"incompatible\",\"a\":65,\"b\":30},{\"tag\":\"incompatible\",\"a\":65,\"b\":37},{\"tag\":\"incompatible\",\"a\":65,\"b\":42},{\"tag\":\"incompatible\",\"a\":65,\"b\":43},{\"tag\":\"incompatible\",\"a\":65,\"b\":50},{\"tag\":\"incompatible\",\"a\":65,\"b\":54},{\"tag\":\"incompatible\",\"a\":65,\"b\":61},{\"tag\":\"incompatible\",\"a\":65,\"b\":64},{\"tag\":\"incompatible\",\"a\":66,\"b\":65},{\"tag\":\"incompatible\",\"a\":67,\"b\":47},{\"tag\":\"incompatible\",\"a\":67,\"b\":60},{\"tag\":\"incompatible\",\"a\":68,\"b\":36},{\"tag\":\"incompatible\",\"a\":69,\"b\":36},{\"tag\":\"incompatible\",\"a\":69,\"b\":53},{\"tag\":\"incompatible\",\"a\":70,\"b\":2},{\"tag\":\"incompatible\",\"a\":70,\"b\":26},{\"tag\":\"incompatible\",\"a\":70,\"b\":28},{\"tag\":\"incompatible\",\"a\":70,\"b\":36},{\"tag\":\"incompatible\",\"a\":70,\"b\":51},{\"tag\":\"incompatible\",\"a\":70,\"b\":53},{\"tag\":\"incompatible\",\"a\":71,\"b\":64},{\"tag\":\"incompatible\",\"a\":72,\"b\":45},{\"tag\":\"incompatible\",\"a\":72,\"b\":50},{\"tag\":\"incompatible\",\"a\":72,\"b\":55},{\"tag\":\"incompatible\",\"a\":73,\"b\":19},{\"tag\":\"incompatible\",\"a\":73,\"b\":25},{\"tag\":\"incompatible\",\"a\":73,\"b\":30},{\"tag\":\"incompatible\",\"a\":73,\"b\":40},{\"tag\":\"incompatible\",\"a\":73,\"b\":69},{\"tag\":\"incompatible\",\"a\":73,\"b\":72},{\"tag\":\"incompatible\",\"a\":74,\"b\":24},{\"tag\":\"incompatible\",\"a\":74,\"b\":25},{\"tag\":\"incompatible\",\"a\":74,\"b\":26},{\"tag\":\"incompatible\",\"a\":74,\"b\":70},{\"tag\":\"incompatible\",\"a\":74,\"b\":72},{\"tag\":\"incompatible\",\"a\":74,\"b\":73},{\"tag\":\"incompatible\",\"a\":75,\"b\":27},{\"tag\":\"incompatible\",\"a\":75,\"b\":28},{\"tag\":\"incompatible\",\"a\":75,\"b\":37},{\"tag\":\"incompatible\",\"a\":75,\"b\":45},{\"tag\":\"incompatible\",\"a\":75,\"b\":50},{\"tag\":\"incompatible\",\"a\":75,\"b\":58},{\"tag\":\"incompatible\",\"a\":75,\"b\":69},{\"tag\":\"incompatible\",\"a\":75,\"b\":72},{\"tag\":\"incompatible\",\"a\":76,\"b\":24},{\"tag\":\"incompatible\",\"a\":76,\"b\":44},{\"tag\":\"incompatible\",\"a\":76,\"b\":75},{\"tag\":\"incompatible\",\"a\":77,\"b\":1},{\"tag\":\"incompatible\",\"a\":77,\"b\":27},{\"tag\":\"incompatible\",\"a\":77,\"b\":28},{\"tag\":\"incompatible\",\"a\":77,\"b\":29},{\"tag\":\"incompatible\",\"a\":77,\"b\":70},{\"tag\":\"incompatible\",\"a\":77,\"b\":74},{\"tag\":\"incompatible\",\"a\":77,\"b\":75},{\"tag\":\"incompatible\",\"a\":77,\"b\":76},{\"tag\":\"incompatible\",\"a\":78,\"b\":73},{\"tag\":\"incompatible\",\"a\":79,\"b\":73},{\"tag\":\"incompatible\",\"a\":80,\"b\":36},{\"tag\":\"incompatible\",\"a\":80,\"b\":73},{\"tag\":\"incompatible\",\"a\":81,\"b\":37},{\"tag\":\"incompatible\",\"a\":81,\"b\":40},{\"tag\":\"incompatible\",\"a\":81,\"b\":45},{\"tag\":\"incompatible\",\"a\":81,\"b\":50},{\"tag\":\"incompatible\",\"a\":81,\"b\":64},{\"tag\":\"incompatible\",\"a\":81,\"b\":73},{\"tag\":\"incompatible\",\"a\":81,\"b\":75},{\"tag\":\"incompatible\",\"a\":82,\"b\":44},{\"tag\":\"incompatible\",\"a\":84,\"b\":24},{\"tag\":\"incompatible\",\"a\":84,\"b\":27},{\"tag\":\"incompatible\",\"a\":84,\"b\":34},{\"tag\":\"incompatible\",\"a\":84,\"b\":37},{\"tag\":\"incompatible\",\"a\":84,\"b\":38},{\"tag\":\"incompatible\",\"a\":84,\"b\":47},{\"tag\":\"incompatible\",\"a\":84,\"b\":68},{\"tag\":\"incompatible\",\"a\":84,\"b\":72},{\"tag\":\"incompatible\",\"a\":84,\"b\":75},{\"tag\":\"incompatible\",\"a\":84,\"b\":78},{\"tag\":\"incompatible\",\"a\":84,\"b\":79},{\"tag\":\"incompatible\",\"a\":84,\"b\":81},{\"tag\":\"incompatible\",\"a\":85,\"b\":24},{\"tag\":\"incompatible\",\"a\":85,\"b\":72},{\"tag\":\"incompatible\",\"a\":85,\"b\":75},{\"tag\":\"incompatible\",\"a\":87,\"b\":24},{\"tag\":\"incompatible\",\"a\":87,\"b\":27},{\"tag\":\"incompatible\",\"a\":87,\"b\":30},{\"tag\":\"incompatible\",\"a\":87,\"b\":31},{\"tag\":\"incompatible\",\"a\":87,\"b\":32},{\"tag\":\"incompatible\",\"a\":87,\"b\":34},{\"tag\":\"incompatible\",\"a\":87,\"b\":37},{\"tag\":\"incompatible\",\"a\":87,\"b\":38},{\"tag\":\"incompatible\",\"a\":87,\"b\":43},{\"tag\":\"incompatible\",\"a\":87,\"b\":44},{\"tag\":\"incompatible\",\"a\":87,\"b\":45},{\"tag\":\"incompatible\",\"a\":87,\"b\":50},{\"tag\":\"incompatible\",\"a\":87,\"b\":68},{\"tag\":\"incompatible\",\"a\":87,\"b\":72},{\"tag\":\"incompatible\",\"a\":87,\"b\":75},{\"tag\":\"incompatible\",\"a\":87,\"b\":76},{\"tag\":\"incompatible\",\"a\":87,\"b\":78},{\"tag\":\"incompatible\",\"a\":87,\"b\":79},{\"tag\":\"incompatible\",\"a\":87,\"b\":81},{\"tag\":\"incompatible\",\"a\":88,\"b\":23},{\"tag\":\"incompatible\",\"a\":88,\"b\":36},{\"tag\":\"incompatible\",\"a\":88,\"b\":51},{\"tag\":\"incompatible\",\"a\":88,\"b\":53},{\"tag\":\"incompatible\",\"a\":88,\"b\":55},{\"tag\":\"incompatible\",\"a\":88,\"b\":58},{\"tag\":\"incompatible\",\"a\":88,\"b\":69},{\"tag\":\"incompatible\",\"a\":88,\"b\":70},{\"tag\":\"incompatible\",\"a\":88,\"b\":72},{\"tag\":\"incompatible\",\"a\":88,\"b\":75},{\"tag\":\"incompatible\",\"a\":89,\"b\":36},{\"tag\":\"incompatible\",\"a\":89,\"b\":56},{\"tag\":\"incompatible\",\"a\":90,\"b\":36},{\"tag\":\"incompatible\",\"a\":91,\"b\":55},{\"tag\":\"incompatible\",\"a\":91,\"b\":64},{\"tag\":\"incompatible\",\"a\":91,\"b\":72},{\"tag\":\"incompatible\",\"a\":91,\"b\":81},{\"tag\":\"incompatible\",\"a\":91,\"b\":88},{\"tag\":\"incompatible\",\"a\":92,\"b\":47},{\"tag\":\"incompatible\",\"a\":92,\"b\":67},{\"tag\":\"incompatible\",\"a\":92,\"b\":87},{\"tag\":\"mate\",\"ridge\":7,\"a\":0,\"owners\":[1,2,27,28,29,30,31,32,33]},{\"tag\":\"mate\",\"ridge\":7,\"a\":2,\"owners\":[0,1,24,25,26,27,28,29,30,31,32,33]},{\"tag\":\"mate\",\"ridge\":7,\"a\":25,\"owners\":[1,2,27,28,29,31,32]},{\"tag\":\"mate\",\"ridge\":7,\"a\":26,\"owners\":[1,2,27,29,30,32]},{\"tag\":\"mate\",\"ridge\":7,\"a\":27,\"owners\":[0,2,25,26,33]},{\"tag\":\"mate\",\"ridge\":7,\"a\":32,\"owners\":[0,1,2,25,26,28,33]},{\"tag\":\"mate\",\"ridge\":11,\"a\":4,\"owners\":[0,3,23,24,26,34,35,37,38,39,40,42]},{\"tag\":\"mate\",\"ridge\":11,\"a\":42,\"owners\":[0,4,23,24,26,34,35,36,38]},{\"tag\":\"three\",\"ridge\":11,\"vertices\":[4,24,42]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[0,53,55]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[25,53,55]},{\"tag\":\"mate\",\"ridge\":14,\"a\":73,\"owners\":[0,16,23,24,68,70]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[0,70,73]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[16,24,73]},{\"tag\":\"mate\",\"ridge\":19,\"a\":47,\"owners\":[1,5,23,27,28,34,35,36,44]},{\"tag\":\"three\",\"ridge\":19,\"vertices\":[1,36,47]},{\"tag\":\"three\",\"ridge\":19,\"vertices\":[5,6,28]},{\"tag\":\"three\",\"ridge\":19,\"vertices\":[5,28,47]},{\"tag\":\"three\",\"ridge\":19,\"vertices\":[6,28,36]},{\"tag\":\"three\",\"ridge\":19,\"vertices\":[28,36,47]},{\"tag\":\"mate\",\"ridge\":21,\"a\":60,\"owners\":[1,11,23,28,52,53]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[1,11,60]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[10,11,28]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[11,28,60]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[28,53,60]},{\"tag\":\"mate\",\"ridge\":22,\"a\":75,\"owners\":[1,18,23,29,70]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[2,4,48]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[2,41,48]},{\"tag\":\"mate\",\"ridge\":261,\"a\":56,\"owners\":[2,11]},{\"tag\":\"mate\",\"ridge\":261,\"a\":59,\"owners\":[2,9]},{\"tag\":\"mate\",\"ridge\":262,\"a\":74,\"owners\":[2,18]},{\"tag\":\"mate\",\"ridge\":262,\"a\":77,\"owners\":[2,16]},{\"tag\":\"mate\",\"ridge\":73,\"a\":42,\"owners\":[12,54,57,64]},{\"tag\":\"mate\",\"ridge\":73,\"a\":64,\"owners\":[3,25,41,42]},{\"tag\":\"mate\",\"ridge\":74,\"a\":41,\"owners\":[19,71,73,81,82]},{\"tag\":\"mate\",\"ridge\":265,\"a\":4,\"owners\":[9,53,56,63]},{\"tag\":\"mate\",\"ridge\":265,\"a\":9,\"owners\":[4,36,41,63]},{\"tag\":\"mate\",\"ridge\":265,\"a\":36,\"owners\":[9,56]},{\"tag\":\"mate\",\"ridge\":265,\"a\":41,\"owners\":[9,53,56,63]},{\"tag\":\"mate\",\"ridge\":265,\"a\":56,\"owners\":[4,36,41]},{\"tag\":\"mate\",\"ridge\":266,\"a\":4,\"owners\":[16,70,74,80]},{\"tag\":\"mate\",\"ridge\":266,\"a\":16,\"owners\":[4,36,41,80]},{\"tag\":\"mate\",\"ridge\":266,\"a\":36,\"owners\":[16,74]},{\"tag\":\"mate\",\"ridge\":266,\"a\":41,\"owners\":[16,70,74,80]},{\"tag\":\"mate\",\"ridge\":266,\"a\":70,\"owners\":[4,41]},{\"tag\":\"mate\",\"ridge\":266,\"a\":74,\"owners\":[4,36,41]},{\"tag\":\"mate\",\"ridge\":273,\"a\":5,\"owners\":[11,53,59,63]},{\"tag\":\"mate\",\"ridge\":273,\"a\":11,\"owners\":[5,36,48,63]},{\"tag\":\"mate\",\"ridge\":273,\"a\":36,\"owners\":[11,59]},{\"tag\":\"mate\",\"ridge\":273,\"a\":48,\"owners\":[11,53,59,63]},{\"tag\":\"mate\",\"ridge\":273,\"a\":53,\"owners\":[5,48]},{\"tag\":\"mate\",\"ridge\":274,\"a\":5,\"owners\":[18,70,77,80]},{\"tag\":\"mate\",\"ridge\":274,\"a\":18,\"owners\":[5,36,48,80]},{\"tag\":\"mate\",\"ridge\":274,\"a\":36,\"owners\":[18,77]},{\"tag\":\"mate\",\"ridge\":274,\"a\":48,\"owners\":[18,70,77,80]},{\"tag\":\"mate\",\"ridge\":274,\"a\":70,\"owners\":[5,48]},{\"tag\":\"mate\",\"ridge\":274,\"a\":77,\"owners\":[5,36,48]},{\"tag\":\"mate\",\"ridge\":274,\"a\":80,\"owners\":[5,18,48]},{\"tag\":\"mate\",\"ridge\":515,\"a\":42,\"owners\":[6,29,32,45,48]},{\"tag\":\"mate\",\"ridge\":515,\"a\":48,\"owners\":[7,32,39,42,50]},{\"tag\":\"mate\",\"ridge\":529,\"a\":60,\"owners\":[6,47,48]},{\"tag\":\"mate\",\"ridge\":530,\"a\":47,\"owners\":[76,85]},{\"tag\":\"mate\",\"ridge\":530,\"a\":86,\"owners\":[6,29,45,48,76]},{\"tag\":\"three\",\"ridge\":530,\"vertices\":[48,76,86]},{\"tag\":\"mate\",\"ridge\":577,\"a\":42,\"owners\":[14,67]},{\"tag\":\"mate\",\"ridge\":577,\"a\":47,\"owners\":[14,65]},{\"tag\":\"mate\",\"ridge\":577,\"a\":65,\"owners\":[7,47]},{\"tag\":\"mate\",\"ridge\":578,\"a\":7,\"owners\":[82,84,86,87]},{\"tag\":\"mate\",\"ridge\":578,\"a\":42,\"owners\":[84,86,87]},{\"tag\":\"mate\",\"ridge\":578,\"a\":47,\"owners\":[82,87]},{\"tag\":\"mate\",\"ridge\":578,\"a\":50,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":578,\"a\":84,\"owners\":[7,42]},{\"tag\":\"mate\",\"ridge\":578,\"a\":86,\"owners\":[7,42,50,82]},{\"tag\":\"mate\",\"ridge\":578,\"a\":87,\"owners\":[7,42,47]},{\"tag\":\"mate\",\"ridge\":37,\"a\":56,\"owners\":[10,27,30,31,32,58,60,61]},{\"tag\":\"mate\",\"ridge\":37,\"a\":59,\"owners\":[8,24,30,31,32,54,55,61]},{\"tag\":\"mate\",\"ridge\":37,\"a\":60,\"owners\":[8,24,30,31,54,55,56,61]},{\"tag\":\"mate\",\"ridge\":41,\"a\":55,\"owners\":[12,34,37,39,63,65]},{\"tag\":\"mate\",\"ridge\":41,\"a\":56,\"owners\":[12,34,37,38,39,62,64,65]},{\"tag\":\"mate\",\"ridge\":41,\"a\":64,\"owners\":[8,24,34,39,51,56,63]},{\"tag\":\"mate\",\"ridge\":41,\"a\":65,\"owners\":[8,24,34,38,51,55,56,62,63]},{\"tag\":\"three\",\"ridge\":41,\"vertices\":[56,62,65]},{\"tag\":\"mate\",\"ridge\":44,\"a\":8,\"owners\":[20,68,71,72,88,89,91]},{\"tag\":\"mate\",\"ridge\":44,\"a\":88,\"owners\":[8,24,54,56,71]},{\"tag\":\"mate\",\"ridge\":268,\"a\":9,\"owners\":[16,70,74,89,90]},{\"tag\":\"mate\",\"ridge\":268,\"a\":16,\"owners\":[9,53,56,89,90]},{\"tag\":\"mate\",\"ridge\":268,\"a\":53,\"owners\":[16,74]},{\"tag\":\"mate\",\"ridge\":268,\"a\":56,\"owners\":[16,70,74,90]},{\"tag\":\"mate\",\"ridge\":49,\"a\":45,\"owners\":[10,51,58,59,62,63,66]},{\"tag\":\"mate\",\"ridge\":49,\"a\":59,\"owners\":[13,34,43,44,45,62,66,67]},{\"tag\":\"mate\",\"ridge\":52,\"a\":60,\"owners\":[21,68,75,88,89]},{\"tag\":\"mate\",\"ridge\":52,\"a\":88,\"owners\":[10,27,59,60,76]},{\"tag\":\"mate\",\"ridge\":276,\"a\":11,\"owners\":[18,70,77,89,90]},{\"tag\":\"mate\",\"ridge\":276,\"a\":18,\"owners\":[11,53,59,89,90]},{\"tag\":\"mate\",\"ridge\":276,\"a\":53,\"owners\":[18,77]},{\"tag\":\"mate\",\"ridge\":276,\"a\":70,\"owners\":[11,59]},{\"tag\":\"mate\",\"ridge\":276,\"a\":77,\"owners\":[11,53,59,89]},{\"tag\":\"mate\",\"ridge\":276,\"a\":90,\"owners\":[11,18,59]},{\"tag\":\"mate\",\"ridge\":97,\"a\":37,\"owners\":[14,61,66,67]},{\"tag\":\"mate\",\"ridge\":97,\"a\":64,\"owners\":[14,30,43,50,67]},{\"tag\":\"mate\",\"ridge\":104,\"a\":65,\"owners\":[22,71,81,91]},{\"tag\":\"mate\",\"ridge\":545,\"a\":45,\"owners\":[14,65]},{\"tag\":\"mate\",\"ridge\":545,\"a\":50,\"owners\":[13,60]},{\"tag\":\"mate\",\"ridge\":560,\"a\":13,\"owners\":[76,84,85,92]},{\"tag\":\"mate\",\"ridge\":560,\"a\":45,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":560,\"a\":60,\"owners\":[84,85,92]},{\"tag\":\"mate\",\"ridge\":560,\"a\":67,\"owners\":[76,85]},{\"tag\":\"mate\",\"ridge\":608,\"a\":14,\"owners\":[82,84,87,92]},{\"tag\":\"mate\",\"ridge\":608,\"a\":50,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":608,\"a\":65,\"owners\":[84,87,92]},{\"tag\":\"mate\",\"ridge\":608,\"a\":67,\"owners\":[82,87]},{\"tag\":\"mate\",\"ridge\":608,\"a\":84,\"owners\":[14,65]},{\"tag\":\"mate\",\"ridge\":608,\"a\":92,\"owners\":[14,50,65,82]},{\"tag\":\"mate\",\"ridge\":134,\"a\":73,\"owners\":[17,28,31,75,77]},{\"tag\":\"mate\",\"ridge\":134,\"a\":74,\"owners\":[17,28,31,33,75,78]},{\"tag\":\"mate\",\"ridge\":134,\"a\":77,\"owners\":[15,26,31,33,72,73,78]},{\"tag\":\"mate\",\"ridge\":138,\"a\":19,\"owners\":[15,26,35,38,69,72,74,79,80]},{\"tag\":\"mate\",\"ridge\":138,\"a\":40,\"owners\":[15,69,72,74,79,80]},{\"tag\":\"mate\",\"ridge\":138,\"a\":74,\"owners\":[19,35,38,40,79,81]},{\"tag\":\"mate\",\"ridge\":138,\"a\":81,\"owners\":[15,26,35,69,74,80]},{\"tag\":\"mate\",\"ridge\":140,\"a\":55,\"owners\":[15,69,73,74,90]},{\"tag\":\"mate\",\"ridge\":140,\"a\":73,\"owners\":[20,52,55,88,90]},{\"tag\":\"mate\",\"ridge\":140,\"a\":88,\"owners\":[15,26,57,73,74]},{\"tag\":\"mate\",\"ridge\":146,\"a\":17,\"owners\":[35,44,46,79,80,83,85,86]},{\"tag\":\"mate\",\"ridge\":146,\"a\":28,\"owners\":[79,80,83,85,86]},{\"tag\":\"mate\",\"ridge\":146,\"a\":69,\"owners\":[44,46,83,85,86]},{\"tag\":\"mate\",\"ridge\":146,\"a\":75,\"owners\":[35,46,80,86]},{\"tag\":\"mate\",\"ridge\":146,\"a\":77,\"owners\":[35,44,46,79,83,85,86]},{\"tag\":\"three\",\"ridge\":146,\"vertices\":[28,80,86]},{\"tag\":\"mate\",\"ridge\":148,\"a\":21,\"owners\":[17,28,52,69,77,90]},{\"tag\":\"mate\",\"ridge\":200,\"a\":64,\"owners\":[19,73]},{\"tag\":\"mate\",\"ridge\":200,\"a\":73,\"owners\":[22,64]},{\"tag\":\"mate\",\"ridge\":164,\"a\":20,\"owners\":[21,31,58,61,75,78]},{\"tag\":\"mate\",\"ridge\":164,\"a\":55,\"owners\":[21,75,78]},{\"tag\":\"mate\",\"ridge\":168,\"a\":55,\"owners\":[22,79,81]},{\"tag\":\"mate\",\"ridge\":168,\"a\":88,\"owners\":[22,38,64,81]},{\"tag\":\"mate\",\"ridge\":176,\"a\":21,\"owners\":[44,62,66,79,83,85,92]},{\"tag\":\"mate\",\"ridge\":176,\"a\":58,\"owners\":[79,83,85,92]},{\"tag\":\"mate\",\"ridge\":176,\"a\":75,\"owners\":[62,66,92]},{\"tag\":\"mate\",\"ridge\":176,\"a\":88,\"owners\":[44,66,83,85,92]},{\"tag\":\"mate\",\"ridge\":176,\"a\":92,\"owners\":[21,44,58,62,75,79,88]},{\"tag\":\"mate\",\"ridge\":224,\"a\":81,\"owners\":[61,66,92]},{\"tag\":\"three\",\"ridge\":224,\"vertices\":[64,78,92]},{\"tag\":\"mate\",\"ridge\":550,\"a\":32,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":197,\"a\":33,\"owners\":[57,61]},{\"tag\":\"mate\",\"ridge\":58,\"a\":79,\"owners\":[34,68]},{\"tag\":\"mate\",\"ridge\":153,\"a\":35,\"owners\":[52,62]},{\"tag\":\"mate\",\"ridge\":153,\"a\":62,\"owners\":[35,52]},{\"tag\":\"mate\",\"ridge\":554,\"a\":39,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":554,\"a\":82,\"owners\":[39]},{\"tag\":\"mate\",\"ridge\":114,\"a\":84,\"owners\":[43,83]},{\"tag\":\"mate\",\"ridge\":209,\"a\":46,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":209,\"a\":66,\"owners\":[46]},{\"tag\":\"mate\",\"ridge\":312,\"a\":89,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":408,\"a\":90,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":674,\"a\":87,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":720,\"a\":86,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":720,\"a\":92,\"owners\":[86]},{\"tag\":\"group_take\",\"kind\":1,\"index\":3,\"member\":3,\"full_literals\":[-4,93]},{\"tag\":\"group_take\",\"kind\":1,\"index\":4,\"member\":4,\"full_literals\":[-5,94]},{\"tag\":\"group_take\",\"kind\":1,\"index\":6,\"member\":6,\"full_literals\":[-7,95]},{\"tag\":\"group_take\",\"kind\":1,\"index\":7,\"member\":7,\"full_literals\":[-8,96]},{\"tag\":\"group_take\",\"kind\":1,\"index\":8,\"member\":8,\"full_literals\":[-9,97]},{\"tag\":\"group_take\",\"kind\":1,\"index\":9,\"member\":9,\"full_literals\":[-10,98]},{\"tag\":\"group_take\",\"kind\":1,\"index\":11,\"member\":11,\"full_literals\":[-12,99]},{\"tag\":\"group_take\",\"kind\":1,\"index\":12,\"member\":12,\"full_literals\":[-13,100]},{\"tag\":\"group_take\",\"kind\":1,\"index\":13,\"member\":13,\"full_literals\":[-14,101]},{\"tag\":\"group_take\",\"kind\":1,\"index\":14,\"member\":14,\"full_literals\":[-15,102]},{\"tag\":\"group_take\",\"kind\":1,\"index\":16,\"member\":16,\"full_literals\":[-17,103]},{\"tag\":\"group_take\",\"kind\":1,\"index\":17,\"member\":17,\"full_literals\":[-18,104]},{\"tag\":\"group_take\",\"kind\":1,\"index\":18,\"member\":18,\"full_literals\":[-19,105]},{\"tag\":\"group_take\",\"kind\":1,\"index\":19,\"member\":19,\"full_literals\":[-20,106]},{\"tag\":\"group_take\",\"kind\":1,\"index\":20,\"member\":20,\"full_literals\":[-21,107]},{\"tag\":\"group_take\",\"kind\":1,\"index\":21,\"member\":21,\"full_literals\":[-22,108]},{\"tag\":\"group_take\",\"kind\":1,\"index\":22,\"member\":22,\"full_literals\":[-23,109]},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped1_0006\",\"right_name\":\"grouped1_0008\",\"joined_name\":\"grouped1_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-94,110],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped1_0006\",\"right_name\":\"grouped1_0008\",\"joined_name\":\"grouped1_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-93,-94,111],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped1_0004\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0005\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-110,112],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped1_0004\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0005\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-111,113],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0005\",\"joined_name\":\"grouped1_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-112,114],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0005\",\"joined_name\":\"grouped1_0001\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-113,115],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0014\",\"joined_name\":\"grouped1_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-96,116],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0014\",\"joined_name\":\"grouped1_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-95,false,116],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped1_0009\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-116,117],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped1_0017\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-98,false,118],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-118,119],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-97,false,119],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0016\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-97,-118,120],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped1_0010\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-119,121],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped1_0010\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0011\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-120,122],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped1_0010\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-117,false,121],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped1_0010\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-117,-119,122],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0011\",\"joined_name\":\"grouped1_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-121,123],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0011\",\"joined_name\":\"grouped1_0002\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-122,124],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0011\",\"joined_name\":\"grouped1_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-114,false,123],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0011\",\"joined_name\":\"grouped1_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-114,-121,124],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0011\",\"joined_name\":\"grouped1_0002\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-115,-121,125],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13],\"left_name\":\"grouped1_0024\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0025\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-100,false,126],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13],\"left_name\":\"grouped1_0024\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0025\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-100,-101,127],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11],\"right\":[12,13],\"left_name\":\"grouped1_0020\",\"right_name\":\"grouped1_0025\",\"joined_name\":\"grouped1_0021\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-127,129],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11],\"right\":[12,13],\"left_name\":\"grouped1_0020\",\"right_name\":\"grouped1_0025\",\"joined_name\":\"grouped1_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-99,false,128],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11],\"right\":[12,13],\"left_name\":\"grouped1_0020\",\"right_name\":\"grouped1_0025\",\"joined_name\":\"grouped1_0021\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-99,-126,129],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15],\"right\":[16],\"left_name\":\"grouped1_0029\",\"right_name\":\"grouped1_0031\",\"joined_name\":\"grouped1_0030\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-103,130],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14],\"right\":[15,16],\"left_name\":\"grouped1_0027\",\"right_name\":\"grouped1_0030\",\"joined_name\":\"grouped1_0028\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-130,131],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14],\"right\":[15,16],\"left_name\":\"grouped1_0027\",\"right_name\":\"grouped1_0030\",\"joined_name\":\"grouped1_0028\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-102,-130,132],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11,12,13],\"right\":[14,15,16],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-128,false,133],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11,12,13],\"right\":[14,15,16],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-128,-131,134],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11,12,13],\"right\":[14,15,16],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0022\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-128,-132,135],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11,12,13],\"right\":[14,15,16],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0022\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-129,false,134],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[18],\"right\":[19],\"left_name\":\"grouped1_0035\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0036\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-105,-106,136],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17],\"right\":[18,19],\"left_name\":\"grouped1_0032\",\"right_name\":\"grouped1_0036\",\"joined_name\":\"grouped1_0033\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-136,138],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17],\"right\":[18,19],\"left_name\":\"grouped1_0032\",\"right_name\":\"grouped1_0036\",\"joined_name\":\"grouped1_0033\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-104,false,137],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[21],\"right\":[22],\"left_name\":\"grouped1_0040\",\"right_name\":\"grouped1_0042\",\"joined_name\":\"grouped1_0041\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-109,139],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[21],\"right\":[22],\"left_name\":\"grouped1_0040\",\"right_name\":\"grouped1_0042\",\"joined_name\":\"grouped1_0041\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-108,false,139],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20],\"right\":[21,22],\"left_name\":\"grouped1_0038\",\"right_name\":\"grouped1_0041\",\"joined_name\":\"grouped1_0039\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-139,140],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20],\"right\":[21,22],\"left_name\":\"grouped1_0038\",\"right_name\":\"grouped1_0041\",\"joined_name\":\"grouped1_0039\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-107,false,140],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20],\"right\":[21,22],\"left_name\":\"grouped1_0038\",\"right_name\":\"grouped1_0041\",\"joined_name\":\"grouped1_0039\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-107,-139,141],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17,18,19],\"right\":[20,21,22],\"left_name\":\"grouped1_0033\",\"right_name\":\"grouped1_0039\",\"joined_name\":\"grouped1_0034\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-140,142],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17,18,19],\"right\":[20,21,22],\"left_name\":\"grouped1_0033\",\"right_name\":\"grouped1_0039\",\"joined_name\":\"grouped1_0034\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-141,143],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17,18,19],\"right\":[20,21,22],\"left_name\":\"grouped1_0033\",\"right_name\":\"grouped1_0039\",\"joined_name\":\"grouped1_0034\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-137,-141,144],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17,18,19],\"right\":[20,21,22],\"left_name\":\"grouped1_0033\",\"right_name\":\"grouped1_0039\",\"joined_name\":\"grouped1_0034\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-138,false,143],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17,18,19],\"right\":[20,21,22],\"left_name\":\"grouped1_0033\",\"right_name\":\"grouped1_0039\",\"joined_name\":\"grouped1_0034\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-138,-140,144],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17,18,19],\"right\":[20,21,22],\"left_name\":\"grouped1_0033\",\"right_name\":\"grouped1_0039\",\"joined_name\":\"grouped1_0034\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-138,-141,145],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11,12,13,14,15,16],\"right\":[17,18,19,20,21,22],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0034\",\"joined_name\":\"grouped1_0023\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-143,146],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11,12,13,14,15,16],\"right\":[17,18,19,20,21,22],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0034\",\"joined_name\":\"grouped1_0023\",\"a\":0,\"b\":4,\"direction\":\"forward\",\"full_literals\":[false,-145,148],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11,12,13,14,15,16],\"right\":[17,18,19,20,21,22],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0034\",\"joined_name\":\"grouped1_0023\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-133,-143,147],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11,12,13,14,15,16],\"right\":[17,18,19,20,21,22],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0034\",\"joined_name\":\"grouped1_0023\",\"a\":1,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-133,-144,148],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11,12,13,14,15,16],\"right\":[17,18,19,20,21,22],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0034\",\"joined_name\":\"grouped1_0023\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-134,-142,147],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11,12,13,14,15,16],\"right\":[17,18,19,20,21,22],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0034\",\"joined_name\":\"grouped1_0023\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-134,-143,148],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11,12,13,14,15,16],\"right\":[17,18,19,20,21,22],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0034\",\"joined_name\":\"grouped1_0023\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-134,-144,149],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11,12,13,14,15,16],\"right\":[17,18,19,20,21,22],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0034\",\"joined_name\":\"grouped1_0023\",\"a\":3,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-135,-142,148],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11,12,13,14,15,16],\"right\":[17,18,19,20,21,22],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0034\",\"joined_name\":\"grouped1_0023\",\"a\":3,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-135,-143,149],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10],\"right\":[11,12,13,14,15,16,17,18,19,20,21,22],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"groupKind1\",\"a\":0,\"b\":5,\"direction\":\"forward\",\"full_literals\":[false,-149,150],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10],\"right\":[11,12,13,14,15,16,17,18,19,20,21,22],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"groupKind1\",\"a\":1,\"b\":4,\"direction\":\"forward\",\"full_literals\":[-123,-148,150],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10],\"right\":[11,12,13,14,15,16,17,18,19,20,21,22],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"groupKind1\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-124,-147,150],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10],\"right\":[11,12,13,14,15,16,17,18,19,20,21,22],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"groupKind1\",\"a\":3,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-125,-146,150],\"grouped\":true,\"kind\":1},{\"tag\":\"quota_upper\",\"kind\":1,\"quota\":4,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[50,65,67],\"full_literals\":[-151,50,65,67]},{\"tag\":\"group_take\",\"kind\":2,\"index\":0,\"member\":50,\"full_literals\":[-50,151]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[25,37,40,41,42],\"full_literals\":[-152,26,38,41,42,43]},{\"tag\":\"group_take\",\"kind\":2,\"index\":1,\"member\":41,\"full_literals\":[-42,152]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[29,45,47,48],\"full_literals\":[-153,30,46,48,49]},{\"tag\":\"group_take\",\"kind\":2,\"index\":2,\"member\":45,\"full_literals\":[-46,153]},{\"tag\":\"group_take\",\"kind\":2,\"index\":2,\"member\":48,\"full_literals\":[-49,153]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[23,69,70,74,77],\"full_literals\":[-154,24,69,70,74,77]},{\"tag\":\"group_take\",\"kind\":2,\"index\":3,\"member\":77,\"full_literals\":[-77,154]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[54,73,91],\"full_literals\":[-155,54,73,91]},{\"tag\":\"group_take\",\"kind\":2,\"index\":4,\"member\":73,\"full_literals\":[-73,155]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[51,53,56,59],\"full_literals\":[-156,51,53,56,59]},{\"tag\":\"group_take\",\"kind\":2,\"index\":5,\"member\":56,\"full_literals\":[-56,156]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[27,58,60],\"full_literals\":[-157,28,58,60]},{\"tag\":\"group_take\",\"kind\":2,\"index\":6,\"member\":60,\"full_literals\":[-60,157]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[36,88],\"full_literals\":[-158,37,88]},{\"tag\":\"group_take\",\"kind\":2,\"index\":7,\"member\":88,\"full_literals\":[-88,158]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[26,28,55,64],\"full_literals\":[-159,27,29,55,64]},{\"tag\":\"group_take\",\"kind\":2,\"index\":8,\"member\":28,\"full_literals\":[-29,159]},{\"tag\":\"group_take\",\"kind\":2,\"index\":8,\"member\":64,\"full_literals\":[-64,159]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[24,72,75,81],\"full_literals\":[-160,25,72,75,81]},{\"tag\":\"group_take\",\"kind\":2,\"index\":9,\"member\":24,\"full_literals\":[-25,160]},{\"tag\":\"group_take\",\"kind\":2,\"index\":9,\"member\":75,\"full_literals\":[-75,160]},{\"tag\":\"group_take\",\"kind\":2,\"index\":9,\"member\":81,\"full_literals\":[-81,160]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0043\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0044\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-161,151,152],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0043\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0044\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-162,151,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0043\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0044\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-162,false,152],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0043\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0044\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-151,-152,162],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0050\",\"right_name\":\"grouped2_0052\",\"joined_name\":\"grouped2_0051\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-163,154,155],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0050\",\"right_name\":\"grouped2_0052\",\"joined_name\":\"grouped2_0051\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-164,154,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0050\",\"right_name\":\"grouped2_0052\",\"joined_name\":\"grouped2_0051\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-164,false,155],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0050\",\"right_name\":\"grouped2_0052\",\"joined_name\":\"grouped2_0051\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-154,-155,164],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0048\",\"right_name\":\"grouped2_0051\",\"joined_name\":\"grouped2_0049\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-165,153,163],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0048\",\"right_name\":\"grouped2_0051\",\"joined_name\":\"grouped2_0049\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-166,153,164],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0048\",\"right_name\":\"grouped2_0051\",\"joined_name\":\"grouped2_0049\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-167,153,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0048\",\"right_name\":\"grouped2_0051\",\"joined_name\":\"grouped2_0049\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-166,false,163],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0048\",\"right_name\":\"grouped2_0051\",\"joined_name\":\"grouped2_0049\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-167,false,164],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0048\",\"right_name\":\"grouped2_0051\",\"joined_name\":\"grouped2_0049\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-153,-164,167],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0044\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0045\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-168,161,167],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0044\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0045\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-169,161,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0044\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0045\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-168,162,166],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0044\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0045\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-169,162,167],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0044\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0045\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-170,162,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0044\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0045\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-168,false,165],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0044\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0045\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-169,false,166],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0044\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0045\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-170,false,167],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0044\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0045\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-162,-167,170],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0053\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0054\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-171,156,157],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0053\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0054\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-172,156,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0053\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0054\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-172,false,157],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0053\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0054\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-156,-157,172],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0059\",\"right_name\":\"grouped2_0061\",\"joined_name\":\"grouped2_0060\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-173,159,160],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0059\",\"right_name\":\"grouped2_0061\",\"joined_name\":\"grouped2_0060\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-174,159,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0059\",\"right_name\":\"grouped2_0061\",\"joined_name\":\"grouped2_0060\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-159,false,173],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0059\",\"right_name\":\"grouped2_0061\",\"joined_name\":\"grouped2_0060\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-174,false,160],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0059\",\"right_name\":\"grouped2_0061\",\"joined_name\":\"grouped2_0060\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-159,-160,174],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0060\",\"joined_name\":\"grouped2_0058\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-175,158,173],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0060\",\"joined_name\":\"grouped2_0058\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-176,158,174],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0060\",\"joined_name\":\"grouped2_0058\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-177,158,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0060\",\"joined_name\":\"grouped2_0058\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-176,false,173],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0060\",\"joined_name\":\"grouped2_0058\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-158,-173,176],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0060\",\"joined_name\":\"grouped2_0058\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-177,false,174],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0060\",\"joined_name\":\"grouped2_0058\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-158,-174,177],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0054\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0055\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-178,171,177],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0054\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0055\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-178,172,176],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0054\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0055\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-179,172,177],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0054\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0055\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-180,172,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0054\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0055\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-178,false,175],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0054\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0055\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-179,false,176],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0054\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0055\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-172,-176,179],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0054\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0055\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-180,false,177],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0045\",\"right_name\":\"grouped2_0055\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-181,168,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0045\",\"right_name\":\"grouped2_0055\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-181,169,180],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0045\",\"right_name\":\"grouped2_0055\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-181,170,179],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0045\",\"right_name\":\"grouped2_0055\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-181,false,178],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0045\",\"right_name\":\"grouped2_0055\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":4,\"direction\":\"forward\",\"full_literals\":[-170,-179,182],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":43,\"full_literals\":[-44,183]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":85,\"full_literals\":[-85,183]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":86,\"full_literals\":[-86,183]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":83,\"full_literals\":[-83,184]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":87,\"full_literals\":[-87,184]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":92,\"full_literals\":[-92,184]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[34,35,63,80],\"full_literals\":[-185,35,36,63,80]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":34,\"full_literals\":[-35,185]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":35,\"full_literals\":[-36,185]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":63,\"full_literals\":[-63,185]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":80,\"full_literals\":[-80,185]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[52,68,89,90],\"full_literals\":[-186,52,68,89,90]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":52,\"full_literals\":[-52,186]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":68,\"full_literals\":[-68,186]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":89,\"full_literals\":[-89,186]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":90,\"full_literals\":[-90,186]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":31,\"full_literals\":[-32,187]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":33,\"full_literals\":[-34,187]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":46,\"full_literals\":[-47,187]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":38,\"full_literals\":[-39,188]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":57,\"full_literals\":[-57,188]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":66,\"full_literals\":[-66,188]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":30,\"full_literals\":[-31,189]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":44,\"full_literals\":[-45,189]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":61,\"full_literals\":[-61,189]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":32,\"full_literals\":[-33,190]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":39,\"full_literals\":[-40,190]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":71,\"full_literals\":[-71,190]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":84,\"full_literals\":[-84,190]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":76,\"full_literals\":[-76,191]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":78,\"full_literals\":[-78,191]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":82,\"full_literals\":[-82,191]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0062\",\"right_name\":\"grouped3_0066\",\"joined_name\":\"grouped3_0063\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-184,192],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0062\",\"right_name\":\"grouped3_0066\",\"joined_name\":\"grouped3_0063\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-183,false,192],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0062\",\"right_name\":\"grouped3_0066\",\"joined_name\":\"grouped3_0063\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-183,-184,193],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0067\",\"right_name\":\"grouped3_0069\",\"joined_name\":\"grouped3_0068\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-194,185,186],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0067\",\"right_name\":\"grouped3_0069\",\"joined_name\":\"grouped3_0068\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-186,194],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0067\",\"right_name\":\"grouped3_0069\",\"joined_name\":\"grouped3_0068\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-185,false,194],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0063\",\"right_name\":\"grouped3_0068\",\"joined_name\":\"grouped3_0064\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-194,195],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0063\",\"right_name\":\"grouped3_0068\",\"joined_name\":\"grouped3_0064\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-192,false,195],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0063\",\"right_name\":\"grouped3_0068\",\"joined_name\":\"grouped3_0064\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-192,-194,196],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0063\",\"right_name\":\"grouped3_0068\",\"joined_name\":\"grouped3_0064\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-193,false,196],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0063\",\"right_name\":\"grouped3_0068\",\"joined_name\":\"grouped3_0064\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-193,-194,197],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0070\",\"right_name\":\"grouped3_0073\",\"joined_name\":\"grouped3_0071\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-188,198],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0070\",\"right_name\":\"grouped3_0073\",\"joined_name\":\"grouped3_0071\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-187,false,198],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0076\",\"right_name\":\"grouped3_0078\",\"joined_name\":\"grouped3_0077\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-191,199],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0076\",\"right_name\":\"grouped3_0078\",\"joined_name\":\"grouped3_0077\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-190,false,199],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0076\",\"right_name\":\"grouped3_0078\",\"joined_name\":\"grouped3_0077\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-190,-191,200],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0074\",\"right_name\":\"grouped3_0077\",\"joined_name\":\"grouped3_0075\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-199,201],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0074\",\"right_name\":\"grouped3_0077\",\"joined_name\":\"grouped3_0075\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-200,202],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0074\",\"right_name\":\"grouped3_0077\",\"joined_name\":\"grouped3_0075\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-189,false,201],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0071\",\"right_name\":\"grouped3_0075\",\"joined_name\":\"grouped3_0072\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-201,203],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0071\",\"right_name\":\"grouped3_0075\",\"joined_name\":\"grouped3_0072\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-202,204],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0071\",\"right_name\":\"grouped3_0075\",\"joined_name\":\"grouped3_0072\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-198,false,203],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0071\",\"right_name\":\"grouped3_0075\",\"joined_name\":\"grouped3_0072\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-198,-202,205],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0064\",\"right_name\":\"grouped3_0072\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-205,206],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0064\",\"right_name\":\"grouped3_0072\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-195,-204,206],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0064\",\"right_name\":\"grouped3_0072\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-196,-203,206],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0064\",\"right_name\":\"grouped3_0072\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-197,false,206],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"block\",\"leaf\":0,\"vertices\":[4,11,14,16,42,48,56,60,64,73,77,83,84,88]},{\"tag\":\"block\",\"leaf\":1,\"vertices\":[4,11,14,16,42,48,56,60,64,73,77,85,87,88]},{\"tag\":\"block\",\"leaf\":2,\"vertices\":[4,7,11,18,40,48,56,60,65,74,75,86,91,92]},{\"tag\":\"block\",\"leaf\":3,\"vertices\":[4,7,11,15,40,48,56,60,65,70,75,86,91,92]},{\"tag\":\"block\",\"leaf\":4,\"vertices\":[4,11,14,20,42,48,56,60,64,70,73,75,86,92]},{\"tag\":\"block\",\"leaf\":5,\"vertices\":[3,4,11,16,48,50,56,60,64,73,77,86,88,92]},{\"tag\":\"block\",\"leaf\":6,\"vertices\":[4,11,14,16,42,48,56,60,64,73,77,86,88,92]},{\"tag\":\"block\",\"leaf\":7,\"vertices\":[4,7,8,18,40,48,53,60,65,74,75,86,91,92]},{\"tag\":\"block\",\"leaf\":8,\"vertices\":[4,10,11,16,42,48,56,64,67,73,77,85,87,88]},{\"tag\":\"block\",\"leaf\":9,\"vertices\":[4,8,9,16,42,48,59,64,67,73,77,85,87,88]},{\"tag\":\"block\",\"leaf\":10,\"vertices\":[5,11,16,22,41,47,56,60,65,73,77,85,87,88]},{\"tag\":\"block\",\"leaf\":11,\"vertices\":[5,16,21,22,41,47,53,55,60,65,73,77,85,87]},{\"tag\":\"block\",\"leaf\":12,\"vertices\":[5,6,11,16,41,50,56,60,64,73,77,86,88,92]},{\"tag\":\"block\",\"leaf\":13,\"vertices\":[5,11,14,16,41,47,56,60,64,73,77,85,87,88]},{\"tag\":\"block\",\"leaf\":14,\"vertices\":[7,9,11,22,41,48,55,60,65,70,73,75,86,92]},{\"tag\":\"block\",\"leaf\":15,\"vertices\":[8,9,11,16,41,48,50,60,64,73,77,86,88,92]},{\"tag\":\"block\",\"leaf\":16,\"vertices\":[7,9,13,22,41,48,55,59,65,70,73,75,86,92]},{\"tag\":\"block\",\"leaf\":17,\"vertices\":[8,9,13,16,41,48,50,59,64,73,77,86,88,92]},{\"tag\":\"block\",\"leaf\":18,\"vertices\":[7,8,9,16,41,48,59,64,67,73,77,85,87,88]},{\"tag\":\"block\",\"leaf\":19,\"vertices\":[6,7,11,18,36,40,56,60,65,74,75,86,91,92]},{\"tag\":\"block\",\"leaf\":20,\"vertices\":[11,17,18,21,36,40,47,56,60,65,74,85,87,91]},{\"tag\":\"block\",\"leaf\":21,\"vertices\":[11,15,16,21,36,40,47,56,60,65,77,85,87,91]},{\"tag\":\"block\",\"leaf\":22,\"vertices\":[10,11,13,16,41,48,50,56,64,73,77,86,88,92]},{\"tag\":\"block\",\"leaf\":23,\"vertices\":[7,10,11,16,41,48,56,64,67,73,77,85,87,88]},{\"tag\":\"block\",\"leaf\":24,\"vertices\":[7,11,14,16,41,48,56,60,64,73,77,83,84,88]},{\"tag\":\"block\",\"leaf\":25,\"vertices\":[7,11,14,16,41,48,56,60,64,73,77,85,87,88]},{\"tag\":\"block\",\"leaf\":26,\"vertices\":[7,11,14,16,41,48,56,60,64,73,77,86,88,92]},{\"tag\":\"block\",\"leaf\":27,\"vertices\":[7,11,14,20,41,48,56,60,64,70,73,75,86,92]},{\"tag\":\"block\",\"leaf\":28,\"vertices\":[7,11,16,22,41,48,56,60,65,73,77,83,84,88]},{\"tag\":\"block\",\"leaf\":29,\"vertices\":[7,11,16,22,41,48,56,60,65,73,77,85,87,88]},{\"tag\":\"block\",\"leaf\":30,\"vertices\":[7,11,18,19,41,48,56,60,65,74,75,86,91,92]},{\"tag\":\"block\",\"leaf\":31,\"vertices\":[7,11,20,22,41,48,56,60,65,70,73,75,86,92]},{\"tag\":\"block\",\"leaf\":32,\"vertices\":[7,11,15,19,41,48,56,60,65,70,75,86,91,92]},{\"tag\":\"block\",\"leaf\":33,\"vertices\":[7,11,16,22,41,48,56,60,65,73,77,86,88,92]},{\"tag\":\"block\",\"leaf\":34,\"vertices\":[7,11,17,18,41,48,56,60,65,74,81,86,88,92]},{\"tag\":\"block\",\"leaf\":35,\"vertices\":[7,11,15,16,41,48,56,60,65,77,81,86,88,92]},{\"tag\":\"block\",\"leaf\":36,\"vertices\":[11,12,16,22,41,48,50,56,60,73,77,86,88,92]},{\"tag\":\"block\",\"leaf\":37,\"vertices\":[11,16,20,21,41,48,50,56,60,64,73,77,86,92]},{\"tag\":\"block\",\"leaf\":38,\"vertices\":[11,17,20,21,41,48,50,56,60,64,70,73,86,92]},{\"tag\":\"block\",\"leaf\":39,\"vertices\":[11,17,18,19,41,48,50,56,60,64,74,86,88,92]},{\"tag\":\"block\",\"leaf\":40,\"vertices\":[11,15,16,19,41,48,50,56,60,64,77,86,88,92]},{\"tag\":\"block\",\"leaf\":41,\"vertices\":[11,16,17,18,41,48,50,56,60,64,73,86,88,92]},{\"tag\":\"block\",\"leaf\":42,\"vertices\":[7,17,18,21,41,48,53,55,60,65,74,81,86,92]},{\"tag\":\"block\",\"leaf\":43,\"vertices\":[7,15,16,21,41,48,53,55,60,65,77,81,86,92]},{\"tag\":\"block\",\"leaf\":44,\"vertices\":[7,16,21,22,41,48,53,55,60,65,73,77,83,84]},{\"tag\":\"block\",\"leaf\":45,\"vertices\":[7,16,21,22,41,48,53,55,60,65,73,77,85,87]},{\"tag\":\"block\",\"leaf\":46,\"vertices\":[7,16,21,22,41,48,53,55,60,65,73,77,86,92]},{\"tag\":\"block\",\"leaf\":47,\"vertices\":[7,8,18,19,41,48,53,60,65,74,75,86,91,92]},{\"tag\":\"block\",\"leaf\":48,\"vertices\":[7,18,19,22,41,48,53,55,60,65,74,75,86,92]},{\"tag\":\"block\",\"leaf\":49,\"vertices\":[7,16,18,22,41,48,53,55,60,65,73,75,86,92]},{\"tag\":\"block\",\"leaf\":50,\"vertices\":[12,16,21,22,41,48,50,53,55,60,73,77,86,92]},{\"tag\":\"block\",\"leaf\":51,\"vertices\":[8,16,20,21,41,48,50,53,60,64,73,77,86,92]},{\"tag\":\"edge\",\"edge\":28,\"owners\":[4,9,16,36,41,53,56,63,70,74,80,89,90]},{\"tag\":\"edge\",\"edge\":32,\"owners\":[17,21,28,35,44,46,52,58,62,66,69,75,77,79,80,83,85,86,88,90,92]},{\"tag\":\"edge\",\"edge\":33,\"owners\":[5,11,18,36,48,53,59,63,70,77,80,89,90]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[13,14,32,39,45,50,60,65,67,76,82,84,85,87,92]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[7,14,42,47,50,65,67,82,84,86,87,92]}]}"
  "663 -149 0 467 463 0\n664 168 0 544 539 0\n665 178 0 544 542 0\n666 165 0 664 511 0\n667 175 0 665 535 0\n668 -205 0 605 601 0\n669 -197 0 605 604 0\n670 45 198 195 0 585 578 551 584 583 554 582 558 378 589 567 369 590 564 579 547 549 553 559 376 368 548 556 355 561 358 370 367 354 356 659 0\n671 -45 192 0 578 551 550 579 546 549 381 340 547 336 339 335 25 26 154 175 337 334 338 661 0\n672 82 192 0 578 551 550 579 546 549 381 340 548 299 339 300 341 298 338 662 0\n673 195 0 668 585 671 670 600 595 672 380 577 572 593 0\n674 -204 0 673 605 602 0\n675 -202 0 674 598 0\n676 -200 0 675 595 0\n677 -82 0 676 380 577 572 593 0\n678 -40 0 677 379 0\n679 192 0 677 672 0\n680 84 87 92 0 677 341 300 387 339 299 340 298 338 662 0\n681 -58 -159 0 74 75 77 106 485 0\n682 43 -77 -73 -64 -56 -88 -49 -60 -152 -15 -84 0 605 679 217 182 176 32 63 242 100 66 574 592 594 597 603 586 583 555 90 213 280 86 381 179 302 470 630 0\n683 65 87 92 0 677 605 679 544 680 574 592 594 597 603 586 583 555 554 187 184 176 183 488 522 529 538 540 507 182 180 178 177 341 300 339 335 342 468 492 493 510 509 541 502 504 536 533 497 498 527 525 516 517 519 681 481 85 86 88 90 472 381 32 34 38 483 213 214 216 217 227 280 479 63 67 71 485 477 144 242 475 682 606 238 0\n684 56 5 90 10 37 42 17 63 70 74 80 89 0 658 317 0\n685 -27 194 0 583 556 555 582 561 560 4 19 67 124 141 271 273 315 684 0\n686 176 70 74 -55 -60 -65 -84 48 46 0 665 544 187 186 365 185 184 364 223 72 60 90 88 85 112 381 297 114 111 179 536 532 541 516 510 513 479 494 502 504 54 122 241 317 470 472 497 498 475 650 477 0\n687 -37 41 30 43 -169 38 48 46 0 11 20 38 470 472 494 502 509 0\n688 -55 -60 -65 -84 48 46 0 665 544 90 88 85 114 111 187 184 176 183 488 522 529 538 540 179 60 72 214 223 687 483 525 536 532 541 516 513 479 504 128 498 686 477 144 0\n689 173 -60 -65 -84 48 46 0 605 679 667 665 544 90 88 85 112 381 297 116 114 111 574 592 594 597 603 586 583 555 187 182 180 179 176 527 524 536 532 541 516 510 513 494 502 504 472 497 498 32 38 483 213 216 217 227 366 280 479 477 63 66 136 144 242 470 475 634 0\n690 -60 -65 -84 48 46 0 544 605 679 574 592 594 597 603 586 685 116 111 583 556 555 582 561 560 187 184 176 183 488 522 529 538 540 179 85 90 688 689 519 485 6 15 34 125 158 254 255 282 687 660 0\n691 -159 37 30 60 27 64 174 28 48 46 0 665 544 529 681 481 517 532 533 525 541 483 513 214 502 485 472 34 0\n692 37 30 60 27 64 160 28 48 46 0 667 665 522 691 519 527 524 532 483 517 215 481 0\n693 -41 60 27 64 160 28 0 665 15 60 76 485 481 519 517 527 532 0\n694 30 60 27 64 43 160 38 28 48 46 0 544 693 522 529 538 540 692 687 0\n695 87 92 0 677 605 679 335 300 680 176 177 179 183 184 187 574 488 592 594 597 603 586 582 583 560 561 555 556 683 111 116 685 690 694 7 12 35 81 159 278 283 281 286 660 0\n696 -30 194 0 583 556 555 582 561 560 7 12 35 81 159 278 283 281 286 660 0\n697 59 -42 -49 -67 -88 -64 -8 60 -87 0 665 544 669 550 386 547 580 588 583 556 103 224 209 205 191 204 488 522 529 192 106 481 517 533 541 513 504 498 477 144 217 274 497 216 210 475 213 212 531 515 555 206 479 322 280 629 0\n698 43 48 60 92 0 605 669 665 544 695 550 386 547 580 588 696 587 603 597 596 570 583 556 209 205 191 204 488 522 529 538 540 685 197 195 194 193 192 339 335 304 694 100 103 104 106 116 224 687 481 517 532 533 525 541 483 510 513 210 216 217 493 494 502 504 468 472 497 498 477 134 144 470 475 258 274 697 260 306 624 0\n699 -17 -59 -77 -73 -49 -67 -88 -64 37 -43 -87 0 669 605 550 386 547 580 587 603 597 596 570 104 103 195 194 193 191 306 83 213 24 588 583 556 582 561 560 272 316 615 0\n700 -59 -77 -73 -49 -67 -88 -64 37 -43 -87 0 669 144 217 24 550 386 547 580 588 583 556 555 582 561 560 83 699 271 315 684 0\n701 37 48 60 92 0 669 665 544 698 111 24 695 550 386 547 580 588 696 583 555 582 561 685 209 205 191 204 488 522 529 531 206 192 339 335 692 103 106 224 481 517 515 532 533 525 541 483 510 513 210 212 213 216 217 493 502 504 468 472 497 498 477 144 475 700 479 322 280 270 318 614 0\n702 -179 60 -87 0 209 205 191 204 488 522 529 192 536 533 527 517 519 481 681 0\n703 48 60 92 0 669 544 695 702 541 513 502 550 386 547 580 588 696 335 701 472 38 0\n704 -37 41 43 -152 38 0 11 20 470 0\n705 -176 37 64 54 -155 -154 -87 0 669 550 386 547 580 588 685 209 205 191 204 488 522 527 525 519 483 210 214 216 217 227 485 477 158 144 475 0\n706 60 92 0 669 544 665 667 695 550 386 547 580 588 685 209 205 191 204 488 197 192 339 702 541 510 513 493 494 504 497 498 703 30 118 468 114 116 693 704 705 532 517 481 215 681 483 519 524 0\n707 -48 -77 -42 -73 -56 -23 -88 29 -65 37 92 0 669 695 550 386 547 580 588 582 560 706 90 213 327 156 217 203 191 210 63 242 583 554 200 196 192 245 616 0\n708 159 176 -152 41 64 43 37 92 0 669 665 544 667 339 706 119 536 541 510 493 468 114 513 504 498 497 502 532 516 90 88 695 550 386 547 580 588 696 582 560 209 205 191 204 488 203 198 197 335 486 519 524 483 210 213 216 217 227 366 479 477 63 66 144 242 470 475 327 707 472 304 635 0\n709 48 -22 -159 -155 -154 -65 -153 -156 -152 41 64 43 92 0 669 114 706 90 88 695 550 386 547 580 588 696 685 209 208 203 197 191 335 472 304 32 34 485 72 223 365 479 477 122 128 240 241 144 242 470 475 651 0\n710 -77 176 -152 41 64 43 37 92 0 669 544 665 532 516 536 541 513 502 339 706 119 510 493 468 504 497 498 708 695 550 386 547 580 588 582 560 205 203 521 528 484 321 709 43 114 90 88 685 209 208 197 158 161 287 485 72 223 365 479 477 241 317 617 470 0\n711 -55 24 74 69 77 -87 37 0 665 544 230 706 90 88 209 205 191 204 488 522 72 214 483 525 536 532 541 516 513 479 504 128 497 475 0\n712 -29 77 -48 -87 37 0 669 43 550 386 547 580 588 583 556 582 561 230 706 94 384 90 6 125 248 254 255 660 0\n713 77 -48 -155 54 -159 -152 41 64 43 -87 37 0 669 550 386 547 580 588 685 197 712 485 223 477 134 137 144 470 711 17 0\n714 -77 -155 54 -152 41 64 43 -87 37 0 230 476 710 705 0\n715 -176 48 -155 54 -159 64 -87 37 0 669 544 209 205 191 204 488 522 529 538 540 512 550 386 547 580 588 685 230 706 85 201 525 705 483 497 214 501 485 472 34 0\n716 -155 -65 -159 -152 41 64 43 -87 37 0 665 544 114 521 230 706 94 384 205 203 714 713 715 536 532 528 541 516 484 513 321 502 504 709 497 0\n717 -88 -159 64 -87 37 0 669 550 386 547 580 588 583 556 582 561 685 230 706 94 384 90 213 214 217 485 6 34 158 254 282 660 0\n718 -159 -152 41 64 43 -87 37 0 544 230 706 119 209 205 191 204 488 522 202 717 483 525 536 541 510 513 493 504 468 498 716 0\n719 -152 41 64 43 -87 37 0 209 205 191 204 488 230 718 519 708 527 0\n720 152 64 -87 37 0 544 209 205 191 204 488 522 529 538 540 507 230 706 119 202 494 492 510 509 468 541 504 114 536 497 498 705 0\n721 64 43 -87 37 0 669 667 665 544 550 386 547 580 588 685 230 706 90 88 209 205 191 204 488 720 719 15 60 136 485 519 527 524 536 532 483 541 516 213 227 513 479 504 71 498 477 0\n722 49 43 -87 37 0 669 544 230 706 94 384 90 209 205 191 204 488 522 202 119 721 116 468 493 510 541 536 525 483 213 529 538 540 509 504 497 224 103 498 477 137 217 210 144 475 327 550 386 547 580 588 583 556 100 507 492 197 134 470 274 88 533 516 479 502 199 193 330 85 201 472 287 619 0\n723 43 -87 37 0 669 544 678 209 205 191 204 488 522 529 538 540 507 550 386 547 580 588 583 556 230 706 94 384 119 90 88 202 199 197 195 193 721 100 103 116 224 330 468 492 493 510 509 541 504 536 533 497 498 525 516 477 483 134 137 144 210 213 217 470 475 479 274 327 722 290 631 0\n724 -87 37 0 544 191 201 202 203 204 205 209 230 386 488 706 522 85 88 90 94 119 529 538 540 723 24 30 111 295 468 493 510 509 541 502 504 536 533 472 497 498 527 525 516 32 519 483 213 216 217 227 717 479 280 103 63 270 477 242 144 607 475 0\n725 -56 -73 -88 -43 -64 37 0 669 677 544 144 219 218 217 216 213 210 116 724 341 48 468 493 510 541 295 24 172 106 695 551 388 548 580 588 582 561 560 696 300 65 83 270 318 488 522 529 538 533 540 517 509 502 504 497 475 157 327 481 612 87 472 0\n726 -25 56 -73 70 -43 37 0 669 144 24 724 695 551 388 548 580 588 583 556 555 582 561 560 1 239 244 684 0\n727 -73 -88 -43 -64 37 0 677 544 219 218 217 213 212 116 724 341 48 468 493 510 541 172 106 725 726 488 522 529 533 516 517 479 90 79 481 0\n728 -88 -43 -64 37 0 669 677 544 116 724 341 48 468 493 24 224 172 103 695 551 388 548 580 588 583 556 555 582 561 560 213 217 218 219 727 477 498 504 509 540 538 529 522 488 1 65 139 239 316 684 0\n729 70 56 -73 -154 -153 -160 -43 81 37 0 677 669 144 138 137 724 695 551 388 548 580 588 696 300 726 488 148 162 472 475 32 0\n730 56 -43 -64 37 0 669 605 544 677 224 103 116 724 341 48 468 493 728 483 526 538 540 509 504 498 477 497 502 510 541 533 517 516 536 525 522 23 172 106 695 551 388 548 580 587 603 599 590 563 588 685 729 123 127 128 243 235 479 481 90 0\n731 -43 -64 37 0 677 669 544 224 172 116 106 104 103 724 695 551 388 548 580 588 583 555 582 561 558 696 341 300 24 48 295 468 493 510 541 536 728 483 525 526 522 538 533 540 517 509 502 504 497 498 477 137 138 144 352 730 64 65 70 83 270 488 145 148 162 481 472 475 280 610 0\n732 -75 177 -70 -56 -73 43 -64 87 0 605 669 677 544 538 540 507 695 551 388 548 580 588 582 561 104 558 217 352 587 603 599 590 563 685 134 63 123 235 83 326 116 106 100 99 696 341 300 148 149 303 343 468 492 493 470 510 509 541 502 533 472 517 633 481 0\n733 -70 -56 -73 -64 37 0 677 669 605 665 544 83 65 63 138 134 731 172 116 106 104 100 99 96 724 695 551 388 548 580 587 603 599 590 563 562 597 596 569 588 583 553 582 559 376 554 558 378 561 696 685 341 300 123 160 217 326 235 483 352 526 732 371 488 344 522 525 536 532 541 517 510 513 481 493 494 502 87 468 470 472 644 0\n734 -162 -42 -77 -167 -49 -60 75 -17 -56 -73 -64 87 0 677 605 669 545 695 551 388 548 580 588 583 555 83 70 280 480 482 518 487 521 116 106 104 587 603 597 596 569 553 582 559 376 554 558 378 561 341 493 514 468 543 537 528 484 352 371 643 0\n735 -42 -167 -49 -60 160 -56 -73 -64 37 0 669 544 677 733 137 64 144 504 497 475 724 695 551 388 548 580 588 583 555 83 70 280 522 490 582 561 318 731 116 471 734 510 495 541 469 536 303 343 525 632 483 0\n736 -167 -49 -60 160 -56 -73 -64 37 0 677 669 544 724 695 551 388 548 580 588 583 555 83 70 280 522 529 538 540 507 582 561 144 733 318 64 137 134 731 116 100 99 341 504 497 475 735 470 264 270 494 492 510 468 541 611 536 483 525 0\n737 -60 -153 160 -56 -73 -64 37 0 677 605 669 544 522 529 538 540 490 724 695 551 388 548 580 588 582 561 144 733 318 83 70 478 134 731 116 100 99 96 587 603 599 590 562 583 556 555 696 341 300 87 472 280 736 513 509 505 541 493 494 499 536 468 470 476 525 285 344 483 647 0\n738 167 60 177 -64 67 0 544 538 540 116 106 513 509 541 493 533 468 517 45 481 0\n739 -153 160 -56 -73 -64 37 0 677 605 669 665 544 522 529 724 695 551 388 548 580 588 582 561 144 733 318 83 70 64 137 134 731 116 106 100 99 587 603 597 594 592 571 599 590 562 596 570 568 560 696 341 300 737 738 504 497 475 157 327 481 305 517 532 533 525 541 483 510 493 494 468 470 49 333 472 628 0\n740 160 -56 -73 -64 37 0 677 605 669 544 724 695 551 388 548 580 588 582 561 144 733 318 83 70 64 137 134 731 116 100 99 587 603 597 594 591 575 560 696 341 522 529 538 540 512 739 473 474 501 502 293 497 513 509 738 475 541 493 494 327 287 536 468 470 618 525 483 0\n741 -56 -73 -64 37 0 677 544 144 138 137 172 116 724 341 64 65 733 740 488 149 162 219 468 475 483 493 497 526 504 538 509 540 0\n742 -180 56 58 37 0 534 538 516 517 526 483 212 213 479 79 90 481 0\n743 -50 -160 72 81 0 44 149 488 0\n744 -160 -73 -64 37 0 677 544 106 741 742 540 507 144 138 137 134 731 172 116 100 99 724 341 743 468 493 492 510 509 470 541 504 17 18 497 488 145 162 219 475 483 127 128 526 533 516 517 479 481 90 0\n745 -59 -157 58 0 79 90 481 0\n746 60 -157 -153 -179 58 0 677 702 481 300 8 28 33 472 0\n747 -53 -158 0 56 213 483 0\n748 151 174 -73 -64 0 544 529 538 540 507 106 100 99 493 492 510 509 541 502 536 533 525 516 517 745 746 85 87 88 747 479 741 38 704 472 30 0\n749 -56 160 -73 -64 0 544 663 467 522 529 538 540 490 167 385 164 144 134 116 107 106 104 102 100 99 98 97 96 95 63 83 741 9 12 38 211 279 273 352 395 399 403 363 431 433 404 434 444 437 447 460 449 450 462 459 442 438 464 400 435 423 344 398 421 156 296 332 414 236 687 413 289 391 0\n750 -37 59 160 -73 -64 0 678 467 749 489 167 385 144 104 102 13 51 91 211 279 273 268 310 352 395 399 394 393 403 431 433 415 446 434 418 448 437 420 458 424 465 0\n751 88 59 160 -73 -64 0 677 669 665 544 750 724 695 551 388 548 580 588 696 116 522 748 341 468 49 45 300 731 749 490 489 167 385 165 144 137 135 134 108 107 106 104 103 102 101 100 99 97 483 352 371 525 536 532 541 516 517 510 513 481 494 502 504 88 307 470 472 497 479 17 128 317 475 657 0\n752 59 160 -73 -64 0 665 677 669 544 749 522 748 529 531 489 167 144 137 134 129 116 106 103 100 99 750 724 731 300 341 695 468 388 551 45 49 548 580 588 583 696 555 751 210 212 213 217 314 479 515 516 481 533 541 510 513 494 502 504 470 472 497 269 274 280 475 621 0\n753 160 -73 -64 0 665 544 167 144 137 135 134 116 107 106 104 103 100 99 97 489 522 529 538 540 748 749 752 78 81 82 90 93 745 706 517 228 229 388 532 533 468 738 525 541 46 48 49 333 502 504 510 306 687 472 497 494 483 470 217 269 274 475 623 0\n754 -73 -64 0 664 172 116 137 138 144 753 743 744 10 12 38 126 273 244 488 148 155 162 190 475 292 337 497 472 468 501 493 508 0\n755 153 25 74 -160 -37 -64 0 666 664 126 121 10 224 103 754 477 498 172 116 100 99 500 501 496 508 475 493 494 162 163 704 488 48 189 468 337 0\n756 -48 -37 -64 0 664 224 103 754 477 498 504 506 116 100 99 30 50 118 704 468 492 0\n757 25 74 -160 -37 -64 0 756 38 12 172 755 472 130 148 488 0\n758 74 -160 -37 -64 0 222 220 56 273 757 1 65 316 0\n759 -160 -37 -64 0 664 756 38 12 224 103 754 477 498 172 116 758 139 143 743 488 148 155 190 472 337 501 468 508 493 0\n760 -37 -64 0 544 224 103 754 477 498 504 513 541 106 12 38 756 759 522 529 538 533 540 517 512 501 472 746 87 0\n761 -74 160 -64 0 544 669 677 224 103 754 477 498 504 760 724 341 522 529 738 87 300 695 551 388 548 580 588 696 538 540 512 501 472 100 88 513 541 533 516 536 525 747 90 479 66 99 731 509 494 470 258 583 555 280 116 493 468 483 490 373 361 98 97 96 261 345 645 0\n762 160 -64 0 677 669 544 760 724 695 551 388 548 580 588 583 555 582 561 696 341 300 731 224 103 754 477 498 504 513 541 536 361 116 105 100 99 95 522 529 525 538 533 738 747 483 540 516 87 88 90 210 216 217 512 509 479 503 501 493 494 66 496 472 468 470 280 761 353 318 475 646 0\n763 -50 -64 0 762 172 131 743 0\n764 -64 0 677 544 103 106 116 172 224 754 477 498 504 760 724 341 762 763 468 493 509 540 538 742 526 65 483 218 219 488 0\n765 -20 -42 -65 -75 -56 74 -60 -49 72 0 605 764 669 544 162 151 32 38 724 695 551 388 548 580 588 685 34 72 485 520 219 483 525 536 541 513 504 497 475 43 297 498 582 558 31 70 251 71 587 603 599 589 565 36 559 376 583 556 37 133 347 477 638 0\n766 -42 -65 -75 -56 74 -60 -49 72 81 0 605 669 544 677 764 162 151 32 38 724 695 551 388 548 580 588 685 34 72 485 520 219 483 525 536 541 513 504 497 475 43 297 582 558 31 70 251 587 603 597 594 592 573 561 765 265 362 352 637 0\n767 -56 74 -60 -49 72 81 50 -160 0 677 669 764 544 36 38 724 695 551 388 548 580 588 582 559 376 583 556 558 685 341 43 34 32 31 65 66 70 71 72 488 251 485 147 151 162 219 520 483 525 536 541 510 513 493 494 504 468 497 498 111 297 475 766 270 470 136 348 477 609 0\n768 -70 -65 172 42 -49 0 669 605 665 544 764 111 110 532 38 724 695 551 388 548 580 587 603 599 590 562 588 685 294 374 35 34 33 31 123 217 233 483 526 525 533 520 541 485 510 60 494 470 0\n769 158 70 172 74 -49 72 81 -160 0 669 665 544 764 532 38 724 695 551 388 548 580 588 685 34 32 526 525 533 520 541 485 513 59 504 488 497 151 162 475 0\n770 70 172 53 42 56 74 -49 72 81 -160 0 669 38 724 695 551 388 548 580 588 583 556 555 582 561 560 769 483 219 488 1 266 316 684 0\n771 53 42 74 -60 -49 72 81 50 -160 0 677 544 767 90 88 38 724 341 479 516 770 217 768 483 468 526 493 533 510 541 0\n772 42 74 -60 -49 72 81 50 -160 0 677 669 605 544 764 38 89 767 742 540 724 695 551 388 548 580 587 603 599 590 562 588 685 294 374 341 35 34 33 32 31 771 53 55 122 128 747 233 488 147 162 475 497 504 513 509 541 493 494 536 468 525 111 520 470 485 60 0\n773 74 72 81 -160 158 70 -65 -42 -49 0 669 544 764 32 35 31 18 488 256 162 151 150 526 538 540 512 503 43 297 114 113 36 38 724 695 551 388 548 580 588 582 559 376 583 556 685 34 33 274 769 475 516 517 496 497 745 481 504 88 767 513 479 541 536 525 520 485 223 365 477 655 0\n774 -55 -53 -60 -74 -19 -75 81 -65 -42 -49 0 605 669 36 38 724 695 551 388 548 580 588 582 559 376 22 587 603 599 589 565 37 349 43 297 365 654 0\n775 -53 -60 -74 -19 -75 72 81 88 -65 -42 -49 0 605 669 467 88 43 297 392 412 414 421 423 464 455 401 36 38 724 695 551 388 548 580 588 582 559 376 22 587 603 599 589 565 37 349 402 440 441 453 18 597 594 592 573 558 378 583 555 560 70 774 311 653 313 331 403 405 447 443 0\n776 -60 -74 -19 -75 72 81 88 -65 -42 -49 0 605 669 467 401 36 38 724 695 551 388 548 580 588 582 559 376 22 587 603 599 589 565 37 349 402 440 441 451 43 297 392 412 414 421 423 464 18 597 594 592 573 558 378 583 555 34 32 31 88 775 251 395 431 436 457 456 452 465 445 424 443 422 405 417 331 365 393 636 311 0\n777 72 81 -160 158 70 -65 -42 -49 0 669 665 544 764 526 484 114 18 38 724 695 551 388 548 580 588 685 35 34 33 32 31 488 150 256 773 144 776 481 517 532 533 525 541 520 513 485 504 223 498 477 0\n778 -72 158 54 -49 0 669 764 544 38 724 695 551 388 548 580 588 685 34 132 138 225 485 477 520 498 525 504 536 513 541 0\n779 74 -53 -60 -22 -55 -154 -81 70 -65 -42 -49 0 669 122 173 43 297 38 724 695 551 388 548 580 588 583 556 582 561 32 274 351 475 649 0\n780 -81 158 70 -65 -42 -49 0 669 605 544 764 526 538 540 512 503 484 43 297 114 258 38 724 695 551 388 548 580 587 603 597 594 591 576 599 590 563 562 36 588 582 559 376 37 558 378 685 40 34 33 173 174 226 477 498 496 504 513 541 536 533 525 516 517 520 681 485 371 745 481 61 72 479 779 261 345 648 0\n781 158 70 -65 -42 -49 0 669 667 764 665 544 43 297 114 18 16 36 38 724 695 551 388 548 580 588 582 559 376 560 685 41 35 34 33 32 484 524 778 780 777 490 522 692 519 525 88 90 321 485 536 532 72 223 365 541 516 479 513 122 504 497 498 477 144 242 652 475 0\n782 160 70 -65 -42 -49 0 605 669 764 665 544 38 724 695 551 388 548 580 588 685 34 781 483 214 485 227 216 212 747 43 297 114 18 16 587 603 599 589 565 582 559 558 41 35 33 32 31 491 692 519 366 90 251 527 536 532 541 516 513 479 504 497 498 477 144 242 639 475 0\n783 74 70 -65 -42 -49 0 544 764 669 38 781 483 212 747 724 695 551 388 548 580 588 685 34 214 485 520 529 227 114 218 18 219 782 488 173 477 498 504 513 541 533 516 215 517 745 479 583 555 280 33 481 538 540 512 503 496 216 43 297 556 37 32 274 475 350 641 0\n784 70 -65 -42 -49 0 669 605 764 544 43 297 114 258 18 38 724 695 551 388 548 580 587 603 597 594 591 576 599 590 563 562 588 583 555 685 34 33 781 747 483 212 214 215 218 219 227 485 520 529 782 488 173 477 498 504 513 541 533 516 517 745 481 280 479 783 261 345 640 0\n785 -179 -70 -49 0 669 764 38 217 483 526 128 127 724 695 551 388 548 580 588 685 34 536 533 525 516 517 520 681 485 745 72 479 0\n786 -59 -55 -10 -65 -42 -49 0 677 669 544 764 784 785 541 513 504 498 114 223 477 362 173 38 217 483 778 43 297 18 37 724 695 551 388 548 580 588 582 558 378 685 341 42 383 41 40 39 36 35 33 90 320 622 692 488 0\n787 -159 56 -65 -42 -49 0 544 669 764 665 38 724 695 551 388 548 580 588 583 555 784 128 269 785 541 513 504 498 217 483 526 531 114 778 127 43 297 18 685 34 33 681 485 223 477 173 362 786 280 479 515 516 481 532 620 525 488 522 0\n788 56 -65 -42 -49 0 665 38 784 217 483 128 127 787 520 525 532 516 517 479 84 745 0\n789 -81 -155 54 0 173 226 477 0\n790 -65 -42 -49 0 669 667 544 764 665 18 38 724 695 551 388 548 580 588 685 34 33 113 114 784 142 217 483 524 778 785 541 513 504 498 788 72 485 520 519 525 532 517 789 767 488 481 150 0\n791 -75 60 174 -49 0 665 38 33 150 219 481 483 517 525 532 0\n792 -72 54 -49 0 38 218 778 483 0\n793 -160 81 72 174 65 25 37 0 677 544 724 341 743 488 468 219 493 483 510 525 541 536 0\n794 81 -56 -42 -49 0 677 605 678 669 667 544 764 71 792 38 724 695 551 388 548 580 588 685 34 72 485 520 258 259 790 37 582 558 378 587 603 599 589 565 21 36 309 18 16 559 341 43 41 35 33 32 793 692 519 527 524 536 483 541 216 217 227 366 510 513 493 504 468 497 498 477 144 242 475 642 0\n795 -56 -42 -49 0 677 669 764 544 790 38 724 695 551 388 548 580 588 685 341 34 71 72 485 520 529 538 540 794 171 789 468 498 493 504 509 0\n796 -180 56 37 0 538 742 526 215 483 0\n797 -81 -42 -49 0 677 669 544 764 38 795 796 540 790 724 695 551 388 548 580 588 685 341 34 171 468 493 510 541 536 509 504 498 789 58 62 485 520 529 525 533 747 483 516 517 479 215 745 0\n798 -158 177 -42 -49 0 669 764 665 797 795 790 18 38 724 695 551 388 548 580 588 685 43 41 35 34 33 747 483 530 212 214 218 485 793 692 519 90 527 479 532 516 0\n799 159 158 81 65 25 37 0 677 667 544 524 724 341 520 519 525 793 536 131 541 468 510 493 0\n800 174 158 -42 -49 0 677 678 669 764 665 544 797 36 38 724 695 551 388 548 580 588 582 559 376 685 34 18 790 799 485 365 583 555 21 308 223 62 61 484 795 16 560 341 43 41 35 33 32 525 523 691 536 532 490 90 321 541 516 479 510 513 122 128 493 504 468 497 498 477 144 242 475 656 0\n801 158 -42 -49 0 677 669 764 544 797 38 795 796 540 790 18 724 695 551 388 548 580 588 685 341 34 32 799 485 62 132 223 800 522 743 488 468 151 162 493 510 509 541 504 785 497 498 475 477 144 0\n802 -42 -49 0 38 18 797 801 483 798 218 219 529 488 522 0\n803 -177 -49 0 669 764 38 724 695 551 388 548 580 588 685 34 526 529 483 520 214 485 0\n804 162 -81 58 51 53 177 0 544 538 540 510 509 541 504 533 498 516 517 789 745 71 479 0\n805 -26 70 -49 0 669 802 38 724 695 551 388 548 580 588 583 556 555 582 561 560 2 66 140 267 272 684 0\n806 -81 -158 -49 0 677 38 483 217 805 215 212 747 803 802 724 341 168 169 171 804 493 494 468 470 111 0\n807 56 -25 -158 -49 0 669 139 1 38 483 217 747 802 724 695 551 388 548 580 588 583 556 555 582 561 560 266 316 684 0\n808 -25 -158 -49 0 807 65 0\n809 -158 -49 0 677 669 605 764 665 544 467 802 38 724 695 551 388 548 580 587 603 599 589 565 597 596 570 588 582 559 558 685 341 42 383 43 41 35 34 33 32 31 747 483 212 214 217 218 219 227 485 805 806 366 405 443 808 445 488 448 692 519 90 251 527 395 536 532 431 541 516 510 513 479 494 504 63 71 270 498 390 477 406 136 242 408 399 410 433 425 464 461 438 435 398 329 295 470 0\n810 -56 25 -49 0 669 605 667 764 544 809 524 802 38 724 695 551 388 548 580 587 603 599 590 563 562 597 596 568 588 583 555 685 294 374 43 35 34 33 31 63 66 70 71 72 83 270 232 792 485 280 520 519 525 536 541 510 513 494 504 498 789 799 488 743 110 111 297 791 772 470 144 261 477 608 0\n811 174 53 -75 56 -49 0 665 809 525 791 532 88 90 516 479 0\n812 59 129 26 54 51 41 53 38 56 -49 0 669 605 544 764 803 802 38 724 695 551 388 548 580 587 603 599 589 566 588 583 555 280 479 395 516 432 533 428 541 396 510 263 494 470 0\n813 -5 53 -75 56 -49 0 677 605 669 467 544 764 174 36 38 724 695 551 388 548 580 588 582 559 376 685 34 811 520 485 365 405 443 445 448 62 61 60 150 147 803 802 587 603 599 589 566 37 558 378 583 555 341 42 383 41 40 39 2 266 390 394 406 415 408 416 410 419 426 465 458 439 430 812 745 320 517 397 533 429 541 396 510 263 494 470 0\n814 5 56 -49 0 669 802 38 724 695 551 388 548 580 588 583 556 555 582 561 560 267 272 275 276 684 0\n815 74 70 81 72 58 50 -160 -49 0 809 802 33 772 769 481 517 0\n816 41 -121 43 -74 -105 81 38 25 -49 0 669 605 678 467 38 724 695 551 388 548 580 587 603 599 590 563 294 374 562 597 596 568 35 34 33 31 810 814 257 231 390 589 565 36 588 582 559 376 685 37 32 349 237 402 389 440 407 441 409 451 411 454 427 466 0\n817 43 -60 -74 -75 25 -49 0 669 605 677 764 544 144 162 810 814 813 325 401 57 174 149 147 809 38 724 695 551 388 548 580 587 603 599 589 565 37 588 582 558 378 583 555 685 36 34 303 392 412 414 421 816 60 485 520 799 525 114 311 536 613 541 477 513 498 504 0\n818 65 73 81 50 25 -49 0 677 669 544 764 809 803 538 540 38 724 695 551 388 548 580 588 685 341 34 468 799 493 485 509 62 223 504 477 498 0\n819 -75 -160 25 -49 0 669 764 810 814 38 724 695 551 388 548 580 588 685 43 34 147 149 150 152 162 174 813 128 325 401 815 144 818 111 297 817 392 791 412 520 414 485 421 60 816 0\n820 152 -81 -49 0 677 544 171 803 538 540 507 38 724 341 494 492 509 468 504 114 498 789 0\n821 -81 26 -49 0 677 669 544 764 809 803 538 540 802 38 724 695 551 388 548 580 588 685 341 34 168 169 171 820 470 111 468 493 510 509 541 504 536 498 525 789 520 62 485 0\n822 -72 25 -49 0 810 814 2 821 131 138 792 818 114 0\n823 160 -65 26 -49 0 669 667 764 544 111 110 809 524 802 38 724 695 551 388 548 580 588 685 34 522 519 525 485 536 60 541 470 510 494 0\n824 -160 25 -49 0 822 810 814 2 821 819 488 0\n825 25 -49 0 677 669 667 764 544 809 524 802 38 724 695 551 388 548 580 588 685 341 34 810 814 2 824 522 519 823 525 485 536 60 541 510 493 494 468 47 48 470 0\n826 -49 0 669 38 724 695 388 551 548 580 588 583 555 825 1 55 65 266 814 0\n827 -25 65 0 544 669 826 1 27 44 65 153 188 191 268 796 292 337 695 540 468 388 551 493 548 509 580 502 588 472 696 0\n828 -46 -179 25 0 536 527 28 87 130 148 170 488 522 519 529 681 533 481 517 0\n829 -30 0 669 85 696 706 588 388 551 580 548 0\n830 60 -151 -157 58 65 0 706 481 229 45 468 0\n831 160 167 48 65 0 544 764 826 513 541 536 527 522 519 529 525 681 538 533 747 540 516 517 509 745 493 830 88 94 119 291 479 384 468 67 72 301 485 6 125 158 254 359 249 247 328 660 0\n832 -50 -160 0 131 171 743 0\n833 -29 53 -7 -60 0 826 94 384 90 6 125 158 254 249 247 288 328 660 0\n834 -60 -159 167 48 65 0 826 544 764 831 832 88 90 119 291 468 493 509 540 538 526 747 833 534 516 479 67 72 485 0\n835 12 90 6 37 77 53 59 70 63 80 89 0 826 660 324 0\n836 -159 167 48 65 0 669 544 831 832 681 834 706 229 388 551 468 548 493 580 509 588 540 582 583 534 538 560 561 555 556 517 526 745 481 747 5 157 279 326 277 835 0\n837 -67 0 119 229 706 0\n838 12 77 70 37 59 53 0 669 724 695 551 388 548 580 588 583 556 555 582 561 560 277 835 0\n839 -46 65 0 837 544 827 49 828 468 541 493 510 0\n840 167 48 65 0 544 837 831 836 832 520 468 529 493 538 509 540 0\n841 48 65 0 826 829 839 472 502 840 0\n842 65 0 677 837 829 544 764 827 841 29 50 228 300 468 706 192 193 204 205 209 724 493 88 90 488 9 56 250 246 510 522 234 541 529 536 533 527 516 519 479 485 72 0\n843 -31 0 842 109 0\n844 -38 0 842 110 0\n845 -43 0 842 111 0\n846 -54 0 842 114 0\n847 -61 0 842 115 0\n848 -66 0 842 117 0\n849 -47 0 848 382 0\n850 -179 -48 0 829 843 848 847 677 764 300 205 191 204 228 372 488 522 529 29 192 724 9 246 234 250 56 706 90 88 536 533 527 516 519 479 485 72 0\n851 77 -164 -48 0 764 829 843 848 847 665 544 845 844 677 846 842 498 300 724 20 11 850 541 510 494 470 136 477 497 228 706 88 90 56 205 191 204 372 488 29 192 9 246 234 250 60 485 519 527 532 516 479 203 220 211 321 279 222 126 121 52 10 181 336 284 475 360 626 0\n852 -164 -48 0 605 544 845 844 764 829 843 848 847 665 677 846 842 228 706 88 90 300 724 56 205 191 204 372 488 29 192 9 246 234 250 20 11 850 541 510 494 470 60 485 519 527 532 516 479 136 550 181 336 547 580 587 603 599 590 563 203 220 211 321 279 207 194 498 477 851 262 346 627 0\n853 -48 0 544 850 541 852 513 504 0\n854 8 0 853 842 297 0\n855 173 37 60 28 0 667 665 527 524 532 483 517 215 481 0\n856 -46 -56 0 842 544 844 845 764 848 312 92 83 72 70 68 67 65 28 87 130 148 170 828 488 541 693 510 494 704 855 519 681 485 319 125 158 253 838 0\n857 -29 37 -56 0 669 724 695 551 388 548 580 588 582 561 221 83 70 6 125 158 838 323 0\n858 37 -56 0 829 853 826 764 544 846 856 472 502 513 541 536 527 72 67 65 857 485 520 519 529 525 538 483 540 218 219 512 488 501 789 498 0\n859 159 -56 0 847 544 844 845 846 826 853 849 848 829 842 854 73 375 67 66 63 858 9 235 83 279 166 126 121 856 472 502 513 541 536 527 312 69 377 65 64 520 519 529 538 533 540 517 512 687 501 76 136 169 497 498 481 477 291 252 225 488 162 357 369 256 475 625 0\n860 -56 0 764 67 72 858 859 485 6 158 284 0\n861 -172 58 -37 0 860 56 51 516 517 479 745 0\n862 -41 -159 27 0 764 15 60 485 0\n863 -159 -37 0 860 853 844 845 829 544 91 13 14 166 552 120 220 52 222 557 581 685 268 1 681 861 534 540 862 704 687 494 828 510 541 0\n864 41 -37 0 860 853 844 845 829 544 863 520 529 538 540 268 1 704 687 494 828 510 541 0\n865 -37 0 860 665 544 826 853 829 268 1 863 520 529 864 76 169 861 532 533 527 541 519 513 502 472 130 148 488 0\n866 -87 0 865 724 0\n867 -180 0 865 860 796 0\n868 92 0 866 695 0\n869 169 0 867 544 540 0\n870 86 0 868 388 0\n871 184 0 868 551 0\n872 166 0 869 512 0\n873 183 0 870 548 0\n874 193 0 873 871 580 0\n875 -194 0 874 669 588 0\n876 -27 0 875 685 0\n877 -46 -41 0 764 876 169 27 28 87 130 148 693 488 0\n878 -41 0 876 826 853 829 872 544 846 865 136 862 520 877 472 502 501 513 498 541 477 536 227 525 483 0\n879 -75 153 0 872 544 865 876 764 860 846 502 513 541 536 501 498 497 146 150 151 162 219 483 526 525 533 520 516 517 485 745 61 223 479 477 54 128 144 475 0\n880 -72 -155 0 846 138 225 477 0\n881 160 -179 0 865 860 536 527 522 519 529 525 681 533 747 483 516 517 212 745 479 0\n882 153 0 872 869 544 846 878 844 845 502 501 513 509 498 541 494 789 879 880 881 488 3 18 470 0\n883 46 0 882 829 853 826 472 0\n884 -25 0 883 27 0\n885 -28 0 883 28 0\n886 -60 0 883 87 0\n887 -72 0 883 130 0\n888 -75 0 883 148 0\n889 -81 0 883 170 0\n890 -160 0 884 888 887 889 488 0\n891 173 0 886 865 885 855 0\n892 -174 0 890 522 0\n893 159 0 890 891 519 0\n894 -177 0 892 529 0\n895 -58 0 893 681 0\n896 171 0 894 665 531 0\n897 -157 0 895 886 885 481 0\n898 -172 0 897 517 0\n899 156 0 897 896 515 0\n900 176 0 898 665 532 0\n901 158 0 900 892 525 0\n902 -53 0 901 747 0\n903 88 0 901 865 483 0\n904 -51 0 903 212 0\n905 -55 0 903 214 0\n906 59 0 904 902 899 860 479 0\n907 29 0 905 893 764 876 485 0\n908 0 906 907 80 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record000.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record000.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record000.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record000.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record000 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeafTable : ConcreteGrowth.Table (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record000.l) :=
(.branch 26
 (.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (⟨0, by decide⟩))
 (.branch 2
 (.leaf (⟨1, by decide⟩))
 (.leaf (⟨2, by decide⟩))))
 (.branch 4
 (.leaf (⟨3, by decide⟩))
 (.branch 5
 (.leaf (⟨4, by decide⟩))
 (.leaf (⟨5, by decide⟩)))))
 (.branch 9
 (.branch 7
 (.leaf (⟨6, by decide⟩))
 (.branch 8
 (.leaf (⟨7, by decide⟩))
 (.leaf (⟨8, by decide⟩))))
 (.branch 11
 (.branch 10
 (.leaf (⟨9, by decide⟩))
 (.leaf (⟨10, by decide⟩)))
 (.branch 12
 (.leaf (⟨11, by decide⟩))
 (.leaf (⟨12, by decide⟩))))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf (⟨13, by decide⟩))
 (.branch 15
 (.leaf (⟨14, by decide⟩))
 (.leaf (⟨15, by decide⟩))))
 (.branch 17
 (.leaf (⟨16, by decide⟩))
 (.branch 18
 (.leaf (⟨17, by decide⟩))
 (.leaf (⟨18, by decide⟩)))))
 (.branch 22
 (.branch 20
 (.leaf (⟨19, by decide⟩))
 (.branch 21
 (.leaf (⟨20, by decide⟩))
 (.leaf (⟨21, by decide⟩))))
 (.branch 24
 (.branch 23
 (.leaf (⟨22, by decide⟩))
 (.leaf (⟨23, by decide⟩)))
 (.branch 25
 (.leaf (⟨24, by decide⟩))
 (.leaf (⟨25, by decide⟩)))))))
 (.branch 39
 (.branch 32
 (.branch 29
 (.branch 27
 (.leaf (⟨26, by decide⟩))
 (.branch 28
 (.leaf (⟨27, by decide⟩))
 (.leaf (⟨28, by decide⟩))))
 (.branch 30
 (.leaf (⟨29, by decide⟩))
 (.branch 31
 (.leaf (⟨30, by decide⟩))
 (.leaf (⟨31, by decide⟩)))))
 (.branch 35
 (.branch 33
 (.leaf (⟨32, by decide⟩))
 (.branch 34
 (.leaf (⟨33, by decide⟩))
 (.leaf (⟨34, by decide⟩))))
 (.branch 37
 (.branch 36
 (.leaf (⟨35, by decide⟩))
 (.leaf (⟨36, by decide⟩)))
 (.branch 38
 (.leaf (⟨37, by decide⟩))
 (.leaf (⟨38, by decide⟩))))))
 (.branch 45
 (.branch 42
 (.branch 40
 (.leaf (⟨39, by decide⟩))
 (.branch 41
 (.leaf (⟨40, by decide⟩))
 (.leaf (⟨41, by decide⟩))))
 (.branch 43
 (.leaf (⟨42, by decide⟩))
 (.branch 44
 (.leaf (⟨43, by decide⟩))
 (.leaf (⟨44, by decide⟩)))))
 (.branch 48
 (.branch 46
 (.leaf (⟨45, by decide⟩))
 (.branch 47
 (.leaf (⟨46, by decide⟩))
 (.leaf (⟨47, by decide⟩))))
 (.branch 50
 (.branch 49
 (.leaf (⟨48, by decide⟩))
 (.leaf (⟨49, by decide⟩)))
 (.branch 51
 (.leaf (⟨50, by decide⟩))
 (.leaf (⟨51, by decide⟩))))))))
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record000.l := originalLeafTable.get j.val
def orbitWordTable : ConcreteGrowth.Table (List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record000.g)) :=
(.branch 26
 (.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([]))
 (.branch 2
 (.leaf ([]))
 (.leaf ([]))))
 (.branch 4
 (.leaf ([]))
 (.branch 5
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 9
 (.branch 7
 (.leaf ([]))
 (.branch 8
 (.leaf ([]))
 (.leaf ([]))))
 (.branch 11
 (.branch 10
 (.leaf ([]))
 (.leaf ([])))
 (.branch 12
 (.leaf ([]))
 (.leaf ([]))))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf ([]))
 (.branch 15
 (.leaf ([]))
 (.leaf ([]))))
 (.branch 17
 (.leaf ([]))
 (.branch 18
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 22
 (.branch 20
 (.leaf ([]))
 (.branch 21
 (.leaf ([]))
 (.leaf ([]))))
 (.branch 24
 (.branch 23
 (.leaf ([]))
 (.leaf ([])))
 (.branch 25
 (.leaf ([]))
 (.leaf ([])))))))
 (.branch 39
 (.branch 32
 (.branch 29
 (.branch 27
 (.leaf ([]))
 (.branch 28
 (.leaf ([]))
 (.leaf ([]))))
 (.branch 30
 (.leaf ([]))
 (.branch 31
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 35
 (.branch 33
 (.leaf ([]))
 (.branch 34
 (.leaf ([]))
 (.leaf ([]))))
 (.branch 37
 (.branch 36
 (.leaf ([]))
 (.leaf ([])))
 (.branch 38
 (.leaf ([]))
 (.leaf ([]))))))
 (.branch 45
 (.branch 42
 (.branch 40
 (.leaf ([]))
 (.branch 41
 (.leaf ([]))
 (.leaf ([]))))
 (.branch 43
 (.leaf ([]))
 (.branch 44
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 48
 (.branch 46
 (.leaf ([]))
 (.branch 47
 (.leaf ([]))
 (.leaf ([]))))
 (.branch 50
 (.branch 49
 (.leaf ([]))
 (.leaf ([])))
 (.branch 51
 (.leaf ([]))
 (.leaf ([]))))))))
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record000.g) := orbitWordTable.get j.val
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record000.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record000.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record000 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record000_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record000 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record000_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record000_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00142.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00142.record006
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "670dc9a8ea568da35a362d8ce4b8ae4789e17ae1b46b19a4e96655936595356352d58d3352d4749d1766338f1354cd38ccb392d4b32e2b4acab1ad1b26c5b31e2749ca785c9715c3723c4f07cac949164382e944d1324a9295152550d2342d90e2384d1314d0b12c2b41c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6db6d24db4da6d24d249269a49349249269a492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record006 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record006 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record006.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record006.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record006.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 50), (facetIndex 63), (facetIndex 65), (facetIndex 71)]))
 (.leaf ([(facetIndex 27), (facetIndex 35), (facetIndex 40), (facetIndex 57), (facetIndex 75)])))
 (.branch 3
 (.leaf ([(facetIndex 29), (facetIndex 58), (facetIndex 76), (facetIndex 77)]))
 (.leaf ([(facetIndex 33), (facetIndex 36), (facetIndex 49), (facetIndex 54)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 56), (facetIndex 59), (facetIndex 60), (facetIndex 68)]))
 (.leaf ([(facetIndex 28), (facetIndex 41), (facetIndex 43), (facetIndex 44), (facetIndex 46), (facetIndex 47)])))
 (.branch 7
 (.leaf ([(facetIndex 30), (facetIndex 32), (facetIndex 61), (facetIndex 64)]))
 (.branch 8
 (.leaf ([(facetIndex 31), (facetIndex 38), (facetIndex 51), (facetIndex 52)]))
 (.leaf ([(facetIndex 34), (facetIndex 42), (facetIndex 45)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "221000000400060064421403077030558558510703183676251z1b;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 48), (facetIndex 62), (facetIndex 70)]))
 (.leaf ([(facetIndex 53), (facetIndex 69), (facetIndex 72)])))
 (.branch 3
 (.leaf ([(facetIndex 79), (facetIndex 80)]))
 (.leaf ([(facetIndex 84), (facetIndex 85)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 39), (facetIndex 55), (facetIndex 66), (facetIndex 67)]))
 (.leaf ([(facetIndex 73), (facetIndex 74), (facetIndex 83), (facetIndex 87)])))
 (.branch 7
 (.leaf ([(facetIndex 37), (facetIndex 82), (facetIndex 86)]))
 (.branch 8
 (.leaf ([(facetIndex 78)]))
 (.leaf ([(facetIndex 81)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "563356822700055100104400000000004010000000000000406z25;"⟩
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
def grouped3_0013 : List Nat := [0]
def grouped3_0014 : List Nat := [0, 1]
def grouped3_0015 : List Nat := [0, 1, 2, 3]
def grouped3_0017 : List Nat := [1]
def grouped3_0018 : List Nat := [2]
def grouped3_0019 : List Nat := [2, 3]
def grouped3_0020 : List Nat := [3]
def grouped3_0021 : List Nat := [4, 5]
def grouped3_0022 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0023 : List Nat := [6]
def grouped3_0024 : List Nat := [6, 7, 8]
def grouped3_0025 : List Nat := [7]
def grouped3_0026 : List Nat := [7, 8]
def grouped3_0027 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record006 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record006_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00142.record006" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00142.record006" 51

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00142.record006" "{\"ridges\":[[10,545],[10,546],[19,200],[20,208],[36,545],[36,546],[44,545],[44,546],[45,200],[49,545],[49,546],[50,208],[53,226],[54,545],[54,546],[59,200],[62,564],[63,208],[65,208],[68,200],[69,616],[70,688],[71,208],[72,736],[80,564],[85,616]],\"owners\":[[10,545,[62,69,70,72],[36,44,49,54]],[36,545,[69,70,72],[10,44,49,54,62]],[44,545,[62,70,72],[10,36,49,54,69]],[49,545,[69,72],[10,36,44,54,62,70]],[54,545,[62,70],[10,36,44,49,69,72]],[10,546,[80,85],[36,44,49,54]],[36,546,[85],[10,44,49,54,80]],[44,546,[80],[10,36,49,54,85]],[49,546,[85],[10,36,44,54,80]],[54,546,[80],[10,36,44,49,85]],[19,200,[78,82,84,86],[45,59,65,68]],[45,200,[86],[19,59,65,68,78,82,84]],[59,200,[82,84],[19,45,65,68,78,86]],[68,200,[78,82,86],[19,45,59,65,84]],[20,208,[81,82,86],[50,63,65,71]],[50,208,[86],[20,63,65,71,81,82]],[63,208,[82],[20,50,65,71,81,86]],[65,208,[81],[20,50,63,71,82,86]],[71,208,[81,82,86],[20,50,63,65]],[53,226,[84],[]],[62,564,[80],[]],[80,564,[62],[]],[69,616,[85],[]],[85,616,[69],[]],[70,688,[],[]],[72,736,[],[]]],\"edges\":[[38,[10,36,44,49,54,62,69,70,72,80,85]],[39,[19,20,37,45,50,53,59,63,65,68,71,72,78,81,82,84,86]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00142.record006" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00142.record006\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-27,-4],[-27,-7],[-1,15,19,20,22],[-5,19,20,22],[-8,15,20,22],[-10,19,22],[-13,15,20],[-1,24,28],[-5,28],[-8,24],[-10,28],[-13,24],[-2,23,26,27,29],[-9,29],[-14,26,27],[-18,23,26,29],[-3,25,26,29],[-11,29],[-16,26],[-17,25],[-21,25,26,29],[-12,27],[-15,24],[-24,15],[-19,28],[-28,19],[-20],[-22],[-30,11,16,17,21],[-31,4,7,9],[-32,30],[-33,32],[-34,31],[-35,34],[-36,35],[-37,33,36],[37],[-15,38],[-19,39],[-24,40],[-28,41],[-6,42],[-26,42],[-29,42],[-23,43],[-25,44],[-39,45],[-38,45],[-41,46],[-40,46],[-45,-46,47],[-44,48],[-43,48],[-48,49],[-42,49],[-49,50],[-47,-50,51],[-51],[1,5,8,10,13,15,19,20,22,24,28],[2,3,6,9,11,12,14,16,17,18,21,22,23,25,26,27,29]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":84,\"b\":34},{\"tag\":\"incompatible\",\"a\":84,\"b\":42},{\"tag\":\"mate\",\"ridge\":545,\"a\":10,\"owners\":[62,69,70,72]},{\"tag\":\"mate\",\"ridge\":545,\"a\":36,\"owners\":[69,70,72]},{\"tag\":\"mate\",\"ridge\":545,\"a\":44,\"owners\":[62,70,72]},{\"tag\":\"mate\",\"ridge\":545,\"a\":49,\"owners\":[69,72]},{\"tag\":\"mate\",\"ridge\":545,\"a\":54,\"owners\":[62,70]},{\"tag\":\"mate\",\"ridge\":546,\"a\":10,\"owners\":[80,85]},{\"tag\":\"mate\",\"ridge\":546,\"a\":36,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":546,\"a\":44,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":546,\"a\":49,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":546,\"a\":54,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":200,\"a\":19,\"owners\":[78,82,84,86]},{\"tag\":\"mate\",\"ridge\":200,\"a\":45,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":200,\"a\":59,\"owners\":[82,84]},{\"tag\":\"mate\",\"ridge\":200,\"a\":68,\"owners\":[78,82,86]},{\"tag\":\"mate\",\"ridge\":208,\"a\":20,\"owners\":[81,82,86]},{\"tag\":\"mate\",\"ridge\":208,\"a\":50,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":208,\"a\":63,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":208,\"a\":65,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":208,\"a\":71,\"owners\":[81,82,86]},{\"tag\":\"mate\",\"ridge\":226,\"a\":53,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":564,\"a\":62,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":564,\"a\":80,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":616,\"a\":69,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":616,\"a\":85,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":688,\"a\":70,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":736,\"a\":72,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[50,63,65,71],\"full_literals\":[-30,11,16,17,21]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[34,42,45],\"full_literals\":[-31,4,7,9]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-32,30,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-33,32,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-34,false,31],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-35,false,34],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-36,false,35],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-37,33,36],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":62,\"full_literals\":[-15,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":69,\"full_literals\":[-19,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":80,\"full_literals\":[-24,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":85,\"full_literals\":[-28,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":37,\"full_literals\":[-6,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":82,\"full_literals\":[-26,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":86,\"full_literals\":[-29,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":78,\"full_literals\":[-23,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":81,\"full_literals\":[-25,44]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-39,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-45,-46,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-44,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-43,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-48,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-49,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-47,-50,51],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":38,\"owners\":[10,36,44,49,54,62,69,70,72,80,85]},{\"tag\":\"edge\",\"edge\":39,\"owners\":[19,20,37,45,50,53,59,63,65,68,71,72,78,81,82,84,86]}]}"
  "61 1 5 8 10 13 15 19 24 28 0 27 28 59 0\n62 2 3 6 9 11 12 14 16 17 18 21 23 25 26 27 29 0 28 60 0\n63 46 0 49 50 41 40 9 11 25 8 10 12 23 61 0\n64 45 0 28 27 47 48 39 38 4 6 26 3 5 7 24 61 0\n65 47 0 64 63 51 0\n66 -50 0 65 58 57 0\n67 -49 0 66 56 0\n68 -48 0 67 54 0\n69 -42 0 67 55 0\n70 -44 0 68 52 0\n71 -43 0 68 53 0\n72 -6 0 69 42 0\n73 -26 0 69 43 0\n74 -29 0 69 44 0\n75 -25 0 70 46 0\n76 -23 0 71 45 0\n77 -16 0 73 19 0\n78 -9 0 74 14 0\n79 -11 0 74 18 0\n80 -3 0 75 73 74 17 0\n81 -17 0 75 20 0\n82 -21 0 75 73 74 21 0\n83 -18 0 76 73 74 16 0\n84 -30 0 82 77 81 79 29 0\n85 -32 0 84 31 0\n86 -33 0 85 32 0\n87 36 0 86 37 36 0\n88 35 0 87 35 0\n89 34 0 88 34 0\n90 31 0 89 33 0\n91 27 0 74 81 73 75 76 82 83 80 77 79 78 72 22 15 13 62 0\n92 -4 0 91 1 0\n93 -7 0 91 2 0\n94 0 93 92 90 78 30 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record006.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record006.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record006.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record006.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record006 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record006.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record006.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record006.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record006.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record006 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record006_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record006 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record006_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record006_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00142.record006
