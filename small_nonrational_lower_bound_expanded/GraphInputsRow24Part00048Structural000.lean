module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00048Data
public import GraphInputsRow24Part00048Frames
public import GraphInputsRow24Part00048Leaves
public import GraphInputsRow24Part00048Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record003
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 108227128545247232, (certNat% 3), 4507997673881600, (certNat% 4), (certNat% 5)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), (certNat% 7), (certNat% 8), (certNat% 9), (certNat% 5), 8623489024]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 11), (certNat% 12), 36174003420790784, 86975786057203712]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 14), 73183519714574336, (certNat% 15), (certNat% 16), 35459249995776]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), (certNat% 7), (certNat% 18), (certNat% 19), (certNat% 20), (certNat% 21)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), (certNat% 23), (certNat% 24), 112590070141157376, 140737521909760, (certNat% 21)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), (certNat% 16), 4503609291046912, (certNat% 27), 18023778718056448]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), (certNat% 16), (certNat% 29), 86975767803592704, (certNat% 18)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 30), (certNat% 31), (certNat% 32), 112590070141157376, 10414592391905280]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), (certNat% 34), (certNat% 35), 18829279232000, 86975794647138304, (certNat% 36), 36028866006876160]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c12 c5
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c13 c4
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c14 c3
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c15 c2
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c16 c1
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c17 c0
  c18
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record003_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record014
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record014
def vertexColumn : Fields := ⟨10, (certNat% 37)⟩
def kindColumn : Fields := ⟨3, (certNat% 38)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c2 c2
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 39), (certNat% 40), 1126002986057728, (certNat% 41)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 42)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c1 c6
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c1 c7
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 43), 171798691840]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c1 c6
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c9 c11
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 44), 144150372447944704, 1125899906842624]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c14 c10
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c1 c6
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c16 c16
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 45), 171798691840, (certNat% 40)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), 1125899906842624, (certNat% 47), (certNat% 48)]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c21 c15
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 49), 1126002986057728, 45035996273704960, 412316860416, (certNat% 50)]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c23 c22
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c24 c5
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 51), (certNat% 52), 412316860416, (certNat% 53), (certNat% 54), (certNat% 55)]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c26 c25
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 56), (certNat% 57), 547608330240, 3536029394927616, (certNat% 58), (certNat% 59), 81074139141505024]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c28 c27
  c29
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record014_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record014_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record014_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record014_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record014_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record014_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record014_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record014_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record014_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record014

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record002
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "5d1acb89aa66a5a699361d98e9392e2b91e17ae15c7896a599965a5595554d4756364d4b4ad176c3a8da398ce364e534cc7362e4b4acab86d1b26c5b61e4749ca745c3783d0f23c4f0bd1ca28661581e686896251949465454554341da0e4328c6314e0b22c1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6d36da4da49a4924d349249a69269249a492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record002 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record002 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record002.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record002.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record002.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 32), (facetIndex 60), (facetIndex 61), (facetIndex 62), (facetIndex 63)]))
 (.leaf ([(facetIndex 45), (facetIndex 59), (facetIndex 66), (facetIndex 67), (facetIndex 68)])))
 (.branch 3
 (.leaf ([(facetIndex 28), (facetIndex 71), (facetIndex 77)]))
 (.leaf ([(facetIndex 30), (facetIndex 33), (facetIndex 35), (facetIndex 40), (facetIndex 52), (facetIndex 72)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 36), (facetIndex 46), (facetIndex 48), (facetIndex 50), (facetIndex 51), (facetIndex 54)]))
 (.leaf ([(facetIndex 57), (facetIndex 64)])))
 (.branch 7
 (.leaf ([(facetIndex 29), (facetIndex 34), (facetIndex 42), (facetIndex 53)]))
 (.branch 8
 (.leaf ([(facetIndex 27), (facetIndex 31), (facetIndex 39), (facetIndex 41)]))
 (.leaf ([(facetIndex 38), (facetIndex 44), (facetIndex 55)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "200003200111050000105084634404041806737804363073627z1b;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 70)]))
 (.leaf ([(facetIndex 83)])))
 (.branch 3
 (.leaf ([(facetIndex 58), (facetIndex 65)]))
 (.branch 4
 (.leaf ([(facetIndex 47), (facetIndex 69)]))
 (.leaf ([(facetIndex 75), (facetIndex 80)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 78), (facetIndex 85)]))
 (.branch 7
 (.leaf ([(facetIndex 37), (facetIndex 43), (facetIndex 56)]))
 (.leaf ([(facetIndex 73), (facetIndex 74), (facetIndex 76)]))))
 (.branch 9
 (.leaf ([(facetIndex 79), (facetIndex 82), (facetIndex 84)]))
 (.branch 10
 (.leaf ([(facetIndex 49)]))
 (.leaf ([(facetIndex 81)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "5818a48507477000300020000002060000009030006000006z25;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 11
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2, 3]
def grouped2_0006 : List Nat := [4]
def grouped2_0007 : List Nat := [4, 5]
def grouped2_0008 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0009 : List Nat := [5]
def grouped2_0010 : List Nat := [6, 7, 8]
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1]
def grouped3_0013 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0015 : List Nat := [1]
def grouped3_0016 : List Nat := [2]
def grouped3_0017 : List Nat := [2, 3, 4]
def grouped3_0018 : List Nat := [3]
def grouped3_0019 : List Nat := [3, 4]
def grouped3_0020 : List Nat := [4]
def grouped3_0021 : List Nat := [5]
def grouped3_0022 : List Nat := [5, 6, 7]
def grouped3_0023 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped3_0024 : List Nat := [6]
def grouped3_0025 : List Nat := [6, 7]
def grouped3_0026 : List Nat := [7]
def grouped3_0027 : List Nat := [8]
def grouped3_0028 : List Nat := [8, 9, 10]
def grouped3_0029 : List Nat := [9]
def grouped3_0030 : List Nat := [9, 10]
def grouped3_0031 : List Nat := [10]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record002 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record002_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record002" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":10},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0030\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record002" 70

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record002" "{\"ridges\":[[10,577],[17,292],[19,392],[21,416],[35,292],[36,577],[37,390],[43,298],[44,578],[45,392],[47,306],[48,577],[51,577],[52,416],[54,577],[56,172],[57,292],[59,392],[61,292],[63,292],[64,292],[64,416],[66,385],[66,392],[67,416],[68,385],[68,392],[69,368],[79,390],[82,298],[84,172]],\"owners\":[[10,577,[58,65,70],[36,44,48,51,54]],[36,577,[65,70],[10,44,48,51,54,58]],[48,577,[58,70],[10,36,44,51,54,65]],[51,577,[58,65],[10,36,44,48,54,70]],[54,577,[58,65],[10,36,44,48,51,70]],[44,578,[83],[10,36,48,51,54,75,80]],[17,292,[74,78,79,84,85],[35,57,61,63,64]],[35,292,[84,85],[17,57,61,63,64,74,78,79]],[57,292,[78,79,85],[17,35,61,63,64,74,84]],[61,292,[74,79,84],[17,35,57,63,64,78,85]],[63,292,[74,78,79,84],[17,35,57,61,64,85]],[64,292,[74,78,85],[17,35,57,61,63,79,84]],[66,385,[21,37,52,64],[19,45,49,59,68]],[68,385,[21,37,49,52,64],[19,45,59,66]],[19,392,[76,81,82,84],[45,59,66,67,68]],[45,392,[84],[19,59,66,67,68,76,81,82]],[59,392,[81,82],[19,45,66,67,68,76,84]],[66,392,[76,82,84],[19,45,59,67,68,81]],[68,392,[76,81,82,84],[19,45,59,66,67]],[21,416,[79,82,84],[52,64,67]],[52,416,[84],[21,64,67,79,82]],[64,416,[82],[21,52,67,79,84]],[67,416,[79],[21,52,64,82,84]],[37,390,[76,79],[]],[79,390,[37,76],[]],[43,298,[74,82],[]],[82,298,[43,74],[]],[47,306,[78],[]],[56,172,[73,84],[]],[84,172,[56,73],[]],[69,368,[85],[]]],\"edges\":[[37,[17,21,35,43,47,52,57,61,63,64,67,69,74,78,79,82,84,85]],[41,[10,36,44,48,51,54,58,65,70,75,80,83]],[42,[19,21,37,45,49,52,59,64,66,67,68,76,79,81,82,84]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record002" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record002\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,19,24,29],[-6,24,29],[-12,19,29],[-14,19,24],[-16,19,24],[-9,39],[-2,31,34,35,40,41],[-5,40,41],[-18,34,35,41],[-21,31,35,40],[-22,31,34,35,40],[-23,31,34,41],[-25,4,7,15,23],[-27,4,7,13,15,23],[-3,33,37,38,40],[-10,40],[-20,37,38],[-25,33,38,40],[-27,33,37,38,40],[-4,35,38,40],[-15,40],[-23,38],[-26,35],[-7,33,35],[-35,7,33],[-8,31,38],[-38,8,31],[-11,34],[-17,30,40],[-40,17,30],[-28,41],[-42,10,20,25,26,27],[-43,18,23],[-44,42],[-45,44],[-46,43],[-47,46],[-48,45,47],[48],[-29,49],[-39,50],[-19,51],[-24,51],[-32,52],[-36,52],[-34,53],[-41,53],[-54,7,8,17],[-7,54],[-8,54],[-17,54],[-30,55],[-31,55],[-33,55],[-35,56],[-38,56],[-40,56],[-13,57],[-37,58],[-50,59],[-49,59],[-52,60],[-60,61],[-51,61],[-61,62],[-59,62],[-63,54,55],[-55,63],[-54,63],[-54,-55,64],[-63,65],[-64,66],[-53,65],[-53,-63,66],[-58,67],[-57,67],[-67,68],[-56,68],[-65,-68,69],[-66,69],[-62,-69,70],[-70],[2,4,5,8,11,15,18,21,22,23,26,28,31,34,35,38,40,41],[1,6,9,12,14,16,19,24,29,32,36,39],[3,4,7,10,13,15,20,23,25,26,27,33,35,37,38,40]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":10,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":577,\"a\":10,\"owners\":[58,65,70]},{\"tag\":\"mate\",\"ridge\":577,\"a\":36,\"owners\":[65,70]},{\"tag\":\"mate\",\"ridge\":577,\"a\":48,\"owners\":[58,70]},{\"tag\":\"mate\",\"ridge\":577,\"a\":51,\"owners\":[58,65]},{\"tag\":\"mate\",\"ridge\":577,\"a\":54,\"owners\":[58,65]},{\"tag\":\"mate\",\"ridge\":578,\"a\":44,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":292,\"a\":17,\"owners\":[74,78,79,84,85]},{\"tag\":\"mate\",\"ridge\":292,\"a\":35,\"owners\":[84,85]},{\"tag\":\"mate\",\"ridge\":292,\"a\":57,\"owners\":[78,79,85]},{\"tag\":\"mate\",\"ridge\":292,\"a\":61,\"owners\":[74,79,84]},{\"tag\":\"mate\",\"ridge\":292,\"a\":63,\"owners\":[74,78,79,84]},{\"tag\":\"mate\",\"ridge\":292,\"a\":64,\"owners\":[74,78,85]},{\"tag\":\"mate\",\"ridge\":385,\"a\":66,\"owners\":[21,37,52,64]},{\"tag\":\"mate\",\"ridge\":385,\"a\":68,\"owners\":[21,37,49,52,64]},{\"tag\":\"mate\",\"ridge\":392,\"a\":19,\"owners\":[76,81,82,84]},{\"tag\":\"mate\",\"ridge\":392,\"a\":45,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":392,\"a\":59,\"owners\":[81,82]},{\"tag\":\"mate\",\"ridge\":392,\"a\":66,\"owners\":[76,82,84]},{\"tag\":\"mate\",\"ridge\":392,\"a\":68,\"owners\":[76,81,82,84]},{\"tag\":\"mate\",\"ridge\":416,\"a\":21,\"owners\":[79,82,84]},{\"tag\":\"mate\",\"ridge\":416,\"a\":52,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":416,\"a\":64,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":416,\"a\":67,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":390,\"a\":37,\"owners\":[76,79]},{\"tag\":\"mate\",\"ridge\":390,\"a\":79,\"owners\":[37,76]},{\"tag\":\"mate\",\"ridge\":298,\"a\":43,\"owners\":[74,82]},{\"tag\":\"mate\",\"ridge\":298,\"a\":82,\"owners\":[43,74]},{\"tag\":\"mate\",\"ridge\":306,\"a\":47,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":172,\"a\":56,\"owners\":[73,84]},{\"tag\":\"mate\",\"ridge\":172,\"a\":84,\"owners\":[56,73]},{\"tag\":\"mate\",\"ridge\":368,\"a\":69,\"owners\":[85]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[45,59,66,67,68],\"full_literals\":[-42,10,20,25,26,27]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[57,64],\"full_literals\":[-43,18,23]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-44,false,42],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-45,44,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-46,false,43],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-47,46,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-48,45,47],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":70,\"full_literals\":[-29,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":83,\"full_literals\":[-39,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":58,\"full_literals\":[-19,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":65,\"full_literals\":[-24,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":75,\"full_literals\":[-32,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":80,\"full_literals\":[-36,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":78,\"full_literals\":[-34,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":85,\"full_literals\":[-41,53]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[37,43,56],\"full_literals\":[-54,7,8,17]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":37,\"full_literals\":[-7,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":43,\"full_literals\":[-8,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":56,\"full_literals\":[-17,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":73,\"full_literals\":[-30,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":74,\"full_literals\":[-31,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":76,\"full_literals\":[-33,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":79,\"full_literals\":[-35,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":82,\"full_literals\":[-38,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":84,\"full_literals\":[-40,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":49,\"full_literals\":[-13,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":81,\"full_literals\":[-37,58]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-50,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-49,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-52,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-60,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-51,false,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-61,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-59,false,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0025\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-63,54,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0025\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-55,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-54,false,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-54,-55,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-63,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-64,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-53,-63,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0030\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-58,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0030\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-57,false,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-67,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-56,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-65,-68,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0023\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-66,false,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-62,-69,70],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":37,\"owners\":[17,21,35,43,47,52,57,61,63,64,67,69,74,78,79,82,84,85]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[10,36,44,48,51,54,58,65,70,75,80,83]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[19,21,37,45,49,52,59,64,66,67,68,76,79,81,82,84]}]}"
  "86 62 0 65 66 63 64 60 61 62 42 43 41 40 44 45 1 4 5 3 2 6 84 0\n87 -69 0 86 82 81 0\n88 -66 0 87 80 0\n89 -64 0 88 72 0\n90 65 0 71 73 68 69 46 47 52 53 54 49 50 51 28 31 30 12 25 27 8 21 20 23 9 7 10 11 83 0\n91 -68 0 90 87 79 0\n92 -67 0 91 77 0\n93 -56 0 91 78 0\n94 -58 0 92 75 0\n95 -57 0 92 76 0\n96 -35 0 93 55 0\n97 -38 0 93 56 0\n98 -40 0 93 57 0\n99 -37 0 94 59 0\n100 -13 0 95 58 0\n101 -4 0 96 97 98 20 0\n102 -26 0 96 23 0\n103 -23 0 97 22 0\n104 -10 0 98 16 0\n105 -15 0 98 21 0\n106 -20 0 99 97 17 0\n107 63 0 98 97 99 96 106 102 100 103 104 105 101 68 69 54 49 18 19 15 85 0\n108 -53 0 107 88 74 0\n109 -34 0 108 46 0\n110 -41 0 108 47 0\n111 -18 0 109 96 110 9 0\n112 -43 0 111 103 33 0\n113 -46 0 112 36 0\n114 -47 0 113 37 0\n115 45 0 114 39 38 0\n116 44 0 115 35 0\n117 42 0 116 34 0\n118 55 0 107 98 97 96 52 53 54 67 29 26 24 48 0\n119 -54 0 118 89 70 0\n120 -7 0 119 49 0\n121 -27 0 120 101 100 105 103 14 0\n122 -25 0 120 101 105 103 13 0\n123 0 121 122 106 117 102 104 32 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record002.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record002.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record002.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record002.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record002 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record002.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record002.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record002.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record002.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record002 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record002_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record002 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record002_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record002_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record006
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "5713caa9aa9693ab19a6659364b86e4785e0fb89aa5a9965594e6c5655554d54d4b46d4745d0f6c3a8da364e534ce8b62e2b4acab1ae1b46c3ba1d8791cc749c6745c970dd0f13c2f07da49285a29856686494a51916585494a545455a0e4328c5382c4b0ac1b21c4709c17"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6d369b6da6da4934934d269269a6924924924924d2449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record006 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record006 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record006.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record006.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record006.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 64)]))
 (.leaf ([(facetIndex 79)])))
 (.branch 3
 (.leaf ([(facetIndex 47), (facetIndex 69), (facetIndex 70)]))
 (.leaf ([(facetIndex 82), (facetIndex 83)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 30), (facetIndex 49), (facetIndex 51)]))
 (.leaf ([(facetIndex 55), (facetIndex 58), (facetIndex 60), (facetIndex 73)])))
 (.branch 7
 (.leaf ([(facetIndex 71), (facetIndex 74), (facetIndex 75), (facetIndex 85)]))
 (.branch 8
 (.leaf ([(facetIndex 76), (facetIndex 77)]))
 (.leaf ([(facetIndex 80), (facetIndex 84)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "683308107766506220000000050500500040402z10;4z1e;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record006 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record006_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record006" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record006" 55

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record006" "{\"ridges\":[[11,641],[13,276],[18,280],[30,270],[33,276],[39,642],[41,280],[48,642],[49,306],[51,402],[53,642],[54,642],[57,280],[61,276],[62,276],[63,276],[65,280],[66,280],[70,904],[71,60],[73,270],[74,108],[75,270],[76,306],[77,402],[80,306],[84,60],[85,332]],\"owners\":[[11,641,[64,69,70],[39,48,53,54]],[39,642,[83],[11,48,53,54,79]],[48,642,[79],[11,39,53,54,83]],[53,642,[79],[11,39,48,54,83]],[54,642,[83],[11,39,48,53,79]],[13,276,[73,76,77,84,85],[33,57,61,62,63]],[33,276,[84,85],[13,57,61,62,63,73,76,77]],[61,276,[73,77,85],[13,33,57,62,63,76,84]],[62,276,[73,76,77,84],[13,33,57,61,63,85]],[63,276,[73,76,84,85],[13,33,57,61,62,77]],[18,280,[73,80,84,85],[41,57,65,66]],[41,280,[84,85],[18,57,65,66,73,80]],[57,280,[80],[18,41,65,66,73,84,85]],[65,280,[73,85],[18,41,57,66,80,84]],[66,280,[73,80,84],[18,41,57,65,85]],[30,270,[73,75],[]],[73,270,[30,75],[]],[75,270,[30,73],[]],[49,306,[76,80],[]],[76,306,[49,80],[]],[80,306,[49,76],[]],[51,402,[77],[]],[77,402,[51],[]],[71,60,[55,84],[]],[84,60,[55,71],[]],[74,108,[58],[]],[85,332,[60],[]],[70,904,[],[]]],\"edges\":[[33,[13,18,33,41,49,51,57,61,62,63,65,66,73,76,77,80,84,85]],[43,[11,39,48,53,54,64,69,70,79,83]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record006" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record006\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,20,23,24],[-6,33],[-8,31],[-11,31],[-12,33],[-2,26,29,30,34,35],[-5,34,35],[-17,26,30,35],[-18,26,29,30,34],[-19,26,29,34,35],[-3,26,32,34,35],[-7,34,35],[-14,32],[-21,26,35],[-22,26,32,34],[-4,26,28],[-26,4,28],[-28,4,26],[-9,29,32],[-29,9,32],[-32,9,29],[-10,30],[-30,10],[-25,13,34],[-34,13,25],[-27,15],[-35,16],[-24],[-20,36],[-31,37],[-23,38],[-33,39],[-40,4,9,10],[-4,40],[-9,40],[-10,40],[-13,41],[-15,41],[-16,41],[-26,41],[-42,25,27,28,35],[-25,42],[-28,42],[-35,42],[-43,29,30],[-29,43],[-30,43],[-44,32,34],[-32,44],[-34,44],[-37,45],[-36,45],[-39,46],[-38,46],[-46,47],[-45,47],[-41,48],[-40,48],[-40,-41,49],[-50,43,44],[-44,50],[-43,50],[-43,-44,51],[-52,42,50],[-50,52],[-51,53],[-42,52],[-42,-50,53],[-53,54],[-48,-52,54],[-49,54],[-47,-54,55],[-55],[2,3,5,7,9,10,14,17,18,19,21,22,26,29,30,32,34,35],[1,6,8,11,12,20,23,24,31,33]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":641,\"a\":11,\"owners\":[64,69,70]},{\"tag\":\"mate\",\"ridge\":642,\"a\":39,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":642,\"a\":48,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":642,\"a\":53,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":642,\"a\":54,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":276,\"a\":13,\"owners\":[73,76,77,84,85]},{\"tag\":\"mate\",\"ridge\":276,\"a\":33,\"owners\":[84,85]},{\"tag\":\"mate\",\"ridge\":276,\"a\":61,\"owners\":[73,77,85]},{\"tag\":\"mate\",\"ridge\":276,\"a\":62,\"owners\":[73,76,77,84]},{\"tag\":\"mate\",\"ridge\":276,\"a\":63,\"owners\":[73,76,84,85]},{\"tag\":\"mate\",\"ridge\":280,\"a\":18,\"owners\":[73,80,84,85]},{\"tag\":\"mate\",\"ridge\":280,\"a\":41,\"owners\":[84,85]},{\"tag\":\"mate\",\"ridge\":280,\"a\":57,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":280,\"a\":65,\"owners\":[73,85]},{\"tag\":\"mate\",\"ridge\":280,\"a\":66,\"owners\":[73,80,84]},{\"tag\":\"mate\",\"ridge\":270,\"a\":30,\"owners\":[73,75]},{\"tag\":\"mate\",\"ridge\":270,\"a\":73,\"owners\":[30,75]},{\"tag\":\"mate\",\"ridge\":270,\"a\":75,\"owners\":[30,73]},{\"tag\":\"mate\",\"ridge\":306,\"a\":49,\"owners\":[76,80]},{\"tag\":\"mate\",\"ridge\":306,\"a\":76,\"owners\":[49,80]},{\"tag\":\"mate\",\"ridge\":306,\"a\":80,\"owners\":[49,76]},{\"tag\":\"mate\",\"ridge\":402,\"a\":51,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":402,\"a\":77,\"owners\":[51]},{\"tag\":\"mate\",\"ridge\":60,\"a\":71,\"owners\":[55,84]},{\"tag\":\"mate\",\"ridge\":60,\"a\":84,\"owners\":[55,71]},{\"tag\":\"mate\",\"ridge\":108,\"a\":74,\"owners\":[58]},{\"tag\":\"mate\",\"ridge\":332,\"a\":85,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":904,\"a\":70,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":64,\"full_literals\":[-20,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":79,\"full_literals\":[-31,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":69,\"full_literals\":[-23,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":83,\"full_literals\":[-33,39]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[30,49,51],\"full_literals\":[-40,4,9,10]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":30,\"full_literals\":[-4,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":49,\"full_literals\":[-9,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":51,\"full_literals\":[-10,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":55,\"full_literals\":[-13,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":58,\"full_literals\":[-15,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":60,\"full_literals\":[-16,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":73,\"full_literals\":[-26,41]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[71,74,75,85],\"full_literals\":[-42,25,27,28,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":71,\"full_literals\":[-25,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":75,\"full_literals\":[-28,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":85,\"full_literals\":[-35,42]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[76,77],\"full_literals\":[-43,29,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":76,\"full_literals\":[-29,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":77,\"full_literals\":[-30,43]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[80,84],\"full_literals\":[-44,32,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":80,\"full_literals\":[-32,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":84,\"full_literals\":[-34,44]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-37,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-36,false,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-39,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-46,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-45,false,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-40,-41,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-50,43,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-44,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-43,false,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-43,-44,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-52,42,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-50,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-51,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-42,-50,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-53,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-48,-52,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-49,false,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-47,-54,55],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":33,\"owners\":[13,18,33,41,49,51,57,61,62,63,65,66,73,76,77,80,84,85]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[11,39,48,53,54,64,69,70,79,83]}]}"
  "76 1 6 8 11 12 20 23 31 33 0 28 75 0\n77 47 0 28 55 56 53 54 51 52 32 31 30 29 2 5 1 3 4 76 0\n78 -54 0 77 73 72 0\n79 -53 0 78 69 0\n80 -49 0 78 71 0\n81 -51 0 79 66 0\n82 -44 34 9 0 81 48 63 21 46 0\n83 -50 48 0 79 58 36 23 35 57 37 68 42 25 82 49 60 20 45 0\n84 -52 0 78 70 57 58 37 38 39 40 34 26 27 18 83 61 64 50 41 24 0\n85 -50 0 84 65 0\n86 -42 0 84 67 0\n87 -44 0 85 61 0\n88 -43 0 85 62 0\n89 -28 0 86 43 0\n90 -35 0 86 44 0\n91 -32 0 87 49 0\n92 -34 0 87 50 0\n93 -29 0 88 46 0\n94 -30 0 88 47 0\n95 -14 0 91 13 0\n96 -5 0 92 90 7 0\n97 -7 0 92 90 12 0\n98 -9 0 93 91 19 0\n99 -10 0 94 22 0\n100 -40 0 99 98 80 89 33 59 16 40 0\n101 -4 0 100 34 0\n102 -26 0 101 89 17 0\n103 -21 0 102 90 14 0\n104 -3 0 102 91 92 90 11 0\n105 -22 0 102 91 92 15 0\n106 -2 0 102 93 94 92 90 6 0\n107 -18 0 102 93 94 92 9 0\n108 -19 0 102 93 92 90 10 0\n109 -17 0 102 94 90 8 0\n110 0 104 109 106 96 98 99 97 95 107 108 103 105 102 93 94 91 92 90 74 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record006.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record006.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record006.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record006.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record006 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record006.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record006.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record006.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record006.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record006 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record006_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record006 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record006_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record006_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record021
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "29c6707cb49aaa687a99a961da8e6392e1ba1e2785e0fad16a5991e565a5595954756346d4749d1743db0da3a4e5334c7362d2b2ac6b16c3ba1d8791d2785c970dd0f23c4f9512ca4a5226a4619a161582e079894a499494651550d0b41d18c9314c8b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36d34d24da4924d269b4924926d24924926d2492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record021 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record021 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record021.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record021.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record021.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 63)]))
 (.leaf ([(facetIndex 78)])))
 (.branch 3
 (.leaf ([(facetIndex 82)]))
 (.leaf ([(facetIndex 38), (facetIndex 50)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 39), (facetIndex 51)]))
 (.leaf ([(facetIndex 61), (facetIndex 66)])))
 (.branch 7
 (.leaf ([(facetIndex 73), (facetIndex 80)]))
 (.branch 8
 (.leaf ([(facetIndex 60), (facetIndex 74)]))
 (.leaf ([(facetIndex 83), (facetIndex 84)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "88206010007600000050000570000000043000000000043z26;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record021 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record021_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record021" "{\"atoms\":[{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record021" 38

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record021" "{\"ridges\":[[18,385],[18,392],[27,642],[38,390],[45,385],[45,392],[49,642],[50,418],[57,385],[60,404],[64,385],[65,385],[65,392],[73,390],[76,656],[79,656],[80,418],[81,642],[83,404],[84,652]],\"owners\":[[18,385,[38,50,60],[45,57,64,65]],[45,385,[60],[18,38,50,57,64,65]],[57,385,[50],[18,38,45,60,64,65]],[64,385,[38,50],[18,45,57,60,65]],[65,385,[38,60],[18,45,50,57,64]],[18,392,[73,80,83],[45,57,64,65]],[45,392,[83],[18,57,64,65,73,80]],[65,392,[73,83],[18,45,57,64,80]],[27,642,[39,51,74],[49,76,79,81]],[49,642,[74],[27,39,51,76,79,81]],[81,642,[39,74],[27,49,51,76,79]],[76,656,[66],[27,49,61,79,81,84]],[79,656,[61,66],[27,49,76,81,84]],[38,390,[73],[]],[73,390,[38],[]],[50,418,[80],[]],[80,418,[50],[]],[60,404,[83],[]],[83,404,[60],[]],[84,652,[74],[]]],\"edges\":[[42,[18,38,45,50,57,60,64,65,73,80,83]],[43,[27,39,49,51,61,66,74,76,79,81,84]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record021" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record021\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-16,-3],[-16,-10],[-21,-16],[-1,3,7,10],[-5,10],[-9,7],[-12,3,7],[-13,3,10],[-1,15,19,21],[-5,21],[-13,15,21],[-2,4,8,16],[-6,16],[-20,4,16],[-17,14],[-18,11,14],[-3,15],[-15,3],[-7,19],[-19,7],[-10,21],[-21,10],[-22,16],[-23,3,7],[-3,23],[-7,23],[-4,24],[-8,24],[-11,25],[-14,25],[-15,26],[-19,26],[-10,27],[-16,27],[-21,28],[-23,29],[-29,30],[-25,31],[-24,31],[-27,32],[-27,-28,33],[-33,35],[-26,34],[-26,-32,35],[-35,36],[-31,-34,36],[-31,-35,37],[-37,38],[-30,-36,38],[-38],[1,3,5,7,9,10,12,13,15,19,21],[2,4,6,8,11,14,16,17,18,20,22]],\"atoms\":[{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":74,\"b\":38},{\"tag\":\"incompatible\",\"a\":74,\"b\":60},{\"tag\":\"incompatible\",\"a\":83,\"b\":74},{\"tag\":\"mate\",\"ridge\":385,\"a\":18,\"owners\":[38,50,60]},{\"tag\":\"mate\",\"ridge\":385,\"a\":45,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":385,\"a\":57,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":385,\"a\":64,\"owners\":[38,50]},{\"tag\":\"mate\",\"ridge\":385,\"a\":65,\"owners\":[38,60]},{\"tag\":\"mate\",\"ridge\":392,\"a\":18,\"owners\":[73,80,83]},{\"tag\":\"mate\",\"ridge\":392,\"a\":45,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":392,\"a\":65,\"owners\":[73,83]},{\"tag\":\"mate\",\"ridge\":642,\"a\":27,\"owners\":[39,51,74]},{\"tag\":\"mate\",\"ridge\":642,\"a\":49,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":642,\"a\":81,\"owners\":[39,74]},{\"tag\":\"mate\",\"ridge\":656,\"a\":76,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":656,\"a\":79,\"owners\":[61,66]},{\"tag\":\"mate\",\"ridge\":390,\"a\":38,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":390,\"a\":73,\"owners\":[38]},{\"tag\":\"mate\",\"ridge\":418,\"a\":50,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":418,\"a\":80,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":404,\"a\":60,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":404,\"a\":83,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":652,\"a\":84,\"owners\":[74]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[38,50],\"full_literals\":[-23,3,7]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":38,\"full_literals\":[-3,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":50,\"full_literals\":[-7,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":39,\"full_literals\":[-4,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":51,\"full_literals\":[-8,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":61,\"full_literals\":[-11,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":66,\"full_literals\":[-14,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":73,\"full_literals\":[-15,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":80,\"full_literals\":[-19,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":60,\"full_literals\":[-10,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":74,\"full_literals\":[-16,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":83,\"full_literals\":[-21,28]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-23,29],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-29,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-25,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-24,false,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-27,false,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-27,-28,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-33,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-26,false,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-26,-32,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-35,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-31,-34,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-31,-35,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-37,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-30,-36,38],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":42,\"owners\":[18,38,45,50,57,60,64,65,73,80,83]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[27,39,49,51,61,66,74,76,79,81,84]}]}"
  "53 -37 0 50 48 0\n54 16 31 0 38 29 30 16 15 39 28 27 13 23 14 12 52 0\n55 -16 23 0 25 26 7 20 6 18 2 3 5 8 4 51 0\n56 21 23 0 25 26 7 20 6 18 10 21 11 9 51 0\n57 23 0 53 55 54 47 42 56 22 35 33 41 0\n58 29 0 57 36 0\n59 30 0 58 37 0\n60 -36 0 59 50 49 0\n61 -35 0 60 45 0\n62 -3 0 60 1 17 54 31 46 43 0\n63 7 0 62 57 24 0\n64 19 0 63 19 0\n65 26 0 64 32 0\n66 34 0 65 43 0\n67 -32 0 65 61 44 0\n68 -31 0 66 60 46 0\n69 -27 0 67 40 0\n70 16 0 68 54 0\n71 0 70 69 34 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record021.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record021.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record021.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record021.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record021 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record021.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record021.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record021.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record021.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record021 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record021_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record021_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record021_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record021_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record021_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record021_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record021_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record021 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record021_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record021_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record021_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record021

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record022
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "29c1f2d26a99a1ea96958764b86e2785e0fad16a69966479996951d68d4b46d8749d1743db0da358e9364e5334c732ac6b46c5b0ee8791d2785c970dd0f23c4f9518a4a89a198560b81ea46516252926645196151542d0758348c6324c5342c8b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db49b49249249349349249a492492493492492249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record022 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record022 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record022.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record022.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record022.data.quota

def groupMembers1 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 16
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
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ([(facetIndex 16)]))
 (.leaf ([(facetIndex 17)])))
 (.branch 19
 (.leaf ([(facetIndex 18)]))
 (.leaf ([(facetIndex 19)]))))
 (.branch 22
 (.branch 21
 (.leaf ([(facetIndex 20)]))
 (.leaf ([(facetIndex 21)])))
 (.branch 23
 (.leaf ([(facetIndex 22)]))
 (.leaf ([(facetIndex 23)])))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ([(facetIndex 24)]))
 (.leaf ([(facetIndex 25)])))
 (.branch 27
 (.leaf ([(facetIndex 26)]))
 (.leaf ([(facetIndex 27)]))))
 (.branch 30
 (.branch 29
 (.leaf ([(facetIndex 28)]))
 (.leaf ([(facetIndex 29)])))
 (.branch 31
 (.leaf ([(facetIndex 30)]))
 (.leaf ([(facetIndex 31)])))))))
def groupColors1 : PackedGraphCertificate.Fields :=
  ⟨5, sparse_nat% "ffbbcdeb38bdab49ca307b9ac5a928398a418820"⟩
def grouping1 : FacetSat.Grouping data.count where
  count := 32
  members := fun g => groupMembers1.get g
  color := fun c => groupColors1.get c.val
def groupKind1 : List Nat := List.range grouping1.count

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 32), (facetIndex 39), (facetIndex 55), (facetIndex 58), (facetIndex 61), (facetIndex 63)]))
 (.leaf ([(facetIndex 35), (facetIndex 38), (facetIndex 41), (facetIndex 44), (facetIndex 46), (facetIndex 51)])))
 (.branch 3
 (.leaf ([(facetIndex 34), (facetIndex 43), (facetIndex 45), (facetIndex 52), (facetIndex 67), (facetIndex 79)]))
 (.branch 4
 (.leaf ([(facetIndex 57), (facetIndex 62), (facetIndex 66), (facetIndex 68)]))
 (.leaf ([(facetIndex 33), (facetIndex 49), (facetIndex 65), (facetIndex 78)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 70), (facetIndex 74), (facetIndex 75)]))
 (.leaf ([(facetIndex 69), (facetIndex 72), (facetIndex 73)])))
 (.branch 8
 (.leaf ([(facetIndex 36), (facetIndex 42), (facetIndex 56), (facetIndex 71)]))
 (.branch 9
 (.leaf ([(facetIndex 54), (facetIndex 59)]))
 (.leaf ([(facetIndex 37), (facetIndex 47), (facetIndex 48), (facetIndex 50)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "24005566756323400300803708021949912127100197124z21;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 64)]))
 (.branch 2
 (.leaf ([(facetIndex 77)]))
 (.leaf ([(facetIndex 81)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 40), (facetIndex 53)]))
 (.leaf ([(facetIndex 60), (facetIndex 76)])))
 (.branch 6
 (.leaf ([(facetIndex 80)]))
 (.leaf ([(facetIndex 82)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "19500c000000000004000018000000003z1e;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped1_0000 : List Nat := [0]
def grouped1_0001 : List Nat := [0, 1]
def grouped1_0002 : List Nat := [0, 1, 2, 3]
def grouped1_0003 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]
def grouped1_0004 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def grouped1_0006 : List Nat := [1]
def grouped1_0007 : List Nat := [2, 3]
def grouped1_0008 : List Nat := [4, 5, 6, 7]
def grouped1_0009 : List Nat := [8, 9, 10, 11]
def grouped1_0010 : List Nat := [8, 9, 10, 11, 12, 13, 14, 15]
def grouped1_0011 : List Nat := [12]
def grouped1_0012 : List Nat := [12, 13]
def grouped1_0013 : List Nat := [12, 13, 14, 15]
def grouped1_0014 : List Nat := [13]
def grouped1_0015 : List Nat := [14]
def grouped1_0016 : List Nat := [14, 15]
def grouped1_0017 : List Nat := [15]
def grouped1_0018 : List Nat := [16, 17]
def grouped1_0019 : List Nat := [16, 17, 18, 19]
def grouped1_0020 : List Nat := [16, 17, 18, 19, 20, 21, 22, 23]
def grouped1_0021 : List Nat := [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]
def grouped1_0022 : List Nat := [18]
def grouped1_0023 : List Nat := [18, 19]
def grouped1_0024 : List Nat := [19]
def grouped1_0025 : List Nat := [20]
def grouped1_0026 : List Nat := [20, 21]
def grouped1_0027 : List Nat := [20, 21, 22, 23]
def grouped1_0028 : List Nat := [21]
def grouped1_0029 : List Nat := [22]
def grouped1_0030 : List Nat := [22, 23]
def grouped1_0031 : List Nat := [23]
def grouped1_0032 : List Nat := [24]
def grouped1_0033 : List Nat := [24, 25]
def grouped1_0034 : List Nat := [24, 25, 26, 27]
def grouped1_0035 : List Nat := [24, 25, 26, 27, 28, 29, 30, 31]
def grouped1_0036 : List Nat := [25]
def grouped1_0037 : List Nat := [26]
def grouped1_0038 : List Nat := [26, 27]
def grouped1_0039 : List Nat := [27]
def grouped1_0040 : List Nat := [28]
def grouped1_0041 : List Nat := [28, 29]
def grouped1_0042 : List Nat := [28, 29, 30, 31]
def grouped1_0043 : List Nat := [29]
def grouped1_0044 : List Nat := [30]
def grouped1_0045 : List Nat := [30, 31]
def grouped1_0046 : List Nat := [31]
def grouped2_0047 : List Nat := [0]
def grouped2_0048 : List Nat := [0, 1]
def grouped2_0049 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0051 : List Nat := [1]
def grouped2_0052 : List Nat := [2]
def grouped2_0053 : List Nat := [2, 3, 4]
def grouped2_0054 : List Nat := [3]
def grouped2_0055 : List Nat := [3, 4]
def grouped2_0056 : List Nat := [4]
def grouped2_0057 : List Nat := [5]
def grouped2_0058 : List Nat := [5, 6]
def grouped2_0059 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0060 : List Nat := [6]
def grouped2_0061 : List Nat := [7]
def grouped2_0062 : List Nat := [7, 8, 9]
def grouped2_0063 : List Nat := [8]
def grouped2_0064 : List Nat := [8, 9]
def grouped2_0065 : List Nat := [9]
def grouped3_0066 : List Nat := [0]
def grouped3_0067 : List Nat := [0, 1, 2]
def grouped3_0069 : List Nat := [1]
def grouped3_0070 : List Nat := [1, 2]
def grouped3_0071 : List Nat := [2]
def grouped3_0072 : List Nat := [3]
def grouped3_0073 : List Nat := [3, 4]
def grouped3_0074 : List Nat := [3, 4, 5, 6]
def grouped3_0075 : List Nat := [4]
def grouped3_0076 : List Nat := [5]
def grouped3_0077 : List Nat := [5, 6]
def grouped3_0078 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record022 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record022_matrix_checked

def leafCount : Nat := 8
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaf0000 : List (Fin data.count) := [(facetIndex 12), (facetIndex 23), (facetIndex 25), (facetIndex 31), (facetIndex 51), (facetIndex 53), (facetIndex 57), (facetIndex 59), (facetIndex 63), (facetIndex 65), (facetIndex 71), (facetIndex 74), (facetIndex 79), (facetIndex 80)]
theorem leaf0000_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0000 = true := by
  decide +kernel
theorem leaf0000_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0000 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0000_counts_checked
def leaf0001 : List (Fin data.count) := [(facetIndex 12), (facetIndex 23), (facetIndex 26), (facetIndex 31), (facetIndex 51), (facetIndex 53), (facetIndex 57), (facetIndex 59), (facetIndex 63), (facetIndex 65), (facetIndex 71), (facetIndex 72), (facetIndex 79), (facetIndex 80)]
theorem leaf0001_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0001 = true := by
  decide +kernel
theorem leaf0001_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0001 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0001_counts_checked
def leaf0002 : List (Fin data.count) := [(facetIndex 12), (facetIndex 19), (facetIndex 27), (facetIndex 31), (facetIndex 51), (facetIndex 53), (facetIndex 54), (facetIndex 62), (facetIndex 63), (facetIndex 67), (facetIndex 70), (facetIndex 73), (facetIndex 78), (facetIndex 80)]
theorem leaf0002_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0002 = true := by
  decide +kernel
theorem leaf0002_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0002 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0002_counts_checked
def leaf0003 : List (Fin data.count) := [(facetIndex 12), (facetIndex 16), (facetIndex 27), (facetIndex 31), (facetIndex 51), (facetIndex 53), (facetIndex 54), (facetIndex 63), (facetIndex 66), (facetIndex 67), (facetIndex 70), (facetIndex 73), (facetIndex 78), (facetIndex 80)]
theorem leaf0003_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0003 = true := by
  decide +kernel
theorem leaf0003_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0003 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0003_counts_checked
def leaf0004 : List (Fin data.count) := [(facetIndex 11), (facetIndex 21), (facetIndex 24), (facetIndex 28), (facetIndex 46), (facetIndex 49), (facetIndex 59), (facetIndex 60), (facetIndex 63), (facetIndex 68), (facetIndex 72), (facetIndex 75), (facetIndex 79), (facetIndex 82)]
theorem leaf0004_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0004 = true := by
  decide +kernel
theorem leaf0004_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0004 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0004_counts_checked
def leaf0005 : List (Fin data.count) := [(facetIndex 8), (facetIndex 21), (facetIndex 24), (facetIndex 28), (facetIndex 49), (facetIndex 51), (facetIndex 59), (facetIndex 60), (facetIndex 63), (facetIndex 68), (facetIndex 72), (facetIndex 75), (facetIndex 79), (facetIndex 82)]
theorem leaf0005_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0005 = true := by
  decide +kernel
theorem leaf0005_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0005 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0005_counts_checked
def leaf0006 : List (Fin data.count) := [(facetIndex 8), (facetIndex 21), (facetIndex 27), (facetIndex 28), (facetIndex 49), (facetIndex 51), (facetIndex 59), (facetIndex 60), (facetIndex 63), (facetIndex 68), (facetIndex 69), (facetIndex 75), (facetIndex 79), (facetIndex 82)]
theorem leaf0006_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0006 = true := by
  decide +kernel
theorem leaf0006_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0006 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0006_counts_checked
def leaf0007 : List (Fin data.count) := [(facetIndex 9), (facetIndex 21), (facetIndex 24), (facetIndex 29), (facetIndex 46), (facetIndex 52), (facetIndex 59), (facetIndex 60), (facetIndex 63), (facetIndex 68), (facetIndex 72), (facetIndex 75), (facetIndex 78), (facetIndex 82)]
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

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record022" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"group\",\"kind\":1,\"index\":0},{\"tag\":\"group\",\"kind\":1,\"index\":12},{\"tag\":\"group\",\"kind\":1,\"index\":14},{\"tag\":\"group\",\"kind\":1,\"index\":19},{\"tag\":\"group\",\"kind\":1,\"index\":21},{\"tag\":\"group\",\"kind\":1,\"index\":22},{\"tag\":\"group\",\"kind\":1,\"index\":23},{\"tag\":\"group\",\"kind\":1,\"index\":25},{\"tag\":\"group\",\"kind\":1,\"index\":26},{\"tag\":\"group\",\"kind\":1,\"index\":27},{\"tag\":\"group\",\"kind\":1,\"index\":28},{\"tag\":\"group\",\"kind\":1,\"index\":31},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0002\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0012\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0016\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0013\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0013\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0010\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0010\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0004\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0004\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0019\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0026\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0030\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0027\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0027\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0020\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0020\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0033\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0038\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0034\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0041\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0045\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0042\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0042\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0035\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0035\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0021\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0021\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":5,\"list_name\":\"grouped1_0021\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":5,\"list_name\":\"groupKind1\"},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0048\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0055\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0055\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0053\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0053\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0049\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0049\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0058\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0058\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0064\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0064\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0062\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0062\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0062\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0059\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0059\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0059\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0070\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0067\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0073\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0073\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0077\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0077\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0074\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0074\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record022" 169

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record022" "{\"ridges\":[[0,11],[0,13],[2,37],[3,67],[6,11],[6,137],[7,11],[7,265],[9,146],[12,131],[13,13],[13,25],[16,517],[16,532],[18,517],[19,137],[19,152],[21,137],[21,265],[22,577],[23,641],[23,656],[24,22],[24,26],[26,22],[28,146],[30,138],[31,84],[31,532],[32,11],[32,13],[33,13],[35,21],[35,37],[36,7],[37,517],[37,532],[38,37],[40,7],[40,517],[40,646],[42,11],[42,67],[42,81],[42,82],[43,25],[47,82],[47,146],[48,592],[49,146],[49,259],[49,385],[50,641],[50,656],[51,67],[51,259],[52,131],[53,67],[53,577],[53,706],[54,25],[54,28],[54,37],[55,13],[55,25],[57,13],[57,25],[57,532],[59,13],[59,37],[59,44],[59,265],[59,296],[60,13],[60,137],[60,517],[60,652],[62,641],[62,656],[63,37],[63,100],[63,517],[63,577],[63,580],[64,120],[65,145],[65,152],[65,265],[66,25],[66,529],[66,641],[68,145],[68,592],[69,26],[70,70],[71,22],[71,146],[71,152],[72,14],[73,14],[73,38],[73,44],[74,22],[74,38],[74,82],[75,82],[76,22],[76,146],[76,646],[77,82],[77,120],[78,146],[78,152],[78,386],[78,392],[79,42],[79,138],[79,386],[79,392],[80,82],[80,146],[80,656],[80,706],[81,120],[82,532],[82,652],[82,656]],\"owners\":[[36,7,[0,2,3,34,38,39],[1,33,37,40]],[40,7,[0,1,2,3,34,38],[33,36,37,39]],[32,11,[4,5,6,7],[0,42,44]],[72,14,[0,24,33,34,71],[25,32,70,73]],[73,14,[0,24,32,33,70,71],[25,34,72]],[35,21,[13,15,16,56,62],[1,36,54,61]],[71,22,[1,26,35,37,74,75],[24,36,69,76]],[73,38,[2,27,35,74],[25,38,69]],[74,38,[2,25,38,73],[27,35,69]],[70,70,[3,27,39],[26,32,72,75]],[13,25,[4,19,41,42,43,64,65,66],[54,55,57]],[43,25,[13,19,54,55,57,64,66],[4,41,42,65]],[55,25,[4,19,41,43,65,66],[13,42,54,57,64]],[57,25,[4,19,41,42,43,64,65],[13,54,55,66]],[24,26,[4,28,41,42,43,77,78],[69,70]],[69,26,[4,28,42,43,78],[24,41,70,77]],[79,42,[5,25,41,44,69,72,77],[29,45]],[12,131,[6,9,33,36,40,45,47,50,53],[52]],[52,131,[6,9,33,36,40,47,50,53],[12,45]],[30,138,[6,28,33,45,71],[79]],[79,138,[6,28,33,71],[30,45]],[49,259,[7,11,34,38,51],[12,43]],[51,259,[7,12,34,43,49],[11,38]],[42,81,[15,22,61,68],[8,46,47,55,64]],[42,82,[26,74,75,80],[8,46,47,48,70,77]],[47,82,[26,70,74,75,77],[8,42,46,48,80]],[75,82,[8,42,46,47,77],[26,48,70,74,80]],[65,145,[9,23,36,47,62,68],[19,49,56]],[68,145,[9,19,36,49,56,65],[23,47,62]],[28,146,[9,36,47,49,50,76,80],[71,78]],[49,146,[28,71,76,80],[9,36,47,50,78]],[78,146,[9,36,47,50,76,80],[28,49,71]],[49,385,[21,67],[12,52,65]],[78,386,[12,52],[30,49,79]],[79,386,[12,49],[30,52,78]],[54,28,[24,70,71,82],[13,55,56,57,69,81]],[59,44,[25,69,72,81],[14,54,58,73]],[73,44,[14,54,58,81],[25,59,69,72]],[31,84,[15,26,55,61,70,74,81],[]],[63,517,[16,37,40,57,60,62],[18,39]],[66,529,[16,22,37,48],[23,50,57]],[57,532,[31,75,76],[16,37,62,82]],[63,100,[27,72,74,81],[17,58,61]],[22,577,[18,39,53,63],[48,68]],[63,580,[31,75],[18,39]],[19,152,[28,71,78,82],[56,65,66]],[65,152,[28,71,82],[19,56,66,78]],[71,152,[19,65,66],[28,56,78,82]],[78,152,[19,56,66,82],[28,65,71]],[59,296,[29,79],[20,67,73]],[78,392,[21,67],[30,65,79]],[79,392,[21,65],[30,67,78]],[48,592,[31],[22,68,75,80]],[68,592,[31,75],[22,48,80]],[23,641,[40,53,60],[50,62,66,68]],[50,641,[60],[23,40,53,62,66,68]],[62,641,[53],[23,40,50,60,66,68]],[66,641,[40,53],[23,50,60,62,68]],[23,656,[76,80,82],[50,62,66,68]],[50,656,[82],[23,62,66,68,76,80]],[62,656,[80],[23,50,66,68,76,82]],[80,656,[23,62,66,82],[50,68,76]],[82,656,[23,50,68,80],[62,66,76]],[40,646,[76],[]],[76,646,[40],[]],[53,706,[80],[]],[80,706,[53],[]],[60,652,[82],[]],[82,652,[60],[]],[64,120,[77,81],[]],[77,120,[64,81],[]],[81,120,[64,77],[]]],\"edges\":[[24,[4,13,19,24,28,41,42,43,54,55,56,57,64,65,66,69,70,71,77,78,81,82]],[41,[18,22,31,39,48,53,63,68,75,80]],[42,[12,21,30,49,52,65,67,78,79]],[43,[23,40,50,53,60,62,66,68,76,80,82]]],\"groupings\":[1,2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record022" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record022\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-37,-35],[-38,-30],[-38,-31],[-38,-33],[-38,-34],[-38,-35],[-38,-37],[-40,-2],[-40,-10],[-40,-32],[-40,-33],[-40,-35],[-40,-39],[-41,-40],[-42,-40],[-43,-40],[-44,-40],[-45,-5],[-45,-33],[-45,-34],[-45,-39],[-45,-40],[-45,-41],[-45,-44],[-46,-15],[-46,-37],[-46,-38],[-46,-40],[-46,-44],[-47,-38],[-47,-40],[-47,-41],[-47,-45],[-48,-18],[-48,-34],[-48,-37],[-48,-40],[-48,-45],[-48,-47],[-49,-3],[-49,-44],[-50,-47],[-50,-49],[-51,-35],[-51,-44],[-51,-45],[-51,-46],[-51,-47],[-52,-1],[-52,-30],[-52,-31],[-52,-32],[-52,-33],[-52,-39],[-53,-40],[-53,-52],[-54,-38],[-54,-48],[-54,-52],[-55,-2],[-55,-33],[-55,-34],[-55,-35],[-55,-52],[-55,-53],[-55,-54],[-56,-40],[-56,-52],[-57,-6],[-57,-32],[-57,-36],[-57,-39],[-57,-42],[-57,-43],[-57,-56],[-58,-52],[-58,-55],[-59,-33],[-59,-46],[-59,-52],[-59,-55],[-60,-34],[-60,-35],[-60,-48],[-60,-54],[-61,-4],[-61,-15],[-62,-46],[-62,-52],[-62,-57],[-63,-7],[-63,-41],[-63,-43],[-63,-48],[-63,-58],[-64,-34],[-64,-45],[-64,-48],[-64,-54],[-64,-60],[-64,-63],[-65,-57],[-65,-63],[-66,-16],[-66,-35],[-66,-45],[-66,-46],[-66,-48],[-67,-1],[-67,-44],[-67,-62],[-68,-34],[-68,-40],[-68,-62],[-68,-67],[-69,-5],[-69,-31],[-69,-38],[-69,-39],[-69,-41],[-69,-60],[-69,-67],[-69,-68],[-70,-40],[-70,-62],[-70,-68],[-71,-32],[-71,-36],[-71,-42],[-71,-43],[-71,-57],[-72,-30],[-72,-33],[-72,-44],[-72,-52],[-72,-59],[-72,-62],[-72,-67],[-72,-70],[-73,-15],[-73,-35],[-73,-37],[-73,-38],[-73,-46],[-73,-48],[-73,-59],[-74,-46],[-74,-68],[-74,-69],[-75,-52],[-75,-67],[-75,-68],[-75,-70],[-75,-71],[-75,-72],[-76,-41],[-76,-69],[-77,-71],[-77,-76],[-78,-35],[-78,-37],[-78,-38],[-78,-45],[-78,-46],[-78,-66],[-78,-73],[-78,-74],[-79,-68],[-79,-70],[-79,-72],[-79,-73],[-80,-31],[-80,-34],[-80,-38],[-80,-54],[-80,-55],[-80,-60],[-80,-64],[-80,-69],[-80,-74],[-34,1,3,4,32,36,37],[-38,1,2,3,4,32,36],[-30,5,6,7,8],[-1,-7,-40],[-1,-8,-40],[-1,-55,-57],[-1,-57,-58],[-13,-57,-58],[-30,-57,-58],[-31,-55,-57],[-53,-57,-58],[-70,1,22,31,32,69],[-71,1,22,30,31,68,69],[-33,13,15,16,54,60],[-69,2,24,33,35,72,73],[-22,-24,-74],[-22,-72,-74],[-3,-52,-61],[-3,-57,-61],[-33,-57,-61],[-36,-52,-61],[-71,3,25,33,72],[-72,3,23,36,71],[-4,-40,-49],[-40,-49,-51],[-68,4,25,37],[-13,5,18,39,40,41,62,63,64],[-41,13,18,52,53,55,62,64],[-53,5,18,39,41,63,64],[-55,5,18,39,40,41,62,63],[-41,-52,-64],[-22,5,26,39,40,41,75,76],[-67,5,26,40,41,76],[-77,6,23,39,42,67,70,75],[-12,7,10,31,34,38,43,45,48,51],[-50,7,10,31,34,38,45,48,51],[-7,-18,-58],[-18,-19,-58],[-28,7,26,31,43,69],[-77,7,26,31,69],[-47,8,11,32,36,49],[-49,8,12,32,41,47],[-8,-19,-57],[-8,-57,-63],[-40,15,20,59,66],[-40,24,72,73,78],[-45,24,68,72,73,75],[-73,9,40,44,45,75],[-40,-72,-78],[-45,-73,-75],[-63,10,21,34,45,60,66],[-66,10,18,34,47,54,63],[-26,10,34,45,47,48,74,78],[-47,26,69,74,78],[-76,10,34,45,48,74,78],[-10,-69,-78],[-26,-45,-74],[-45,-74,-76],[-47,19,65],[-76,12,50],[-77,12,47],[-52,22,68,69,80],[-57,23,67,70,79],[-71,14,52,56,79],[-29,15,24,53,59,68,72,79],[-61,16,35,38,55,58,60],[-16,-38,-61],[-17,-35,-58],[-35,-58,-61],[-64,16,20,35,46],[-55,29,73,74],[-16,-29,-80],[-29,-35,-80],[-61,25,70,72,79],[-20,17,37,51,61],[-20,-51,-61],[-61,29,73],[-18,26,69,76,80],[-63,26,69,80],[-69,18,63,64],[-76,18,54,64,80],[-57,27,77],[-76,19,65],[-77,19,63],[-46,29],[-66,29,73],[-21,38,51,58],[-48,58],[-60,51],[-64,38,51],[-21,74,78,80],[-48,80],[-60,78],[-78,21,60,64,80],[-80,21,48,66,78],[-38,74],[-74,38],[-51,78],[-78,51],[-58,80],[-80,58],[-62,75,79],[-75,62,79],[-79,62,75],[-1,81],[-12,82],[-14,83],[-18,84],[-19,85],[-20,86],[-21,87],[-23,88],[-24,89],[-25,90],[-26,91],[-29,92],[-81,93],[-93,94],[-94,95],[-82,96],[-83,97],[-96,98],[-96,-97,99],[-98,100],[-99,101],[-95,-100,102],[-95,-101,103],[-84,104],[-104,105],[-85,106],[-87,107],[-86,107],[-107,108],[-106,-107,109],[-108,110],[-109,111],[-105,110],[-88,112],[-90,113],[-89,113],[-113,114],[-112,114],[-91,115],[-92,116],[-116,117],[-115,-116,118],[-117,119],[-114,-118,120],[-120,122],[-110,-119,121],[-111,-120,123],[-123,124],[-102,-122,124],[-103,-121,124],[-124],[-125,30,37,53,56,59,61],[-126,33,36,39,42,44,49],[-127,32,41,43,50,65,77],[-128,55,60,64,66],[-129,31,47,63,76],[-130,68,72,73],[-131,67,70,71],[-132,34,40,54,69],[-133,52,57],[-134,35,45,46,48],[-135,125],[-135,126],[-136,128,129],[-137,128],[-137,129],[-138,127,137],[-139,127],[-138,136],[-139,137],[-140,135,139],[-141,135],[-140,138],[-141,139],[-142,130,131],[-143,130],[-143,131],[-144,133,134],[-145,133],[-145,134],[-146,132,144],[-147,132,145],[-148,132],[-147,144],[-148,145],[-149,142,148],[-150,142],[-149,143,147],[-150,143,148],[-149,146],[-150,147],[-151,148],[-152,140,151],[-152,141,150],[-152,149],[152],[-153,62],[-62,153],[-154,75],[-75,154],[-155,79],[-79,155],[-156,38,51],[-38,156],[-157,58,74],[-58,157],[-74,157],[-158,78],[-78,158],[-159,80],[-80,159],[-160,154,155],[-155,160],[-154,160],[-161,153,160],[-160,161],[-153,161],[-157,162],[-163,156],[-163,157],[-156,-157,163],[-164,158,159],[-165,159],[-158,-159,165],[-166,163,164],[-162,-165,167],[-163,166],[-168,161,166],[-167,169],[-161,-166,169],[168],[-169],[-12,-21,-23,-29,-49,-51,-55,-57,-61,-63,-69,-72,-77,-78],[-12,-21,-24,-29,-49,-51,-55,-57,-61,-63,-69,-70,-77,-78],[-12,-18,-25,-29,-49,-51,-52,-60,-61,-65,-68,-71,-76,-78],[-12,-16,-25,-29,-49,-51,-52,-61,-64,-65,-68,-71,-76,-78],[-11,-19,-22,-26,-44,-47,-57,-58,-61,-66,-70,-73,-77,-80],[-9,-19,-22,-26,-47,-49,-57,-58,-61,-66,-70,-73,-77,-80],[-9,-19,-25,-26,-47,-49,-57,-58,-61,-66,-67,-73,-77,-80],[-10,-19,-22,-27,-44,-50,-57,-58,-61,-66,-70,-73,-76,-80],[5,13,18,22,26,39,40,41,52,53,54,55,62,63,64,67,68,69,75,76,79,80],[17,20,29,37,46,51,61,66,73,78],[12,19,28,47,50,63,65,76,77],[21,38,48,51,58,60,64,66,74,78,80]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"group\",\"index\":0,\"kind\":1},{\"tag\":\"group\",\"index\":12,\"kind\":1},{\"tag\":\"group\",\"index\":14,\"kind\":1},{\"tag\":\"group\",\"index\":19,\"kind\":1},{\"tag\":\"group\",\"index\":21,\"kind\":1},{\"tag\":\"group\",\"index\":22,\"kind\":1},{\"tag\":\"group\",\"index\":23,\"kind\":1},{\"tag\":\"group\",\"index\":25,\"kind\":1},{\"tag\":\"group\",\"index\":26,\"kind\":1},{\"tag\":\"group\",\"index\":27,\"kind\":1},{\"tag\":\"group\",\"index\":28,\"kind\":1},{\"tag\":\"group\",\"index\":31,\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":39,\"b\":37},{\"tag\":\"incompatible\",\"a\":40,\"b\":32},{\"tag\":\"incompatible\",\"a\":40,\"b\":33},{\"tag\":\"incompatible\",\"a\":40,\"b\":35},{\"tag\":\"incompatible\",\"a\":40,\"b\":36},{\"tag\":\"incompatible\",\"a\":40,\"b\":37},{\"tag\":\"incompatible\",\"a\":40,\"b\":39},{\"tag\":\"incompatible\",\"a\":42,\"b\":1},{\"tag\":\"incompatible\",\"a\":42,\"b\":9},{\"tag\":\"incompatible\",\"a\":42,\"b\":34},{\"tag\":\"incompatible\",\"a\":42,\"b\":35},{\"tag\":\"incompatible\",\"a\":42,\"b\":37},{\"tag\":\"incompatible\",\"a\":42,\"b\":41},{\"tag\":\"incompatible\",\"a\":43,\"b\":42},{\"tag\":\"incompatible\",\"a\":44,\"b\":42},{\"tag\":\"incompatible\",\"a\":45,\"b\":42},{\"tag\":\"incompatible\",\"a\":46,\"b\":42},{\"tag\":\"incompatible\",\"a\":47,\"b\":4},{\"tag\":\"incompatible\",\"a\":47,\"b\":35},{\"tag\":\"incompatible\",\"a\":47,\"b\":36},{\"tag\":\"incompatible\",\"a\":47,\"b\":41},{\"tag\":\"incompatible\",\"a\":47,\"b\":42},{\"tag\":\"incompatible\",\"a\":47,\"b\":43},{\"tag\":\"incompatible\",\"a\":47,\"b\":46},{\"tag\":\"incompatible\",\"a\":48,\"b\":15},{\"tag\":\"incompatible\",\"a\":48,\"b\":39},{\"tag\":\"incompatible\",\"a\":48,\"b\":40},{\"tag\":\"incompatible\",\"a\":48,\"b\":42},{\"tag\":\"incompatible\",\"a\":48,\"b\":46},{\"tag\":\"incompatible\",\"a\":49,\"b\":40},{\"tag\":\"incompatible\",\"a\":49,\"b\":42},{\"tag\":\"incompatible\",\"a\":49,\"b\":43},{\"tag\":\"incompatible\",\"a\":49,\"b\":47},{\"tag\":\"incompatible\",\"a\":50,\"b\":19},{\"tag\":\"incompatible\",\"a\":50,\"b\":36},{\"tag\":\"incompatible\",\"a\":50,\"b\":39},{\"tag\":\"incompatible\",\"a\":50,\"b\":42},{\"tag\":\"incompatible\",\"a\":50,\"b\":47},{\"tag\":\"incompatible\",\"a\":50,\"b\":49},{\"tag\":\"incompatible\",\"a\":51,\"b\":2},{\"tag\":\"incompatible\",\"a\":51,\"b\":46},{\"tag\":\"incompatible\",\"a\":52,\"b\":49},{\"tag\":\"incompatible\",\"a\":52,\"b\":51},{\"tag\":\"incompatible\",\"a\":53,\"b\":37},{\"tag\":\"incompatible\",\"a\":53,\"b\":46},{\"tag\":\"incompatible\",\"a\":53,\"b\":47},{\"tag\":\"incompatible\",\"a\":53,\"b\":48},{\"tag\":\"incompatible\",\"a\":53,\"b\":49},{\"tag\":\"incompatible\",\"a\":54,\"b\":0},{\"tag\":\"incompatible\",\"a\":54,\"b\":32},{\"tag\":\"incompatible\",\"a\":54,\"b\":33},{\"tag\":\"incompatible\",\"a\":54,\"b\":34},{\"tag\":\"incompatible\",\"a\":54,\"b\":35},{\"tag\":\"incompatible\",\"a\":54,\"b\":41},{\"tag\":\"incompatible\",\"a\":55,\"b\":42},{\"tag\":\"incompatible\",\"a\":55,\"b\":54},{\"tag\":\"incompatible\",\"a\":56,\"b\":40},{\"tag\":\"incompatible\",\"a\":56,\"b\":50},{\"tag\":\"incompatible\",\"a\":56,\"b\":54},{\"tag\":\"incompatible\",\"a\":57,\"b\":1},{\"tag\":\"incompatible\",\"a\":57,\"b\":35},{\"tag\":\"incompatible\",\"a\":57,\"b\":36},{\"tag\":\"incompatible\",\"a\":57,\"b\":37},{\"tag\":\"incompatible\",\"a\":57,\"b\":54},{\"tag\":\"incompatible\",\"a\":57,\"b\":55},{\"tag\":\"incompatible\",\"a\":57,\"b\":56},{\"tag\":\"incompatible\",\"a\":58,\"b\":42},{\"tag\":\"incompatible\",\"a\":58,\"b\":54},{\"tag\":\"incompatible\",\"a\":59,\"b\":5},{\"tag\":\"incompatible\",\"a\":59,\"b\":34},{\"tag\":\"incompatible\",\"a\":59,\"b\":38},{\"tag\":\"incompatible\",\"a\":59,\"b\":41},{\"tag\":\"incompatible\",\"a\":59,\"b\":44},{\"tag\":\"incompatible\",\"a\":59,\"b\":45},{\"tag\":\"incompatible\",\"a\":59,\"b\":58},{\"tag\":\"incompatible\",\"a\":60,\"b\":54},{\"tag\":\"incompatible\",\"a\":60,\"b\":57},{\"tag\":\"incompatible\",\"a\":61,\"b\":35},{\"tag\":\"incompatible\",\"a\":61,\"b\":48},{\"tag\":\"incompatible\",\"a\":61,\"b\":54},{\"tag\":\"incompatible\",\"a\":61,\"b\":57},{\"tag\":\"incompatible\",\"a\":62,\"b\":36},{\"tag\":\"incompatible\",\"a\":62,\"b\":37},{\"tag\":\"incompatible\",\"a\":62,\"b\":50},{\"tag\":\"incompatible\",\"a\":62,\"b\":56},{\"tag\":\"incompatible\",\"a\":63,\"b\":3},{\"tag\":\"incompatible\",\"a\":63,\"b\":15},{\"tag\":\"incompatible\",\"a\":64,\"b\":48},{\"tag\":\"incompatible\",\"a\":64,\"b\":54},{\"tag\":\"incompatible\",\"a\":64,\"b\":59},{\"tag\":\"incompatible\",\"a\":65,\"b\":6},{\"tag\":\"incompatible\",\"a\":65,\"b\":43},{\"tag\":\"incompatible\",\"a\":65,\"b\":45},{\"tag\":\"incompatible\",\"a\":65,\"b\":50},{\"tag\":\"incompatible\",\"a\":65,\"b\":60},{\"tag\":\"incompatible\",\"a\":66,\"b\":36},{\"tag\":\"incompatible\",\"a\":66,\"b\":47},{\"tag\":\"incompatible\",\"a\":66,\"b\":50},{\"tag\":\"incompatible\",\"a\":66,\"b\":56},{\"tag\":\"incompatible\",\"a\":66,\"b\":62},{\"tag\":\"incompatible\",\"a\":66,\"b\":65},{\"tag\":\"incompatible\",\"a\":67,\"b\":59},{\"tag\":\"incompatible\",\"a\":67,\"b\":65},{\"tag\":\"incompatible\",\"a\":68,\"b\":16},{\"tag\":\"incompatible\",\"a\":68,\"b\":37},{\"tag\":\"incompatible\",\"a\":68,\"b\":47},{\"tag\":\"incompatible\",\"a\":68,\"b\":48},{\"tag\":\"incompatible\",\"a\":68,\"b\":50},{\"tag\":\"incompatible\",\"a\":69,\"b\":0},{\"tag\":\"incompatible\",\"a\":69,\"b\":46},{\"tag\":\"incompatible\",\"a\":69,\"b\":64},{\"tag\":\"incompatible\",\"a\":70,\"b\":36},{\"tag\":\"incompatible\",\"a\":70,\"b\":42},{\"tag\":\"incompatible\",\"a\":70,\"b\":64},{\"tag\":\"incompatible\",\"a\":70,\"b\":69},{\"tag\":\"incompatible\",\"a\":71,\"b\":4},{\"tag\":\"incompatible\",\"a\":71,\"b\":33},{\"tag\":\"incompatible\",\"a\":71,\"b\":40},{\"tag\":\"incompatible\",\"a\":71,\"b\":41},{\"tag\":\"incompatible\",\"a\":71,\"b\":43},{\"tag\":\"incompatible\",\"a\":71,\"b\":62},{\"tag\":\"incompatible\",\"a\":71,\"b\":69},{\"tag\":\"incompatible\",\"a\":71,\"b\":70},{\"tag\":\"incompatible\",\"a\":72,\"b\":42},{\"tag\":\"incompatible\",\"a\":72,\"b\":64},{\"tag\":\"incompatible\",\"a\":72,\"b\":70},{\"tag\":\"incompatible\",\"a\":73,\"b\":34},{\"tag\":\"incompatible\",\"a\":73,\"b\":38},{\"tag\":\"incompatible\",\"a\":73,\"b\":44},{\"tag\":\"incompatible\",\"a\":73,\"b\":45},{\"tag\":\"incompatible\",\"a\":73,\"b\":59},{\"tag\":\"incompatible\",\"a\":74,\"b\":32},{\"tag\":\"incompatible\",\"a\":74,\"b\":35},{\"tag\":\"incompatible\",\"a\":74,\"b\":46},{\"tag\":\"incompatible\",\"a\":74,\"b\":54},{\"tag\":\"incompatible\",\"a\":74,\"b\":61},{\"tag\":\"incompatible\",\"a\":74,\"b\":64},{\"tag\":\"incompatible\",\"a\":74,\"b\":69},{\"tag\":\"incompatible\",\"a\":74,\"b\":72},{\"tag\":\"incompatible\",\"a\":75,\"b\":15},{\"tag\":\"incompatible\",\"a\":75,\"b\":37},{\"tag\":\"incompatible\",\"a\":75,\"b\":39},{\"tag\":\"incompatible\",\"a\":75,\"b\":40},{\"tag\":\"incompatible\",\"a\":75,\"b\":48},{\"tag\":\"incompatible\",\"a\":75,\"b\":50},{\"tag\":\"incompatible\",\"a\":75,\"b\":61},{\"tag\":\"incompatible\",\"a\":76,\"b\":48},{\"tag\":\"incompatible\",\"a\":76,\"b\":70},{\"tag\":\"incompatible\",\"a\":76,\"b\":71},{\"tag\":\"incompatible\",\"a\":77,\"b\":54},{\"tag\":\"incompatible\",\"a\":77,\"b\":69},{\"tag\":\"incompatible\",\"a\":77,\"b\":70},{\"tag\":\"incompatible\",\"a\":77,\"b\":72},{\"tag\":\"incompatible\",\"a\":77,\"b\":73},{\"tag\":\"incompatible\",\"a\":77,\"b\":74},{\"tag\":\"incompatible\",\"a\":78,\"b\":43},{\"tag\":\"incompatible\",\"a\":78,\"b\":71},{\"tag\":\"incompatible\",\"a\":79,\"b\":73},{\"tag\":\"incompatible\",\"a\":79,\"b\":78},{\"tag\":\"incompatible\",\"a\":80,\"b\":37},{\"tag\":\"incompatible\",\"a\":80,\"b\":39},{\"tag\":\"incompatible\",\"a\":80,\"b\":40},{\"tag\":\"incompatible\",\"a\":80,\"b\":47},{\"tag\":\"incompatible\",\"a\":80,\"b\":48},{\"tag\":\"incompatible\",\"a\":80,\"b\":68},{\"tag\":\"incompatible\",\"a\":80,\"b\":75},{\"tag\":\"incompatible\",\"a\":80,\"b\":76},{\"tag\":\"incompatible\",\"a\":81,\"b\":70},{\"tag\":\"incompatible\",\"a\":81,\"b\":72},{\"tag\":\"incompatible\",\"a\":81,\"b\":74},{\"tag\":\"incompatible\",\"a\":81,\"b\":75},{\"tag\":\"incompatible\",\"a\":82,\"b\":33},{\"tag\":\"incompatible\",\"a\":82,\"b\":36},{\"tag\":\"incompatible\",\"a\":82,\"b\":40},{\"tag\":\"incompatible\",\"a\":82,\"b\":56},{\"tag\":\"incompatible\",\"a\":82,\"b\":57},{\"tag\":\"incompatible\",\"a\":82,\"b\":62},{\"tag\":\"incompatible\",\"a\":82,\"b\":66},{\"tag\":\"incompatible\",\"a\":82,\"b\":71},{\"tag\":\"incompatible\",\"a\":82,\"b\":76},{\"tag\":\"mate\",\"ridge\":7,\"a\":36,\"owners\":[0,2,3,34,38,39]},{\"tag\":\"mate\",\"ridge\":7,\"a\":40,\"owners\":[0,1,2,3,34,38]},{\"tag\":\"mate\",\"ridge\":11,\"a\":32,\"owners\":[4,5,6,7]},{\"tag\":\"three\",\"ridge\":11,\"vertices\":[0,6,42]},{\"tag\":\"three\",\"ridge\":11,\"vertices\":[0,7,42]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[0,57,59]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[0,59,60]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[13,59,60]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[32,59,60]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[33,57,59]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[55,59,60]},{\"tag\":\"mate\",\"ridge\":14,\"a\":72,\"owners\":[0,24,33,34,71]},{\"tag\":\"mate\",\"ridge\":14,\"a\":73,\"owners\":[0,24,32,33,70,71]},{\"tag\":\"mate\",\"ridge\":21,\"a\":35,\"owners\":[13,15,16,56,62]},{\"tag\":\"mate\",\"ridge\":22,\"a\":71,\"owners\":[1,26,35,37,74,75]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[24,26,76]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[24,74,76]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[2,54,63]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[2,59,63]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[35,59,63]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[38,54,63]},{\"tag\":\"mate\",\"ridge\":38,\"a\":73,\"owners\":[2,27,35,74]},{\"tag\":\"mate\",\"ridge\":38,\"a\":74,\"owners\":[2,25,38,73]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[3,42,51]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[42,51,53]},{\"tag\":\"mate\",\"ridge\":70,\"a\":70,\"owners\":[3,27,39]},{\"tag\":\"mate\",\"ridge\":25,\"a\":13,\"owners\":[4,19,41,42,43,64,65,66]},{\"tag\":\"mate\",\"ridge\":25,\"a\":43,\"owners\":[13,19,54,55,57,64,66]},{\"tag\":\"mate\",\"ridge\":25,\"a\":55,\"owners\":[4,19,41,43,65,66]},{\"tag\":\"mate\",\"ridge\":25,\"a\":57,\"owners\":[4,19,41,42,43,64,65]},{\"tag\":\"three\",\"ridge\":25,\"vertices\":[43,54,66]},{\"tag\":\"mate\",\"ridge\":26,\"a\":24,\"owners\":[4,28,41,42,43,77,78]},{\"tag\":\"mate\",\"ridge\":26,\"a\":69,\"owners\":[4,28,42,43,78]},{\"tag\":\"mate\",\"ridge\":42,\"a\":79,\"owners\":[5,25,41,44,69,72,77]},{\"tag\":\"mate\",\"ridge\":131,\"a\":12,\"owners\":[6,9,33,36,40,45,47,50,53]},{\"tag\":\"mate\",\"ridge\":131,\"a\":52,\"owners\":[6,9,33,36,40,47,50,53]},{\"tag\":\"three\",\"ridge\":137,\"vertices\":[6,19,60]},{\"tag\":\"three\",\"ridge\":137,\"vertices\":[19,21,60]},{\"tag\":\"mate\",\"ridge\":138,\"a\":30,\"owners\":[6,28,33,45,71]},{\"tag\":\"mate\",\"ridge\":138,\"a\":79,\"owners\":[6,28,33,71]},{\"tag\":\"mate\",\"ridge\":259,\"a\":49,\"owners\":[7,11,34,38,51]},{\"tag\":\"mate\",\"ridge\":259,\"a\":51,\"owners\":[7,12,34,43,49]},{\"tag\":\"three\",\"ridge\":265,\"vertices\":[7,21,59]},{\"tag\":\"three\",\"ridge\":265,\"vertices\":[7,59,65]},{\"tag\":\"mate\",\"ridge\":81,\"a\":42,\"owners\":[15,22,61,68]},{\"tag\":\"mate\",\"ridge\":82,\"a\":42,\"owners\":[26,74,75,80]},{\"tag\":\"mate\",\"ridge\":82,\"a\":47,\"owners\":[26,70,74,75,77]},{\"tag\":\"mate\",\"ridge\":82,\"a\":75,\"owners\":[8,42,46,47,77]},{\"tag\":\"three\",\"ridge\":82,\"vertices\":[42,74,80]},{\"tag\":\"three\",\"ridge\":82,\"vertices\":[47,75,77]},{\"tag\":\"mate\",\"ridge\":145,\"a\":65,\"owners\":[9,23,36,47,62,68]},{\"tag\":\"mate\",\"ridge\":145,\"a\":68,\"owners\":[9,19,36,49,56,65]},{\"tag\":\"mate\",\"ridge\":146,\"a\":28,\"owners\":[9,36,47,49,50,76,80]},{\"tag\":\"mate\",\"ridge\":146,\"a\":49,\"owners\":[28,71,76,80]},{\"tag\":\"mate\",\"ridge\":146,\"a\":78,\"owners\":[9,36,47,50,76,80]},{\"tag\":\"three\",\"ridge\":146,\"vertices\":[9,71,80]},{\"tag\":\"three\",\"ridge\":146,\"vertices\":[28,47,76]},{\"tag\":\"three\",\"ridge\":146,\"vertices\":[47,76,78]},{\"tag\":\"mate\",\"ridge\":385,\"a\":49,\"owners\":[21,67]},{\"tag\":\"mate\",\"ridge\":386,\"a\":78,\"owners\":[12,52]},{\"tag\":\"mate\",\"ridge\":386,\"a\":79,\"owners\":[12,49]},{\"tag\":\"mate\",\"ridge\":28,\"a\":54,\"owners\":[24,70,71,82]},{\"tag\":\"mate\",\"ridge\":44,\"a\":59,\"owners\":[25,69,72,81]},{\"tag\":\"mate\",\"ridge\":44,\"a\":73,\"owners\":[14,54,58,81]},{\"tag\":\"mate\",\"ridge\":84,\"a\":31,\"owners\":[15,26,55,61,70,74,81]},{\"tag\":\"mate\",\"ridge\":517,\"a\":63,\"owners\":[16,37,40,57,60,62]},{\"tag\":\"three\",\"ridge\":517,\"vertices\":[16,40,63]},{\"tag\":\"three\",\"ridge\":517,\"vertices\":[18,37,60]},{\"tag\":\"three\",\"ridge\":517,\"vertices\":[37,60,63]},{\"tag\":\"mate\",\"ridge\":529,\"a\":66,\"owners\":[16,22,37,48]},{\"tag\":\"mate\",\"ridge\":532,\"a\":57,\"owners\":[31,75,76]},{\"tag\":\"three\",\"ridge\":532,\"vertices\":[16,31,82]},{\"tag\":\"three\",\"ridge\":532,\"vertices\":[31,37,82]},{\"tag\":\"mate\",\"ridge\":100,\"a\":63,\"owners\":[27,72,74,81]},{\"tag\":\"mate\",\"ridge\":577,\"a\":22,\"owners\":[18,39,53,63]},{\"tag\":\"three\",\"ridge\":577,\"vertices\":[22,53,63]},{\"tag\":\"mate\",\"ridge\":580,\"a\":63,\"owners\":[31,75]},{\"tag\":\"mate\",\"ridge\":152,\"a\":19,\"owners\":[28,71,78,82]},{\"tag\":\"mate\",\"ridge\":152,\"a\":65,\"owners\":[28,71,82]},{\"tag\":\"mate\",\"ridge\":152,\"a\":71,\"owners\":[19,65,66]},{\"tag\":\"mate\",\"ridge\":152,\"a\":78,\"owners\":[19,56,66,82]},{\"tag\":\"mate\",\"ridge\":296,\"a\":59,\"owners\":[29,79]},{\"tag\":\"mate\",\"ridge\":392,\"a\":78,\"owners\":[21,67]},{\"tag\":\"mate\",\"ridge\":392,\"a\":79,\"owners\":[21,65]},{\"tag\":\"mate\",\"ridge\":592,\"a\":48,\"owners\":[31]},{\"tag\":\"mate\",\"ridge\":592,\"a\":68,\"owners\":[31,75]},{\"tag\":\"mate\",\"ridge\":641,\"a\":23,\"owners\":[40,53,60]},{\"tag\":\"mate\",\"ridge\":641,\"a\":50,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":641,\"a\":62,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":641,\"a\":66,\"owners\":[40,53]},{\"tag\":\"mate\",\"ridge\":656,\"a\":23,\"owners\":[76,80,82]},{\"tag\":\"mate\",\"ridge\":656,\"a\":50,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":656,\"a\":62,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":656,\"a\":80,\"owners\":[23,62,66,82]},{\"tag\":\"mate\",\"ridge\":656,\"a\":82,\"owners\":[23,50,68,80]},{\"tag\":\"mate\",\"ridge\":646,\"a\":40,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":646,\"a\":76,\"owners\":[40]},{\"tag\":\"mate\",\"ridge\":706,\"a\":53,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":706,\"a\":80,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":652,\"a\":60,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":652,\"a\":82,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":120,\"a\":64,\"owners\":[77,81]},{\"tag\":\"mate\",\"ridge\":120,\"a\":77,\"owners\":[64,81]},{\"tag\":\"mate\",\"ridge\":120,\"a\":81,\"owners\":[64,77]},{\"tag\":\"group_take\",\"kind\":1,\"index\":0,\"member\":0,\"full_literals\":[-1,81]},{\"tag\":\"group_take\",\"kind\":1,\"index\":12,\"member\":12,\"full_literals\":[-12,82]},{\"tag\":\"group_take\",\"kind\":1,\"index\":14,\"member\":14,\"full_literals\":[-14,83]},{\"tag\":\"group_take\",\"kind\":1,\"index\":19,\"member\":19,\"full_literals\":[-18,84]},{\"tag\":\"group_take\",\"kind\":1,\"index\":21,\"member\":21,\"full_literals\":[-19,85]},{\"tag\":\"group_take\",\"kind\":1,\"index\":22,\"member\":22,\"full_literals\":[-20,86]},{\"tag\":\"group_take\",\"kind\":1,\"index\":23,\"member\":23,\"full_literals\":[-21,87]},{\"tag\":\"group_take\",\"kind\":1,\"index\":25,\"member\":25,\"full_literals\":[-23,88]},{\"tag\":\"group_take\",\"kind\":1,\"index\":26,\"member\":26,\"full_literals\":[-24,89]},{\"tag\":\"group_take\",\"kind\":1,\"index\":27,\"member\":27,\"full_literals\":[-25,90]},{\"tag\":\"group_take\",\"kind\":1,\"index\":28,\"member\":28,\"full_literals\":[-26,91]},{\"tag\":\"group_take\",\"kind\":1,\"index\":31,\"member\":31,\"full_literals\":[-29,92]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0006\",\"joined_name\":\"grouped1_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-81,false,93],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-93,false,94],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0008\",\"joined_name\":\"grouped1_0003\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-94,false,95],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13],\"left_name\":\"grouped1_0011\",\"right_name\":\"grouped1_0014\",\"joined_name\":\"grouped1_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-82,false,96],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14],\"right\":[15],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0017\",\"joined_name\":\"grouped1_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-83,false,97],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12,13],\"right\":[14,15],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-96,false,98],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12,13],\"right\":[14,15],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-96,-97,99],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8,9,10,11],\"right\":[12,13,14,15],\"left_name\":\"grouped1_0009\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-98,100],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8,9,10,11],\"right\":[12,13,14,15],\"left_name\":\"grouped1_0009\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0010\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-99,101],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7],\"right\":[8,9,10,11,12,13,14,15],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0010\",\"joined_name\":\"grouped1_0004\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-95,-100,102],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7],\"right\":[8,9,10,11,12,13,14,15],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0010\",\"joined_name\":\"grouped1_0004\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-95,-101,103],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[18],\"right\":[19],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0024\",\"joined_name\":\"grouped1_0023\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-84,104],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17],\"right\":[18,19],\"left_name\":\"grouped1_0018\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"grouped1_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-104,105],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20],\"right\":[21],\"left_name\":\"grouped1_0025\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-85,106],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[22],\"right\":[23],\"left_name\":\"grouped1_0029\",\"right_name\":\"grouped1_0031\",\"joined_name\":\"grouped1_0030\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-87,107],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[22],\"right\":[23],\"left_name\":\"grouped1_0029\",\"right_name\":\"grouped1_0031\",\"joined_name\":\"grouped1_0030\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-86,false,107],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20,21],\"right\":[22,23],\"left_name\":\"grouped1_0026\",\"right_name\":\"grouped1_0030\",\"joined_name\":\"grouped1_0027\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-107,108],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20,21],\"right\":[22,23],\"left_name\":\"grouped1_0026\",\"right_name\":\"grouped1_0030\",\"joined_name\":\"grouped1_0027\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-106,-107,109],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17,18,19],\"right\":[20,21,22,23],\"left_name\":\"grouped1_0019\",\"right_name\":\"grouped1_0027\",\"joined_name\":\"grouped1_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-108,110],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17,18,19],\"right\":[20,21,22,23],\"left_name\":\"grouped1_0019\",\"right_name\":\"grouped1_0027\",\"joined_name\":\"grouped1_0020\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-109,111],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17,18,19],\"right\":[20,21,22,23],\"left_name\":\"grouped1_0019\",\"right_name\":\"grouped1_0027\",\"joined_name\":\"grouped1_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-105,false,110],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[24],\"right\":[25],\"left_name\":\"grouped1_0032\",\"right_name\":\"grouped1_0036\",\"joined_name\":\"grouped1_0033\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-88,112],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[26],\"right\":[27],\"left_name\":\"grouped1_0037\",\"right_name\":\"grouped1_0039\",\"joined_name\":\"grouped1_0038\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-90,113],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[26],\"right\":[27],\"left_name\":\"grouped1_0037\",\"right_name\":\"grouped1_0039\",\"joined_name\":\"grouped1_0038\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-89,false,113],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[24,25],\"right\":[26,27],\"left_name\":\"grouped1_0033\",\"right_name\":\"grouped1_0038\",\"joined_name\":\"grouped1_0034\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-113,114],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[24,25],\"right\":[26,27],\"left_name\":\"grouped1_0033\",\"right_name\":\"grouped1_0038\",\"joined_name\":\"grouped1_0034\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-112,false,114],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[28],\"right\":[29],\"left_name\":\"grouped1_0040\",\"right_name\":\"grouped1_0043\",\"joined_name\":\"grouped1_0041\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-91,false,115],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[30],\"right\":[31],\"left_name\":\"grouped1_0044\",\"right_name\":\"grouped1_0046\",\"joined_name\":\"grouped1_0045\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-92,116],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[28,29],\"right\":[30,31],\"left_name\":\"grouped1_0041\",\"right_name\":\"grouped1_0045\",\"joined_name\":\"grouped1_0042\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-116,117],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[28,29],\"right\":[30,31],\"left_name\":\"grouped1_0041\",\"right_name\":\"grouped1_0045\",\"joined_name\":\"grouped1_0042\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-115,-116,118],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[24,25,26,27],\"right\":[28,29,30,31],\"left_name\":\"grouped1_0034\",\"right_name\":\"grouped1_0042\",\"joined_name\":\"grouped1_0035\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-117,119],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[24,25,26,27],\"right\":[28,29,30,31],\"left_name\":\"grouped1_0034\",\"right_name\":\"grouped1_0042\",\"joined_name\":\"grouped1_0035\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-114,-118,120],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17,18,19,20,21,22,23],\"right\":[24,25,26,27,28,29,30,31],\"left_name\":\"grouped1_0020\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0021\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-120,122],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17,18,19,20,21,22,23],\"right\":[24,25,26,27,28,29,30,31],\"left_name\":\"grouped1_0020\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0021\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-110,-119,121],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17,18,19,20,21,22,23],\"right\":[24,25,26,27,28,29,30,31],\"left_name\":\"grouped1_0020\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0021\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-111,-120,123],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],\"right\":[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],\"left_name\":\"grouped1_0004\",\"right_name\":\"grouped1_0021\",\"joined_name\":\"groupKind1\",\"a\":0,\"b\":5,\"direction\":\"forward\",\"full_literals\":[false,-123,124],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],\"right\":[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],\"left_name\":\"grouped1_0004\",\"right_name\":\"grouped1_0021\",\"joined_name\":\"groupKind1\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-102,-122,124],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],\"right\":[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],\"left_name\":\"grouped1_0004\",\"right_name\":\"grouped1_0021\",\"joined_name\":\"groupKind1\",\"a\":3,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-103,-121,124],\"grouped\":true,\"kind\":1},{\"tag\":\"quota_upper\",\"kind\":1,\"quota\":4,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[32,39,55,58,61,63],\"full_literals\":[-125,30,37,53,56,59,61]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[35,38,41,44,46,51],\"full_literals\":[-126,33,36,39,42,44,49]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[34,43,45,52,67,79],\"full_literals\":[-127,32,41,43,50,65,77]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[57,62,66,68],\"full_literals\":[-128,55,60,64,66]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[33,49,65,78],\"full_literals\":[-129,31,47,63,76]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[70,74,75],\"full_literals\":[-130,68,72,73]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[69,72,73],\"full_literals\":[-131,67,70,71]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[36,42,56,71],\"full_literals\":[-132,34,40,54,69]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[54,59],\"full_literals\":[-133,52,57]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[37,47,48,50],\"full_literals\":[-134,35,45,46,48]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0047\",\"right_name\":\"grouped2_0051\",\"joined_name\":\"grouped2_0048\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-135,125,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0047\",\"right_name\":\"grouped2_0051\",\"joined_name\":\"grouped2_0048\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-135,false,126],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0054\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0055\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-136,128,129],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0054\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0055\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-137,128,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0054\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0055\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-137,false,129],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0055\",\"joined_name\":\"grouped2_0053\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-138,127,137],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0055\",\"joined_name\":\"grouped2_0053\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-139,127,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0055\",\"joined_name\":\"grouped2_0053\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-138,false,136],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0055\",\"joined_name\":\"grouped2_0053\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-139,false,137],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0048\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"grouped2_0049\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-140,135,139],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0048\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"grouped2_0049\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-141,135,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0048\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"grouped2_0049\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-140,false,138],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0048\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"grouped2_0049\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-141,false,139],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0060\",\"joined_name\":\"grouped2_0058\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-142,130,131],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0060\",\"joined_name\":\"grouped2_0058\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-143,130,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0060\",\"joined_name\":\"grouped2_0058\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-143,false,131],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0063\",\"right_name\":\"grouped2_0065\",\"joined_name\":\"grouped2_0064\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-144,133,134],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0063\",\"right_name\":\"grouped2_0065\",\"joined_name\":\"grouped2_0064\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-145,133,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0063\",\"right_name\":\"grouped2_0065\",\"joined_name\":\"grouped2_0064\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-145,false,134],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0061\",\"right_name\":\"grouped2_0064\",\"joined_name\":\"grouped2_0062\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-146,132,144],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0061\",\"right_name\":\"grouped2_0064\",\"joined_name\":\"grouped2_0062\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-147,132,145],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0061\",\"right_name\":\"grouped2_0064\",\"joined_name\":\"grouped2_0062\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-148,132,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0061\",\"right_name\":\"grouped2_0064\",\"joined_name\":\"grouped2_0062\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-147,false,144],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0061\",\"right_name\":\"grouped2_0064\",\"joined_name\":\"grouped2_0062\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-148,false,145],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0058\",\"right_name\":\"grouped2_0062\",\"joined_name\":\"grouped2_0059\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-149,142,148],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0058\",\"right_name\":\"grouped2_0062\",\"joined_name\":\"grouped2_0059\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-150,142,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0058\",\"right_name\":\"grouped2_0062\",\"joined_name\":\"grouped2_0059\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-149,143,147],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0058\",\"right_name\":\"grouped2_0062\",\"joined_name\":\"grouped2_0059\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-150,143,148],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0058\",\"right_name\":\"grouped2_0062\",\"joined_name\":\"grouped2_0059\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-149,false,146],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0058\",\"right_name\":\"grouped2_0062\",\"joined_name\":\"grouped2_0059\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-150,false,147],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0058\",\"right_name\":\"grouped2_0062\",\"joined_name\":\"grouped2_0059\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-151,false,148],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0049\",\"right_name\":\"grouped2_0059\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-152,140,151],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0049\",\"right_name\":\"grouped2_0059\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-152,141,150],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0049\",\"right_name\":\"grouped2_0059\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-152,false,149],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[64],\"full_literals\":[-153,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":64,\"full_literals\":[-62,153]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[77],\"full_literals\":[-154,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":77,\"full_literals\":[-75,154]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[81],\"full_literals\":[-155,79]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":81,\"full_literals\":[-79,155]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[40,53],\"full_literals\":[-156,38,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":40,\"full_literals\":[-38,156]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[60,76],\"full_literals\":[-157,58,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":60,\"full_literals\":[-58,157]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":76,\"full_literals\":[-74,157]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[80],\"full_literals\":[-158,78]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":80,\"full_literals\":[-78,158]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[82],\"full_literals\":[-159,80]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":82,\"full_literals\":[-80,159]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0069\",\"right_name\":\"grouped3_0071\",\"joined_name\":\"grouped3_0070\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-160,154,155],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0069\",\"right_name\":\"grouped3_0071\",\"joined_name\":\"grouped3_0070\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-155,160],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0069\",\"right_name\":\"grouped3_0071\",\"joined_name\":\"grouped3_0070\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-154,false,160],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0066\",\"right_name\":\"grouped3_0070\",\"joined_name\":\"grouped3_0067\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-161,153,160],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0066\",\"right_name\":\"grouped3_0070\",\"joined_name\":\"grouped3_0067\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-160,161],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0066\",\"right_name\":\"grouped3_0070\",\"joined_name\":\"grouped3_0067\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-153,false,161],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0072\",\"right_name\":\"grouped3_0075\",\"joined_name\":\"grouped3_0073\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-157,162],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0072\",\"right_name\":\"grouped3_0075\",\"joined_name\":\"grouped3_0073\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-163,156,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0072\",\"right_name\":\"grouped3_0075\",\"joined_name\":\"grouped3_0073\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-163,false,157],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0072\",\"right_name\":\"grouped3_0075\",\"joined_name\":\"grouped3_0073\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-156,-157,163],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0076\",\"right_name\":\"grouped3_0078\",\"joined_name\":\"grouped3_0077\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-164,158,159],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0076\",\"right_name\":\"grouped3_0078\",\"joined_name\":\"grouped3_0077\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-165,false,159],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0076\",\"right_name\":\"grouped3_0078\",\"joined_name\":\"grouped3_0077\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-158,-159,165],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0073\",\"right_name\":\"grouped3_0077\",\"joined_name\":\"grouped3_0074\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-166,163,164],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0073\",\"right_name\":\"grouped3_0077\",\"joined_name\":\"grouped3_0074\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-162,-165,167],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0073\",\"right_name\":\"grouped3_0077\",\"joined_name\":\"grouped3_0074\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-163,false,166],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0067\",\"right_name\":\"grouped3_0074\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-168,161,166],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0067\",\"right_name\":\"grouped3_0074\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-167,169],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0067\",\"right_name\":\"grouped3_0074\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-161,-166,169],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"block\",\"leaf\":0,\"vertices\":[12,23,25,31,51,53,57,59,63,65,71,74,79,80]},{\"tag\":\"block\",\"leaf\":1,\"vertices\":[12,23,26,31,51,53,57,59,63,65,71,72,79,80]},{\"tag\":\"block\",\"leaf\":2,\"vertices\":[12,19,27,31,51,53,54,62,63,67,70,73,78,80]},{\"tag\":\"block\",\"leaf\":3,\"vertices\":[12,16,27,31,51,53,54,63,66,67,70,73,78,80]},{\"tag\":\"block\",\"leaf\":4,\"vertices\":[11,21,24,28,46,49,59,60,63,68,72,75,79,82]},{\"tag\":\"block\",\"leaf\":5,\"vertices\":[8,21,24,28,49,51,59,60,63,68,72,75,79,82]},{\"tag\":\"block\",\"leaf\":6,\"vertices\":[8,21,27,28,49,51,59,60,63,68,69,75,79,82]},{\"tag\":\"block\",\"leaf\":7,\"vertices\":[9,21,24,29,46,52,59,60,63,68,72,75,78,82]},{\"tag\":\"edge\",\"edge\":24,\"owners\":[4,13,19,24,28,41,42,43,54,55,56,57,64,65,66,69,70,71,77,78,81,82]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[18,22,31,39,48,53,63,68,75,80]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[12,21,30,49,52,65,67,78,79]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[23,40,50,53,60,62,66,68,76,80,82]}]}"
  "429 -123 0 335 332 0\n430 149 0 380 379 0\n431 146 0 430 374 0\n432 -167 0 416 413 0\n433 -165 0 432 407 410 394 402 281 390 0\n434 -148 -80 0 179 175 173 367 369 343 364 12 22 28 37 345 0\n435 -35 46 -159 0 433 408 393 278 394 281 1 105 141 248 249 253 255 426 0\n436 -45 -57 -80 0 380 102 74 73 72 71 70 434 376 377 357 353 281 95 178 177 176 172 19 23 24 33 106 339 348 349 340 354 351 159 355 338 347 43 337 0\n437 46 48 -145 -159 0 394 281 76 363 344 436 364 435 345 0\n438 -41 -129 -80 0 281 95 172 32 156 340 0\n439 48 -145 -159 79 0 433 380 429 394 281 76 363 344 191 188 189 131 102 75 74 73 72 71 70 434 376 377 357 353 95 408 393 180 179 178 177 176 175 172 437 25 26 29 79 107 265 339 275 252 296 348 349 291 194 324 354 351 311 355 346 347 336 337 86 199 43 438 338 159 264 340 289 234 310 295 314 323 316 326 331 328 321 322 319 320 318 294 293 292 206 245 203 0\n440 -33 -125 37 53 30 -57 0 75 78 200 336 0\n441 -145 -159 161 0 380 394 434 376 377 357 353 281 95 76 178 177 176 172 400 397 386 401 382 363 344 70 71 72 73 74 102 131 189 188 191 439 34 36 39 108 145 208 339 348 349 340 354 351 159 358 355 338 378 346 347 43 373 360 361 440 337 110 134 342 341 126 0\n442 -48 145 69 64 60 55 54 34 0 380 37 108 343 339 366 349 375 354 378 358 0\n443 128 48 145 -136 63 78 74 69 54 34 31 0 380 348 349 354 358 378 375 366 343 9 22 31 235 340 0\n444 -147 -66 48 145 78 -58 74 69 54 38 34 31 0 105 106 107 345 278 95 76 366 368 343 362 9 16 31 344 233 235 232 102 217 218 215 220 216 219 427 0\n445 -40 -129 45 48 63 78 74 34 31 0 9 31 235 340 0\n446 70 -61 -9 -73 72 -49 -77 -26 -47 -57 -131 -66 -80 79 0 102 239 131 281 342 254 423 0\n447 -73 72 37 -49 -77 -26 -47 -57 40 -125 -131 -66 -80 160 0 41 102 239 281 191 187 189 75 70 106 179 172 398 384 397 386 146 228 336 446 192 422 0\n448 -68 71 -131 0 115 126 342 0\n449 70 -61 -73 72 -57 40 -129 -127 -126 -131 -66 78 -80 160 0 177 175 104 281 188 140 194 131 102 74 73 72 71 70 438 106 95 180 179 172 398 384 397 386 342 254 110 337 228 43 338 159 264 340 423 234 0\n450 -47 -70 -73 72 -57 40 41 -127 -126 -125 -131 -66 78 -80 160 0 179 70 172 281 187 192 75 142 191 189 146 336 177 175 104 188 140 194 102 74 73 72 71 180 42 234 239 338 223 447 221 337 421 0\n451 72 -129 -127 -126 -125 -131 -130 -66 48 78 -80 160 0 431 281 76 105 106 107 345 175 173 179 172 180 95 445 343 365 362 344 131 448 191 188 187 189 102 75 74 73 72 71 70 438 104 177 341 140 142 146 194 336 449 192 450 340 159 235 263 262 338 424 43 337 0\n452 -159 161 0 433 430 380 431 400 394 408 172 173 174 175 176 177 178 179 180 281 393 76 95 434 376 377 357 353 441 442 443 339 105 106 107 345 444 375 372 378 360 361 356 358 346 347 352 354 350 445 343 365 362 344 131 451 138 139 342 0\n453 60 64 -23 -72 -57 -78 80 0 430 380 73 71 279 45 72 133 160 163 272 164 345 364 369 131 138 139 342 361 373 378 356 347 337 43 358 354 350 349 352 346 372 366 229 136 132 102 75 74 70 48 167 166 165 161 274 339 62 65 66 190 251 343 336 120 157 338 340 241 417 0\n454 -60 -132 40 0 82 85 121 343 0\n455 -72 -57 -78 161 0 430 380 131 160 163 452 395 272 164 345 364 369 279 48 400 397 386 138 139 229 243 342 361 372 373 366 378 358 354 350 454 453 96 99 101 343 117 157 340 0\n456 -69 63 72 148 47 73 0 380 117 123 157 341 340 360 350 373 354 378 358 0\n457 -143 72 71 73 0 360 361 341 448 0\n458 -40 -126 42 39 36 -51 0 45 11 205 337 0\n459 -54 -128 60 66 0 66 99 339 0\n460 -34 -128 60 66 0 62 96 339 0\n461 -57 -78 161 0 430 380 160 163 452 395 272 164 345 364 369 370 279 48 45 167 166 165 161 69 70 71 72 73 74 75 102 131 455 457 372 373 366 378 356 358 346 347 352 354 458 454 349 459 460 343 116 120 122 123 236 456 341 91 101 224 231 359 339 183 342 60 61 65 81 251 195 337 336 43 222 338 418 0\n462 -137 64 -69 57 47 44 134 73 66 0 430 380 157 123 122 121 120 119 117 349 350 339 340 61 64 93 103 344 362 368 375 372 378 360 361 356 358 341 347 352 139 342 127 128 129 158 337 338 43 0\n463 -150 68 57 134 73 0 364 369 373 375 360 368 341 362 135 344 0\n464 -69 57 47 44 134 73 66 0 380 117 123 157 463 378 358 354 350 462 340 101 0\n465 -72 -128 57 134 -78 0 431 165 166 279 45 48 464 135 229 344 362 365 454 459 460 343 0\n466 144 72 -128 69 73 66 0 431 430 368 365 372 360 341 112 113 343 454 459 0\n467 60 -49 -25 -68 -71 -61 -52 -129 -128 -127 -78 58 0 43 158 130 166 257 64 52 51 279 48 165 162 160 339 246 101 211 340 338 240 420 0\n468 -76 -60 -49 -25 -68 -71 -61 -52 -127 -78 80 0 100 43 158 130 166 257 59 52 279 156 261 240 338 419 0\n469 -141 57 -78 80 0 430 165 166 160 163 272 164 345 279 45 48 464 364 161 280 356 358 346 347 352 354 349 350 465 466 362 344 49 50 51 52 53 54 56 59 68 80 336 86 87 256 198 201 225 181 343 366 372 360 457 341 129 130 158 202 337 43 467 468 340 92 103 338 0\n470 -78 161 0 380 452 395 272 160 163 164 165 166 279 345 45 48 364 461 464 469 378 375 463 366 368 112 113 362 343 344 59 0\n471 -52 -166 0 416 430 414 452 395 280 470 392 406 409 404 389 148 278 403 387 143 118 57 27 6 5 272 400 398 384 135 242 341 196 360 226 227 372 343 345 366 364 0\n472 134 57 -166 0 416 380 431 430 335 471 344 414 452 395 280 470 392 406 409 404 389 148 278 403 387 143 118 57 30 27 7 6 5 4 3 2 400 397 386 463 362 378 368 365 356 358 372 343 346 347 352 354 360 361 10 13 14 15 16 17 55 67 124 350 341 136 138 197 336 342 193 257 247 128 158 244 285 185 296 337 287 297 222 324 43 301 298 286 325 338 299 300 327 103 303 340 305 307 334 330 315 317 313 309 312 308 290 288 250 261 0\n473 -45 -166 0 416 471 414 452 395 280 470 392 406 409 404 389 148 278 403 387 118 57 400 398 384 397 386 401 382 18 21 22 23 97 237 238 258 259 212 213 207 210 209 425 0\n474 -143 -166 0 416 414 470 278 452 392 406 409 403 387 6 27 395 272 473 345 472 131 143 361 457 138 139 342 0\n475 -166 0 416 430 380 335 414 400 398 384 452 395 272 470 273 278 392 406 409 403 387 3 4 5 6 27 30 57 118 143 473 345 364 472 369 69 70 71 72 73 74 102 474 372 373 366 378 343 356 358 8 14 17 124 347 352 354 337 349 350 40 43 204 182 338 109 285 186 184 159 241 214 297 220 340 286 292 298 295 101 300 318 299 323 339 302 322 266 304 296 306 324 333 326 329 328 0\n476 -163 0 475 411 0\n477 161 0 475 415 412 0\n478 -72 0 477 137 155 170 381 383 385 399 396 0\n479 -40 -148 0 434 272 369 364 12 22 28 345 0\n480 -45 54 -148 0 367 479 454 434 280 272 20 46 97 106 163 343 118 149 267 428 0\n481 -46 -148 0 367 479 454 434 280 272 27 47 107 147 164 270 267 428 0\n482 -35 142 0 380 430 370 367 479 454 371 378 358 354 349 6 44 63 105 270 339 0\n483 142 0 430 380 370 371 367 369 434 378 364 272 358 354 349 479 454 481 482 345 106 480 459 0\n484 -68 0 477 114 152 168 381 383 385 399 396 0\n485 -70 0 477 125 153 169 381 383 385 399 396 0\n486 -55 38 -45 0 277 46 269 163 106 97 38 77 176 267 428 0\n487 80 74 38 48 58 60 51 64 66 78 0 428 271 0\n488 38 -45 143 0 380 46 269 163 106 97 38 277 486 339 349 354 358 378 373 434 280 487 0\n489 -38 0 476 276 388 391 405 0\n490 -74 0 489 277 0\n491 -48 57 0 34 35 58 84 94 98 268 260 76 77 442 344 363 0\n492 62 75 0 477 383 381 284 399 385 396 0\n493 -35 -71 0 490 489 154 492 88 131 491 44 83 105 160 435 270 395 280 487 0\n494 130 67 0 483 485 489 430 359 342 131 154 491 492 88 89 344 493 360 488 372 345 368 362 0\n495 75 79 0 492 282 0\n496 67 0 484 478 485 430 494 341 141 144 145 171 495 150 154 283 230 342 90 345 361 344 362 372 368 0\n497 -62 0 496 111 0\n498 -75 0 496 151 0\n499 0 497 498 492 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record022.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record022.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record022.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record022.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record022 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeafTable : ConcreteGrowth.Table (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record022.l) :=
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
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record022.l := originalLeafTable.get j.val
def orbitWordTable : ConcreteGrowth.Table (List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record022.g)) :=
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
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record022.g) := orbitWordTable.get j.val
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record022.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record022.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record022 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record022_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record022_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record022_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record022_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record022_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record022_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record022_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record022 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record022_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record022_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record022_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record022
