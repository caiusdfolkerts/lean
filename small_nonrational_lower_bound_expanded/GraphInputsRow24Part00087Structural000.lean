module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00087Data
public import GraphInputsRow24Part00087Frames
public import GraphInputsRow24Part00087Leaves
public import GraphInputsRow24Part00087Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00087.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record002
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨77, by decide⟩, ⟨80, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [13907115675089895424, (certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), 116549977374720, 3661098842587136]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record002_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00087.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00087.record009
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record009
def vertexColumn : Fields := ⟨10, (certNat% 6)⟩
def kindColumn : Fields := ⟨3, (certNat% 7)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), (certNat% 9), 9008298766368768, 2378045738786488320, 4504149383184384]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), 9008298766368768, 144123984168878080, 2378045738786488320]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), 2305847407260205056, 1305670057984, 8796093022208, (certNat% 12)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), 8864812498944, 4504149383184384, 1236950581248, (certNat% 14)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), 1030792151040, 144123984168878080, 13510798882111488, 2378045738786488320, 1099511627776]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c7 c0
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), (certNat% 17), 13510798882111488, 1729382274090139648, 18691697672192, (certNat% 18)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), 2308094809027379200, 18897889656832, 4503612512272384, (certNat% 20), (certNat% 14)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), 1161928703861587968, (certNat% 12), (certNat% 22), 578712556412076032]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), 2308094809027379200, 1855459426304, (certNat% 20), (certNat% 24), 4503603922337792]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), 1873497462165995520, (certNat% 27), 18691966107648, 10995116277760]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), 1873497444986126336, (certNat% 26), 28587302322176, 2378045738786488320, (certNat% 29)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 30), 74450135634935808, 1649300996096, 1297036709862572032, (certNat% 14), (certNat% 31)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 32), 1873497462165995520, (certNat% 33), (certNat% 34), 2380293140553662464, 4294967296]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 35), 2305847407260205056, (certNat% 36), 26388547502080, (certNat% 37)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c20 c21
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c20 c22
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c20 c23
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c20 c19
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c20 c25
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c20 c26
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c20 c27
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), 9007199254740992, (certNat% 39), 4402341478400]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c29 c28
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c30 c24
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), (certNat% 14), (certNat% 36), 4402341478400, 2308094809027379200]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c32 c31
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 41), (certNat% 42), (certNat% 36), 1161928703861587968, (certNat% 43)]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 44), 2380152403065307136, (certNat% 43), 26405727371264, 1161928703861587968, (certNat% 45)]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c35 c34
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c36 c33
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c37 c18
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), 2380293140553662464, 1161928721075011584, 26388547502080, (certNat% 47), (certNat% 18), 4402341478400]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c39 c38
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c40 c17
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c41 c16
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c42 c15
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c43 c14
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c44 c13
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c45 c10
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c46 c9
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c47 c8
  c48
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record009_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record009_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00087.record009

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00087.record010
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ae0f4572d2ac8f2aaa9a8e8ba398d62d8765392e8785e0fad1ac4f1aa699566392e4e5554d52d4755352d8751d176c370ea338e9394cd38ccb31cf0ba2d4b8ad2b2ae1b26c5b0ecc749ca719e1725c570de0f13c1f0f1464382ea44d12c6190e545154354342d0768350cc328e0b42c2b41c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6db6db49b49269a4d249249249269a6924926d2493692489249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record010 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record010 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record010.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record010.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record010.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 27), (facetIndex 35), (facetIndex 44), (facetIndex 61), (facetIndex 79)]))
 (.leaf ([(facetIndex 36), (facetIndex 50), (facetIndex 53), (facetIndex 54), (facetIndex 55), (facetIndex 56)])))
 (.branch 3
 (.leaf ([(facetIndex 57), (facetIndex 58), (facetIndex 62), (facetIndex 65)]))
 (.leaf ([(facetIndex 28), (facetIndex 40), (facetIndex 42), (facetIndex 43), (facetIndex 45), (facetIndex 46)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 59), (facetIndex 67), (facetIndex 68), (facetIndex 70)]))
 (.leaf ([(facetIndex 26), (facetIndex 60), (facetIndex 75), (facetIndex 78)])))
 (.branch 7
 (.leaf ([(facetIndex 63), (facetIndex 64), (facetIndex 72), (facetIndex 73), (facetIndex 74)]))
 (.branch 8
 (.leaf ([(facetIndex 29), (facetIndex 33), (facetIndex 34), (facetIndex 41)]))
 (.leaf ([(facetIndex 30), (facetIndex 37), (facetIndex 48), (facetIndex 52)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "50056660404402662054221111801080330337300810770087305z1a;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 38), (facetIndex 69)]))
 (.leaf ([(facetIndex 76), (facetIndex 91)])))
 (.branch 3
 (.leaf ([(facetIndex 31), (facetIndex 47), (facetIndex 66)]))
 (.branch 4
 (.leaf ([(facetIndex 39), (facetIndex 49), (facetIndex 71)]))
 (.leaf ([(facetIndex 80), (facetIndex 81), (facetIndex 83)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 84), (facetIndex 85), (facetIndex 87)]))
 (.leaf ([(facetIndex 82), (facetIndex 88), (facetIndex 92)])))
 (.branch 8
 (.leaf ([(facetIndex 86), (facetIndex 89), (facetIndex 93)]))
 (.branch 9
 (.leaf ([(facetIndex 32), (facetIndex 51)]))
 (.leaf ([(facetIndex 77), (facetIndex 90)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "761976575546440091000030000200000000000000803020000000300000082z1f;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4]
def grouped2_0003 : List Nat := [4, 5]
def grouped2_0004 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0005 : List Nat := [5]
def grouped2_0006 : List Nat := [6]
def grouped2_0007 : List Nat := [6, 7, 8]
def grouped2_0008 : List Nat := [7]
def grouped2_0009 : List Nat := [7, 8]
def grouped2_0010 : List Nat := [8]
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
def grouped3_0022 : List Nat := [5, 6]
def grouped3_0023 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0024 : List Nat := [6]
def grouped3_0025 : List Nat := [7]
def grouped3_0026 : List Nat := [7, 8, 9]
def grouped3_0027 : List Nat := [8]
def grouped3_0028 : List Nat := [8, 9]
def grouped3_0029 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record010 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record010_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00087.record010" "{\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00087.record010" 97

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00087.record010" "{\"ridges\":[[6,522],[7,162],[8,193],[10,642],[15,84],[18,536],[19,176],[20,81],[20,208],[21,656],[28,522],[30,84],[34,162],[36,194],[38,90],[40,529],[41,162],[43,522],[45,522],[45,642],[46,522],[47,114],[48,162],[50,194],[50,208],[51,594],[52,642],[53,162],[53,194],[54,162],[54,642],[55,193],[56,193],[56,642],[57,84],[59,536],[62,84],[63,176],[64,84],[64,208],[65,84],[67,176],[68,529],[68,536],[69,344],[70,536],[70,656],[71,680],[72,81],[72,176],[72,208],[73,176],[73,656],[74,208],[74,656],[76,90],[82,150],[86,656],[87,680],[88,114],[89,562],[89,656],[90,594],[91,344],[92,228],[93,656],[93,680]],\"owners\":[[6,522,[77,85,86,87],[28,40,43,45,46]],[28,522,[85,86,87],[6,40,43,45,46,77]],[43,522,[77,86],[6,28,40,45,46,85,87]],[45,522,[77,85],[6,28,40,43,46,86,87]],[46,522,[77,85,86,87],[6,28,40,43,45]],[7,162,[81,83,84,87,88,89],[34,41,48,53,54]],[34,162,[84,87,88,89],[7,41,48,53,54,81,83]],[41,162,[81,83,88,89],[7,34,48,53,54,84,87]],[48,162,[83,87],[7,34,41,53,54,81,84,88,89]],[53,162,[81,84,87,89],[7,34,41,48,54,83,88]],[54,162,[81,83,84,88],[7,34,41,48,53,87,89]],[8,193,[20,64,66,72,74],[36,53,55,56]],[55,193,[20,64,66,72,74],[8,36,53,56]],[56,193,[20,64,66,72],[8,36,53,55,74]],[36,194,[88,90],[8,50,53,55,56,82,83]],[50,194,[83],[8,36,53,55,56,82,88,90]],[53,194,[82,90],[8,36,50,55,56,83,88]],[10,642,[86,87,89,90],[45,52,54,56]],[45,642,[89,90],[10,52,54,56,86,87]],[52,642,[87],[10,45,54,56,86,89,90]],[54,642,[86,90],[10,45,52,56,87,89]],[56,642,[86,87,89],[10,45,52,54,90]],[20,81,[15,30,38,47,51,57,62,65,69],[50,72,74]],[72,81,[15,30,38,51,57,65,69],[20,47,50,62,74]],[15,84,[76,80,82,91,92],[30,57,62,64,65]],[30,84,[91,92],[15,57,62,64,65,76,80,82]],[57,84,[80,82,92],[15,30,62,64,65,76,91]],[62,84,[76,82,91],[15,30,57,64,65,80,92]],[64,84,[76,80,91],[15,30,57,62,65,82,92]],[65,84,[76,80,82,92],[15,30,57,62,64,91]],[40,529,[21,73,74],[18,32,49,51,52,59,68]],[68,529,[21,32,51,52,74],[18,40,49,59,73]],[18,536,[77,85,86,93],[40,59,68,70]],[59,536,[85,86,93],[18,40,68,70,77]],[68,536,[77,86],[18,40,59,70,85,93]],[70,536,[77,85],[18,40,59,68,86,93]],[19,176,[81,84,88,89,92,93],[48,63,67,72,73]],[63,176,[84,88,89,93],[19,48,67,72,73,81,92]],[67,176,[81,88,89,92],[19,48,63,72,73,84,93]],[72,176,[81,84,89,93],[19,48,63,67,73,88,92]],[73,176,[81,84,88,92],[19,48,63,67,72,89,93]],[20,208,[82,88,90,92],[50,64,72,74]],[50,208,[92],[20,64,72,74,82,88,90]],[64,208,[88,90],[20,50,72,74,82,92]],[72,208,[82,90],[20,50,64,74,88,92]],[74,208,[82,88,92],[20,50,64,72,90]],[21,656,[86,89,90,93],[52,70,73,74]],[70,656,[89,90],[21,52,73,74,86,93]],[73,656,[86,90],[21,52,70,74,89,93]],[74,656,[86,89,93],[21,52,70,73,90]],[86,656,[21,73,74],[52,70,89,90,93]],[89,656,[21,70,74],[52,73,86,90,93]],[93,656,[21,52,74,90],[70,73,86,89]],[82,150,[31,81],[]],[38,90,[76],[]],[76,90,[38],[]],[47,114,[80,88],[]],[88,114,[47,80],[]],[89,562,[49,85],[]],[51,594,[90],[]],[90,594,[51],[]],[92,228,[66,83],[]],[69,344,[91],[]],[91,344,[69],[]],[71,680,[87,93],[]],[87,680,[71,93],[]],[93,680,[71,87],[]]],\"edges\":[[16,[6,10,28,32,40,43,45,46,49,51,52,54,56,77,85,86,87,89,90]],[31,[15,20,30,38,47,50,51,57,62,64,65,69,72,74,76,80,82,88,90,91,92]],[34,[18,21,32,40,49,51,52,59,68,70,73,74,77,85,86,89,90,93]],[36,[7,19,34,41,48,53,54,63,66,67,71,72,73,81,83,84,87,88,89,92,93]],[39,[8,20,36,50,53,55,56,64,66,72,74,82,83,88,90,92]],[43,[10,21,45,52,54,56,70,71,73,74,86,87,89,90,93]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00087.record010" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00087.record010\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-34,-17],[-45,-9],[-45,-28],[-45,-43],[-46,-45],[-47,-45],[-48,-16],[-48,-24],[-48,-28],[-49,-48],[-50,-39],[-51,-48],[-52,-13],[-52,-18],[-52,-25],[-52,-28],[-52,-49],[-53,-50],[-54,-27],[-55,-27],[-55,-48],[-55,-52],[-56,-48],[-56,-52],[-58,-13],[-58,-18],[-58,-25],[-58,-28],[-58,-49],[-58,-55],[-58,-56],[-59,-48],[-59,-52],[-59,-58],[-60,-54],[-60,-55],[-1,49,55,56,57],[-10,55,56,57],[-20,49,56],[-21,49,55],[-22,49,55,56,57],[-2,51,53,54,57,58,59],[-14,54,57,58,59],[-19,51,53,58,59],[-24,53,57],[-29,51,54,57,59],[-30,51,53,54,58],[-3,8,37,39,45,47],[-31,8,37,39,45,47],[-32,8,37,39,45],[-15,58,60],[-26,53],[-29,52,60],[-4,56,57,59,60],[-21,59,60],[-28,57],[-30,56,60],[-32,56,57,59],[-8,5,11,17,23,27,33,35,38,42],[-45,5,11,17,27,33,38,42],[-5,48,50,52,61,62],[-11,61,62],[-33,50,52,62],[-35,48,52,61],[-37,48,50,61],[-38,48,50,52,62],[-18,9,46,47],[-41,9,13,27,28,47],[-6,49,55,56,63],[-34,55,56,63],[-41,49,56],[-43,49,55],[-7,51,54,58,59,62,63],[-36,54,58,59,63],[-40,51,58,59,62],[-45,51,54,59,63],[-46,51,54,58,62],[-8,52,58,60,62],[-26,62],[-37,58,60],[-45,52,60],[-47,52,58,62],[-9,56,59,60,63],[-43,59,60],[-46,56,60],[-47,56,59,63],[-56,9,46,47],[-59,9,43,47],[-63,9,28,47,60],[-52,12,51],[-17,48],[-48,17],[-23,50,58],[-58,23,50],[-59,25,55],[-27,60],[-60,27],[-62,39,53],[-42,61],[-61,42],[-44,57,63],[-57,44,63],[-63,44,57],[-64,34,40,41,43],[-65,11,16,24,28],[-66,64],[-67,65],[-68,67],[-69,66,68],[-70,69],[70],[-17,71],[-42,71],[-48,72],[-61,72],[-12,73],[-23,73],[-39,73],[-25,74],[-44,74],[-50,75],[-51,75],[-53,75],[-76,54,55,57],[-54,76],[-55,76],[-57,76],[-52,77],[-58,77],[-62,77],[-56,78],[-59,78],[-63,78],[-27,79],[-60,80],[-72,81],[-71,81],[-71,-72,82],[-75,83],[-74,83],[-83,84],[-73,84],[-84,85],[-81,85],[-82,86],[-82,-84,87],[-77,88],[-76,88],[-76,-77,89],[-80,90],[-79,90],[-79,-80,91],[-91,93],[-78,92],[-78,-90,93],[-93,95],[-88,94],[-88,-92,95],[-88,-93,96],[-89,95],[-96,97],[-85,-95,97],[-86,-94,97],[-87,97],[-97],[1,4,10,13,18,20,21,22,25,27,28,30,32,49,55,56,57,59,60],[5,8,11,17,23,26,27,33,35,37,38,42,45,47,48,50,52,58,60,61,62],[6,9,13,18,25,27,28,34,41,43,46,47,49,55,56,59,60,63],[2,7,14,19,24,29,30,36,39,40,44,45,46,51,53,54,57,58,59,62,63],[3,8,15,26,29,31,32,37,39,45,47,52,53,58,60,62],[4,9,21,28,30,32,43,44,46,47,56,57,59,60,63]],\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":59,\"b\":38},{\"tag\":\"incompatible\",\"a\":72,\"b\":21},{\"tag\":\"incompatible\",\"a\":72,\"b\":52},{\"tag\":\"incompatible\",\"a\":72,\"b\":70},{\"tag\":\"incompatible\",\"a\":73,\"b\":72},{\"tag\":\"incompatible\",\"a\":74,\"b\":72},{\"tag\":\"incompatible\",\"a\":76,\"b\":37},{\"tag\":\"incompatible\",\"a\":76,\"b\":48},{\"tag\":\"incompatible\",\"a\":76,\"b\":52},{\"tag\":\"incompatible\",\"a\":77,\"b\":76},{\"tag\":\"incompatible\",\"a\":80,\"b\":66},{\"tag\":\"incompatible\",\"a\":81,\"b\":76},{\"tag\":\"incompatible\",\"a\":82,\"b\":32},{\"tag\":\"incompatible\",\"a\":82,\"b\":40},{\"tag\":\"incompatible\",\"a\":82,\"b\":49},{\"tag\":\"incompatible\",\"a\":82,\"b\":52},{\"tag\":\"incompatible\",\"a\":82,\"b\":77},{\"tag\":\"incompatible\",\"a\":83,\"b\":80},{\"tag\":\"incompatible\",\"a\":84,\"b\":51},{\"tag\":\"incompatible\",\"a\":85,\"b\":51},{\"tag\":\"incompatible\",\"a\":85,\"b\":76},{\"tag\":\"incompatible\",\"a\":85,\"b\":82},{\"tag\":\"incompatible\",\"a\":86,\"b\":76},{\"tag\":\"incompatible\",\"a\":86,\"b\":82},{\"tag\":\"incompatible\",\"a\":88,\"b\":32},{\"tag\":\"incompatible\",\"a\":88,\"b\":40},{\"tag\":\"incompatible\",\"a\":88,\"b\":49},{\"tag\":\"incompatible\",\"a\":88,\"b\":52},{\"tag\":\"incompatible\",\"a\":88,\"b\":77},{\"tag\":\"incompatible\",\"a\":88,\"b\":85},{\"tag\":\"incompatible\",\"a\":88,\"b\":86},{\"tag\":\"incompatible\",\"a\":89,\"b\":76},{\"tag\":\"incompatible\",\"a\":89,\"b\":82},{\"tag\":\"incompatible\",\"a\":89,\"b\":88},{\"tag\":\"incompatible\",\"a\":90,\"b\":84},{\"tag\":\"incompatible\",\"a\":90,\"b\":85},{\"tag\":\"mate\",\"ridge\":522,\"a\":6,\"owners\":[77,85,86,87]},{\"tag\":\"mate\",\"ridge\":522,\"a\":28,\"owners\":[85,86,87]},{\"tag\":\"mate\",\"ridge\":522,\"a\":43,\"owners\":[77,86]},{\"tag\":\"mate\",\"ridge\":522,\"a\":45,\"owners\":[77,85]},{\"tag\":\"mate\",\"ridge\":522,\"a\":46,\"owners\":[77,85,86,87]},{\"tag\":\"mate\",\"ridge\":162,\"a\":7,\"owners\":[81,83,84,87,88,89]},{\"tag\":\"mate\",\"ridge\":162,\"a\":34,\"owners\":[84,87,88,89]},{\"tag\":\"mate\",\"ridge\":162,\"a\":41,\"owners\":[81,83,88,89]},{\"tag\":\"mate\",\"ridge\":162,\"a\":48,\"owners\":[83,87]},{\"tag\":\"mate\",\"ridge\":162,\"a\":53,\"owners\":[81,84,87,89]},{\"tag\":\"mate\",\"ridge\":162,\"a\":54,\"owners\":[81,83,84,88]},{\"tag\":\"mate\",\"ridge\":193,\"a\":8,\"owners\":[20,64,66,72,74]},{\"tag\":\"mate\",\"ridge\":193,\"a\":55,\"owners\":[20,64,66,72,74]},{\"tag\":\"mate\",\"ridge\":193,\"a\":56,\"owners\":[20,64,66,72]},{\"tag\":\"mate\",\"ridge\":194,\"a\":36,\"owners\":[88,90]},{\"tag\":\"mate\",\"ridge\":194,\"a\":50,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":194,\"a\":53,\"owners\":[82,90]},{\"tag\":\"mate\",\"ridge\":642,\"a\":10,\"owners\":[86,87,89,90]},{\"tag\":\"mate\",\"ridge\":642,\"a\":45,\"owners\":[89,90]},{\"tag\":\"mate\",\"ridge\":642,\"a\":52,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":642,\"a\":54,\"owners\":[86,90]},{\"tag\":\"mate\",\"ridge\":642,\"a\":56,\"owners\":[86,87,89]},{\"tag\":\"mate\",\"ridge\":81,\"a\":20,\"owners\":[15,30,38,47,51,57,62,65,69]},{\"tag\":\"mate\",\"ridge\":81,\"a\":72,\"owners\":[15,30,38,51,57,65,69]},{\"tag\":\"mate\",\"ridge\":84,\"a\":15,\"owners\":[76,80,82,91,92]},{\"tag\":\"mate\",\"ridge\":84,\"a\":30,\"owners\":[91,92]},{\"tag\":\"mate\",\"ridge\":84,\"a\":57,\"owners\":[80,82,92]},{\"tag\":\"mate\",\"ridge\":84,\"a\":62,\"owners\":[76,82,91]},{\"tag\":\"mate\",\"ridge\":84,\"a\":64,\"owners\":[76,80,91]},{\"tag\":\"mate\",\"ridge\":84,\"a\":65,\"owners\":[76,80,82,92]},{\"tag\":\"mate\",\"ridge\":529,\"a\":40,\"owners\":[21,73,74]},{\"tag\":\"mate\",\"ridge\":529,\"a\":68,\"owners\":[21,32,51,52,74]},{\"tag\":\"mate\",\"ridge\":536,\"a\":18,\"owners\":[77,85,86,93]},{\"tag\":\"mate\",\"ridge\":536,\"a\":59,\"owners\":[85,86,93]},{\"tag\":\"mate\",\"ridge\":536,\"a\":68,\"owners\":[77,86]},{\"tag\":\"mate\",\"ridge\":536,\"a\":70,\"owners\":[77,85]},{\"tag\":\"mate\",\"ridge\":176,\"a\":19,\"owners\":[81,84,88,89,92,93]},{\"tag\":\"mate\",\"ridge\":176,\"a\":63,\"owners\":[84,88,89,93]},{\"tag\":\"mate\",\"ridge\":176,\"a\":67,\"owners\":[81,88,89,92]},{\"tag\":\"mate\",\"ridge\":176,\"a\":72,\"owners\":[81,84,89,93]},{\"tag\":\"mate\",\"ridge\":176,\"a\":73,\"owners\":[81,84,88,92]},{\"tag\":\"mate\",\"ridge\":208,\"a\":20,\"owners\":[82,88,90,92]},{\"tag\":\"mate\",\"ridge\":208,\"a\":50,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":208,\"a\":64,\"owners\":[88,90]},{\"tag\":\"mate\",\"ridge\":208,\"a\":72,\"owners\":[82,90]},{\"tag\":\"mate\",\"ridge\":208,\"a\":74,\"owners\":[82,88,92]},{\"tag\":\"mate\",\"ridge\":656,\"a\":21,\"owners\":[86,89,90,93]},{\"tag\":\"mate\",\"ridge\":656,\"a\":70,\"owners\":[89,90]},{\"tag\":\"mate\",\"ridge\":656,\"a\":73,\"owners\":[86,90]},{\"tag\":\"mate\",\"ridge\":656,\"a\":74,\"owners\":[86,89,93]},{\"tag\":\"mate\",\"ridge\":656,\"a\":86,\"owners\":[21,73,74]},{\"tag\":\"mate\",\"ridge\":656,\"a\":89,\"owners\":[21,70,74]},{\"tag\":\"mate\",\"ridge\":656,\"a\":93,\"owners\":[21,52,74,90]},{\"tag\":\"mate\",\"ridge\":150,\"a\":82,\"owners\":[31,81]},{\"tag\":\"mate\",\"ridge\":90,\"a\":38,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":90,\"a\":76,\"owners\":[38]},{\"tag\":\"mate\",\"ridge\":114,\"a\":47,\"owners\":[80,88]},{\"tag\":\"mate\",\"ridge\":114,\"a\":88,\"owners\":[47,80]},{\"tag\":\"mate\",\"ridge\":562,\"a\":89,\"owners\":[49,85]},{\"tag\":\"mate\",\"ridge\":594,\"a\":51,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":594,\"a\":90,\"owners\":[51]},{\"tag\":\"mate\",\"ridge\":228,\"a\":92,\"owners\":[66,83]},{\"tag\":\"mate\",\"ridge\":344,\"a\":69,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":344,\"a\":91,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":680,\"a\":71,\"owners\":[87,93]},{\"tag\":\"mate\",\"ridge\":680,\"a\":87,\"owners\":[71,93]},{\"tag\":\"mate\",\"ridge\":680,\"a\":93,\"owners\":[71,87]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[59,67,68,70],\"full_literals\":[-64,34,40,41,43]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[30,37,48,52],\"full_literals\":[-65,11,16,24,28]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-66,64,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-67,false,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-68,false,67],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-69,66,68],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-70,false,69],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":38,\"full_literals\":[-17,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":69,\"full_literals\":[-42,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":76,\"full_literals\":[-48,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":91,\"full_literals\":[-61,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":31,\"full_literals\":[-12,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":47,\"full_literals\":[-23,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":66,\"full_literals\":[-39,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":49,\"full_literals\":[-25,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":71,\"full_literals\":[-44,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":80,\"full_literals\":[-50,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":81,\"full_literals\":[-51,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":83,\"full_literals\":[-53,75]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[84,85,87],\"full_literals\":[-76,54,55,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":84,\"full_literals\":[-54,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":85,\"full_literals\":[-55,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":87,\"full_literals\":[-57,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":82,\"full_literals\":[-52,77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":88,\"full_literals\":[-58,77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":92,\"full_literals\":[-62,77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":86,\"full_literals\":[-56,78]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":89,\"full_literals\":[-59,78]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":93,\"full_literals\":[-63,78]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":51,\"full_literals\":[-27,79]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":90,\"full_literals\":[-60,80]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-72,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-71,false,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-71,-72,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-75,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-74,false,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-83,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-73,false,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-84,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-81,false,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-82,false,86],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-82,-84,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-77,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-76,false,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-76,-77,89],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-80,90],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-79,false,90],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-79,-80,91],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-91,93],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-78,false,92],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-78,-90,93],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-93,95],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-88,false,94],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-88,-92,95],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-88,-93,96],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-89,false,95],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-96,97],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-85,-95,97],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-86,-94,97],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-87,false,97],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":16,\"owners\":[6,10,28,32,40,43,45,46,49,51,52,54,56,77,85,86,87,89,90]},{\"tag\":\"edge\",\"edge\":31,\"owners\":[15,20,30,38,47,50,51,57,62,64,65,69,72,74,76,80,82,88,90,91,92]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[18,21,32,40,49,51,52,59,68,70,73,74,77,85,86,89,90,93]},{\"tag\":\"edge\",\"edge\":36,\"owners\":[7,19,34,41,48,53,54,63,66,67,71,72,73,81,83,84,87,88,89,92,93]},{\"tag\":\"edge\",\"edge\":39,\"owners\":[8,20,36,50,53,55,56,64,66,72,74,82,83,88,90,92]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[10,21,45,52,54,56,70,71,73,74,86,87,89,90,93]}]}"
  "172 69 0 111 110 0\n173 -96 0 165 161 0\n174 -87 0 165 164 0\n175 76 84 0 142 118 141 139 123 98 117 121 94 140 120 119 122 125 126 127 47 77 95 45 103 44 43 74 46 76 42 75 73 169 0\n176 -54 85 0 143 142 116 141 139 122 90 121 144 136 114 118 123 98 66 63 115 62 61 64 117 94 82 52 65 137 113 112 19 35 60 59 167 0\n177 -55 85 0 143 142 116 141 139 122 90 121 144 136 114 118 123 98 66 63 115 62 61 64 117 94 82 52 65 137 113 112 20 36 60 59 167 0\n178 60 62 5 38 17 26 27 33 11 23 37 42 35 47 48 50 52 58 45 61 0 167 78 0\n179 85 0 173 143 144 141 142 136 137 139 140 116 117 118 114 115 112 113 121 122 123 120 65 94 90 52 98 82 64 61 62 63 66 175 148 159 176 177 124 102 133 155 150 151 135 134 81 178 0\n180 -95 0 179 165 162 0\n181 -93 0 180 156 0\n182 -89 0 180 160 0\n183 -91 0 181 153 0\n184 48 50 52 60 61 45 58 62 0 63 93 82 80 96 62 99 79 91 64 66 61 178 0\n185 -48 11 58 62 0 172 7 8 9 10 12 21 23 32 92 105 72 71 75 1 107 104 108 106 109 0\n186 52 60 61 45 58 62 0 80 51 62 185 79 82 53 78 184 11 18 48 50 49 170 0\n187 60 61 45 58 62 0 182 96 186 13 14 15 16 17 22 24 33 128 40 39 57 149 127 38 54 37 41 58 166 0\n188 -60 0 183 97 135 134 152 0\n189 -27 0 188 96 0\n190 -82 0 174 165 145 146 163 175 157 148 0\n191 -61 0 190 100 115 113 138 0\n192 -45 0 188 189 2 3 4 5 6 81 67 89 88 87 13 15 17 22 70 69 68 168 0\n193 -58 0 182 188 189 25 26 27 28 29 30 31 34 129 40 39 57 149 127 38 54 37 41 58 166 0\n194 62 0 193 188 191 192 187 0\n195 77 0 194 130 0\n196 88 0 195 147 0\n197 -76 0 195 182 149 0\n198 -92 0 196 180 158 0\n199 -57 0 197 127 0\n200 -78 0 198 154 0\n201 -28 0 199 56 0\n202 -56 0 200 131 0\n203 -59 0 200 132 0\n204 -63 0 200 133 0\n205 -30 0 202 188 57 0\n206 -46 0 202 188 85 0\n207 -32 0 202 199 203 58 0\n208 -21 0 203 188 55 0\n209 -43 0 203 188 84 0\n210 -4 0 203 188 199 202 54 0\n211 -9 0 204 203 202 188 83 0\n212 -47 0 204 203 202 86 0\n213 -44 0 204 199 101 0\n214 0 210 213 199 201 205 207 209 204 206 212 202 208 203 188 211 171 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record010.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record010.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record010.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record010.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record010 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record010.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record010.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record010.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record010.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record010 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record010_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record010 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record010_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record010_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00087.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00087.record012
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3e2b42f2d2ac8f23a8da2e87a55a365392e1783eb46b13c5c93a4d92e479a9695556352d68d5352d2b49d1743db0ea338e9394d5334e332cc73a2ccb4acab1ac9b16c3bc1d4789d2745c5783c4f07d4a858364382ea44d12c549324a9854354342d50e1314c3342c4b0ae0741c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6db6926924924da69349369b6924926924d2492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record012 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record012 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record012.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record012.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record012.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 55), (facetIndex 63)]))
 (.leaf ([(facetIndex 75), (facetIndex 79)])))
 (.branch 3
 (.leaf ([(facetIndex 56), (facetIndex 60), (facetIndex 65)]))
 (.leaf ([(facetIndex 38), (facetIndex 43), (facetIndex 51), (facetIndex 52), (facetIndex 53)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 81), (facetIndex 83), (facetIndex 85), (facetIndex 86)]))
 (.leaf ([(facetIndex 66), (facetIndex 82), (facetIndex 84)])))
 (.branch 7
 (.leaf ([(facetIndex 80), (facetIndex 87)]))
 (.branch 8
 (.leaf ([(facetIndex 89)]))
 (.leaf ([(facetIndex 88)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "7864454546100010000000052000020002003330000000300003z26;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record012 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record012_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00087.record012" "{\"atoms\":[{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00087.record012" 46

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00087.record012" "{\"ridges\":[[16,168],[17,200],[21,641],[38,154],[40,168],[42,200],[43,650],[50,641],[52,674],[53,706],[56,156],[57,168],[60,652],[64,641],[65,676],[67,168],[68,200],[68,208],[69,200],[70,200],[72,641],[73,641],[85,674],[86,706],[88,676]],\"owners\":[[16,168,[81,83,87,89],[40,57,67,69]],[40,168,[87,89],[16,57,67,69,81,83]],[57,168,[81,83,89],[16,40,67,69,87]],[67,168,[83],[16,40,57,69,81,87,89]],[17,200,[82,83,89],[42,68,69,70]],[42,200,[89],[17,68,69,70,82,83]],[68,200,[83],[17,42,69,70,82,89]],[69,200,[82],[17,42,68,70,83,89]],[70,200,[82,83,89],[17,42,68,69]],[68,208,[84,86],[20,47,71,73,82,89]],[21,641,[43,52,53,60,65],[50,64,72,73]],[50,641,[60,65],[21,43,52,53,64,72,73]],[64,641,[43,52,53],[21,50,60,65,72,73]],[72,641,[43,53,60],[21,50,52,64,65,73]],[73,641,[43,52,60,65],[21,50,53,64,72]],[38,154,[81,82],[]],[43,650,[],[]],[52,674,[85],[]],[85,674,[52],[]],[53,706,[86],[]],[86,706,[53],[]],[56,156,[87],[]],[60,652,[],[]],[65,676,[88],[]],[88,676,[65],[]]],\"edges\":[[27,[16,17,38,40,42,43,56,57,60,67,68,69,70,81,82,83,87,89]],[43,[21,43,50,52,53,60,64,65,72,73,85,86,88]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00087.record012" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00087.record012\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-9,-4],[-9,-5],[-9,-6],[-10,-4],[-10,-5],[-10,-6],[-15,-11],[-15,-12],[-16,-9],[-16,-15],[-17,-10],[-22,-9],[-22,-10],[-23,-9],[-23,-10],[-24,-9],[-24,-10],[-28,-15],[-1,22,24,28,30],[-5,28,30],[-12,22,24,30],[-16,24],[-2,23,24,30],[-6,30],[-17,24],[-18,23],[-19,23,24,30],[-17,25,27],[-3,7,9,10,13,15],[-8,13,15],[-14,7,9,10],[-20,7,10,13],[-21,7,9,13,15],[-4,22,23],[-7],[-9,26],[-26,9],[-10,27],[-27,10],[-11,28],[-13],[-15,29],[-29,15],[-15,31],[-9,32],[-10,32],[-22,33],[-24,33],[-26,33],[-27,33],[-23,34],[-25,34],[-28,35],[-30,36],[-29,37],[-32,38],[-31,38],[-38,39],[-34,40],[-33,40],[-37,41],[-36,41],[-36,-37,42],[-41,43],[-42,44],[-35,43],[-44,45],[-40,-43,45],[-39,-45,46],[-46],[1,2,4,5,6,7,11,12,13,16,17,18,19,22,23,24,28,30],[3,7,8,9,10,13,14,15,20,21,26,27,29]],\"atoms\":[{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":52,\"b\":38},{\"tag\":\"incompatible\",\"a\":52,\"b\":40},{\"tag\":\"incompatible\",\"a\":52,\"b\":42},{\"tag\":\"incompatible\",\"a\":53,\"b\":38},{\"tag\":\"incompatible\",\"a\":53,\"b\":40},{\"tag\":\"incompatible\",\"a\":53,\"b\":42},{\"tag\":\"incompatible\",\"a\":65,\"b\":56},{\"tag\":\"incompatible\",\"a\":65,\"b\":57},{\"tag\":\"incompatible\",\"a\":67,\"b\":52},{\"tag\":\"incompatible\",\"a\":67,\"b\":65},{\"tag\":\"incompatible\",\"a\":68,\"b\":53},{\"tag\":\"incompatible\",\"a\":81,\"b\":52},{\"tag\":\"incompatible\",\"a\":81,\"b\":53},{\"tag\":\"incompatible\",\"a\":82,\"b\":52},{\"tag\":\"incompatible\",\"a\":82,\"b\":53},{\"tag\":\"incompatible\",\"a\":83,\"b\":52},{\"tag\":\"incompatible\",\"a\":83,\"b\":53},{\"tag\":\"incompatible\",\"a\":87,\"b\":65},{\"tag\":\"mate\",\"ridge\":168,\"a\":16,\"owners\":[81,83,87,89]},{\"tag\":\"mate\",\"ridge\":168,\"a\":40,\"owners\":[87,89]},{\"tag\":\"mate\",\"ridge\":168,\"a\":57,\"owners\":[81,83,89]},{\"tag\":\"mate\",\"ridge\":168,\"a\":67,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":200,\"a\":17,\"owners\":[82,83,89]},{\"tag\":\"mate\",\"ridge\":200,\"a\":42,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":200,\"a\":68,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":200,\"a\":69,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":200,\"a\":70,\"owners\":[82,83,89]},{\"tag\":\"mate\",\"ridge\":208,\"a\":68,\"owners\":[84,86]},{\"tag\":\"mate\",\"ridge\":641,\"a\":21,\"owners\":[43,52,53,60,65]},{\"tag\":\"mate\",\"ridge\":641,\"a\":50,\"owners\":[60,65]},{\"tag\":\"mate\",\"ridge\":641,\"a\":64,\"owners\":[43,52,53]},{\"tag\":\"mate\",\"ridge\":641,\"a\":72,\"owners\":[43,53,60]},{\"tag\":\"mate\",\"ridge\":641,\"a\":73,\"owners\":[43,52,60,65]},{\"tag\":\"mate\",\"ridge\":154,\"a\":38,\"owners\":[81,82]},{\"tag\":\"mate\",\"ridge\":650,\"a\":43,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":674,\"a\":52,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":674,\"a\":85,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":706,\"a\":53,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":706,\"a\":86,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":156,\"a\":56,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":652,\"a\":60,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":676,\"a\":65,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":676,\"a\":88,\"owners\":[65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":65,\"full_literals\":[-15,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":52,\"full_literals\":[-9,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":53,\"full_literals\":[-10,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":81,\"full_literals\":[-22,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":83,\"full_literals\":[-24,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":85,\"full_literals\":[-26,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":86,\"full_literals\":[-27,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":82,\"full_literals\":[-23,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":84,\"full_literals\":[-25,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":87,\"full_literals\":[-28,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":89,\"full_literals\":[-30,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":88,\"full_literals\":[-29,37]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-32,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-31,false,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-38,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-34,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-33,false,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-37,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-36,false,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-36,-37,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-42,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-35,false,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-44,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-40,-43,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-39,-45,46],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":27,\"owners\":[16,17,38,40,42,43,56,57,60,67,68,69,70,81,82,83,87,89]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[21,43,50,52,53,60,64,65,72,73,85,86,88]}]}"
  "73 1 2 4 5 6 11 12 16 17 18 19 22 23 24 28 30 0 35 41 71 0\n74 3 8 9 10 14 15 20 21 26 27 29 0 35 41 72 0\n75 9 15 10 0 41 35 29 31 33 37 32 39 30 43 74 0\n76 38 0 56 57 45 46 44 75 0\n77 39 0 76 58 0\n78 -45 0 77 70 69 0\n79 -44 0 78 67 0\n80 -42 0 79 65 0\n81 -9 0 78 1 2 3 9 12 14 16 36 26 25 49 60 68 64 66 62 53 54 40 19 21 23 27 73 0\n82 -10 0 78 4 5 6 11 13 15 17 38 26 22 50 60 68 64 66 62 53 54 40 19 21 23 27 73 0\n83 -27 0 82 39 0\n84 15 0 82 81 75 0\n85 -11 0 84 7 0\n86 -12 0 84 8 0\n87 -16 0 84 10 0\n88 -28 0 84 18 0\n89 29 0 84 42 0\n90 37 0 89 55 0\n91 41 0 90 61 0\n92 -36 0 90 80 63 0\n93 43 0 91 64 0\n94 -30 0 92 54 0\n95 -40 0 93 78 68 0\n96 -6 0 94 24 0\n97 -5 0 94 88 20 0\n98 -34 0 95 59 0\n99 -33 0 95 60 0\n100 -23 0 98 51 0\n101 -25 0 98 52 0\n102 -22 0 99 47 0\n103 -24 0 99 48 0\n104 -18 0 100 26 0\n105 -2 0 100 103 94 23 0\n106 -19 0 100 103 94 27 0\n107 -17 0 101 83 28 0\n108 -4 0 102 100 34 0\n109 -1 0 102 103 88 94 19 0\n110 0 105 107 109 108 97 85 86 87 96 104 106 102 100 103 88 94 73 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record012.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record012.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record012.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record012.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record012 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record012.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record012.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record012.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record012.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record012 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record012_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record012 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record012_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record012_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00087.record012
