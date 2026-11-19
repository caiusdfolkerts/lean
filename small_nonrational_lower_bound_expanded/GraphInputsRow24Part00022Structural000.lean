module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00022Data
public import GraphInputsRow24Part00022Frames
public import GraphInputsRow24Part00022Leaves
public import GraphInputsRow24Part00022Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00022.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record000
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨36, by decide⟩, ⟨41, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨55, by decide⟩, ⟨59, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨79, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 612489549339164672, 1688854155231232, (certNat% 3), (certNat% 4), 281474976710656]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), 1724038527320064, (certNat% 3), (certNat% 6), (certNat% 4), 9223512774343131136]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), 844431372582912, 9225623836936896512, (certNat% 9), (certNat% 10), (certNat% 4)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record000_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00022.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00022.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record003
def vertexColumn : Fields := ⟨10, (certNat% 11)⟩
def kindColumn : Fields := ⟨3, (certNat% 12)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨26, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨56, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨71, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨81, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 14), (certNat% 15), 562956395872256, (certNat% 16), 9126805504]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), 3377699720527872, (certNat% 18), 562956395872256, (certNat% 16), (certNat% 19)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), (certNat% 21), (certNat% 22), (certNat% 23), (certNat% 24)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), (certNat% 27), (certNat% 28)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), 3377699720527872, (certNat% 23), (certNat% 27), (certNat% 30), (certNat% 31)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 32), (certNat% 24), (certNat% 14), 2322168557862912, 4611686018427387904]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), (certNat% 34), (certNat% 35), (certNat% 36), 3448068464705536, 4611686018427387904]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), (certNat% 38), (certNat% 39), (certNat% 40), 563089548247040]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 41), (certNat% 42), (certNat% 43), 4616189618121867264, (certNat% 39), (certNat% 40)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 44), (certNat% 35), (certNat% 45), 4611967493404098560, (certNat% 21), 8589934592]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), (certNat% 31), (certNat% 47), (certNat% 48), 1689951519375360, 72057731485270016]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 49), (certNat% 43), (certNat% 50), (certNat% 51), 563089548247040, 72057594037927936, 4616189618121867264]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c16 c11
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c17 c10
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c18 c9
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c19 c6
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c20 c1
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c21 c0
  c22
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record003_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00022.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00022.record005
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record005
def vertexColumn : Fields := ⟨10, (certNat% 52)⟩
def kindColumn : Fields := ⟨3, (certNat% 53)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 54), (certNat% 55), (certNat% 56), (certNat% 57), 285890471526400]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [3262896721100800, (certNat% 58), (certNat% 59), 756604737398243328, (certNat% 60), 72057594037927936]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [252201582488190976, 576460769483292672, (certNat% 61), 427718881574912, (certNat% 62), (certNat% 63), 4611704229088722944]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record005_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record005_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00022.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00022.record011
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "f81f3923c9ca3a8da2e87ac59968d876c398e4b86e2785e0fb913c5c93a4d92e479c55958d475c358d4b46d2745d0f78370ce3c4e9364e5334e332cc73c2d8b52ccb4acab1ac9b16c3bc1d8789d2719e1745c9715c3783d0f23c4f0bc1f34872628ca1ab06858364382e34471624c91a705854354342d"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db49269349249b4d249a4d24926d36db6d369a69b4db4db69b69a6d3249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record011 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record011 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record011.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record011.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record011.data.quota

def groupMembers1 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 10
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
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 5)]))
 (.leaf ([(facetIndex 6)])))
 (.branch 8
 (.leaf ([(facetIndex 7)]))
 (.branch 9
 (.leaf ([(facetIndex 8)]))
 (.leaf ([(facetIndex 9)]))))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ([(facetIndex 10)]))
 (.leaf ([(facetIndex 11)])))
 (.branch 13
 (.leaf ([(facetIndex 12)]))
 (.branch 14
 (.leaf ([(facetIndex 13)]))
 (.leaf ([(facetIndex 14)])))))
 (.branch 17
 (.branch 16
 (.leaf ([(facetIndex 15)]))
 (.leaf ([(facetIndex 16)])))
 (.branch 18
 (.leaf ([(facetIndex 17)]))
 (.branch 19
 (.leaf ([(facetIndex 18)]))
 (.leaf ([(facetIndex 19)])))))))
def groupColors1 : PackedGraphCertificate.Fields :=
  ⟨5, sparse_nat% "9ca307b9ac5a928398a418820"⟩
def grouping1 : FacetSat.Grouping data.count where
  count := 20
  members := fun g => groupMembers1.get g
  color := fun c => groupColors1.get c.val
def groupKind1 : List Nat := List.range grouping1.count

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 30), (facetIndex 35), (facetIndex 67), (facetIndex 85)]))
 (.leaf ([(facetIndex 24), (facetIndex 61), (facetIndex 62), (facetIndex 63)])))
 (.branch 3
 (.leaf ([(facetIndex 79), (facetIndex 80), (facetIndex 81)]))
 (.leaf ([(facetIndex 26), (facetIndex 65), (facetIndex 83)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 42), (facetIndex 44), (facetIndex 72), (facetIndex 90)]))
 (.leaf ([(facetIndex 71), (facetIndex 73), (facetIndex 89), (facetIndex 91)])))
 (.branch 7
 (.leaf ([(facetIndex 60), (facetIndex 64), (facetIndex 78), (facetIndex 82)]))
 (.branch 8
 (.leaf ([(facetIndex 57), (facetIndex 68), (facetIndex 70), (facetIndex 75), (facetIndex 86), (facetIndex 88)]))
 (.leaf ([(facetIndex 21), (facetIndex 39), (facetIndex 46), (facetIndex 49)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "54570700362226007054570700361116007000000080080404008000000000000301008z15;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 29), (facetIndex 66), (facetIndex 74)]))
 (.leaf ([(facetIndex 51), (facetIndex 84), (facetIndex 92)])))
 (.branch 3
 (.leaf ([(facetIndex 20), (facetIndex 58), (facetIndex 59), (facetIndex 69)]))
 (.leaf ([(facetIndex 36), (facetIndex 76), (facetIndex 77), (facetIndex 87)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 37), (facetIndex 93), (facetIndex 94)]))
 (.leaf ([(facetIndex 22), (facetIndex 23), (facetIndex 25), (facetIndex 32), (facetIndex 33), (facetIndex 38), (facetIndex 40), (facetIndex 43), (facetIndex 50), (facetIndex 52), (facetIndex 53)])))
 (.branch 7
 (.leaf ([(facetIndex 27), (facetIndex 28), (facetIndex 41), (facetIndex 45), (facetIndex 47), (facetIndex 48), (facetIndex 55), (facetIndex 56)]))
 (.leaf ([(facetIndex 31), (facetIndex 34), (facetIndex 54)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "12100060100001b000010000000486ded346c30a351631ede06c28b42000000000000000"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped1_0000 : List Nat := [0]
def grouped1_0001 : List Nat := [0, 1]
def grouped1_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped1_0003 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
def grouped1_0005 : List Nat := [1]
def grouped1_0006 : List Nat := [2]
def grouped1_0007 : List Nat := [2, 3, 4]
def grouped1_0008 : List Nat := [3]
def grouped1_0009 : List Nat := [3, 4]
def grouped1_0010 : List Nat := [4]
def grouped1_0011 : List Nat := [5]
def grouped1_0012 : List Nat := [5, 6]
def grouped1_0013 : List Nat := [5, 6, 7, 8, 9]
def grouped1_0014 : List Nat := [6]
def grouped1_0015 : List Nat := [7]
def grouped1_0016 : List Nat := [7, 8, 9]
def grouped1_0017 : List Nat := [8]
def grouped1_0018 : List Nat := [8, 9]
def grouped1_0019 : List Nat := [9]
def grouped1_0020 : List Nat := [10]
def grouped1_0021 : List Nat := [10, 11]
def grouped1_0022 : List Nat := [10, 11, 12, 13, 14]
def grouped1_0023 : List Nat := [10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
def grouped1_0024 : List Nat := [11]
def grouped1_0025 : List Nat := [12]
def grouped1_0026 : List Nat := [12, 13, 14]
def grouped1_0027 : List Nat := [13]
def grouped1_0028 : List Nat := [13, 14]
def grouped1_0029 : List Nat := [14]
def grouped1_0030 : List Nat := [15]
def grouped1_0031 : List Nat := [15, 16]
def grouped1_0032 : List Nat := [15, 16, 17, 18, 19]
def grouped1_0033 : List Nat := [16]
def grouped1_0034 : List Nat := [17]
def grouped1_0035 : List Nat := [17, 18, 19]
def grouped1_0036 : List Nat := [18]
def grouped1_0037 : List Nat := [18, 19]
def grouped1_0038 : List Nat := [19]
def grouped2_0039 : List Nat := [0]
def grouped2_0040 : List Nat := [0, 1]
def grouped2_0041 : List Nat := [0, 1, 2, 3]
def grouped2_0043 : List Nat := [1]
def grouped2_0044 : List Nat := [2]
def grouped2_0045 : List Nat := [2, 3]
def grouped2_0046 : List Nat := [3]
def grouped2_0047 : List Nat := [4]
def grouped2_0048 : List Nat := [4, 5]
def grouped2_0049 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0050 : List Nat := [5]
def grouped2_0051 : List Nat := [6]
def grouped2_0052 : List Nat := [6, 7, 8]
def grouped2_0053 : List Nat := [7]
def grouped2_0054 : List Nat := [7, 8]
def grouped2_0055 : List Nat := [8]
def grouped3_0056 : List Nat := [0]
def grouped3_0057 : List Nat := [0, 1]
def grouped3_0058 : List Nat := [0, 1, 2, 3]
def grouped3_0060 : List Nat := [1]
def grouped3_0061 : List Nat := [2]
def grouped3_0062 : List Nat := [2, 3]
def grouped3_0063 : List Nat := [3]
def grouped3_0064 : List Nat := [4]
def grouped3_0065 : List Nat := [4, 5]
def grouped3_0066 : List Nat := [4, 5, 6, 7]
def grouped3_0067 : List Nat := [5]
def grouped3_0068 : List Nat := [6]
def grouped3_0069 : List Nat := [6, 7]
def grouped3_0070 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record011 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record011_matrix_checked

def leafCount : Nat := 78
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaf0000 : List (Fin data.count) := [(facetIndex 2), (facetIndex 3), (facetIndex 8), (facetIndex 15), (facetIndex 35), (facetIndex 60), (facetIndex 62), (facetIndex 70), (facetIndex 74), (facetIndex 79), (facetIndex 83), (facetIndex 90), (facetIndex 91), (facetIndex 92)]
theorem leaf0000_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0000 = true := by
  decide +kernel
theorem leaf0000_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0000 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0000_counts_checked
def leaf0001 : List (Fin data.count) := [(facetIndex 2), (facetIndex 3), (facetIndex 6), (facetIndex 19), (facetIndex 35), (facetIndex 60), (facetIndex 62), (facetIndex 73), (facetIndex 74), (facetIndex 79), (facetIndex 83), (facetIndex 86), (facetIndex 90), (facetIndex 92)]
theorem leaf0001_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0001 = true := by
  decide +kernel
theorem leaf0001_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0001 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0001_counts_checked
def leaf0002 : List (Fin data.count) := [(facetIndex 2), (facetIndex 3), (facetIndex 9), (facetIndex 16), (facetIndex 35), (facetIndex 61), (facetIndex 68), (facetIndex 72), (facetIndex 74), (facetIndex 78), (facetIndex 80), (facetIndex 83), (facetIndex 91), (facetIndex 92)]
theorem leaf0002_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0002 = true := by
  decide +kernel
theorem leaf0002_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0002 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0002_counts_checked
def leaf0003 : List (Fin data.count) := [(facetIndex 2), (facetIndex 3), (facetIndex 5), (facetIndex 18), (facetIndex 35), (facetIndex 61), (facetIndex 72), (facetIndex 73), (facetIndex 74), (facetIndex 78), (facetIndex 80), (facetIndex 83), (facetIndex 88), (facetIndex 92)]
theorem leaf0003_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0003 = true := by
  decide +kernel
theorem leaf0003_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0003 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0003_counts_checked
def leaf0004 : List (Fin data.count) := [(facetIndex 3), (facetIndex 4), (facetIndex 9), (facetIndex 19), (facetIndex 46), (facetIndex 57), (facetIndex 62), (facetIndex 71), (facetIndex 74), (facetIndex 78), (facetIndex 81), (facetIndex 83), (facetIndex 90), (facetIndex 92)]
theorem leaf0004_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0004 = true := by
  decide +kernel
theorem leaf0004_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0004 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0004_counts_checked
def leaf0005 : List (Fin data.count) := [(facetIndex 3), (facetIndex 4), (facetIndex 8), (facetIndex 18), (facetIndex 49), (facetIndex 57), (facetIndex 62), (facetIndex 71), (facetIndex 74), (facetIndex 78), (facetIndex 81), (facetIndex 83), (facetIndex 90), (facetIndex 92)]
theorem leaf0005_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0005 = true := by
  decide +kernel
theorem leaf0005_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0005 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0005_counts_checked
def leaf0006 : List (Fin data.count) := [(facetIndex 0), (facetIndex 3), (facetIndex 4), (facetIndex 10), (facetIndex 39), (facetIndex 62), (facetIndex 64), (facetIndex 70), (facetIndex 74), (facetIndex 81), (facetIndex 83), (facetIndex 90), (facetIndex 91), (facetIndex 92)]
theorem leaf0006_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0006 = true := by
  decide +kernel
theorem leaf0006_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0006 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0006_counts_checked
def leaf0007 : List (Fin data.count) := [(facetIndex 0), (facetIndex 3), (facetIndex 4), (facetIndex 10), (facetIndex 49), (facetIndex 62), (facetIndex 64), (facetIndex 71), (facetIndex 74), (facetIndex 81), (facetIndex 83), (facetIndex 86), (facetIndex 90), (facetIndex 92)]
theorem leaf0007_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0007 = true := by
  decide +kernel
theorem leaf0007_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0007 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0007_counts_checked
def leaf0008 : List (Fin data.count) := [(facetIndex 0), (facetIndex 3), (facetIndex 4), (facetIndex 14), (facetIndex 39), (facetIndex 62), (facetIndex 64), (facetIndex 70), (facetIndex 74), (facetIndex 79), (facetIndex 83), (facetIndex 90), (facetIndex 91), (facetIndex 92)]
theorem leaf0008_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0008 = true := by
  decide +kernel
theorem leaf0008_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0008 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0008_counts_checked
def leaf0009 : List (Fin data.count) := [(facetIndex 0), (facetIndex 3), (facetIndex 4), (facetIndex 14), (facetIndex 49), (facetIndex 62), (facetIndex 64), (facetIndex 71), (facetIndex 74), (facetIndex 79), (facetIndex 83), (facetIndex 86), (facetIndex 90), (facetIndex 92)]
theorem leaf0009_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0009 = true := by
  decide +kernel
theorem leaf0009_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0009 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0009_counts_checked
def leaf0010 : List (Fin data.count) := [(facetIndex 0), (facetIndex 3), (facetIndex 7), (facetIndex 14), (facetIndex 39), (facetIndex 63), (facetIndex 64), (facetIndex 70), (facetIndex 74), (facetIndex 79), (facetIndex 83), (facetIndex 90), (facetIndex 91), (facetIndex 92)]
theorem leaf0010_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0010 = true := by
  decide +kernel
theorem leaf0010_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0010 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0010_counts_checked
def leaf0011 : List (Fin data.count) := [(facetIndex 0), (facetIndex 3), (facetIndex 7), (facetIndex 14), (facetIndex 49), (facetIndex 63), (facetIndex 64), (facetIndex 71), (facetIndex 74), (facetIndex 79), (facetIndex 83), (facetIndex 86), (facetIndex 90), (facetIndex 92)]
theorem leaf0011_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0011 = true := by
  decide +kernel
theorem leaf0011_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0011 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0011_counts_checked
def leaf0012 : List (Fin data.count) := [(facetIndex 0), (facetIndex 3), (facetIndex 5), (facetIndex 15), (facetIndex 35), (facetIndex 62), (facetIndex 64), (facetIndex 70), (facetIndex 74), (facetIndex 79), (facetIndex 83), (facetIndex 90), (facetIndex 91), (facetIndex 92)]
theorem leaf0012_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0012 = true := by
  decide +kernel
theorem leaf0012_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0012 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0012_counts_checked
def leaf0013 : List (Fin data.count) := [(facetIndex 0), (facetIndex 3), (facetIndex 9), (facetIndex 19), (facetIndex 35), (facetIndex 62), (facetIndex 64), (facetIndex 71), (facetIndex 74), (facetIndex 79), (facetIndex 83), (facetIndex 86), (facetIndex 90), (facetIndex 92)]
theorem leaf0013_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0013 = true := by
  decide +kernel
theorem leaf0013_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0013 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0013_counts_checked
def leaf0014 : List (Fin data.count) := [(facetIndex 3), (facetIndex 4), (facetIndex 5), (facetIndex 15), (facetIndex 21), (facetIndex 62), (facetIndex 64), (facetIndex 70), (facetIndex 74), (facetIndex 81), (facetIndex 83), (facetIndex 90), (facetIndex 91), (facetIndex 92)]
theorem leaf0014_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0014 = true := by
  decide +kernel
theorem leaf0014_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0014 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0014_counts_checked
def leaf0015 : List (Fin data.count) := [(facetIndex 3), (facetIndex 4), (facetIndex 9), (facetIndex 19), (facetIndex 21), (facetIndex 62), (facetIndex 64), (facetIndex 71), (facetIndex 74), (facetIndex 81), (facetIndex 83), (facetIndex 86), (facetIndex 90), (facetIndex 92)]
theorem leaf0015_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0015 = true := by
  decide +kernel
theorem leaf0015_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0015 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0015_counts_checked
def leaf0016 : List (Fin data.count) := [(facetIndex 0), (facetIndex 13), (facetIndex 14), (facetIndex 17), (facetIndex 39), (facetIndex 63), (facetIndex 65), (facetIndex 72), (facetIndex 73), (facetIndex 74), (facetIndex 79), (facetIndex 82), (facetIndex 88), (facetIndex 92)]
theorem leaf0016_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0016 = true := by
  decide +kernel
theorem leaf0016_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0016 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0016_counts_checked
def leaf0017 : List (Fin data.count) := [(facetIndex 0), (facetIndex 13), (facetIndex 14), (facetIndex 17), (facetIndex 49), (facetIndex 63), (facetIndex 65), (facetIndex 68), (facetIndex 72), (facetIndex 74), (facetIndex 79), (facetIndex 82), (facetIndex 89), (facetIndex 92)]
theorem leaf0017_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0017 = true := by
  decide +kernel
theorem leaf0017_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0017 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0017_counts_checked
def leaf0018 : List (Fin data.count) := [(facetIndex 5), (facetIndex 6), (facetIndex 8), (facetIndex 9), (facetIndex 52), (facetIndex 56), (facetIndex 57), (facetIndex 62), (facetIndex 67), (facetIndex 78), (facetIndex 81), (facetIndex 83), (facetIndex 90), (facetIndex 91)]
theorem leaf0018_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0018 = true := by
  decide +kernel
theorem leaf0018_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0018 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0018_counts_checked
def leaf0019 : List (Fin data.count) := [(facetIndex 8), (facetIndex 9), (facetIndex 18), (facetIndex 19), (facetIndex 52), (facetIndex 56), (facetIndex 57), (facetIndex 62), (facetIndex 67), (facetIndex 71), (facetIndex 78), (facetIndex 81), (facetIndex 83), (facetIndex 90)]
theorem leaf0019_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0019 = true := by
  decide +kernel
theorem leaf0019_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0019 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0019_counts_checked
def leaf0020 : List (Fin data.count) := [(facetIndex 5), (facetIndex 6), (facetIndex 18), (facetIndex 19), (facetIndex 52), (facetIndex 56), (facetIndex 57), (facetIndex 62), (facetIndex 67), (facetIndex 73), (facetIndex 78), (facetIndex 81), (facetIndex 83), (facetIndex 90)]
theorem leaf0020_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0020 = true := by
  decide +kernel
theorem leaf0020_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0020 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0020_counts_checked
def leaf0021 : List (Fin data.count) := [(facetIndex 0), (facetIndex 9), (facetIndex 10), (facetIndex 19), (facetIndex 52), (facetIndex 56), (facetIndex 62), (facetIndex 64), (facetIndex 67), (facetIndex 71), (facetIndex 81), (facetIndex 83), (facetIndex 86), (facetIndex 90)]
theorem leaf0021_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0021 = true := by
  decide +kernel
theorem leaf0021_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0021 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0021_counts_checked
def leaf0022 : List (Fin data.count) := [(facetIndex 0), (facetIndex 9), (facetIndex 14), (facetIndex 19), (facetIndex 52), (facetIndex 56), (facetIndex 62), (facetIndex 64), (facetIndex 67), (facetIndex 71), (facetIndex 79), (facetIndex 83), (facetIndex 86), (facetIndex 90)]
theorem leaf0022_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0022 = true := by
  decide +kernel
theorem leaf0022_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0022 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0022_counts_checked
def leaf0023 : List (Fin data.count) := [(facetIndex 0), (facetIndex 9), (facetIndex 17), (facetIndex 19), (facetIndex 52), (facetIndex 56), (facetIndex 63), (facetIndex 65), (facetIndex 68), (facetIndex 72), (facetIndex 79), (facetIndex 82), (facetIndex 85), (facetIndex 89)]
theorem leaf0023_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0023 = true := by
  decide +kernel
theorem leaf0023_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0023 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0023_counts_checked
def leaf0024 : List (Fin data.count) := [(facetIndex 0), (facetIndex 2), (facetIndex 6), (facetIndex 9), (facetIndex 52), (facetIndex 56), (facetIndex 62), (facetIndex 67), (facetIndex 68), (facetIndex 78), (facetIndex 81), (facetIndex 83), (facetIndex 90), (facetIndex 91)]
theorem leaf0024_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0024 = true := by
  decide +kernel
theorem leaf0024_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0024 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0024_counts_checked
def leaf0025 : List (Fin data.count) := [(facetIndex 0), (facetIndex 9), (facetIndex 12), (facetIndex 16), (facetIndex 52), (facetIndex 56), (facetIndex 63), (facetIndex 65), (facetIndex 68), (facetIndex 72), (facetIndex 78), (facetIndex 80), (facetIndex 85), (facetIndex 91)]
theorem leaf0025_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0025 = true := by
  decide +kernel
theorem leaf0025_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0025 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0025_counts_checked
def leaf0026 : List (Fin data.count) := [(facetIndex 2), (facetIndex 6), (facetIndex 7), (facetIndex 9), (facetIndex 52), (facetIndex 56), (facetIndex 61), (facetIndex 67), (facetIndex 68), (facetIndex 78), (facetIndex 81), (facetIndex 83), (facetIndex 90), (facetIndex 91)]
theorem leaf0026_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0026 = true := by
  decide +kernel
theorem leaf0026_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0026 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0026_counts_checked
def leaf0027 : List (Fin data.count) := [(facetIndex 2), (facetIndex 9), (facetIndex 16), (facetIndex 17), (facetIndex 52), (facetIndex 56), (facetIndex 61), (facetIndex 67), (facetIndex 68), (facetIndex 72), (facetIndex 78), (facetIndex 81), (facetIndex 83), (facetIndex 91)]
theorem leaf0027_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0027 = true := by
  decide +kernel
theorem leaf0027_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0027 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0027_counts_checked
def leaf0028 : List (Fin data.count) := [(facetIndex 2), (facetIndex 9), (facetIndex 14), (facetIndex 16), (facetIndex 52), (facetIndex 56), (facetIndex 61), (facetIndex 67), (facetIndex 68), (facetIndex 72), (facetIndex 78), (facetIndex 80), (facetIndex 83), (facetIndex 91)]
theorem leaf0028_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0028 = true := by
  decide +kernel
theorem leaf0028_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0028 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0028_counts_checked
def leaf0029 : List (Fin data.count) := [(facetIndex 2), (facetIndex 6), (facetIndex 14), (facetIndex 19), (facetIndex 52), (facetIndex 56), (facetIndex 60), (facetIndex 62), (facetIndex 67), (facetIndex 73), (facetIndex 79), (facetIndex 83), (facetIndex 86), (facetIndex 90)]
theorem leaf0029_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0029 = true := by
  decide +kernel
theorem leaf0029_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0029 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0029_counts_checked
def leaf0030 : List (Fin data.count) := [(facetIndex 0), (facetIndex 2), (facetIndex 5), (facetIndex 8), (facetIndex 52), (facetIndex 56), (facetIndex 62), (facetIndex 67), (facetIndex 70), (facetIndex 78), (facetIndex 81), (facetIndex 83), (facetIndex 90), (facetIndex 91)]
theorem leaf0030_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0030 = true := by
  decide +kernel
theorem leaf0030_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0030 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0030_counts_checked
def leaf0031 : List (Fin data.count) := [(facetIndex 0), (facetIndex 5), (facetIndex 10), (facetIndex 15), (facetIndex 52), (facetIndex 56), (facetIndex 62), (facetIndex 64), (facetIndex 67), (facetIndex 70), (facetIndex 81), (facetIndex 83), (facetIndex 90), (facetIndex 91)]
theorem leaf0031_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0031 = true := by
  decide +kernel
theorem leaf0031_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0031 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0031_counts_checked
def leaf0032 : List (Fin data.count) := [(facetIndex 0), (facetIndex 5), (facetIndex 14), (facetIndex 15), (facetIndex 52), (facetIndex 56), (facetIndex 62), (facetIndex 64), (facetIndex 67), (facetIndex 70), (facetIndex 79), (facetIndex 83), (facetIndex 90), (facetIndex 91)]
theorem leaf0032_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0032 = true := by
  decide +kernel
theorem leaf0032_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0032 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0032_counts_checked
def leaf0033 : List (Fin data.count) := [(facetIndex 0), (facetIndex 5), (facetIndex 15), (facetIndex 17), (facetIndex 52), (facetIndex 56), (facetIndex 63), (facetIndex 65), (facetIndex 72), (facetIndex 73), (facetIndex 79), (facetIndex 82), (facetIndex 85), (facetIndex 88)]
theorem leaf0033_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0033 = true := by
  decide +kernel
theorem leaf0033_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0033 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0033_counts_checked
def leaf0034 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 7), (facetIndex 8), (facetIndex 52), (facetIndex 56), (facetIndex 61), (facetIndex 67), (facetIndex 70), (facetIndex 78), (facetIndex 81), (facetIndex 83), (facetIndex 90), (facetIndex 91)]
theorem leaf0034_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0034 = true := by
  decide +kernel
theorem leaf0034_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0034 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0034_counts_checked
def leaf0035 : List (Fin data.count) := [(facetIndex 0), (facetIndex 5), (facetIndex 12), (facetIndex 18), (facetIndex 52), (facetIndex 56), (facetIndex 63), (facetIndex 65), (facetIndex 72), (facetIndex 73), (facetIndex 78), (facetIndex 80), (facetIndex 85), (facetIndex 88)]
theorem leaf0035_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0035 = true := by
  decide +kernel
theorem leaf0035_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0035 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0035_counts_checked
def leaf0036 : List (Fin data.count) := [(facetIndex 2), (facetIndex 8), (facetIndex 14), (facetIndex 15), (facetIndex 52), (facetIndex 56), (facetIndex 60), (facetIndex 62), (facetIndex 67), (facetIndex 70), (facetIndex 79), (facetIndex 83), (facetIndex 90), (facetIndex 91)]
theorem leaf0036_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0036 = true := by
  decide +kernel
theorem leaf0036_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0036 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0036_counts_checked
def leaf0037 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 17), (facetIndex 18), (facetIndex 52), (facetIndex 56), (facetIndex 61), (facetIndex 67), (facetIndex 72), (facetIndex 73), (facetIndex 78), (facetIndex 81), (facetIndex 83), (facetIndex 88)]
theorem leaf0037_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0037 = true := by
  decide +kernel
theorem leaf0037_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0037 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0037_counts_checked
def leaf0038 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 14), (facetIndex 18), (facetIndex 52), (facetIndex 56), (facetIndex 61), (facetIndex 67), (facetIndex 72), (facetIndex 73), (facetIndex 78), (facetIndex 80), (facetIndex 83), (facetIndex 88)]
theorem leaf0038_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0038 = true := by
  decide +kernel
theorem leaf0038_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0038 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0038_counts_checked
def leaf0039 : List (Fin data.count) := [(facetIndex 5), (facetIndex 12), (facetIndex 13), (facetIndex 18), (facetIndex 35), (facetIndex 61), (facetIndex 65), (facetIndex 72), (facetIndex 73), (facetIndex 74), (facetIndex 78), (facetIndex 80), (facetIndex 88), (facetIndex 92)]
theorem leaf0039_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0039 = true := by
  decide +kernel
theorem leaf0039_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0039 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0039_counts_checked
def leaf0040 : List (Fin data.count) := [(facetIndex 9), (facetIndex 12), (facetIndex 13), (facetIndex 16), (facetIndex 35), (facetIndex 61), (facetIndex 65), (facetIndex 68), (facetIndex 72), (facetIndex 74), (facetIndex 78), (facetIndex 80), (facetIndex 91), (facetIndex 92)]
theorem leaf0040_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0040 = true := by
  decide +kernel
theorem leaf0040_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0040 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0040_counts_checked
def leaf0041 : List (Fin data.count) := [(facetIndex 6), (facetIndex 12), (facetIndex 13), (facetIndex 19), (facetIndex 35), (facetIndex 60), (facetIndex 62), (facetIndex 65), (facetIndex 73), (facetIndex 74), (facetIndex 79), (facetIndex 86), (facetIndex 90), (facetIndex 92)]
theorem leaf0041_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0041 = true := by
  decide +kernel
theorem leaf0041_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0041 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0041_counts_checked
def leaf0042 : List (Fin data.count) := [(facetIndex 8), (facetIndex 12), (facetIndex 13), (facetIndex 15), (facetIndex 35), (facetIndex 60), (facetIndex 62), (facetIndex 65), (facetIndex 70), (facetIndex 74), (facetIndex 79), (facetIndex 90), (facetIndex 91), (facetIndex 92)]
theorem leaf0042_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0042 = true := by
  decide +kernel
theorem leaf0042_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0042 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0042_counts_checked
def leaf0043 : List (Fin data.count) := [(facetIndex 9), (facetIndex 13), (facetIndex 14), (facetIndex 19), (facetIndex 46), (facetIndex 60), (facetIndex 63), (facetIndex 65), (facetIndex 72), (facetIndex 74), (facetIndex 75), (facetIndex 80), (facetIndex 89), (facetIndex 92)]
theorem leaf0043_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0043 = true := by
  decide +kernel
theorem leaf0043_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0043 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0043_counts_checked
def leaf0044 : List (Fin data.count) := [(facetIndex 8), (facetIndex 13), (facetIndex 14), (facetIndex 18), (facetIndex 49), (facetIndex 60), (facetIndex 63), (facetIndex 65), (facetIndex 72), (facetIndex 74), (facetIndex 75), (facetIndex 80), (facetIndex 89), (facetIndex 92)]
theorem leaf0044_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0044 = true := by
  decide +kernel
theorem leaf0044_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0044 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0044_counts_checked
def leaf0045 : List (Fin data.count) := [(facetIndex 0), (facetIndex 10), (facetIndex 13), (facetIndex 14), (facetIndex 39), (facetIndex 63), (facetIndex 65), (facetIndex 72), (facetIndex 73), (facetIndex 74), (facetIndex 80), (facetIndex 82), (facetIndex 88), (facetIndex 92)]
theorem leaf0045_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0045 = true := by
  decide +kernel
theorem leaf0045_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0045 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0045_counts_checked
def leaf0046 : List (Fin data.count) := [(facetIndex 0), (facetIndex 10), (facetIndex 13), (facetIndex 14), (facetIndex 49), (facetIndex 63), (facetIndex 65), (facetIndex 68), (facetIndex 72), (facetIndex 74), (facetIndex 80), (facetIndex 82), (facetIndex 89), (facetIndex 92)]
theorem leaf0046_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0046 = true := by
  decide +kernel
theorem leaf0046_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0046 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0046_counts_checked
def leaf0047 : List (Fin data.count) := [(facetIndex 4), (facetIndex 10), (facetIndex 13), (facetIndex 14), (facetIndex 39), (facetIndex 61), (facetIndex 65), (facetIndex 72), (facetIndex 73), (facetIndex 74), (facetIndex 80), (facetIndex 82), (facetIndex 88), (facetIndex 92)]
theorem leaf0047_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0047 = true := by
  decide +kernel
theorem leaf0047_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0047 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0047_counts_checked
def leaf0048 : List (Fin data.count) := [(facetIndex 4), (facetIndex 10), (facetIndex 13), (facetIndex 14), (facetIndex 49), (facetIndex 61), (facetIndex 65), (facetIndex 68), (facetIndex 72), (facetIndex 74), (facetIndex 80), (facetIndex 82), (facetIndex 89), (facetIndex 92)]
theorem leaf0048_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0048 = true := by
  decide +kernel
theorem leaf0048_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0048 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0048_counts_checked
def leaf0049 : List (Fin data.count) := [(facetIndex 4), (facetIndex 10), (facetIndex 13), (facetIndex 17), (facetIndex 39), (facetIndex 61), (facetIndex 65), (facetIndex 72), (facetIndex 73), (facetIndex 74), (facetIndex 81), (facetIndex 82), (facetIndex 88), (facetIndex 92)]
theorem leaf0049_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0049 = true := by
  decide +kernel
theorem leaf0049_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0049 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0049_counts_checked
def leaf0050 : List (Fin data.count) := [(facetIndex 4), (facetIndex 10), (facetIndex 13), (facetIndex 17), (facetIndex 49), (facetIndex 61), (facetIndex 65), (facetIndex 68), (facetIndex 72), (facetIndex 74), (facetIndex 81), (facetIndex 82), (facetIndex 89), (facetIndex 92)]
theorem leaf0050_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0050 = true := by
  decide +kernel
theorem leaf0050_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0050 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0050_counts_checked
def leaf0051 : List (Fin data.count) := [(facetIndex 5), (facetIndex 10), (facetIndex 13), (facetIndex 15), (facetIndex 35), (facetIndex 61), (facetIndex 65), (facetIndex 72), (facetIndex 73), (facetIndex 74), (facetIndex 80), (facetIndex 82), (facetIndex 88), (facetIndex 92)]
theorem leaf0051_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0051 = true := by
  decide +kernel
theorem leaf0051_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0051 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0051_counts_checked
def leaf0052 : List (Fin data.count) := [(facetIndex 9), (facetIndex 10), (facetIndex 13), (facetIndex 19), (facetIndex 35), (facetIndex 61), (facetIndex 65), (facetIndex 68), (facetIndex 72), (facetIndex 74), (facetIndex 80), (facetIndex 82), (facetIndex 89), (facetIndex 92)]
theorem leaf0052_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0052 = true := by
  decide +kernel
theorem leaf0052_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0052 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0052_counts_checked
def leaf0053 : List (Fin data.count) := [(facetIndex 5), (facetIndex 13), (facetIndex 14), (facetIndex 15), (facetIndex 21), (facetIndex 63), (facetIndex 65), (facetIndex 72), (facetIndex 73), (facetIndex 74), (facetIndex 80), (facetIndex 82), (facetIndex 88), (facetIndex 92)]
theorem leaf0053_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0053 = true := by
  decide +kernel
theorem leaf0053_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0053 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0053_counts_checked
def leaf0054 : List (Fin data.count) := [(facetIndex 9), (facetIndex 13), (facetIndex 14), (facetIndex 19), (facetIndex 21), (facetIndex 63), (facetIndex 65), (facetIndex 68), (facetIndex 72), (facetIndex 74), (facetIndex 80), (facetIndex 82), (facetIndex 89), (facetIndex 92)]
theorem leaf0054_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0054 = true := by
  decide +kernel
theorem leaf0054_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0054 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0054_counts_checked
def leaf0055 : List (Fin data.count) := [(facetIndex 3), (facetIndex 4), (facetIndex 7), (facetIndex 10), (facetIndex 39), (facetIndex 61), (facetIndex 64), (facetIndex 70), (facetIndex 74), (facetIndex 81), (facetIndex 83), (facetIndex 90), (facetIndex 91), (facetIndex 92)]
theorem leaf0055_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0055 = true := by
  decide +kernel
theorem leaf0055_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0055 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0055_counts_checked
def leaf0056 : List (Fin data.count) := [(facetIndex 3), (facetIndex 4), (facetIndex 7), (facetIndex 10), (facetIndex 49), (facetIndex 61), (facetIndex 64), (facetIndex 71), (facetIndex 74), (facetIndex 81), (facetIndex 83), (facetIndex 86), (facetIndex 90), (facetIndex 92)]
theorem leaf0056_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0056 = true := by
  decide +kernel
theorem leaf0056_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0056 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0056_counts_checked
def leaf0057 : List (Fin data.count) := [(facetIndex 15), (facetIndex 16), (facetIndex 18), (facetIndex 19), (facetIndex 52), (facetIndex 56), (facetIndex 60), (facetIndex 63), (facetIndex 65), (facetIndex 72), (facetIndex 73), (facetIndex 75), (facetIndex 80), (facetIndex 85)]
theorem leaf0057_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0057 = true := by
  decide +kernel
theorem leaf0057_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0057 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0057_counts_checked
def leaf0058 : List (Fin data.count) := [(facetIndex 8), (facetIndex 9), (facetIndex 18), (facetIndex 19), (facetIndex 52), (facetIndex 56), (facetIndex 60), (facetIndex 63), (facetIndex 65), (facetIndex 72), (facetIndex 75), (facetIndex 80), (facetIndex 85), (facetIndex 89)]
theorem leaf0058_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0058 = true := by
  decide +kernel
theorem leaf0058_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0058 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0058_counts_checked
def leaf0059 : List (Fin data.count) := [(facetIndex 8), (facetIndex 9), (facetIndex 15), (facetIndex 16), (facetIndex 52), (facetIndex 56), (facetIndex 60), (facetIndex 63), (facetIndex 65), (facetIndex 72), (facetIndex 75), (facetIndex 80), (facetIndex 85), (facetIndex 91)]
theorem leaf0059_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0059 = true := by
  decide +kernel
theorem leaf0059_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0059 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0059_counts_checked
def leaf0060 : List (Fin data.count) := [(facetIndex 0), (facetIndex 9), (facetIndex 10), (facetIndex 19), (facetIndex 52), (facetIndex 56), (facetIndex 63), (facetIndex 65), (facetIndex 68), (facetIndex 72), (facetIndex 80), (facetIndex 82), (facetIndex 85), (facetIndex 89)]
theorem leaf0060_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0060 = true := by
  decide +kernel
theorem leaf0060_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0060 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0060_counts_checked
def leaf0061 : List (Fin data.count) := [(facetIndex 4), (facetIndex 9), (facetIndex 10), (facetIndex 19), (facetIndex 52), (facetIndex 56), (facetIndex 61), (facetIndex 65), (facetIndex 68), (facetIndex 72), (facetIndex 80), (facetIndex 82), (facetIndex 85), (facetIndex 89)]
theorem leaf0061_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0061 = true := by
  decide +kernel
theorem leaf0061_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0061 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0061_counts_checked
def leaf0062 : List (Fin data.count) := [(facetIndex 7), (facetIndex 9), (facetIndex 10), (facetIndex 19), (facetIndex 52), (facetIndex 56), (facetIndex 61), (facetIndex 64), (facetIndex 67), (facetIndex 71), (facetIndex 81), (facetIndex 83), (facetIndex 86), (facetIndex 90)]
theorem leaf0062_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0062 = true := by
  decide +kernel
theorem leaf0062_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0062 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0062_counts_checked
def leaf0063 : List (Fin data.count) := [(facetIndex 10), (facetIndex 12), (facetIndex 16), (facetIndex 19), (facetIndex 52), (facetIndex 56), (facetIndex 60), (facetIndex 63), (facetIndex 65), (facetIndex 72), (facetIndex 73), (facetIndex 80), (facetIndex 85), (facetIndex 86)]
theorem leaf0063_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0063 = true := by
  decide +kernel
theorem leaf0063_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0063 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0063_counts_checked
def leaf0064 : List (Fin data.count) := [(facetIndex 2), (facetIndex 6), (facetIndex 10), (facetIndex 19), (facetIndex 52), (facetIndex 56), (facetIndex 60), (facetIndex 62), (facetIndex 67), (facetIndex 73), (facetIndex 81), (facetIndex 83), (facetIndex 86), (facetIndex 90)]
theorem leaf0064_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0064 = true := by
  decide +kernel
theorem leaf0064_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0064 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0064_counts_checked
def leaf0065 : List (Fin data.count) := [(facetIndex 12), (facetIndex 16), (facetIndex 17), (facetIndex 19), (facetIndex 52), (facetIndex 56), (facetIndex 60), (facetIndex 63), (facetIndex 65), (facetIndex 72), (facetIndex 73), (facetIndex 79), (facetIndex 85), (facetIndex 86)]
theorem leaf0065_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0065 = true := by
  decide +kernel
theorem leaf0065_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0065 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0065_counts_checked
def leaf0066 : List (Fin data.count) := [(facetIndex 6), (facetIndex 7), (facetIndex 12), (facetIndex 19), (facetIndex 52), (facetIndex 56), (facetIndex 60), (facetIndex 63), (facetIndex 65), (facetIndex 73), (facetIndex 79), (facetIndex 85), (facetIndex 86), (facetIndex 90)]
theorem leaf0066_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0066 = true := by
  decide +kernel
theorem leaf0066_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0066 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0066_counts_checked
def leaf0067 : List (Fin data.count) := [(facetIndex 4), (facetIndex 6), (facetIndex 12), (facetIndex 19), (facetIndex 52), (facetIndex 56), (facetIndex 60), (facetIndex 62), (facetIndex 65), (facetIndex 73), (facetIndex 79), (facetIndex 85), (facetIndex 86), (facetIndex 90)]
theorem leaf0067_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0067 = true := by
  decide +kernel
theorem leaf0067_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0067 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0067_counts_checked
def leaf0068 : List (Fin data.count) := [(facetIndex 4), (facetIndex 9), (facetIndex 12), (facetIndex 16), (facetIndex 52), (facetIndex 56), (facetIndex 61), (facetIndex 65), (facetIndex 68), (facetIndex 72), (facetIndex 78), (facetIndex 80), (facetIndex 85), (facetIndex 91)]
theorem leaf0068_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0068 = true := by
  decide +kernel
theorem leaf0068_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0068 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0068_counts_checked
def leaf0069 : List (Fin data.count) := [(facetIndex 10), (facetIndex 12), (facetIndex 15), (facetIndex 18), (facetIndex 52), (facetIndex 56), (facetIndex 60), (facetIndex 63), (facetIndex 65), (facetIndex 72), (facetIndex 73), (facetIndex 80), (facetIndex 85), (facetIndex 88)]
theorem leaf0069_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0069 = true := by
  decide +kernel
theorem leaf0069_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0069 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0069_counts_checked
def leaf0070 : List (Fin data.count) := [(facetIndex 0), (facetIndex 5), (facetIndex 10), (facetIndex 15), (facetIndex 52), (facetIndex 56), (facetIndex 63), (facetIndex 65), (facetIndex 72), (facetIndex 73), (facetIndex 80), (facetIndex 82), (facetIndex 85), (facetIndex 88)]
theorem leaf0070_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0070 = true := by
  decide +kernel
theorem leaf0070_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0070 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0070_counts_checked
def leaf0071 : List (Fin data.count) := [(facetIndex 4), (facetIndex 5), (facetIndex 10), (facetIndex 15), (facetIndex 52), (facetIndex 56), (facetIndex 61), (facetIndex 65), (facetIndex 72), (facetIndex 73), (facetIndex 80), (facetIndex 82), (facetIndex 85), (facetIndex 88)]
theorem leaf0071_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0071 = true := by
  decide +kernel
theorem leaf0071_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0071 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0071_counts_checked
def leaf0072 : List (Fin data.count) := [(facetIndex 5), (facetIndex 7), (facetIndex 10), (facetIndex 15), (facetIndex 52), (facetIndex 56), (facetIndex 61), (facetIndex 64), (facetIndex 67), (facetIndex 70), (facetIndex 81), (facetIndex 83), (facetIndex 90), (facetIndex 91)]
theorem leaf0072_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0072 = true := by
  decide +kernel
theorem leaf0072_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0072 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0072_counts_checked
def leaf0073 : List (Fin data.count) := [(facetIndex 12), (facetIndex 15), (facetIndex 17), (facetIndex 18), (facetIndex 52), (facetIndex 56), (facetIndex 60), (facetIndex 63), (facetIndex 65), (facetIndex 72), (facetIndex 73), (facetIndex 79), (facetIndex 85), (facetIndex 88)]
theorem leaf0073_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0073 = true := by
  decide +kernel
theorem leaf0073_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0073 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0073_counts_checked
def leaf0074 : List (Fin data.count) := [(facetIndex 2), (facetIndex 8), (facetIndex 10), (facetIndex 15), (facetIndex 52), (facetIndex 56), (facetIndex 60), (facetIndex 62), (facetIndex 67), (facetIndex 70), (facetIndex 81), (facetIndex 83), (facetIndex 90), (facetIndex 91)]
theorem leaf0074_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0074 = true := by
  decide +kernel
theorem leaf0074_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0074 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0074_counts_checked
def leaf0075 : List (Fin data.count) := [(facetIndex 4), (facetIndex 5), (facetIndex 12), (facetIndex 18), (facetIndex 52), (facetIndex 56), (facetIndex 61), (facetIndex 65), (facetIndex 72), (facetIndex 73), (facetIndex 78), (facetIndex 80), (facetIndex 85), (facetIndex 88)]
theorem leaf0075_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0075 = true := by
  decide +kernel
theorem leaf0075_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0075 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0075_counts_checked
def leaf0076 : List (Fin data.count) := [(facetIndex 7), (facetIndex 8), (facetIndex 12), (facetIndex 15), (facetIndex 52), (facetIndex 56), (facetIndex 60), (facetIndex 63), (facetIndex 65), (facetIndex 70), (facetIndex 79), (facetIndex 85), (facetIndex 90), (facetIndex 91)]
theorem leaf0076_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0076 = true := by
  decide +kernel
theorem leaf0076_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0076 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0076_counts_checked
def leaf0077 : List (Fin data.count) := [(facetIndex 4), (facetIndex 8), (facetIndex 12), (facetIndex 15), (facetIndex 52), (facetIndex 56), (facetIndex 60), (facetIndex 62), (facetIndex 65), (facetIndex 70), (facetIndex 79), (facetIndex 85), (facetIndex 90), (facetIndex 91)]
theorem leaf0077_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0077 = true := by
  decide +kernel
theorem leaf0077_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0077 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0077_counts_checked
def leavesTable : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 39
 (.branch 19
 (.branch 9
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
 (.branch 8
 (.leaf (leaf0007))
 (.leaf (leaf0008))))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf (leaf0009))
 (.leaf (leaf0010)))
 (.branch 12
 (.leaf (leaf0011))
 (.branch 13
 (.leaf (leaf0012))
 (.leaf (leaf0013)))))
 (.branch 16
 (.branch 15
 (.leaf (leaf0014))
 (.leaf (leaf0015)))
 (.branch 17
 (.leaf (leaf0016))
 (.branch 18
 (.leaf (leaf0017))
 (.leaf (leaf0018)))))))
 (.branch 29
 (.branch 24
 (.branch 21
 (.branch 20
 (.leaf (leaf0019))
 (.leaf (leaf0020)))
 (.branch 22
 (.leaf (leaf0021))
 (.branch 23
 (.leaf (leaf0022))
 (.leaf (leaf0023)))))
 (.branch 26
 (.branch 25
 (.leaf (leaf0024))
 (.leaf (leaf0025)))
 (.branch 27
 (.leaf (leaf0026))
 (.branch 28
 (.leaf (leaf0027))
 (.leaf (leaf0028))))))
 (.branch 34
 (.branch 31
 (.branch 30
 (.leaf (leaf0029))
 (.leaf (leaf0030)))
 (.branch 32
 (.leaf (leaf0031))
 (.branch 33
 (.leaf (leaf0032))
 (.leaf (leaf0033)))))
 (.branch 36
 (.branch 35
 (.leaf (leaf0034))
 (.leaf (leaf0035)))
 (.branch 37
 (.leaf (leaf0036))
 (.branch 38
 (.leaf (leaf0037))
 (.leaf (leaf0038))))))))
 (.branch 58
 (.branch 48
 (.branch 43
 (.branch 41
 (.branch 40
 (.leaf (leaf0039))
 (.leaf (leaf0040)))
 (.branch 42
 (.leaf (leaf0041))
 (.leaf (leaf0042))))
 (.branch 45
 (.branch 44
 (.leaf (leaf0043))
 (.leaf (leaf0044)))
 (.branch 46
 (.leaf (leaf0045))
 (.branch 47
 (.leaf (leaf0046))
 (.leaf (leaf0047))))))
 (.branch 53
 (.branch 50
 (.branch 49
 (.leaf (leaf0048))
 (.leaf (leaf0049)))
 (.branch 51
 (.leaf (leaf0050))
 (.branch 52
 (.leaf (leaf0051))
 (.leaf (leaf0052)))))
 (.branch 55
 (.branch 54
 (.leaf (leaf0053))
 (.leaf (leaf0054)))
 (.branch 56
 (.leaf (leaf0055))
 (.branch 57
 (.leaf (leaf0056))
 (.leaf (leaf0057)))))))
 (.branch 68
 (.branch 63
 (.branch 60
 (.branch 59
 (.leaf (leaf0058))
 (.leaf (leaf0059)))
 (.branch 61
 (.leaf (leaf0060))
 (.branch 62
 (.leaf (leaf0061))
 (.leaf (leaf0062)))))
 (.branch 65
 (.branch 64
 (.leaf (leaf0063))
 (.leaf (leaf0064)))
 (.branch 66
 (.leaf (leaf0065))
 (.branch 67
 (.leaf (leaf0066))
 (.leaf (leaf0067))))))
 (.branch 73
 (.branch 70
 (.branch 69
 (.leaf (leaf0068))
 (.leaf (leaf0069)))
 (.branch 71
 (.leaf (leaf0070))
 (.branch 72
 (.leaf (leaf0071))
 (.leaf (leaf0072)))))
 (.branch 75
 (.branch 74
 (.leaf (leaf0073))
 (.leaf (leaf0074)))
 (.branch 76
 (.leaf (leaf0075))
 (.branch 77
 (.leaf (leaf0076))
 (.leaf (leaf0077)))))))))
def leaves (j : Fin leafCount) : List (Fin data.count) := leavesTable.get j.val

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00022.record011" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"group\",\"kind\":1,\"index\":0},{\"tag\":\"group\",\"kind\":1,\"index\":1},{\"tag\":\"group\",\"kind\":1,\"index\":2},{\"tag\":\"group\",\"kind\":1,\"index\":4},{\"tag\":\"group\",\"kind\":1,\"index\":5},{\"tag\":\"group\",\"kind\":1,\"index\":6},{\"tag\":\"group\",\"kind\":1,\"index\":7},{\"tag\":\"group\",\"kind\":1,\"index\":8},{\"tag\":\"group\",\"kind\":1,\"index\":9},{\"tag\":\"group\",\"kind\":1,\"index\":10},{\"tag\":\"group\",\"kind\":1,\"index\":11},{\"tag\":\"group\",\"kind\":1,\"index\":12},{\"tag\":\"group\",\"kind\":1,\"index\":13},{\"tag\":\"group\",\"kind\":1,\"index\":14},{\"tag\":\"group\",\"kind\":1,\"index\":15},{\"tag\":\"group\",\"kind\":1,\"index\":16},{\"tag\":\"group\",\"kind\":1,\"index\":17},{\"tag\":\"group\",\"kind\":1,\"index\":18},{\"tag\":\"group\",\"kind\":1,\"index\":19},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0009\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0007\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0002\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0012\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0018\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0018\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0016\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0016\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0013\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0013\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0013\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0021\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0028\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0028\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0026\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0026\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0026\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0022\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0022\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0022\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0031\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0037\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0037\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0035\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0035\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0032\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0032\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":4,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":5,\"list_name\":\"groupKind1\"},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0040\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0040\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0045\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0041\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0041\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0048\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0054\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0054\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0052\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0052\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0049\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0049\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0057\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0057\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0062\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0058\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0058\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0065\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0069\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0066\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00022.record011" 186

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00022.record011" "{\"ridges\":[[0,44],[3,517],[3,529],[4,769],[5,73],[5,104],[6,73],[6,137],[6,193],[8,81],[8,97],[9,81],[9,193],[12,38],[12,50],[13,22],[13,518],[13,530],[14,518],[14,770],[15,42],[17,266],[19,82],[21,41],[21,42],[22,14],[23,14],[23,138],[25,14],[25,523],[30,530],[31,37],[31,71],[32,291],[33,547],[34,135],[35,261],[35,262],[35,517],[35,518],[35,769],[35,770],[36,50],[39,41],[39,42],[41,41],[43,323],[44,137],[44,265],[44,386],[45,523],[46,82],[48,547],[49,81],[49,82],[49,145],[50,579],[52,145],[52,146],[52,643],[53,275],[53,770],[55,323],[56,386],[56,643],[56,769],[57,41],[57,49],[60,37],[60,44],[60,73],[60,97],[60,104],[61,37],[61,41],[61,44],[61,261],[61,265],[61,268],[62,13],[62,137],[62,261],[63,13],[63,265],[63,769],[63,772],[64,37],[64,81],[64,97],[65,37],[65,52],[65,529],[65,532],[66,404],[67,21],[67,529],[67,532],[67,769],[67,772],[68,49],[68,73],[68,81],[70,81],[70,137],[70,200],[71,41],[71,137],[71,193],[72,73],[72,193],[72,200],[72,392],[73,112],[73,193],[74,385],[77,156],[78,38],[78,44],[78,98],[78,104],[79,38],[79,42],[79,44],[79,262],[79,266],[80,14],[80,262],[80,268],[80,392],[81,14],[81,266],[81,770],[81,772],[82,38],[82,98],[83,38],[83,50],[83,530],[83,532],[84,404],[85,22],[85,530],[85,770],[86,42],[86,50],[86,74],[86,82],[88,74],[89,42],[89,194],[90,74],[90,194],[90,200],[90,392],[91,50],[91,98],[91,112],[91,194],[91,208],[92,386],[92,912],[93,92],[94,184]],\"owners\":[[62,13,[0,20,21,22,25,57,58,60],[1,23,24,59,63]],[63,13,[0,20,21,22,23,57,58,59,60],[1,24,25,62]],[60,37,[2,26,32,33,65],[0,21,31,61,64]],[61,37,[2,26,31,33,64,65],[0,21,32,60]],[64,37,[0,21,32,33,61],[2,26,31,60,65]],[65,37,[0,21,31,32,60,61],[2,26,33,64]],[21,41,[5,68,69,71],[0,36,39,40,41,57,61]],[39,41,[0,57,61,69],[5,21,36,40,41,68,71]],[41,41,[0,5,57,68,69,71],[21,36,39,40,61]],[57,41,[5,39,40,41,71],[0,21,36,61,68,69]],[61,41,[5,36,39,40,68,69,71],[0,21,41,57]],[71,41,[0,21,36,41,57,61],[5,39,40,68,69]],[0,44,[10,75,78,79,93],[57,60,61]],[60,44,[10,75,79],[0,57,61,78,93]],[61,44,[10,75,78,93],[0,57,60,79]],[78,44,[0,57,61],[10,60,75,79,93]],[79,44,[0,57,60,93],[10,61,75,78]],[35,261,[1,61,62,66],[4,24,29,32,34,67]],[61,261,[4,29,34,35,66,67],[1,24,32,62]],[62,261,[4,29,32,35,67],[1,24,34,61,66]],[44,265,[1,61,63],[7,24,41,43,45,72]],[61,265,[7,43,44,45,72],[1,24,41,63]],[63,265,[7,41,43,44,72],[1,24,45,61]],[61,268,[11,80,81],[1,62,63,79]],[80,268,[1,61,63],[11,62,79,81]],[67,21,[2,20,26,27,28,57,58,59,64],[3,29,30,66]],[57,49,[8,46,47,48,73],[2,26,36,65,68,69]],[68,49,[2,26,47,48,65],[8,36,46,57,69,73]],[65,52,[12,75,82,93],[2,57,64,83]],[3,517,[4,25,33,35,63],[30,65]],[35,517,[3,65],[4,25,30,33,63]],[3,529,[48,50,52,53,74],[30,65,67]],[65,529,[50,52,53,74],[3,30,48,67]],[67,529,[48,50,52],[3,30,53,65,74]],[65,532,[13,85],[3,67,83]],[67,532,[13,83],[3,65,85]],[83,532,[3,67],[13,65,85]],[4,769,[45,53,56,74],[35,63,67]],[35,769,[74],[4,45,53,56,63,67]],[56,769,[4,63,67],[35,45,53,74]],[63,769,[53,56,74],[4,35,45,67]],[67,769,[45,56],[4,35,53,63,74]],[63,772,[14,85],[4,67,81]],[67,772,[14,81],[4,63,85]],[81,772,[4,67],[14,63,85]],[5,73,[6,22,37,42,43,58,70,72],[39,60,68]],[6,73,[5,22,37,39,43,58,60,68],[42,70,72]],[60,73,[6,37,42,43,70,72],[5,22,39,58,68]],[68,73,[6,22,42,43,72],[5,37,39,58,60,70]],[72,73,[5,22,37,39,58,60,68],[6,42,43,70]],[8,97,[5,31,39,54,60,71],[46,64,73]],[60,97,[8,46,54,73],[5,31,39,64,71]],[64,97,[5,39,54,71],[8,31,46,60,73]],[5,104,[15,78,86,89,93,94],[60,68,71]],[60,104,[15,86,89,94],[5,68,71,78,93]],[78,104,[5,68,71,94],[15,60,86,89,93]],[6,137,[7,23,38,40,44,59,62,69],[42,70,71]],[44,137,[6,59,69,70,71],[7,23,38,40,42,62]],[62,137,[6,38,40,42,69,70,71],[7,23,44,59]],[70,137,[7,23,40,44,62],[6,38,42,59,69,71]],[71,137,[7,23,38,44,59,62],[6,40,42,69,70]],[6,193,[9,49,54,55,73],[42,71,72]],[9,193,[6,42,54,55,71,72],[49,73]],[71,193,[9,49,55],[6,42,54,72,73]],[72,193,[9,49,54,73],[6,42,55,71]],[73,193,[6,42,55,72],[9,49,54,71]],[70,200,[16,89,90],[6,71,72,88,94]],[72,200,[16,88,89,94],[6,70,71,90]],[90,200,[6,70,71,94],[16,72,88,89]],[74,385,[7,34,44,55,62,72],[51,56,66]],[72,392,[17,80],[7,62,90]],[80,392,[7,72],[17,62,90]],[90,392,[7,62],[17,72,80]],[8,81,[9,27,37,49,50,58,70],[46,64,68]],[9,81,[8,27,37,46,50,58,64,68],[49,70]],[49,81,[8,58,64,68],[9,27,37,46,50,70]],[64,81,[9,37,49,50,70],[8,27,46,58,68]],[68,81,[9,27,49,50],[8,37,46,58,64,70]],[70,81,[8,27,46,50,64],[9,37,49,58,68]],[73,112,[18,82,86,93],[8,64,68,91,94]],[91,112,[8,64,68,93],[18,73,82,86,94]],[49,145,[59,66,69,74],[9,28,38,47,51,52,70,73]],[52,145,[9,59,66,69,70,73],[28,38,47,49,51,74]],[91,208,[9,70],[19,73,88,94]],[22,14,[10,11,75,77,80,81],[20,21,23,24,25,76,78]],[23,14,[10,11,75,76,78,81],[20,21,22,24,25,77,80]],[25,14,[10,11,75,76,77,78,80],[20,21,22,23,24,81]],[80,14,[10,20,21,22,25,75,76,78],[11,23,24,77,81]],[81,14,[10,20,21,22,23,75,76,77,78],[11,24,25,80]],[12,38,[10,21,31,32,33,78,79],[26,82,83]],[78,38,[12,26,32,33,83],[10,21,31,79,82]],[79,38,[12,26,31,33,82,83],[10,21,32,78]],[82,38,[10,21,32,33,79],[12,26,31,78,83]],[83,38,[10,21,31,32,78,79],[12,26,33,82]],[15,42,[10,21,36,40,41,75,79,87],[39,86,89]],[21,42,[15,86,87,89],[10,36,39,40,41,75,79]],[39,42,[10,75,79,87],[15,21,36,40,41,86,89]],[79,42,[15,36,39,40,86,87,89],[10,21,41,75]],[86,42,[10,21,40,41,79],[15,36,39,75,87,89]],[89,42,[10,21,36,41,75,79],[15,39,40,86,87]],[35,262,[11,79,80,84],[14,24,29,32,34,85]],[79,262,[14,29,34,35,84,85],[11,24,32,80]],[80,262,[14,29,32,35,85],[11,24,34,79,84]],[17,266,[11,24,41,43,45,79,81],[44,90]],[79,266,[17,43,44,45,90],[11,24,41,81]],[81,266,[17,41,43,44,90],[11,24,45,79]],[13,22,[12,20,26,27,28,29,75,76,77,82,84],[30,85]],[85,22,[12,20,26,27,28,75,76,77,82],[13,29,30,84]],[83,50,[18,36,46,47,86,87,91],[12,26,48,75]],[86,50,[12,26,47,48,83],[18,36,46,75,87,91]],[91,50,[12,26,36,48,75,83],[18,46,47,86,87]],[13,518,[14,25,33,35,81],[30,83]],[14,518,[13,25,30,33,83],[35,81]],[35,518,[13,83],[14,25,30,33,81]],[13,530,[48,50,52,53,92],[30,83,85]],[30,530,[92],[13,48,50,52,53,83,85]],[83,530,[50,52,53,92],[13,30,48,85]],[85,530,[48,50,52],[13,30,53,83,92]],[14,770,[45,53,56,92],[35,81,85]],[35,770,[92],[14,45,53,56,81,85]],[53,770,[14,81],[35,45,56,85,92]],[81,770,[53,56,92],[14,35,45,85]],[85,770,[45,56],[14,35,53,81,92]],[86,74,[16,22,42,43,90],[15,37,39,76,78,88]],[88,74,[15,22,39,43,78],[16,37,42,76,86,90]],[90,74,[15,22,37,39,76,78,86],[16,42,43,88]],[78,98,[18,46,54,91],[15,31,39,82,89]],[82,98,[15,39,54,89],[18,31,46,78,91]],[91,98,[15,31,39,78],[18,46,54,82,89]],[23,138,[16,17,87,88,89],[38,40,42,44,77,80]],[89,194,[19,49,55],[16,42,54,90,91]],[90,194,[19,49,54,91],[16,42,55,89]],[91,194,[16,42,55,90],[19,49,54,89]],[44,386,[84,92],[17,34,51,55,56,80,90]],[56,386,[17,80,84,90],[34,44,51,55,92]],[92,386,[17,34,44,55,80,90],[51,56,84]],[19,82,[18,27,37,46,50,76,82,86],[49,88]],[46,82,[19,76,88],[18,27,37,49,50,82,86]],[49,82,[18,76,82,86],[19,27,37,46,50,88]],[86,82,[19,27,49,50],[18,37,46,76,82,88]],[52,146,[19,77,84,87,88,91],[28,38,47,49,51,92]],[31,71,[22,27],[]],[34,135,[23,28],[]],[25,523,[45],[]],[45,523,[25],[]],[53,275,[29,51],[]],[32,291,[41],[]],[33,547,[48],[]],[48,547,[33],[]],[43,323,[55],[]],[55,323,[43],[]],[50,579,[],[]],[52,643,[56],[]],[56,643,[52],[]],[93,92,[58,76],[]],[77,156,[59],[]],[66,404,[84],[]],[84,404,[66],[]],[94,184,[69,87],[]],[92,912,[74],[]]],\"edges\":[[34,[3,13,30,48,50,52,53,65,67,74,83,85,92]]],\"groupings\":[1,2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00022.record011" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00022.record011\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-23,-22],[-25,-22],[-27,-22],[-27,-23],[-27,-24],[-27,-26],[-31,-22],[-31,-27],[-33,-27],[-34,-27],[-36,-22],[-36,-25],[-36,-27],[-36,-32],[-36,-33],[-36,-34],[-37,-36],[-38,-22],[-38,-36],[-39,-27],[-40,-22],[-40,-25],[-40,-26],[-40,-27],[-40,-30],[-40,-31],[-40,-32],[-40,-33],[-40,-34],[-40,-35],[-40,-36],[-41,-27],[-41,-36],[-42,-36],[-42,-40],[-43,-22],[-43,-36],[-43,-40],[-44,-27],[-44,-36],[-44,-40],[-45,-22],[-45,-36],[-45,-40],[-46,-22],[-46,-40],[-47,-25],[-47,-26],[-47,-27],[-47,-31],[-47,-34],[-47,-36],[-47,-43],[-47,-45],[-47,-46],[-48,-36],[-49,-22],[-49,-36],[-49,-40],[-50,-21],[-50,-22],[-50,-23],[-50,-25],[-50,-26],[-50,-27],[-50,-30],[-50,-31],[-50,-32],[-50,-33],[-50,-34],[-50,-35],[-50,-36],[-50,-43],[-50,-45],[-50,-46],[-50,-47],[-50,-49],[-53,-22],[-53,-23],[-53,-24],[-53,-25],[-53,-26],[-53,-27],[-53,-32],[-53,-33],[-53,-38],[-53,-39],[-53,-40],[-53,-41],[-53,-42],[-53,-43],[-53,-44],[-53,-46],[-53,-47],[-53,-48],[-54,-22],[-54,-40],[-54,-47],[-54,-50],[-55,-22],[-55,-36],[-55,-47],[-55,-50],[-55,-53],[-56,-22],[-56,-36],[-56,-53],[-57,-22],[-57,-23],[-57,-24],[-57,-25],[-57,-28],[-57,-29],[-57,-32],[-57,-33],[-57,-35],[-57,-38],[-57,-39],[-57,-40],[-57,-41],[-57,-42],[-57,-43],[-57,-44],[-57,-47],[-57,-48],[-57,-55],[-57,-56],[-58,-22],[-58,-27],[-61,-1],[-61,-6],[-61,-22],[-61,-40],[-61,-58],[-62,-22],[-62,-58],[-62,-61],[-63,-2],[-63,-8],[-63,-62],[-64,-5],[-64,-36],[-65,-9],[-65,-27],[-65,-28],[-65,-47],[-65,-49],[-65,-58],[-66,-21],[-66,-27],[-66,-29],[-66,-30],[-66,-31],[-66,-34],[-66,-49],[-66,-58],[-66,-59],[-66,-60],[-66,-65],[-67,-66],[-68,-26],[-68,-34],[-68,-64],[-68,-66],[-69,-40],[-69,-61],[-69,-65],[-71,-7],[-71,-10],[-71,-50],[-71,-56],[-71,-58],[-71,-69],[-72,-40],[-72,-43],[-72,-44],[-72,-59],[-72,-61],[-72,-69],[-72,-71],[-73,-7],[-73,-8],[-73,-24],[-73,-56],[-73,-63],[-73,-71],[-73,-72],[-74,-10],[-74,-47],[-74,-50],[-74,-65],[-74,-69],[-74,-71],[-76,-13],[-76,-22],[-76,-69],[-76,-71],[-79,-16],[-79,-22],[-79,-40],[-79,-61],[-79,-65],[-79,-76],[-79,-77],[-80,-22],[-80,-62],[-80,-76],[-80,-79],[-81,-45],[-81,-46],[-81,-63],[-82,-15],[-82,-33],[-82,-36],[-82,-64],[-82,-81],[-83,-27],[-83,-47],[-83,-59],[-83,-61],[-83,-76],[-84,-28],[-84,-29],[-84,-31],[-84,-34],[-84,-49],[-84,-66],[-84,-76],[-84,-83],[-85,-84],[-86,-26],[-86,-34],[-86,-68],[-86,-82],[-86,-84],[-87,-38],[-87,-40],[-87,-47],[-87,-58],[-87,-71],[-87,-76],[-87,-79],[-87,-83],[-89,-17],[-89,-20],[-89,-43],[-89,-50],[-89,-56],[-89,-58],[-89,-70],[-89,-76],[-90,-40],[-90,-74],[-90,-77],[-90,-79],[-90,-87],[-90,-89],[-91,-73],[-91,-81],[-91,-89],[-91,-90],[-92,-28],[-92,-38],[-92,-41],[-92,-47],[-92,-50],[-92,-55],[-92,-70],[-92,-72],[-92,-74],[-92,-77],[-92,-83],[-92,-87],[-92,-88],[-92,-89],[-92,-90],[-94,-40],[-94,-83],[-94,-87],[-94,-89],[-95,-92],[-63,1,21,22,23,26,58,59,61],[-64,1,21,22,23,24,58,59,60,61],[-61,3,27,33,34,66],[-62,3,27,32,34,65,66],[-65,1,22,33,34,62],[-66,1,22,32,33,61,62],[-32,-62,-66],[-22,6,69,70,72],[-40,1,58,62,70],[-42,1,6,58,69,70,72],[-58,6,40,41,42,72],[-62,6,37,40,41,69,70,72],[-72,1,22,37,42,58,62],[-1,11,76,79,80,94],[-61,11,76,80],[-62,11,76,79,94],[-79,1,58,62],[-80,1,58,61,94],[-36,2,62,63,67],[-62,5,30,35,36,67,68],[-63,5,30,33,36,68],[-45,2,62,64],[-62,8,44,45,46,73],[-64,8,42,44,45,73],[-62,12,81,82],[-81,2,62,64],[-68,3,21,27,28,29,58,59,60,65],[-58,9,47,48,49,74],[-69,3,27,48,49,66],[-66,13,76,83,94],[-4,5,26,34,36,64],[-36,4,66],[-4,49,51,53,54,75],[-66,51,53,54,75],[-68,49,51,53],[-66,14,86],[-68,14,84],[-84,4,68],[-5,46,54,57,75],[-36,75],[-57,5,64,68],[-64,54,57,75],[-68,46,57],[-64,15,86],[-68,15,82],[-82,5,68],[-6,7,23,38,43,44,59,71,73],[-7,6,23,38,40,44,59,61,69],[-61,7,38,43,44,71,73],[-69,7,23,43,44,73],[-73,6,23,38,40,59,61,69],[-9,6,32,40,55,61,72],[-61,9,47,55,74],[-65,6,40,55,72],[-6,16,79,87,90,94,95],[-61,16,87,90,95],[-79,6,69,72,95],[-7,8,24,39,41,45,60,63,70],[-45,7,60,70,71,72],[-63,7,39,41,43,70,71,72],[-71,8,24,41,45,63],[-72,8,24,39,45,60,63],[-7,10,50,55,56,74],[-10,7,43,55,56,72,73],[-72,10,50,56],[-73,10,50,55,74],[-74,7,43,56,73],[-71,17,90,91],[-73,17,89,90,95],[-91,7,71,72,95],[-75,8,35,45,56,63,73],[-73,18,81],[-81,8,73],[-91,8,63],[-9,10,28,38,50,51,59,71],[-10,9,28,38,47,51,59,65,69],[-50,9,59,65,69],[-65,10,38,50,51,71],[-69,10,28,50,51],[-71,9,28,47,51,65],[-74,19,83,87,94],[-92,9,65,69,94],[-50,60,67,70,75],[-53,10,60,67,70,71,74],[-92,10,71],[-23,11,12,76,78,81,82],[-24,11,12,76,77,79,82],[-26,11,12,76,77,78,79,81],[-81,11,21,22,23,26,76,77,79],[-82,11,21,22,23,24,76,77,78,79],[-13,11,22,32,33,34,79,80],[-79,13,27,33,34,84],[-80,13,27,32,34,83,84],[-83,11,22,33,34,80],[-84,11,22,32,33,79,80],[-16,11,22,37,41,42,76,80,88],[-22,16,87,88,90],[-40,11,76,80,88],[-80,16,37,40,41,87,88,90],[-87,11,22,41,42,80],[-90,11,22,37,42,76,80],[-36,12,80,81,85],[-80,15,30,35,36,85,86],[-81,15,30,33,36,86],[-18,12,25,42,44,46,80,82],[-80,18,44,45,46,91],[-82,18,42,44,45,91],[-14,13,21,27,28,29,30,76,77,78,83,85],[-86,13,21,27,28,29,76,77,78,83],[-84,19,37,47,48,87,88,92],[-87,13,27,48,49,84],[-92,13,27,37,49,76,84],[-13,-37,-92],[-14,15,26,34,36,82],[-15,14,26,31,34,84],[-36,14,84],[-14,49,51,53,54,93],[-31,93],[-84,51,53,54,93],[-86,49,51,53],[-15,46,54,57,93],[-36,93],[-54,15,82],[-82,54,57,93],[-86,46,57],[-87,17,23,43,44,91],[-89,16,23,40,44,79],[-91,16,23,38,40,77,79,87],[-79,19,47,55,92],[-83,16,40,55,90],[-92,16,32,40,79],[-24,17,18,88,89,90],[-90,20,50,56],[-91,20,50,55,92],[-92,17,43,56,91],[-45,85,93],[-57,18,81,85,91],[-93,18,35,45,56,81,91],[-20,19,28,38,47,51,77,83,87],[-47,20,77,89],[-50,19,77,83,87],[-87,20,28,50,51],[-53,20,78,85,88,89,92],[-32,23,28],[-35,24,29],[-26,46],[-46,26],[-54,30,52],[-33,42],[-34,49],[-49,34],[-44,56],[-56,44],[-51],[-53,57],[-57,53],[-94,59,77],[-78,60],[-67,85],[-85,67],[-95,70,88],[-93,75],[-1,96],[-2,97],[-3,98],[-5,99],[-100,6],[-6,100],[-101,7],[-7,101],[-102,8],[-8,102],[-103,9],[-9,103],[-104,10],[-10,104],[-11,105],[-12,106],[-13,107],[-14,108],[-15,109],[-110,16],[-16,110],[-111,17],[-17,111],[-112,18],[-18,112],[-19,113],[-114,20],[-97,115],[-96,115],[-99,116],[-116,117],[-98,117],[-117,118],[-115,118],[-119,100,101],[-101,119],[-100,119],[-120,103,104],[-104,120],[-103,120],[-103,-104,121],[-122,102,120],[-120,122],[-121,123],[-102,122],[-102,-120,123],[-124,119,122],[-122,124],[-123,125],[-119,124],[-119,-122,125],[-119,-123,126],[-124,127],[-125,128],[-126,129],[-118,-124,128],[-118,-125,129],[-106,130],[-105,130],[-108,131],[-108,-109,132],[-131,133],[-132,134],[-107,-131,134],[-107,-132,135],[-133,136],[-134,137],[-135,138],[-130,136],[-130,-134,138],[-139,110,111],[-111,139],[-110,139],[-113,140],[-141,114],[-143,112,141],[-112,142],[-112,-140,143],[-142,144],[-145,139,143],[-143,145],[-139,144],[-139,-142,145],[-136,-144,146],[-136,-145,147],[-137,146],[-137,-144,147],[-137,-145,148],[-138,147],[-138,-144,148],[-127,-148,149],[-128,-147,149],[-129,-146,149],[-149],[-150,31,36,68,86],[-36,150],[-151,25,62,63,64],[-152,80,81,82],[-153,27,66,84],[-154,43,45,73,91],[-155,72,74,90,92],[-156,61,65,79,83],[-157,58,69,71,76,87,89],[-158,22,40,47,50],[-159,150,151],[-160,150],[-160,151],[-161,152],[-161,153],[-162,159],[-162,160,161],[-163,160],[-163,161],[-164,154],[-164,155],[-165,157,158],[-166,157],[-166,158],[-167,156,166],[-168,156],[-167,165],[-168,166],[-169,164,168],[-170,164],[-169,167],[-170,168],[-171,162],[-171,163,170],[-171,169],[171],[-30,172],[-67,172],[-75,172],[-52,173],[-85,173],[-93,173],[-21,174],[-59,174],[-60,174],[-70,174],[-37,175],[-77,175],[-78,175],[-88,175],[-176,23,24,26,33,34,39,41,44,51,53,54],[-34,176],[-53,176],[-57,177],[-173,178],[-172,178],[-172,-173,179],[-175,180],[-174,180],[-180,181],[-178,181],[-179,-180,182],[-176,183],[-177,184],[-183,-184,185],[-181,-185,186],[-182,186],[-186],[-3,-4,-9,-16,-36,-61,-63,-71,-75,-80,-84,-91,-92,-93],[-3,-4,-7,-20,-36,-61,-63,-74,-75,-80,-84,-87,-91,-93],[-3,-4,-10,-17,-36,-62,-69,-73,-75,-79,-81,-84,-92,-93],[-3,-4,-6,-19,-36,-62,-73,-74,-75,-79,-81,-84,-89,-93],[-4,-5,-10,-20,-47,-58,-63,-72,-75,-79,-82,-84,-91,-93],[-4,-5,-9,-19,-50,-58,-63,-72,-75,-79,-82,-84,-91,-93],[-1,-4,-5,-11,-40,-63,-65,-71,-75,-82,-84,-91,-92,-93],[-1,-4,-5,-11,-50,-63,-65,-72,-75,-82,-84,-87,-91,-93],[-1,-4,-5,-15,-40,-63,-65,-71,-75,-80,-84,-91,-92,-93],[-1,-4,-5,-15,-50,-63,-65,-72,-75,-80,-84,-87,-91,-93],[-1,-4,-8,-15,-40,-64,-65,-71,-75,-80,-84,-91,-92,-93],[-1,-4,-8,-15,-50,-64,-65,-72,-75,-80,-84,-87,-91,-93],[-1,-4,-6,-16,-36,-63,-65,-71,-75,-80,-84,-91,-92,-93],[-1,-4,-10,-20,-36,-63,-65,-72,-75,-80,-84,-87,-91,-93],[-4,-5,-6,-16,-22,-63,-65,-71,-75,-82,-84,-91,-92,-93],[-4,-5,-10,-20,-22,-63,-65,-72,-75,-82,-84,-87,-91,-93],[-1,-14,-15,-18,-40,-64,-66,-73,-74,-75,-80,-83,-89,-93],[-1,-14,-15,-18,-50,-64,-66,-69,-73,-75,-80,-83,-90,-93],[-6,-7,-9,-10,-53,-57,-58,-63,-68,-79,-82,-84,-91,-92],[-9,-10,-19,-20,-53,-57,-58,-63,-68,-72,-79,-82,-84,-91],[-6,-7,-19,-20,-53,-57,-58,-63,-68,-74,-79,-82,-84,-91],[-1,-10,-11,-20,-53,-57,-63,-65,-68,-72,-82,-84,-87,-91],[-1,-10,-15,-20,-53,-57,-63,-65,-68,-72,-80,-84,-87,-91],[-1,-10,-18,-20,-53,-57,-64,-66,-69,-73,-80,-83,-86,-90],[-1,-3,-7,-10,-53,-57,-63,-68,-69,-79,-82,-84,-91,-92],[-1,-10,-13,-17,-53,-57,-64,-66,-69,-73,-79,-81,-86,-92],[-3,-7,-8,-10,-53,-57,-62,-68,-69,-79,-82,-84,-91,-92],[-3,-10,-17,-18,-53,-57,-62,-68,-69,-73,-79,-82,-84,-92],[-3,-10,-15,-17,-53,-57,-62,-68,-69,-73,-79,-81,-84,-92],[-3,-7,-15,-20,-53,-57,-61,-63,-68,-74,-80,-84,-87,-91],[-1,-3,-6,-9,-53,-57,-63,-68,-71,-79,-82,-84,-91,-92],[-1,-6,-11,-16,-53,-57,-63,-65,-68,-71,-82,-84,-91,-92],[-1,-6,-15,-16,-53,-57,-63,-65,-68,-71,-80,-84,-91,-92],[-1,-6,-16,-18,-53,-57,-64,-66,-73,-74,-80,-83,-86,-89],[-3,-6,-8,-9,-53,-57,-62,-68,-71,-79,-82,-84,-91,-92],[-1,-6,-13,-19,-53,-57,-64,-66,-73,-74,-79,-81,-86,-89],[-3,-9,-15,-16,-53,-57,-61,-63,-68,-71,-80,-84,-91,-92],[-3,-6,-18,-19,-53,-57,-62,-68,-73,-74,-79,-82,-84,-89],[-3,-6,-15,-19,-53,-57,-62,-68,-73,-74,-79,-81,-84,-89],[-6,-13,-14,-19,-36,-62,-66,-73,-74,-75,-79,-81,-89,-93],[-10,-13,-14,-17,-36,-62,-66,-69,-73,-75,-79,-81,-92,-93],[-7,-13,-14,-20,-36,-61,-63,-66,-74,-75,-80,-87,-91,-93],[-9,-13,-14,-16,-36,-61,-63,-66,-71,-75,-80,-91,-92,-93],[-10,-14,-15,-20,-47,-61,-64,-66,-73,-75,-76,-81,-90,-93],[-9,-14,-15,-19,-50,-61,-64,-66,-73,-75,-76,-81,-90,-93],[-1,-11,-14,-15,-40,-64,-66,-73,-74,-75,-81,-83,-89,-93],[-1,-11,-14,-15,-50,-64,-66,-69,-73,-75,-81,-83,-90,-93],[-5,-11,-14,-15,-40,-62,-66,-73,-74,-75,-81,-83,-89,-93],[-5,-11,-14,-15,-50,-62,-66,-69,-73,-75,-81,-83,-90,-93],[-5,-11,-14,-18,-40,-62,-66,-73,-74,-75,-82,-83,-89,-93],[-5,-11,-14,-18,-50,-62,-66,-69,-73,-75,-82,-83,-90,-93],[-6,-11,-14,-16,-36,-62,-66,-73,-74,-75,-81,-83,-89,-93],[-10,-11,-14,-20,-36,-62,-66,-69,-73,-75,-81,-83,-90,-93],[-6,-14,-15,-16,-22,-64,-66,-73,-74,-75,-81,-83,-89,-93],[-10,-14,-15,-20,-22,-64,-66,-69,-73,-75,-81,-83,-90,-93],[-4,-5,-8,-11,-40,-62,-65,-71,-75,-82,-84,-91,-92,-93],[-4,-5,-8,-11,-50,-62,-65,-72,-75,-82,-84,-87,-91,-93],[-16,-17,-19,-20,-53,-57,-61,-64,-66,-73,-74,-76,-81,-86],[-9,-10,-19,-20,-53,-57,-61,-64,-66,-73,-76,-81,-86,-90],[-9,-10,-16,-17,-53,-57,-61,-64,-66,-73,-76,-81,-86,-92],[-1,-10,-11,-20,-53,-57,-64,-66,-69,-73,-81,-83,-86,-90],[-5,-10,-11,-20,-53,-57,-62,-66,-69,-73,-81,-83,-86,-90],[-8,-10,-11,-20,-53,-57,-62,-65,-68,-72,-82,-84,-87,-91],[-11,-13,-17,-20,-53,-57,-61,-64,-66,-73,-74,-81,-86,-87],[-3,-7,-11,-20,-53,-57,-61,-63,-68,-74,-82,-84,-87,-91],[-13,-17,-18,-20,-53,-57,-61,-64,-66,-73,-74,-80,-86,-87],[-7,-8,-13,-20,-53,-57,-61,-64,-66,-74,-80,-86,-87,-91],[-5,-7,-13,-20,-53,-57,-61,-63,-66,-74,-80,-86,-87,-91],[-5,-10,-13,-17,-53,-57,-62,-66,-69,-73,-79,-81,-86,-92],[-11,-13,-16,-19,-53,-57,-61,-64,-66,-73,-74,-81,-86,-89],[-1,-6,-11,-16,-53,-57,-64,-66,-73,-74,-81,-83,-86,-89],[-5,-6,-11,-16,-53,-57,-62,-66,-73,-74,-81,-83,-86,-89],[-6,-8,-11,-16,-53,-57,-62,-65,-68,-71,-82,-84,-91,-92],[-13,-16,-18,-19,-53,-57,-61,-64,-66,-73,-74,-80,-86,-89],[-3,-9,-11,-16,-53,-57,-61,-63,-68,-71,-82,-84,-91,-92],[-5,-6,-13,-19,-53,-57,-62,-66,-73,-74,-79,-81,-86,-89],[-8,-9,-13,-16,-53,-57,-61,-64,-66,-71,-80,-86,-91,-92],[-5,-9,-13,-16,-53,-57,-61,-63,-66,-71,-80,-86,-91,-92],[4,14,31,49,51,53,54,66,68,75,84,86,93]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"group\",\"index\":0,\"kind\":1},{\"tag\":\"group\",\"index\":1,\"kind\":1},{\"tag\":\"group\",\"index\":2,\"kind\":1},{\"tag\":\"group\",\"index\":4,\"kind\":1},{\"tag\":\"group\",\"index\":5,\"kind\":1},{\"tag\":\"group\",\"index\":6,\"kind\":1},{\"tag\":\"group\",\"index\":7,\"kind\":1},{\"tag\":\"group\",\"index\":8,\"kind\":1},{\"tag\":\"group\",\"index\":9,\"kind\":1},{\"tag\":\"group\",\"index\":10,\"kind\":1},{\"tag\":\"group\",\"index\":11,\"kind\":1},{\"tag\":\"group\",\"index\":12,\"kind\":1},{\"tag\":\"group\",\"index\":13,\"kind\":1},{\"tag\":\"group\",\"index\":14,\"kind\":1},{\"tag\":\"group\",\"index\":15,\"kind\":1},{\"tag\":\"group\",\"index\":16,\"kind\":1},{\"tag\":\"group\",\"index\":17,\"kind\":1},{\"tag\":\"group\",\"index\":18,\"kind\":1},{\"tag\":\"group\",\"index\":19,\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":22,\"b\":21},{\"tag\":\"incompatible\",\"a\":24,\"b\":21},{\"tag\":\"incompatible\",\"a\":26,\"b\":21},{\"tag\":\"incompatible\",\"a\":26,\"b\":22},{\"tag\":\"incompatible\",\"a\":26,\"b\":23},{\"tag\":\"incompatible\",\"a\":26,\"b\":25},{\"tag\":\"incompatible\",\"a\":30,\"b\":21},{\"tag\":\"incompatible\",\"a\":30,\"b\":26},{\"tag\":\"incompatible\",\"a\":32,\"b\":26},{\"tag\":\"incompatible\",\"a\":33,\"b\":26},{\"tag\":\"incompatible\",\"a\":35,\"b\":21},{\"tag\":\"incompatible\",\"a\":35,\"b\":24},{\"tag\":\"incompatible\",\"a\":35,\"b\":26},{\"tag\":\"incompatible\",\"a\":35,\"b\":31},{\"tag\":\"incompatible\",\"a\":35,\"b\":32},{\"tag\":\"incompatible\",\"a\":35,\"b\":33},{\"tag\":\"incompatible\",\"a\":36,\"b\":35},{\"tag\":\"incompatible\",\"a\":37,\"b\":21},{\"tag\":\"incompatible\",\"a\":37,\"b\":35},{\"tag\":\"incompatible\",\"a\":38,\"b\":26},{\"tag\":\"incompatible\",\"a\":39,\"b\":21},{\"tag\":\"incompatible\",\"a\":39,\"b\":24},{\"tag\":\"incompatible\",\"a\":39,\"b\":25},{\"tag\":\"incompatible\",\"a\":39,\"b\":26},{\"tag\":\"incompatible\",\"a\":39,\"b\":29},{\"tag\":\"incompatible\",\"a\":39,\"b\":30},{\"tag\":\"incompatible\",\"a\":39,\"b\":31},{\"tag\":\"incompatible\",\"a\":39,\"b\":32},{\"tag\":\"incompatible\",\"a\":39,\"b\":33},{\"tag\":\"incompatible\",\"a\":39,\"b\":34},{\"tag\":\"incompatible\",\"a\":39,\"b\":35},{\"tag\":\"incompatible\",\"a\":40,\"b\":26},{\"tag\":\"incompatible\",\"a\":40,\"b\":35},{\"tag\":\"incompatible\",\"a\":41,\"b\":35},{\"tag\":\"incompatible\",\"a\":41,\"b\":39},{\"tag\":\"incompatible\",\"a\":42,\"b\":21},{\"tag\":\"incompatible\",\"a\":42,\"b\":35},{\"tag\":\"incompatible\",\"a\":42,\"b\":39},{\"tag\":\"incompatible\",\"a\":43,\"b\":26},{\"tag\":\"incompatible\",\"a\":43,\"b\":35},{\"tag\":\"incompatible\",\"a\":43,\"b\":39},{\"tag\":\"incompatible\",\"a\":44,\"b\":21},{\"tag\":\"incompatible\",\"a\":44,\"b\":35},{\"tag\":\"incompatible\",\"a\":44,\"b\":39},{\"tag\":\"incompatible\",\"a\":45,\"b\":21},{\"tag\":\"incompatible\",\"a\":45,\"b\":39},{\"tag\":\"incompatible\",\"a\":46,\"b\":24},{\"tag\":\"incompatible\",\"a\":46,\"b\":25},{\"tag\":\"incompatible\",\"a\":46,\"b\":26},{\"tag\":\"incompatible\",\"a\":46,\"b\":30},{\"tag\":\"incompatible\",\"a\":46,\"b\":33},{\"tag\":\"incompatible\",\"a\":46,\"b\":35},{\"tag\":\"incompatible\",\"a\":46,\"b\":42},{\"tag\":\"incompatible\",\"a\":46,\"b\":44},{\"tag\":\"incompatible\",\"a\":46,\"b\":45},{\"tag\":\"incompatible\",\"a\":47,\"b\":35},{\"tag\":\"incompatible\",\"a\":48,\"b\":21},{\"tag\":\"incompatible\",\"a\":48,\"b\":35},{\"tag\":\"incompatible\",\"a\":48,\"b\":39},{\"tag\":\"incompatible\",\"a\":49,\"b\":20},{\"tag\":\"incompatible\",\"a\":49,\"b\":21},{\"tag\":\"incompatible\",\"a\":49,\"b\":22},{\"tag\":\"incompatible\",\"a\":49,\"b\":24},{\"tag\":\"incompatible\",\"a\":49,\"b\":25},{\"tag\":\"incompatible\",\"a\":49,\"b\":26},{\"tag\":\"incompatible\",\"a\":49,\"b\":29},{\"tag\":\"incompatible\",\"a\":49,\"b\":30},{\"tag\":\"incompatible\",\"a\":49,\"b\":31},{\"tag\":\"incompatible\",\"a\":49,\"b\":32},{\"tag\":\"incompatible\",\"a\":49,\"b\":33},{\"tag\":\"incompatible\",\"a\":49,\"b\":34},{\"tag\":\"incompatible\",\"a\":49,\"b\":35},{\"tag\":\"incompatible\",\"a\":49,\"b\":42},{\"tag\":\"incompatible\",\"a\":49,\"b\":44},{\"tag\":\"incompatible\",\"a\":49,\"b\":45},{\"tag\":\"incompatible\",\"a\":49,\"b\":46},{\"tag\":\"incompatible\",\"a\":49,\"b\":48},{\"tag\":\"incompatible\",\"a\":52,\"b\":21},{\"tag\":\"incompatible\",\"a\":52,\"b\":22},{\"tag\":\"incompatible\",\"a\":52,\"b\":23},{\"tag\":\"incompatible\",\"a\":52,\"b\":24},{\"tag\":\"incompatible\",\"a\":52,\"b\":25},{\"tag\":\"incompatible\",\"a\":52,\"b\":26},{\"tag\":\"incompatible\",\"a\":52,\"b\":31},{\"tag\":\"incompatible\",\"a\":52,\"b\":32},{\"tag\":\"incompatible\",\"a\":52,\"b\":37},{\"tag\":\"incompatible\",\"a\":52,\"b\":38},{\"tag\":\"incompatible\",\"a\":52,\"b\":39},{\"tag\":\"incompatible\",\"a\":52,\"b\":40},{\"tag\":\"incompatible\",\"a\":52,\"b\":41},{\"tag\":\"incompatible\",\"a\":52,\"b\":42},{\"tag\":\"incompatible\",\"a\":52,\"b\":43},{\"tag\":\"incompatible\",\"a\":52,\"b\":45},{\"tag\":\"incompatible\",\"a\":52,\"b\":46},{\"tag\":\"incompatible\",\"a\":52,\"b\":47},{\"tag\":\"incompatible\",\"a\":53,\"b\":21},{\"tag\":\"incompatible\",\"a\":53,\"b\":39},{\"tag\":\"incompatible\",\"a\":53,\"b\":46},{\"tag\":\"incompatible\",\"a\":53,\"b\":49},{\"tag\":\"incompatible\",\"a\":54,\"b\":21},{\"tag\":\"incompatible\",\"a\":54,\"b\":35},{\"tag\":\"incompatible\",\"a\":54,\"b\":46},{\"tag\":\"incompatible\",\"a\":54,\"b\":49},{\"tag\":\"incompatible\",\"a\":54,\"b\":52},{\"tag\":\"incompatible\",\"a\":55,\"b\":21},{\"tag\":\"incompatible\",\"a\":55,\"b\":35},{\"tag\":\"incompatible\",\"a\":55,\"b\":52},{\"tag\":\"incompatible\",\"a\":56,\"b\":21},{\"tag\":\"incompatible\",\"a\":56,\"b\":22},{\"tag\":\"incompatible\",\"a\":56,\"b\":23},{\"tag\":\"incompatible\",\"a\":56,\"b\":24},{\"tag\":\"incompatible\",\"a\":56,\"b\":27},{\"tag\":\"incompatible\",\"a\":56,\"b\":28},{\"tag\":\"incompatible\",\"a\":56,\"b\":31},{\"tag\":\"incompatible\",\"a\":56,\"b\":32},{\"tag\":\"incompatible\",\"a\":56,\"b\":34},{\"tag\":\"incompatible\",\"a\":56,\"b\":37},{\"tag\":\"incompatible\",\"a\":56,\"b\":38},{\"tag\":\"incompatible\",\"a\":56,\"b\":39},{\"tag\":\"incompatible\",\"a\":56,\"b\":40},{\"tag\":\"incompatible\",\"a\":56,\"b\":41},{\"tag\":\"incompatible\",\"a\":56,\"b\":42},{\"tag\":\"incompatible\",\"a\":56,\"b\":43},{\"tag\":\"incompatible\",\"a\":56,\"b\":46},{\"tag\":\"incompatible\",\"a\":56,\"b\":47},{\"tag\":\"incompatible\",\"a\":56,\"b\":54},{\"tag\":\"incompatible\",\"a\":56,\"b\":55},{\"tag\":\"incompatible\",\"a\":57,\"b\":21},{\"tag\":\"incompatible\",\"a\":57,\"b\":26},{\"tag\":\"incompatible\",\"a\":60,\"b\":0},{\"tag\":\"incompatible\",\"a\":60,\"b\":5},{\"tag\":\"incompatible\",\"a\":60,\"b\":21},{\"tag\":\"incompatible\",\"a\":60,\"b\":39},{\"tag\":\"incompatible\",\"a\":60,\"b\":57},{\"tag\":\"incompatible\",\"a\":61,\"b\":21},{\"tag\":\"incompatible\",\"a\":61,\"b\":57},{\"tag\":\"incompatible\",\"a\":61,\"b\":60},{\"tag\":\"incompatible\",\"a\":62,\"b\":1},{\"tag\":\"incompatible\",\"a\":62,\"b\":7},{\"tag\":\"incompatible\",\"a\":62,\"b\":61},{\"tag\":\"incompatible\",\"a\":63,\"b\":4},{\"tag\":\"incompatible\",\"a\":63,\"b\":35},{\"tag\":\"incompatible\",\"a\":64,\"b\":8},{\"tag\":\"incompatible\",\"a\":64,\"b\":26},{\"tag\":\"incompatible\",\"a\":64,\"b\":27},{\"tag\":\"incompatible\",\"a\":64,\"b\":46},{\"tag\":\"incompatible\",\"a\":64,\"b\":48},{\"tag\":\"incompatible\",\"a\":64,\"b\":57},{\"tag\":\"incompatible\",\"a\":65,\"b\":20},{\"tag\":\"incompatible\",\"a\":65,\"b\":26},{\"tag\":\"incompatible\",\"a\":65,\"b\":28},{\"tag\":\"incompatible\",\"a\":65,\"b\":29},{\"tag\":\"incompatible\",\"a\":65,\"b\":30},{\"tag\":\"incompatible\",\"a\":65,\"b\":33},{\"tag\":\"incompatible\",\"a\":65,\"b\":48},{\"tag\":\"incompatible\",\"a\":65,\"b\":57},{\"tag\":\"incompatible\",\"a\":65,\"b\":58},{\"tag\":\"incompatible\",\"a\":65,\"b\":59},{\"tag\":\"incompatible\",\"a\":65,\"b\":64},{\"tag\":\"incompatible\",\"a\":66,\"b\":65},{\"tag\":\"incompatible\",\"a\":67,\"b\":25},{\"tag\":\"incompatible\",\"a\":67,\"b\":33},{\"tag\":\"incompatible\",\"a\":67,\"b\":63},{\"tag\":\"incompatible\",\"a\":67,\"b\":65},{\"tag\":\"incompatible\",\"a\":68,\"b\":39},{\"tag\":\"incompatible\",\"a\":68,\"b\":60},{\"tag\":\"incompatible\",\"a\":68,\"b\":64},{\"tag\":\"incompatible\",\"a\":70,\"b\":6},{\"tag\":\"incompatible\",\"a\":70,\"b\":9},{\"tag\":\"incompatible\",\"a\":70,\"b\":49},{\"tag\":\"incompatible\",\"a\":70,\"b\":55},{\"tag\":\"incompatible\",\"a\":70,\"b\":57},{\"tag\":\"incompatible\",\"a\":70,\"b\":68},{\"tag\":\"incompatible\",\"a\":71,\"b\":39},{\"tag\":\"incompatible\",\"a\":71,\"b\":42},{\"tag\":\"incompatible\",\"a\":71,\"b\":43},{\"tag\":\"incompatible\",\"a\":71,\"b\":58},{\"tag\":\"incompatible\",\"a\":71,\"b\":60},{\"tag\":\"incompatible\",\"a\":71,\"b\":68},{\"tag\":\"incompatible\",\"a\":71,\"b\":70},{\"tag\":\"incompatible\",\"a\":72,\"b\":6},{\"tag\":\"incompatible\",\"a\":72,\"b\":7},{\"tag\":\"incompatible\",\"a\":72,\"b\":23},{\"tag\":\"incompatible\",\"a\":72,\"b\":55},{\"tag\":\"incompatible\",\"a\":72,\"b\":62},{\"tag\":\"incompatible\",\"a\":72,\"b\":70},{\"tag\":\"incompatible\",\"a\":72,\"b\":71},{\"tag\":\"incompatible\",\"a\":73,\"b\":9},{\"tag\":\"incompatible\",\"a\":73,\"b\":46},{\"tag\":\"incompatible\",\"a\":73,\"b\":49},{\"tag\":\"incompatible\",\"a\":73,\"b\":64},{\"tag\":\"incompatible\",\"a\":73,\"b\":68},{\"tag\":\"incompatible\",\"a\":73,\"b\":70},{\"tag\":\"incompatible\",\"a\":75,\"b\":12},{\"tag\":\"incompatible\",\"a\":75,\"b\":21},{\"tag\":\"incompatible\",\"a\":75,\"b\":68},{\"tag\":\"incompatible\",\"a\":75,\"b\":70},{\"tag\":\"incompatible\",\"a\":78,\"b\":15},{\"tag\":\"incompatible\",\"a\":78,\"b\":21},{\"tag\":\"incompatible\",\"a\":78,\"b\":39},{\"tag\":\"incompatible\",\"a\":78,\"b\":60},{\"tag\":\"incompatible\",\"a\":78,\"b\":64},{\"tag\":\"incompatible\",\"a\":78,\"b\":75},{\"tag\":\"incompatible\",\"a\":78,\"b\":76},{\"tag\":\"incompatible\",\"a\":79,\"b\":21},{\"tag\":\"incompatible\",\"a\":79,\"b\":61},{\"tag\":\"incompatible\",\"a\":79,\"b\":75},{\"tag\":\"incompatible\",\"a\":79,\"b\":78},{\"tag\":\"incompatible\",\"a\":80,\"b\":44},{\"tag\":\"incompatible\",\"a\":80,\"b\":45},{\"tag\":\"incompatible\",\"a\":80,\"b\":62},{\"tag\":\"incompatible\",\"a\":81,\"b\":14},{\"tag\":\"incompatible\",\"a\":81,\"b\":32},{\"tag\":\"incompatible\",\"a\":81,\"b\":35},{\"tag\":\"incompatible\",\"a\":81,\"b\":63},{\"tag\":\"incompatible\",\"a\":81,\"b\":80},{\"tag\":\"incompatible\",\"a\":82,\"b\":26},{\"tag\":\"incompatible\",\"a\":82,\"b\":46},{\"tag\":\"incompatible\",\"a\":82,\"b\":58},{\"tag\":\"incompatible\",\"a\":82,\"b\":60},{\"tag\":\"incompatible\",\"a\":82,\"b\":75},{\"tag\":\"incompatible\",\"a\":83,\"b\":27},{\"tag\":\"incompatible\",\"a\":83,\"b\":28},{\"tag\":\"incompatible\",\"a\":83,\"b\":30},{\"tag\":\"incompatible\",\"a\":83,\"b\":33},{\"tag\":\"incompatible\",\"a\":83,\"b\":48},{\"tag\":\"incompatible\",\"a\":83,\"b\":65},{\"tag\":\"incompatible\",\"a\":83,\"b\":75},{\"tag\":\"incompatible\",\"a\":83,\"b\":82},{\"tag\":\"incompatible\",\"a\":84,\"b\":83},{\"tag\":\"incompatible\",\"a\":85,\"b\":25},{\"tag\":\"incompatible\",\"a\":85,\"b\":33},{\"tag\":\"incompatible\",\"a\":85,\"b\":67},{\"tag\":\"incompatible\",\"a\":85,\"b\":81},{\"tag\":\"incompatible\",\"a\":85,\"b\":83},{\"tag\":\"incompatible\",\"a\":86,\"b\":37},{\"tag\":\"incompatible\",\"a\":86,\"b\":39},{\"tag\":\"incompatible\",\"a\":86,\"b\":46},{\"tag\":\"incompatible\",\"a\":86,\"b\":57},{\"tag\":\"incompatible\",\"a\":86,\"b\":70},{\"tag\":\"incompatible\",\"a\":86,\"b\":75},{\"tag\":\"incompatible\",\"a\":86,\"b\":78},{\"tag\":\"incompatible\",\"a\":86,\"b\":82},{\"tag\":\"incompatible\",\"a\":88,\"b\":16},{\"tag\":\"incompatible\",\"a\":88,\"b\":19},{\"tag\":\"incompatible\",\"a\":88,\"b\":42},{\"tag\":\"incompatible\",\"a\":88,\"b\":49},{\"tag\":\"incompatible\",\"a\":88,\"b\":55},{\"tag\":\"incompatible\",\"a\":88,\"b\":57},{\"tag\":\"incompatible\",\"a\":88,\"b\":69},{\"tag\":\"incompatible\",\"a\":88,\"b\":75},{\"tag\":\"incompatible\",\"a\":89,\"b\":39},{\"tag\":\"incompatible\",\"a\":89,\"b\":73},{\"tag\":\"incompatible\",\"a\":89,\"b\":76},{\"tag\":\"incompatible\",\"a\":89,\"b\":78},{\"tag\":\"incompatible\",\"a\":89,\"b\":86},{\"tag\":\"incompatible\",\"a\":89,\"b\":88},{\"tag\":\"incompatible\",\"a\":90,\"b\":72},{\"tag\":\"incompatible\",\"a\":90,\"b\":80},{\"tag\":\"incompatible\",\"a\":90,\"b\":88},{\"tag\":\"incompatible\",\"a\":90,\"b\":89},{\"tag\":\"incompatible\",\"a\":91,\"b\":27},{\"tag\":\"incompatible\",\"a\":91,\"b\":37},{\"tag\":\"incompatible\",\"a\":91,\"b\":40},{\"tag\":\"incompatible\",\"a\":91,\"b\":46},{\"tag\":\"incompatible\",\"a\":91,\"b\":49},{\"tag\":\"incompatible\",\"a\":91,\"b\":54},{\"tag\":\"incompatible\",\"a\":91,\"b\":69},{\"tag\":\"incompatible\",\"a\":91,\"b\":71},{\"tag\":\"incompatible\",\"a\":91,\"b\":73},{\"tag\":\"incompatible\",\"a\":91,\"b\":76},{\"tag\":\"incompatible\",\"a\":91,\"b\":82},{\"tag\":\"incompatible\",\"a\":91,\"b\":86},{\"tag\":\"incompatible\",\"a\":91,\"b\":87},{\"tag\":\"incompatible\",\"a\":91,\"b\":88},{\"tag\":\"incompatible\",\"a\":91,\"b\":89},{\"tag\":\"incompatible\",\"a\":93,\"b\":39},{\"tag\":\"incompatible\",\"a\":93,\"b\":82},{\"tag\":\"incompatible\",\"a\":93,\"b\":86},{\"tag\":\"incompatible\",\"a\":93,\"b\":88},{\"tag\":\"incompatible\",\"a\":94,\"b\":91},{\"tag\":\"mate\",\"ridge\":13,\"a\":62,\"owners\":[0,20,21,22,25,57,58,60]},{\"tag\":\"mate\",\"ridge\":13,\"a\":63,\"owners\":[0,20,21,22,23,57,58,59,60]},{\"tag\":\"mate\",\"ridge\":37,\"a\":60,\"owners\":[2,26,32,33,65]},{\"tag\":\"mate\",\"ridge\":37,\"a\":61,\"owners\":[2,26,31,33,64,65]},{\"tag\":\"mate\",\"ridge\":37,\"a\":64,\"owners\":[0,21,32,33,61]},{\"tag\":\"mate\",\"ridge\":37,\"a\":65,\"owners\":[0,21,31,32,60,61]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[31,61,65]},{\"tag\":\"mate\",\"ridge\":41,\"a\":21,\"owners\":[5,68,69,71]},{\"tag\":\"mate\",\"ridge\":41,\"a\":39,\"owners\":[0,57,61,69]},{\"tag\":\"mate\",\"ridge\":41,\"a\":41,\"owners\":[0,5,57,68,69,71]},{\"tag\":\"mate\",\"ridge\":41,\"a\":57,\"owners\":[5,39,40,41,71]},{\"tag\":\"mate\",\"ridge\":41,\"a\":61,\"owners\":[5,36,39,40,68,69,71]},{\"tag\":\"mate\",\"ridge\":41,\"a\":71,\"owners\":[0,21,36,41,57,61]},{\"tag\":\"mate\",\"ridge\":44,\"a\":0,\"owners\":[10,75,78,79,93]},{\"tag\":\"mate\",\"ridge\":44,\"a\":60,\"owners\":[10,75,79]},{\"tag\":\"mate\",\"ridge\":44,\"a\":61,\"owners\":[10,75,78,93]},{\"tag\":\"mate\",\"ridge\":44,\"a\":78,\"owners\":[0,57,61]},{\"tag\":\"mate\",\"ridge\":44,\"a\":79,\"owners\":[0,57,60,93]},{\"tag\":\"mate\",\"ridge\":261,\"a\":35,\"owners\":[1,61,62,66]},{\"tag\":\"mate\",\"ridge\":261,\"a\":61,\"owners\":[4,29,34,35,66,67]},{\"tag\":\"mate\",\"ridge\":261,\"a\":62,\"owners\":[4,29,32,35,67]},{\"tag\":\"mate\",\"ridge\":265,\"a\":44,\"owners\":[1,61,63]},{\"tag\":\"mate\",\"ridge\":265,\"a\":61,\"owners\":[7,43,44,45,72]},{\"tag\":\"mate\",\"ridge\":265,\"a\":63,\"owners\":[7,41,43,44,72]},{\"tag\":\"mate\",\"ridge\":268,\"a\":61,\"owners\":[11,80,81]},{\"tag\":\"mate\",\"ridge\":268,\"a\":80,\"owners\":[1,61,63]},{\"tag\":\"mate\",\"ridge\":21,\"a\":67,\"owners\":[2,20,26,27,28,57,58,59,64]},{\"tag\":\"mate\",\"ridge\":49,\"a\":57,\"owners\":[8,46,47,48,73]},{\"tag\":\"mate\",\"ridge\":49,\"a\":68,\"owners\":[2,26,47,48,65]},{\"tag\":\"mate\",\"ridge\":52,\"a\":65,\"owners\":[12,75,82,93]},{\"tag\":\"mate\",\"ridge\":517,\"a\":3,\"owners\":[4,25,33,35,63]},{\"tag\":\"mate\",\"ridge\":517,\"a\":35,\"owners\":[3,65]},{\"tag\":\"mate\",\"ridge\":529,\"a\":3,\"owners\":[48,50,52,53,74]},{\"tag\":\"mate\",\"ridge\":529,\"a\":65,\"owners\":[50,52,53,74]},{\"tag\":\"mate\",\"ridge\":529,\"a\":67,\"owners\":[48,50,52]},{\"tag\":\"mate\",\"ridge\":532,\"a\":65,\"owners\":[13,85]},{\"tag\":\"mate\",\"ridge\":532,\"a\":67,\"owners\":[13,83]},{\"tag\":\"mate\",\"ridge\":532,\"a\":83,\"owners\":[3,67]},{\"tag\":\"mate\",\"ridge\":769,\"a\":4,\"owners\":[45,53,56,74]},{\"tag\":\"mate\",\"ridge\":769,\"a\":35,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":769,\"a\":56,\"owners\":[4,63,67]},{\"tag\":\"mate\",\"ridge\":769,\"a\":63,\"owners\":[53,56,74]},{\"tag\":\"mate\",\"ridge\":769,\"a\":67,\"owners\":[45,56]},{\"tag\":\"mate\",\"ridge\":772,\"a\":63,\"owners\":[14,85]},{\"tag\":\"mate\",\"ridge\":772,\"a\":67,\"owners\":[14,81]},{\"tag\":\"mate\",\"ridge\":772,\"a\":81,\"owners\":[4,67]},{\"tag\":\"mate\",\"ridge\":73,\"a\":5,\"owners\":[6,22,37,42,43,58,70,72]},{\"tag\":\"mate\",\"ridge\":73,\"a\":6,\"owners\":[5,22,37,39,43,58,60,68]},{\"tag\":\"mate\",\"ridge\":73,\"a\":60,\"owners\":[6,37,42,43,70,72]},{\"tag\":\"mate\",\"ridge\":73,\"a\":68,\"owners\":[6,22,42,43,72]},{\"tag\":\"mate\",\"ridge\":73,\"a\":72,\"owners\":[5,22,37,39,58,60,68]},{\"tag\":\"mate\",\"ridge\":97,\"a\":8,\"owners\":[5,31,39,54,60,71]},{\"tag\":\"mate\",\"ridge\":97,\"a\":60,\"owners\":[8,46,54,73]},{\"tag\":\"mate\",\"ridge\":97,\"a\":64,\"owners\":[5,39,54,71]},{\"tag\":\"mate\",\"ridge\":104,\"a\":5,\"owners\":[15,78,86,89,93,94]},{\"tag\":\"mate\",\"ridge\":104,\"a\":60,\"owners\":[15,86,89,94]},{\"tag\":\"mate\",\"ridge\":104,\"a\":78,\"owners\":[5,68,71,94]},{\"tag\":\"mate\",\"ridge\":137,\"a\":6,\"owners\":[7,23,38,40,44,59,62,69]},{\"tag\":\"mate\",\"ridge\":137,\"a\":44,\"owners\":[6,59,69,70,71]},{\"tag\":\"mate\",\"ridge\":137,\"a\":62,\"owners\":[6,38,40,42,69,70,71]},{\"tag\":\"mate\",\"ridge\":137,\"a\":70,\"owners\":[7,23,40,44,62]},{\"tag\":\"mate\",\"ridge\":137,\"a\":71,\"owners\":[7,23,38,44,59,62]},{\"tag\":\"mate\",\"ridge\":193,\"a\":6,\"owners\":[9,49,54,55,73]},{\"tag\":\"mate\",\"ridge\":193,\"a\":9,\"owners\":[6,42,54,55,71,72]},{\"tag\":\"mate\",\"ridge\":193,\"a\":71,\"owners\":[9,49,55]},{\"tag\":\"mate\",\"ridge\":193,\"a\":72,\"owners\":[9,49,54,73]},{\"tag\":\"mate\",\"ridge\":193,\"a\":73,\"owners\":[6,42,55,72]},{\"tag\":\"mate\",\"ridge\":200,\"a\":70,\"owners\":[16,89,90]},{\"tag\":\"mate\",\"ridge\":200,\"a\":72,\"owners\":[16,88,89,94]},{\"tag\":\"mate\",\"ridge\":200,\"a\":90,\"owners\":[6,70,71,94]},{\"tag\":\"mate\",\"ridge\":385,\"a\":74,\"owners\":[7,34,44,55,62,72]},{\"tag\":\"mate\",\"ridge\":392,\"a\":72,\"owners\":[17,80]},{\"tag\":\"mate\",\"ridge\":392,\"a\":80,\"owners\":[7,72]},{\"tag\":\"mate\",\"ridge\":392,\"a\":90,\"owners\":[7,62]},{\"tag\":\"mate\",\"ridge\":81,\"a\":8,\"owners\":[9,27,37,49,50,58,70]},{\"tag\":\"mate\",\"ridge\":81,\"a\":9,\"owners\":[8,27,37,46,50,58,64,68]},{\"tag\":\"mate\",\"ridge\":81,\"a\":49,\"owners\":[8,58,64,68]},{\"tag\":\"mate\",\"ridge\":81,\"a\":64,\"owners\":[9,37,49,50,70]},{\"tag\":\"mate\",\"ridge\":81,\"a\":68,\"owners\":[9,27,49,50]},{\"tag\":\"mate\",\"ridge\":81,\"a\":70,\"owners\":[8,27,46,50,64]},{\"tag\":\"mate\",\"ridge\":112,\"a\":73,\"owners\":[18,82,86,93]},{\"tag\":\"mate\",\"ridge\":112,\"a\":91,\"owners\":[8,64,68,93]},{\"tag\":\"mate\",\"ridge\":145,\"a\":49,\"owners\":[59,66,69,74]},{\"tag\":\"mate\",\"ridge\":145,\"a\":52,\"owners\":[9,59,66,69,70,73]},{\"tag\":\"mate\",\"ridge\":208,\"a\":91,\"owners\":[9,70]},{\"tag\":\"mate\",\"ridge\":14,\"a\":22,\"owners\":[10,11,75,77,80,81]},{\"tag\":\"mate\",\"ridge\":14,\"a\":23,\"owners\":[10,11,75,76,78,81]},{\"tag\":\"mate\",\"ridge\":14,\"a\":25,\"owners\":[10,11,75,76,77,78,80]},{\"tag\":\"mate\",\"ridge\":14,\"a\":80,\"owners\":[10,20,21,22,25,75,76,78]},{\"tag\":\"mate\",\"ridge\":14,\"a\":81,\"owners\":[10,20,21,22,23,75,76,77,78]},{\"tag\":\"mate\",\"ridge\":38,\"a\":12,\"owners\":[10,21,31,32,33,78,79]},{\"tag\":\"mate\",\"ridge\":38,\"a\":78,\"owners\":[12,26,32,33,83]},{\"tag\":\"mate\",\"ridge\":38,\"a\":79,\"owners\":[12,26,31,33,82,83]},{\"tag\":\"mate\",\"ridge\":38,\"a\":82,\"owners\":[10,21,32,33,79]},{\"tag\":\"mate\",\"ridge\":38,\"a\":83,\"owners\":[10,21,31,32,78,79]},{\"tag\":\"mate\",\"ridge\":42,\"a\":15,\"owners\":[10,21,36,40,41,75,79,87]},{\"tag\":\"mate\",\"ridge\":42,\"a\":21,\"owners\":[15,86,87,89]},{\"tag\":\"mate\",\"ridge\":42,\"a\":39,\"owners\":[10,75,79,87]},{\"tag\":\"mate\",\"ridge\":42,\"a\":79,\"owners\":[15,36,39,40,86,87,89]},{\"tag\":\"mate\",\"ridge\":42,\"a\":86,\"owners\":[10,21,40,41,79]},{\"tag\":\"mate\",\"ridge\":42,\"a\":89,\"owners\":[10,21,36,41,75,79]},{\"tag\":\"mate\",\"ridge\":262,\"a\":35,\"owners\":[11,79,80,84]},{\"tag\":\"mate\",\"ridge\":262,\"a\":79,\"owners\":[14,29,34,35,84,85]},{\"tag\":\"mate\",\"ridge\":262,\"a\":80,\"owners\":[14,29,32,35,85]},{\"tag\":\"mate\",\"ridge\":266,\"a\":17,\"owners\":[11,24,41,43,45,79,81]},{\"tag\":\"mate\",\"ridge\":266,\"a\":79,\"owners\":[17,43,44,45,90]},{\"tag\":\"mate\",\"ridge\":266,\"a\":81,\"owners\":[17,41,43,44,90]},{\"tag\":\"mate\",\"ridge\":22,\"a\":13,\"owners\":[12,20,26,27,28,29,75,76,77,82,84]},{\"tag\":\"mate\",\"ridge\":22,\"a\":85,\"owners\":[12,20,26,27,28,75,76,77,82]},{\"tag\":\"mate\",\"ridge\":50,\"a\":83,\"owners\":[18,36,46,47,86,87,91]},{\"tag\":\"mate\",\"ridge\":50,\"a\":86,\"owners\":[12,26,47,48,83]},{\"tag\":\"mate\",\"ridge\":50,\"a\":91,\"owners\":[12,26,36,48,75,83]},{\"tag\":\"three\",\"ridge\":50,\"vertices\":[12,36,91]},{\"tag\":\"mate\",\"ridge\":518,\"a\":13,\"owners\":[14,25,33,35,81]},{\"tag\":\"mate\",\"ridge\":518,\"a\":14,\"owners\":[13,25,30,33,83]},{\"tag\":\"mate\",\"ridge\":518,\"a\":35,\"owners\":[13,83]},{\"tag\":\"mate\",\"ridge\":530,\"a\":13,\"owners\":[48,50,52,53,92]},{\"tag\":\"mate\",\"ridge\":530,\"a\":30,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":530,\"a\":83,\"owners\":[50,52,53,92]},{\"tag\":\"mate\",\"ridge\":530,\"a\":85,\"owners\":[48,50,52]},{\"tag\":\"mate\",\"ridge\":770,\"a\":14,\"owners\":[45,53,56,92]},{\"tag\":\"mate\",\"ridge\":770,\"a\":35,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":770,\"a\":53,\"owners\":[14,81]},{\"tag\":\"mate\",\"ridge\":770,\"a\":81,\"owners\":[53,56,92]},{\"tag\":\"mate\",\"ridge\":770,\"a\":85,\"owners\":[45,56]},{\"tag\":\"mate\",\"ridge\":74,\"a\":86,\"owners\":[16,22,42,43,90]},{\"tag\":\"mate\",\"ridge\":74,\"a\":88,\"owners\":[15,22,39,43,78]},{\"tag\":\"mate\",\"ridge\":74,\"a\":90,\"owners\":[15,22,37,39,76,78,86]},{\"tag\":\"mate\",\"ridge\":98,\"a\":78,\"owners\":[18,46,54,91]},{\"tag\":\"mate\",\"ridge\":98,\"a\":82,\"owners\":[15,39,54,89]},{\"tag\":\"mate\",\"ridge\":98,\"a\":91,\"owners\":[15,31,39,78]},{\"tag\":\"mate\",\"ridge\":138,\"a\":23,\"owners\":[16,17,87,88,89]},{\"tag\":\"mate\",\"ridge\":194,\"a\":89,\"owners\":[19,49,55]},{\"tag\":\"mate\",\"ridge\":194,\"a\":90,\"owners\":[19,49,54,91]},{\"tag\":\"mate\",\"ridge\":194,\"a\":91,\"owners\":[16,42,55,90]},{\"tag\":\"mate\",\"ridge\":386,\"a\":44,\"owners\":[84,92]},{\"tag\":\"mate\",\"ridge\":386,\"a\":56,\"owners\":[17,80,84,90]},{\"tag\":\"mate\",\"ridge\":386,\"a\":92,\"owners\":[17,34,44,55,80,90]},{\"tag\":\"mate\",\"ridge\":82,\"a\":19,\"owners\":[18,27,37,46,50,76,82,86]},{\"tag\":\"mate\",\"ridge\":82,\"a\":46,\"owners\":[19,76,88]},{\"tag\":\"mate\",\"ridge\":82,\"a\":49,\"owners\":[18,76,82,86]},{\"tag\":\"mate\",\"ridge\":82,\"a\":86,\"owners\":[19,27,49,50]},{\"tag\":\"mate\",\"ridge\":146,\"a\":52,\"owners\":[19,77,84,87,88,91]},{\"tag\":\"mate\",\"ridge\":71,\"a\":31,\"owners\":[22,27]},{\"tag\":\"mate\",\"ridge\":135,\"a\":34,\"owners\":[23,28]},{\"tag\":\"mate\",\"ridge\":523,\"a\":25,\"owners\":[45]},{\"tag\":\"mate\",\"ridge\":523,\"a\":45,\"owners\":[25]},{\"tag\":\"mate\",\"ridge\":275,\"a\":53,\"owners\":[29,51]},{\"tag\":\"mate\",\"ridge\":291,\"a\":32,\"owners\":[41]},{\"tag\":\"mate\",\"ridge\":547,\"a\":33,\"owners\":[48]},{\"tag\":\"mate\",\"ridge\":547,\"a\":48,\"owners\":[33]},{\"tag\":\"mate\",\"ridge\":323,\"a\":43,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":323,\"a\":55,\"owners\":[43]},{\"tag\":\"mate\",\"ridge\":579,\"a\":50,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":643,\"a\":52,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":643,\"a\":56,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":92,\"a\":93,\"owners\":[58,76]},{\"tag\":\"mate\",\"ridge\":156,\"a\":77,\"owners\":[59]},{\"tag\":\"mate\",\"ridge\":404,\"a\":66,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":404,\"a\":84,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":184,\"a\":94,\"owners\":[69,87]},{\"tag\":\"mate\",\"ridge\":912,\"a\":92,\"owners\":[74]},{\"tag\":\"group_take\",\"kind\":1,\"index\":0,\"member\":0,\"full_literals\":[-1,96]},{\"tag\":\"group_take\",\"kind\":1,\"index\":1,\"member\":1,\"full_literals\":[-2,97]},{\"tag\":\"group_take\",\"kind\":1,\"index\":2,\"member\":2,\"full_literals\":[-3,98]},{\"tag\":\"group_take\",\"kind\":1,\"index\":4,\"member\":4,\"full_literals\":[-5,99]},{\"tag\":\"group_or\",\"kind\":1,\"index\":5,\"members\":[5],\"full_literals\":[-100,6]},{\"tag\":\"group_take\",\"kind\":1,\"index\":5,\"member\":5,\"full_literals\":[-6,100]},{\"tag\":\"group_or\",\"kind\":1,\"index\":6,\"members\":[6],\"full_literals\":[-101,7]},{\"tag\":\"group_take\",\"kind\":1,\"index\":6,\"member\":6,\"full_literals\":[-7,101]},{\"tag\":\"group_or\",\"kind\":1,\"index\":7,\"members\":[7],\"full_literals\":[-102,8]},{\"tag\":\"group_take\",\"kind\":1,\"index\":7,\"member\":7,\"full_literals\":[-8,102]},{\"tag\":\"group_or\",\"kind\":1,\"index\":8,\"members\":[8],\"full_literals\":[-103,9]},{\"tag\":\"group_take\",\"kind\":1,\"index\":8,\"member\":8,\"full_literals\":[-9,103]},{\"tag\":\"group_or\",\"kind\":1,\"index\":9,\"members\":[9],\"full_literals\":[-104,10]},{\"tag\":\"group_take\",\"kind\":1,\"index\":9,\"member\":9,\"full_literals\":[-10,104]},{\"tag\":\"group_take\",\"kind\":1,\"index\":10,\"member\":10,\"full_literals\":[-11,105]},{\"tag\":\"group_take\",\"kind\":1,\"index\":11,\"member\":11,\"full_literals\":[-12,106]},{\"tag\":\"group_take\",\"kind\":1,\"index\":12,\"member\":12,\"full_literals\":[-13,107]},{\"tag\":\"group_take\",\"kind\":1,\"index\":13,\"member\":13,\"full_literals\":[-14,108]},{\"tag\":\"group_take\",\"kind\":1,\"index\":14,\"member\":14,\"full_literals\":[-15,109]},{\"tag\":\"group_or\",\"kind\":1,\"index\":15,\"members\":[15],\"full_literals\":[-110,16]},{\"tag\":\"group_take\",\"kind\":1,\"index\":15,\"member\":15,\"full_literals\":[-16,110]},{\"tag\":\"group_or\",\"kind\":1,\"index\":16,\"members\":[16],\"full_literals\":[-111,17]},{\"tag\":\"group_take\",\"kind\":1,\"index\":16,\"member\":16,\"full_literals\":[-17,111]},{\"tag\":\"group_or\",\"kind\":1,\"index\":17,\"members\":[17],\"full_literals\":[-112,18]},{\"tag\":\"group_take\",\"kind\":1,\"index\":17,\"member\":17,\"full_literals\":[-18,112]},{\"tag\":\"group_take\",\"kind\":1,\"index\":18,\"member\":18,\"full_literals\":[-19,113]},{\"tag\":\"group_or\",\"kind\":1,\"index\":19,\"members\":[19],\"full_literals\":[-114,20]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0005\",\"joined_name\":\"grouped1_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-97,115],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0005\",\"joined_name\":\"grouped1_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-96,false,115],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped1_0008\",\"right_name\":\"grouped1_0010\",\"joined_name\":\"grouped1_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-99,116],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped1_0006\",\"right_name\":\"grouped1_0009\",\"joined_name\":\"grouped1_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-116,117],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped1_0006\",\"right_name\":\"grouped1_0009\",\"joined_name\":\"grouped1_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-98,false,117],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-117,118],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-115,false,118],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped1_0011\",\"right_name\":\"grouped1_0014\",\"joined_name\":\"grouped1_0012\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-119,100,101],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped1_0011\",\"right_name\":\"grouped1_0014\",\"joined_name\":\"grouped1_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-101,119],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped1_0011\",\"right_name\":\"grouped1_0014\",\"joined_name\":\"grouped1_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-100,false,119],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped1_0017\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0018\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-120,103,104],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped1_0017\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-104,120],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped1_0017\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-103,false,120],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped1_0017\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0018\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-103,-104,121],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0016\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-122,102,120],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-120,122],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0016\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-121,123],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-102,false,122],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0016\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-102,-120,123],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-124,119,122],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-122,124],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-123,125],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-119,false,124],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-119,-122,125],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-119,-123,126],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-124,127],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-125,128],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-126,129],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-118,-124,128],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0003\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-118,-125,129],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped1_0020\",\"right_name\":\"grouped1_0024\",\"joined_name\":\"grouped1_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-106,130],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped1_0020\",\"right_name\":\"grouped1_0024\",\"joined_name\":\"grouped1_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-105,false,130],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13],\"right\":[14],\"left_name\":\"grouped1_0027\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-108,false,131],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13],\"right\":[14],\"left_name\":\"grouped1_0027\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0028\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-108,-109,132],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13,14],\"left_name\":\"grouped1_0025\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-131,133],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13,14],\"left_name\":\"grouped1_0025\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0026\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-132,134],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13,14],\"left_name\":\"grouped1_0025\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0026\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-107,-131,134],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13,14],\"left_name\":\"grouped1_0025\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0026\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-107,-132,135],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13,14],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-133,136],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13,14],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0022\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-134,137],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13,14],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0022\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-135,138],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13,14],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-130,false,136],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13,14],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0022\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-130,-134,138],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15],\"right\":[16],\"left_name\":\"grouped1_0030\",\"right_name\":\"grouped1_0033\",\"joined_name\":\"grouped1_0031\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-139,110,111],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15],\"right\":[16],\"left_name\":\"grouped1_0030\",\"right_name\":\"grouped1_0033\",\"joined_name\":\"grouped1_0031\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-111,139],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15],\"right\":[16],\"left_name\":\"grouped1_0030\",\"right_name\":\"grouped1_0033\",\"joined_name\":\"grouped1_0031\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-110,false,139],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[18],\"right\":[19],\"left_name\":\"grouped1_0036\",\"right_name\":\"grouped1_0038\",\"joined_name\":\"grouped1_0037\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-113,false,140],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[18],\"right\":[19],\"left_name\":\"grouped1_0036\",\"right_name\":\"grouped1_0038\",\"joined_name\":\"grouped1_0037\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-141,false,114],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17],\"right\":[18,19],\"left_name\":\"grouped1_0034\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0035\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-143,112,141],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17],\"right\":[18,19],\"left_name\":\"grouped1_0034\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0035\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-112,false,142],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17],\"right\":[18,19],\"left_name\":\"grouped1_0034\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0035\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-112,-140,143],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16],\"right\":[17,18,19],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0032\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-142,144],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16],\"right\":[17,18,19],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0032\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-145,139,143],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16],\"right\":[17,18,19],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0032\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-143,145],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16],\"right\":[17,18,19],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0032\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-139,false,144],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16],\"right\":[17,18,19],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0032\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-139,-142,145],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-136,-144,146],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-136,-145,147],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-137,false,146],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-137,-144,147],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-137,-145,148],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-138,false,147],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0023\",\"a\":3,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-138,-144,148],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9],\"right\":[10,11,12,13,14,15,16,17,18,19],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"groupKind1\",\"a\":1,\"b\":4,\"direction\":\"forward\",\"full_literals\":[-127,-148,149],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9],\"right\":[10,11,12,13,14,15,16,17,18,19],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"groupKind1\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-128,-147,149],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9],\"right\":[10,11,12,13,14,15,16,17,18,19],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"groupKind1\",\"a\":3,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-129,-146,149],\"grouped\":true,\"kind\":1},{\"tag\":\"quota_upper\",\"kind\":1,\"quota\":4,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[30,35,67,85],\"full_literals\":[-150,31,36,68,86]},{\"tag\":\"group_take\",\"kind\":2,\"index\":0,\"member\":35,\"full_literals\":[-36,150]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[24,61,62,63],\"full_literals\":[-151,25,62,63,64]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[79,80,81],\"full_literals\":[-152,80,81,82]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[26,65,83],\"full_literals\":[-153,27,66,84]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[42,44,72,90],\"full_literals\":[-154,43,45,73,91]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[71,73,89,91],\"full_literals\":[-155,72,74,90,92]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[60,64,78,82],\"full_literals\":[-156,61,65,79,83]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[57,68,70,75,86,88],\"full_literals\":[-157,58,69,71,76,87,89]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[21,39,46,49],\"full_literals\":[-158,22,40,47,50]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0039\",\"right_name\":\"grouped2_0043\",\"joined_name\":\"grouped2_0040\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-159,150,151],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0039\",\"right_name\":\"grouped2_0043\",\"joined_name\":\"grouped2_0040\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-160,150,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0039\",\"right_name\":\"grouped2_0043\",\"joined_name\":\"grouped2_0040\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-160,false,151],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0044\",\"right_name\":\"grouped2_0046\",\"joined_name\":\"grouped2_0045\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-161,152,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0044\",\"right_name\":\"grouped2_0046\",\"joined_name\":\"grouped2_0045\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-161,false,153],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0041\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-162,159,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0041\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-162,160,161],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0041\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-163,160,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0041\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-163,false,161],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0047\",\"right_name\":\"grouped2_0050\",\"joined_name\":\"grouped2_0048\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-164,154,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0047\",\"right_name\":\"grouped2_0050\",\"joined_name\":\"grouped2_0048\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-164,false,155],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0053\",\"right_name\":\"grouped2_0055\",\"joined_name\":\"grouped2_0054\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-165,157,158],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0053\",\"right_name\":\"grouped2_0055\",\"joined_name\":\"grouped2_0054\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-166,157,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0053\",\"right_name\":\"grouped2_0055\",\"joined_name\":\"grouped2_0054\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-166,false,158],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0052\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-167,156,166],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0052\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-168,156,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0052\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-167,false,165],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0054\",\"joined_name\":\"grouped2_0052\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-168,false,166],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0048\",\"right_name\":\"grouped2_0052\",\"joined_name\":\"grouped2_0049\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-169,164,168],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0048\",\"right_name\":\"grouped2_0052\",\"joined_name\":\"grouped2_0049\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-170,164,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0048\",\"right_name\":\"grouped2_0052\",\"joined_name\":\"grouped2_0049\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-169,false,167],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0048\",\"right_name\":\"grouped2_0052\",\"joined_name\":\"grouped2_0049\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-170,false,168],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-171,162,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-171,163,170],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-171,false,169],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":29,\"full_literals\":[-30,172]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":66,\"full_literals\":[-67,172]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":74,\"full_literals\":[-75,172]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":51,\"full_literals\":[-52,173]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":84,\"full_literals\":[-85,173]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":92,\"full_literals\":[-93,173]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":20,\"full_literals\":[-21,174]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":58,\"full_literals\":[-59,174]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":59,\"full_literals\":[-60,174]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":69,\"full_literals\":[-70,174]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":36,\"full_literals\":[-37,175]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":76,\"full_literals\":[-77,175]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":77,\"full_literals\":[-78,175]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":87,\"full_literals\":[-88,175]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[22,23,25,32,33,38,40,43,50,52,53],\"full_literals\":[-176,23,24,26,33,34,39,41,44,51,53,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":33,\"full_literals\":[-34,176]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":52,\"full_literals\":[-53,176]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":56,\"full_literals\":[-57,177]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0056\",\"right_name\":\"grouped3_0060\",\"joined_name\":\"grouped3_0057\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-173,178],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0056\",\"right_name\":\"grouped3_0060\",\"joined_name\":\"grouped3_0057\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-172,false,178],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0056\",\"right_name\":\"grouped3_0060\",\"joined_name\":\"grouped3_0057\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-172,-173,179],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0061\",\"right_name\":\"grouped3_0063\",\"joined_name\":\"grouped3_0062\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-175,180],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0061\",\"right_name\":\"grouped3_0063\",\"joined_name\":\"grouped3_0062\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-174,false,180],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0057\",\"right_name\":\"grouped3_0062\",\"joined_name\":\"grouped3_0058\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-180,181],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0057\",\"right_name\":\"grouped3_0062\",\"joined_name\":\"grouped3_0058\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-178,false,181],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0057\",\"right_name\":\"grouped3_0062\",\"joined_name\":\"grouped3_0058\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-179,-180,182],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0064\",\"right_name\":\"grouped3_0067\",\"joined_name\":\"grouped3_0065\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-176,183],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0068\",\"right_name\":\"grouped3_0070\",\"joined_name\":\"grouped3_0069\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-177,false,184],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0065\",\"right_name\":\"grouped3_0069\",\"joined_name\":\"grouped3_0066\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-183,-184,185],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0058\",\"right_name\":\"grouped3_0066\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-181,-185,186],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0058\",\"right_name\":\"grouped3_0066\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-182,false,186],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"block\",\"leaf\":0,\"vertices\":[2,3,8,15,35,60,62,70,74,79,83,90,91,92]},{\"tag\":\"block\",\"leaf\":1,\"vertices\":[2,3,6,19,35,60,62,73,74,79,83,86,90,92]},{\"tag\":\"block\",\"leaf\":2,\"vertices\":[2,3,9,16,35,61,68,72,74,78,80,83,91,92]},{\"tag\":\"block\",\"leaf\":3,\"vertices\":[2,3,5,18,35,61,72,73,74,78,80,83,88,92]},{\"tag\":\"block\",\"leaf\":4,\"vertices\":[3,4,9,19,46,57,62,71,74,78,81,83,90,92]},{\"tag\":\"block\",\"leaf\":5,\"vertices\":[3,4,8,18,49,57,62,71,74,78,81,83,90,92]},{\"tag\":\"block\",\"leaf\":6,\"vertices\":[0,3,4,10,39,62,64,70,74,81,83,90,91,92]},{\"tag\":\"block\",\"leaf\":7,\"vertices\":[0,3,4,10,49,62,64,71,74,81,83,86,90,92]},{\"tag\":\"block\",\"leaf\":8,\"vertices\":[0,3,4,14,39,62,64,70,74,79,83,90,91,92]},{\"tag\":\"block\",\"leaf\":9,\"vertices\":[0,3,4,14,49,62,64,71,74,79,83,86,90,92]},{\"tag\":\"block\",\"leaf\":10,\"vertices\":[0,3,7,14,39,63,64,70,74,79,83,90,91,92]},{\"tag\":\"block\",\"leaf\":11,\"vertices\":[0,3,7,14,49,63,64,71,74,79,83,86,90,92]},{\"tag\":\"block\",\"leaf\":12,\"vertices\":[0,3,5,15,35,62,64,70,74,79,83,90,91,92]},{\"tag\":\"block\",\"leaf\":13,\"vertices\":[0,3,9,19,35,62,64,71,74,79,83,86,90,92]},{\"tag\":\"block\",\"leaf\":14,\"vertices\":[3,4,5,15,21,62,64,70,74,81,83,90,91,92]},{\"tag\":\"block\",\"leaf\":15,\"vertices\":[3,4,9,19,21,62,64,71,74,81,83,86,90,92]},{\"tag\":\"block\",\"leaf\":16,\"vertices\":[0,13,14,17,39,63,65,72,73,74,79,82,88,92]},{\"tag\":\"block\",\"leaf\":17,\"vertices\":[0,13,14,17,49,63,65,68,72,74,79,82,89,92]},{\"tag\":\"block\",\"leaf\":18,\"vertices\":[5,6,8,9,52,56,57,62,67,78,81,83,90,91]},{\"tag\":\"block\",\"leaf\":19,\"vertices\":[8,9,18,19,52,56,57,62,67,71,78,81,83,90]},{\"tag\":\"block\",\"leaf\":20,\"vertices\":[5,6,18,19,52,56,57,62,67,73,78,81,83,90]},{\"tag\":\"block\",\"leaf\":21,\"vertices\":[0,9,10,19,52,56,62,64,67,71,81,83,86,90]},{\"tag\":\"block\",\"leaf\":22,\"vertices\":[0,9,14,19,52,56,62,64,67,71,79,83,86,90]},{\"tag\":\"block\",\"leaf\":23,\"vertices\":[0,9,17,19,52,56,63,65,68,72,79,82,85,89]},{\"tag\":\"block\",\"leaf\":24,\"vertices\":[0,2,6,9,52,56,62,67,68,78,81,83,90,91]},{\"tag\":\"block\",\"leaf\":25,\"vertices\":[0,9,12,16,52,56,63,65,68,72,78,80,85,91]},{\"tag\":\"block\",\"leaf\":26,\"vertices\":[2,6,7,9,52,56,61,67,68,78,81,83,90,91]},{\"tag\":\"block\",\"leaf\":27,\"vertices\":[2,9,16,17,52,56,61,67,68,72,78,81,83,91]},{\"tag\":\"block\",\"leaf\":28,\"vertices\":[2,9,14,16,52,56,61,67,68,72,78,80,83,91]},{\"tag\":\"block\",\"leaf\":29,\"vertices\":[2,6,14,19,52,56,60,62,67,73,79,83,86,90]},{\"tag\":\"block\",\"leaf\":30,\"vertices\":[0,2,5,8,52,56,62,67,70,78,81,83,90,91]},{\"tag\":\"block\",\"leaf\":31,\"vertices\":[0,5,10,15,52,56,62,64,67,70,81,83,90,91]},{\"tag\":\"block\",\"leaf\":32,\"vertices\":[0,5,14,15,52,56,62,64,67,70,79,83,90,91]},{\"tag\":\"block\",\"leaf\":33,\"vertices\":[0,5,15,17,52,56,63,65,72,73,79,82,85,88]},{\"tag\":\"block\",\"leaf\":34,\"vertices\":[2,5,7,8,52,56,61,67,70,78,81,83,90,91]},{\"tag\":\"block\",\"leaf\":35,\"vertices\":[0,5,12,18,52,56,63,65,72,73,78,80,85,88]},{\"tag\":\"block\",\"leaf\":36,\"vertices\":[2,8,14,15,52,56,60,62,67,70,79,83,90,91]},{\"tag\":\"block\",\"leaf\":37,\"vertices\":[2,5,17,18,52,56,61,67,72,73,78,81,83,88]},{\"tag\":\"block\",\"leaf\":38,\"vertices\":[2,5,14,18,52,56,61,67,72,73,78,80,83,88]},{\"tag\":\"block\",\"leaf\":39,\"vertices\":[5,12,13,18,35,61,65,72,73,74,78,80,88,92]},{\"tag\":\"block\",\"leaf\":40,\"vertices\":[9,12,13,16,35,61,65,68,72,74,78,80,91,92]},{\"tag\":\"block\",\"leaf\":41,\"vertices\":[6,12,13,19,35,60,62,65,73,74,79,86,90,92]},{\"tag\":\"block\",\"leaf\":42,\"vertices\":[8,12,13,15,35,60,62,65,70,74,79,90,91,92]},{\"tag\":\"block\",\"leaf\":43,\"vertices\":[9,13,14,19,46,60,63,65,72,74,75,80,89,92]},{\"tag\":\"block\",\"leaf\":44,\"vertices\":[8,13,14,18,49,60,63,65,72,74,75,80,89,92]},{\"tag\":\"block\",\"leaf\":45,\"vertices\":[0,10,13,14,39,63,65,72,73,74,80,82,88,92]},{\"tag\":\"block\",\"leaf\":46,\"vertices\":[0,10,13,14,49,63,65,68,72,74,80,82,89,92]},{\"tag\":\"block\",\"leaf\":47,\"vertices\":[4,10,13,14,39,61,65,72,73,74,80,82,88,92]},{\"tag\":\"block\",\"leaf\":48,\"vertices\":[4,10,13,14,49,61,65,68,72,74,80,82,89,92]},{\"tag\":\"block\",\"leaf\":49,\"vertices\":[4,10,13,17,39,61,65,72,73,74,81,82,88,92]},{\"tag\":\"block\",\"leaf\":50,\"vertices\":[4,10,13,17,49,61,65,68,72,74,81,82,89,92]},{\"tag\":\"block\",\"leaf\":51,\"vertices\":[5,10,13,15,35,61,65,72,73,74,80,82,88,92]},{\"tag\":\"block\",\"leaf\":52,\"vertices\":[9,10,13,19,35,61,65,68,72,74,80,82,89,92]},{\"tag\":\"block\",\"leaf\":53,\"vertices\":[5,13,14,15,21,63,65,72,73,74,80,82,88,92]},{\"tag\":\"block\",\"leaf\":54,\"vertices\":[9,13,14,19,21,63,65,68,72,74,80,82,89,92]},{\"tag\":\"block\",\"leaf\":55,\"vertices\":[3,4,7,10,39,61,64,70,74,81,83,90,91,92]},{\"tag\":\"block\",\"leaf\":56,\"vertices\":[3,4,7,10,49,61,64,71,74,81,83,86,90,92]},{\"tag\":\"block\",\"leaf\":57,\"vertices\":[15,16,18,19,52,56,60,63,65,72,73,75,80,85]},{\"tag\":\"block\",\"leaf\":58,\"vertices\":[8,9,18,19,52,56,60,63,65,72,75,80,85,89]},{\"tag\":\"block\",\"leaf\":59,\"vertices\":[8,9,15,16,52,56,60,63,65,72,75,80,85,91]},{\"tag\":\"block\",\"leaf\":60,\"vertices\":[0,9,10,19,52,56,63,65,68,72,80,82,85,89]},{\"tag\":\"block\",\"leaf\":61,\"vertices\":[4,9,10,19,52,56,61,65,68,72,80,82,85,89]},{\"tag\":\"block\",\"leaf\":62,\"vertices\":[7,9,10,19,52,56,61,64,67,71,81,83,86,90]},{\"tag\":\"block\",\"leaf\":63,\"vertices\":[10,12,16,19,52,56,60,63,65,72,73,80,85,86]},{\"tag\":\"block\",\"leaf\":64,\"vertices\":[2,6,10,19,52,56,60,62,67,73,81,83,86,90]},{\"tag\":\"block\",\"leaf\":65,\"vertices\":[12,16,17,19,52,56,60,63,65,72,73,79,85,86]},{\"tag\":\"block\",\"leaf\":66,\"vertices\":[6,7,12,19,52,56,60,63,65,73,79,85,86,90]},{\"tag\":\"block\",\"leaf\":67,\"vertices\":[4,6,12,19,52,56,60,62,65,73,79,85,86,90]},{\"tag\":\"block\",\"leaf\":68,\"vertices\":[4,9,12,16,52,56,61,65,68,72,78,80,85,91]},{\"tag\":\"block\",\"leaf\":69,\"vertices\":[10,12,15,18,52,56,60,63,65,72,73,80,85,88]},{\"tag\":\"block\",\"leaf\":70,\"vertices\":[0,5,10,15,52,56,63,65,72,73,80,82,85,88]},{\"tag\":\"block\",\"leaf\":71,\"vertices\":[4,5,10,15,52,56,61,65,72,73,80,82,85,88]},{\"tag\":\"block\",\"leaf\":72,\"vertices\":[5,7,10,15,52,56,61,64,67,70,81,83,90,91]},{\"tag\":\"block\",\"leaf\":73,\"vertices\":[12,15,17,18,52,56,60,63,65,72,73,79,85,88]},{\"tag\":\"block\",\"leaf\":74,\"vertices\":[2,8,10,15,52,56,60,62,67,70,81,83,90,91]},{\"tag\":\"block\",\"leaf\":75,\"vertices\":[4,5,12,18,52,56,61,65,72,73,78,80,85,88]},{\"tag\":\"block\",\"leaf\":76,\"vertices\":[7,8,12,15,52,56,60,63,65,70,79,85,90,91]},{\"tag\":\"block\",\"leaf\":77,\"vertices\":[4,8,12,15,52,56,60,62,65,70,79,85,90,91]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[3,13,30,48,50,52,53,65,67,74,83,85,92]}]}"
  "685 162 0 573 570 0\n686 169 0 573 572 0\n687 159 0 685 553 0\n688 167 0 686 568 0\n689 165 0 688 564 0\n690 -176 23 24 26 33 34 39 41 44 53 54 0 435 588 0\n691 -182 0 605 604 0\n692 4 14 31 49 53 54 66 68 75 84 86 93 0 435 684 0\n693 176 178 0 435 592 579 399 593 574 577 429 576 589 590 432 316 401 400 398 315 314 692 0\n694 -27 178 0 693 593 574 592 577 429 4 5 6 9 10 20 32 39 83 690 0\n695 161 84 86 181 0 685 573 435 598 592 579 403 399 593 574 577 429 576 575 597 596 582 583 364 556 554 571 549 569 538 565 162 318 561 432 398 78 88 94 547 0\n696 -66 86 181 0 435 573 598 592 579 403 399 593 574 577 429 576 575 597 596 582 583 364 164 315 538 78 88 94 549 547 555 561 571 565 569 0\n697 84 86 181 0 696 598 694 695 542 552 0\n698 124 86 181 0 573 435 598 592 579 403 399 593 574 577 429 697 400 88 576 575 597 596 582 583 364 78 94 547 561 565 569 571 555 549 538 163 550 107 104 91 89 87 81 222 595 584 491 493 486 479 480 482 483 451 449 457 455 346 360 293 335 540 361 341 0\n699 -145 147 -89 -3 -19 -62 -79 -73 -74 -6 -68 -53 -84 0 245 470 518 198 463 244 465 514 208 436 93 92 90 81 528 523 512 519 501 467 459 643 386 0\n700 71 -6 7 10 86 181 0 689 688 573 435 537 131 598 593 576 575 597 596 582 583 364 697 222 360 592 579 574 577 429 400 107 346 698 403 399 88 78 94 547 561 565 569 571 555 549 538 163 550 562 559 436 104 92 91 89 87 86 85 84 81 79 229 228 225 696 694 581 366 359 365 341 328 545 540 242 410 136 285 469 546 446 517 475 476 499 535 699 524 521 468 353 385 644 0\n701 -15 -92 -16 -1 81 -91 -65 -63 -71 -6 -68 -152 -53 -84 0 436 212 638 541 0\n702 101 122 86 181 0 686 573 435 598 592 579 593 574 577 429 697 400 107 576 575 597 596 582 583 364 486 482 457 346 483 455 488 453 698 490 403 399 88 78 94 547 561 565 569 571 555 549 538 556 551 566 558 557 436 91 89 82 80 79 228 222 578 417 595 587 442 581 585 438 580 586 451 478 448 131 700 172 186 193 240 342 361 543 354 282 202 261 336 544 701 326 371 637 0\n703 -6 -20 81 -91 65 92 -74 -63 -7 69 -68 -152 -156 -157 -53 -84 0 260 168 436 104 94 229 228 131 545 208 242 410 541 546 626 0\n704 -82 -87 -3 79 -61 -20 -91 -74 -63 -7 -68 -53 -84 180 0 436 80 79 78 228 596 580 595 586 585 371 670 0\n705 122 86 181 0 689 688 686 573 435 598 592 579 403 399 593 574 577 429 697 400 88 576 575 597 596 582 583 364 78 94 547 561 565 569 571 555 549 538 556 551 566 557 562 559 436 107 104 92 91 90 89 87 86 85 80 79 228 225 222 696 694 578 417 595 587 442 581 486 488 482 453 457 346 360 702 450 168 181 339 344 366 359 543 354 415 260 703 329 292 338 284 546 704 541 326 635 0\n706 10 71 86 181 0 689 688 686 573 435 705 598 592 579 403 399 593 574 577 429 697 400 88 576 575 597 596 582 583 364 78 94 547 561 565 569 571 555 549 538 163 550 566 557 562 559 91 86 81 229 228 222 578 417 581 356 456 360 359 454 481 485 452 139 182 540 543 136 137 260 546 545 242 0\n707 -87 63 -10 86 181 0 688 686 573 435 598 592 579 403 399 593 574 577 429 697 400 88 576 575 597 596 582 583 364 78 94 547 561 565 569 571 555 549 538 163 550 81 540 206 137 188 556 551 566 558 557 562 436 91 90 89 87 80 229 222 578 417 242 256 273 423 381 545 544 187 343 543 668 259 541 0\n708 73 87 -62 -10 71 -68 -152 -155 -154 -156 -157 -84 66 178 0 435 206 137 136 188 592 579 593 574 577 429 400 436 95 93 92 91 79 229 228 226 694 578 417 543 304 259 260 261 541 546 167 179 310 331 545 544 632 0\n709 -82 -69 -92 -3 -79 -73 -62 -10 -68 -53 -84 45 0 258 107 91 416 436 92 90 388 633 0\n710 -79 -73 87 -62 -10 71 -68 -152 -155 -157 -84 66 178 0 435 258 187 206 136 188 592 579 593 574 577 429 400 436 107 91 84 228 225 694 578 417 202 255 285 544 275 416 546 709 541 326 634 0\n711 63 71 86 181 0 689 688 686 435 573 706 188 598 592 579 403 399 593 574 577 429 697 400 88 576 575 597 596 582 583 364 78 94 547 561 565 569 571 555 549 538 163 556 551 550 566 558 557 562 559 81 229 228 696 540 136 137 707 708 187 710 545 167 546 257 275 544 0\n712 -65 87 89 71 -157 76 0 148 167 546 0\n713 -61 87 89 71 -157 76 0 134 166 546 0\n714 58 87 71 86 181 0 686 689 688 435 573 711 211 598 592 579 593 574 577 429 697 400 88 576 575 597 596 582 583 364 78 94 547 561 565 569 571 556 551 229 562 228 559 566 557 91 578 417 185 543 260 712 713 545 208 541 261 706 188 403 399 555 549 538 558 436 92 82 79 223 222 694 581 580 282 546 308 179 331 544 630 0\n715 -92 -58 -82 -79 -91 -63 -10 -68 -53 -84 0 226 95 94 188 309 185 436 107 104 91 90 89 88 269 345 292 624 0\n716 87 71 86 181 0 689 688 573 435 686 598 592 579 593 574 577 429 697 400 88 576 575 597 596 582 583 364 78 94 547 561 565 566 557 91 578 417 711 185 543 261 260 211 706 188 403 399 569 571 555 549 538 556 551 558 562 559 436 104 95 229 228 226 595 587 584 712 713 545 208 541 714 309 715 544 391 415 625 0\n717 -82 -65 -72 -20 -87 -91 -63 -10 -68 -53 -84 180 0 140 239 90 595 584 78 294 242 436 80 79 228 596 580 586 585 371 627 0\n718 71 86 181 0 688 686 573 435 598 592 579 403 399 593 574 577 429 697 400 88 576 575 597 596 582 583 364 78 94 547 561 565 569 571 555 549 538 556 551 566 558 557 562 436 91 90 229 222 578 417 595 584 706 188 711 140 185 211 543 261 716 239 242 273 423 544 178 294 545 717 541 326 628 0\n719 -65 -92 -91 -71 -122 -68 -152 -151 -53 -84 180 0 259 169 456 240 180 163 436 104 88 86 81 79 228 596 581 595 585 438 143 202 335 454 409 481 485 452 139 540 206 297 541 678 0\n720 -82 -63 -61 79 -3 -9 -92 -91 -71 -68 -53 -84 180 0 240 86 595 585 88 79 409 436 80 78 228 596 580 586 371 680 0\n721 79 -3 65 -92 -91 -71 -68 -152 -151 -156 -53 -84 180 0 435 222 94 361 259 240 163 436 88 86 81 79 229 595 585 409 545 137 540 720 541 326 642 0\n722 -63 -82 -6 -79 -3 -9 -92 -91 -71 -68 -53 -84 174 0 201 172 436 82 79 78 581 580 282 636 0\n723 86 181 0 688 686 573 435 598 694 592 578 579 417 403 399 593 574 577 429 576 575 597 596 582 583 364 595 587 442 581 580 697 222 223 400 78 80 81 88 89 91 94 436 547 561 565 562 569 566 571 557 558 555 556 549 550 551 538 163 705 718 172 173 180 186 193 543 259 261 544 719 361 308 721 208 338 541 722 342 540 640 0\n724 63 -71 181 0 435 573 688 686 180 193 723 231 428 406 119 598 593 576 575 597 596 582 583 364 108 124 547 561 565 566 558 557 122 592 578 579 417 186 543 261 544 272 562 235 694 569 571 556 552 542 159 234 551 259 541 208 545 595 584 197 232 432 393 240 587 120 380 206 112 361 555 550 111 110 401 342 540 682 0\n725 -71 181 0 688 686 573 435 723 235 598 694 231 428 406 119 593 576 575 597 596 582 583 364 108 124 547 561 565 569 571 556 552 542 159 551 566 558 557 562 122 120 115 112 232 432 401 234 233 592 578 579 417 403 574 595 587 584 180 186 193 197 240 361 543 259 261 541 544 208 380 272 393 545 724 302 683 0\n726 -92 -91 181 0 689 688 573 723 234 231 428 406 119 598 593 576 575 597 596 582 583 364 108 124 547 561 565 569 571 556 551 259 541 208 207 260 725 235 694 552 542 159 562 559 272 273 545 713 0\n727 -61 -63 -91 181 0 435 689 686 573 598 592 579 403 723 231 428 406 115 593 574 233 302 126 576 575 597 596 582 583 364 726 415 234 119 108 124 547 561 565 569 571 556 551 259 541 207 261 260 258 725 235 694 552 542 566 558 559 123 122 117 113 112 232 432 401 580 595 586 585 178 220 330 713 544 390 673 0\n728 -69 92 90 -155 0 179 192 544 0\n729 -91 181 0 435 689 688 686 573 725 723 235 598 694 231 428 406 119 593 576 575 597 596 582 583 364 108 124 547 561 565 569 571 556 552 542 159 156 551 555 550 566 558 562 559 126 125 123 122 120 118 117 111 110 232 432 401 234 592 578 579 417 258 259 260 261 541 206 207 208 726 415 728 546 243 392 545 178 330 727 544 339 540 672 0\n730 -80 -74 -87 181 0 435 688 573 686 723 231 428 406 119 598 593 576 575 597 596 582 583 364 108 124 547 561 565 566 557 122 592 578 579 417 729 543 185 569 571 555 550 111 242 562 235 694 556 552 542 159 243 545 137 540 123 109 407 112 423 232 432 125 392 401 387 671 0\n731 -87 92 181 0 688 573 686 435 723 231 428 406 119 598 593 576 575 597 596 582 583 364 108 124 547 561 565 566 557 122 592 578 579 417 729 543 187 185 235 694 569 571 556 552 542 159 551 555 550 558 562 125 123 112 111 109 232 432 401 234 241 242 243 256 392 423 407 545 544 137 540 730 296 541 669 0\n732 -13 80 -61 -74 87 181 0 435 689 686 573 723 234 231 428 406 119 598 593 576 575 597 596 582 583 364 108 124 547 561 565 569 571 556 551 541 581 595 585 438 220 362 566 557 122 592 578 579 417 729 543 185 555 550 111 137 540 587 442 253 337 201 725 235 694 552 542 559 115 114 232 432 401 194 372 713 675 0\n733 80 -61 -74 92 181 0 435 573 686 597 596 581 595 585 438 731 220 362 723 231 428 406 119 598 593 576 575 582 583 364 108 124 547 561 565 566 557 122 592 578 579 417 729 543 185 569 571 555 550 111 137 540 587 442 253 337 235 694 556 552 542 551 232 432 401 234 586 541 732 311 251 350 424 663 0\n734 -61 -74 92 181 0 435 689 573 686 253 731 723 231 428 406 119 598 593 576 575 597 596 582 583 364 108 124 547 561 565 566 557 122 592 578 579 417 729 543 185 725 235 694 569 571 556 552 542 555 550 559 123 114 111 232 432 401 595 587 442 581 585 438 137 220 337 540 362 733 207 387 374 713 679 0\n735 -80 61 -74 87 181 0 435 689 688 573 686 723 231 428 406 119 598 593 576 575 597 596 582 583 364 108 124 547 561 565 566 557 122 592 578 579 417 729 543 581 109 117 192 332 253 185 725 235 694 569 571 556 552 542 159 156 555 550 562 559 123 120 111 232 432 401 595 585 438 587 584 206 207 208 387 380 299 540 546 545 639 0\n736 -16 -89 76 -64 80 61 -74 181 0 435 688 686 573 723 235 598 694 231 428 406 119 593 576 575 597 596 582 583 364 108 124 547 561 565 569 571 556 552 542 156 581 109 110 580 283 234 551 541 566 557 122 592 578 579 417 729 543 117 192 332 159 562 121 120 232 432 401 595 587 584 198 377 545 676 0\n737 76 -64 61 -74 87 181 0 435 689 686 573 723 235 598 694 231 428 406 119 593 576 575 597 596 582 583 364 108 124 547 561 565 569 571 556 552 542 156 581 109 110 580 283 234 551 735 541 566 557 122 592 578 579 417 729 543 117 192 332 253 725 559 126 123 113 112 232 432 401 595 585 438 586 546 736 411 408 362 390 641 0\n738 -76 61 181 0 688 573 723 235 598 694 231 428 406 119 593 576 575 597 596 582 583 364 108 124 547 561 565 569 571 556 552 542 159 562 203 221 545 0\n739 83 61 -74 87 181 0 435 688 689 573 686 723 231 428 406 119 598 593 576 575 597 596 582 583 364 108 124 547 561 565 566 557 122 592 578 579 417 729 543 185 569 571 555 550 111 738 737 540 233 322 192 725 559 235 694 556 552 542 156 546 234 551 735 541 581 109 117 332 159 562 113 112 232 432 401 595 585 438 580 586 545 362 390 681 0\n740 -74 92 181 0 435 689 573 686 731 723 231 428 406 119 598 593 576 575 597 596 582 583 364 108 124 547 561 565 566 557 122 592 578 579 417 729 543 185 725 235 694 569 571 556 552 542 156 551 555 550 559 126 117 115 111 109 232 432 401 234 233 581 192 253 734 332 735 541 738 546 737 322 540 739 375 411 677 0\n741 -62 -81 61 92 181 0 435 688 573 689 686 723 231 428 406 119 598 593 576 575 597 596 582 583 364 108 124 547 561 565 566 557 122 592 578 579 417 729 543 187 558 740 544 255 595 585 738 109 580 370 257 731 725 559 235 694 569 571 556 552 542 156 546 562 159 545 127 414 126 347 116 232 432 401 233 403 574 301 667 0\n742 -81 61 92 181 0 435 688 573 689 686 723 231 428 406 119 598 593 576 575 597 596 582 583 364 108 124 547 561 565 566 557 122 592 578 579 417 729 543 187 558 740 544 257 731 725 559 235 694 569 571 556 552 542 156 738 546 255 562 159 545 127 414 126 347 185 555 550 115 114 111 109 232 432 401 580 595 585 370 741 540 287 666 0\n743 61 92 181 0 435 689 688 573 686 723 231 428 406 127 598 593 576 575 597 596 582 583 364 119 108 124 547 561 565 566 557 122 592 578 579 417 729 543 187 558 740 544 414 257 255 126 347 731 185 725 235 694 569 571 556 552 542 159 156 551 555 550 562 559 111 232 432 401 234 581 595 585 438 738 545 546 742 418 541 206 299 540 629 0\n744 92 181 0 689 573 686 435 723 231 428 406 119 598 593 576 575 597 596 582 583 364 108 124 547 561 565 566 557 122 592 578 579 417 729 543 187 185 725 235 694 569 571 556 552 542 551 555 550 558 559 127 126 117 112 111 232 432 401 234 595 585 731 740 347 544 257 414 743 137 220 334 713 540 420 207 664 541 0\n745 -61 181 0 435 689 573 686 729 723 231 428 406 127 122 744 416 725 366 276 275 273 270 119 598 593 576 575 597 596 582 583 364 108 124 547 561 565 566 557 592 578 579 417 543 185 235 694 569 571 556 552 542 551 555 550 559 126 111 232 432 401 234 595 587 442 137 337 334 713 540 665 207 541 0\n746 62 181 0 435 686 689 688 573 723 234 231 428 406 119 598 593 576 575 597 596 582 583 364 108 124 547 561 565 569 571 556 551 744 272 562 235 694 552 542 159 745 545 208 541 595 584 232 432 738 393 275 273 725 559 156 546 729 127 122 416 366 566 557 592 578 579 417 543 185 555 550 111 401 298 540 631 0\n747 181 0 435 689 688 686 573 597 598 595 596 592 593 584 582 583 578 579 574 575 576 364 403 417 694 723 231 232 233 234 235 428 432 406 401 108 116 119 122 124 127 547 561 559 565 562 569 566 571 557 556 551 552 542 156 159 725 729 543 744 272 273 275 366 416 745 738 545 546 393 208 541 746 301 674 0\n748 -185 0 747 605 603 0\n749 -86 0 435 748 231 232 428 432 406 401 591 590 601 600 602 0\n750 -53 0 748 436 590 591 600 601 602 0\n751 -57 0 750 437 0\n752 -69 -62 -81 -73 -66 -92 0 749 537 688 137 135 210 427 216 281 276 275 350 466 515 525 266 267 270 347 457 482 486 491 496 534 533 511 317 461 160 441 158 439 159 154 152 151 150 149 272 271 265 262 165 196 547 389 561 460 562 508 545 504 462 395 321 403 646 0\n753 -62 -81 -73 -66 -92 0 749 537 317 461 503 505 509 281 276 275 350 466 515 525 527 536 498 266 267 270 347 457 151 183 426 271 157 438 164 160 159 152 269 137 288 752 363 455 484 487 492 495 500 480 476 449 474 333 473 31 447 301 0\n754 -125 62 -81 -144 -108 0 537 749 503 505 509 527 536 497 500 535 477 530 471 510 445 506 307 504 325 462 0\n755 -81 -73 -66 -92 0 749 435 537 281 276 275 350 466 515 525 266 267 270 347 457 482 486 491 496 534 533 511 185 317 461 503 160 441 158 439 159 157 154 152 151 150 149 272 271 265 263 262 210 216 427 753 754 492 487 484 455 357 196 389 460 507 508 510 504 530 462 535 395 499 300 477 445 471 0\n756 -73 -66 -92 0 749 537 317 461 503 505 509 160 441 158 439 271 157 438 159 152 151 150 149 281 276 275 272 270 267 266 262 347 350 457 466 482 515 486 491 496 534 755 353 468 520 526 531 528 510 535 507 497 460 492 389 487 196 484 363 455 0\n757 -76 121 -66 -92 0 271 157 438 159 196 197 363 366 455 457 484 0\n758 -139 33 82 1 2 22 79 -71 -9 76 81 -66 -92 0 537 749 750 435 317 461 503 160 441 272 158 439 271 262 152 151 150 149 389 460 507 510 455 483 486 491 496 534 531 171 156 155 154 268 525 526 533 520 511 513 468 508 501 502 504 459 458 462 368 367 369 306 325 404 426 425 395 303 290 315 398 372 287 300 412 419 648 0\n759 69 128 125 81 -66 -92 0 435 492 487 757 271 157 438 164 159 156 152 281 276 273 269 268 266 263 262 363 455 483 484 486 489 457 491 494 453 356 499 480 476 477 449 474 471 472 338 289 473 445 444 447 291 327 430 758 515 516 466 464 349 337 355 140 302 287 14 0\n760 128 125 81 -66 -92 0 435 685 573 749 756 271 157 438 164 158 156 153 281 269 268 266 262 759 166 173 360 457 482 486 491 494 499 479 476 477 451 474 472 340 351 473 444 447 299 327 541 551 556 554 571 549 567 538 557 37 543 0\n761 40 125 81 -66 -92 0 537 749 573 276 274 273 317 461 503 160 441 272 158 439 271 262 152 151 150 149 492 487 757 389 460 507 510 760 535 530 525 516 464 378 532 513 501 459 394 164 153 266 265 264 380 547 383 561 538 565 549 569 555 571 0\n762 125 81 -66 -92 0 537 749 317 461 503 160 441 158 439 152 151 150 149 276 275 274 272 271 262 492 487 757 389 460 507 510 760 535 532 530 511 513 522 525 508 502 520 515 504 458 468 466 462 413 426 761 31 379 384 0\n763 -80 -168 65 -92 0 565 561 563 272 266 265 205 208 547 545 133 0\n764 160 81 -66 -92 0 749 685 573 537 762 317 461 503 505 509 227 164 159 154 150 281 276 273 272 554 555 551 571 569 563 763 541 213 327 447 473 474 476 500 536 529 527 510 525 507 516 460 464 373 337 545 0\n765 81 -66 -92 0 749 689 688 573 164 159 153 276 275 274 273 272 270 267 266 265 264 764 549 550 538 11 12 15 17 31 142 214 547 561 559 565 562 569 571 556 551 541 206 207 208 380 540 545 464 138 130 334 713 516 758 0\n766 -36 -66 -92 0 686 765 259 209 756 266 265 11 31 37 547 543 561 557 565 566 0\n767 -66 -92 0 749 573 266 265 153 164 756 765 209 259 766 538 549 555 571 567 569 557 565 543 561 36 38 547 0\n768 40 150 68 -168 -92 0 687 685 573 750 435 549 555 571 567 557 554 552 551 548 565 561 560 563 767 276 275 274 273 272 269 267 266 265 547 2 3 36 42 96 132 135 195 199 205 378 542 545 400 319 712 335 443 186 543 259 541 215 327 540 620 0\n769 62 -5 -82 -11 -91 -71 -4 -65 -84 -40 -151 -92 0 435 750 215 97 400 443 29 28 22 21 286 540 612 0\n770 80 -91 -71 -65 -84 -40 -152 -151 68 -92 0 435 750 259 186 97 400 443 319 200 46 44 41 28 27 21 376 541 327 769 304 661 0\n771 -5 -15 -80 -91 -71 -4 -65 -84 -40 -151 -92 0 435 750 277 133 148 299 206 97 400 443 22 141 614 540 0\n772 150 68 -168 -92 0 687 685 573 750 435 749 565 560 563 767 275 273 272 539 548 549 554 555 551 552 571 567 557 768 23 24 25 29 30 35 38 41 44 97 133 200 277 542 545 228 230 400 319 148 712 443 186 543 770 384 299 771 312 305 616 0\n773 -40 -150 68 0 749 26 31 538 0\n774 68 -168 -92 0 749 565 561 266 265 772 773 547 7 11 538 0\n775 -68 0 751 161 324 428 0\n776 -31 -92 0 775 573 774 569 571 556 552 767 8 224 542 0\n777 -65 -91 -92 0 689 749 775 573 774 569 571 555 550 549 776 538 142 12 556 551 214 259 541 206 540 273 274 264 773 17 276 380 767 552 13 542 228 265 266 11 547 559 403 321 313 16 15 275 269 267 712 335 286 618 0\n778 -91 -92 0 689 749 573 775 688 265 266 774 569 571 555 549 773 776 538 11 547 561 562 767 556 552 13 542 228 559 403 321 313 214 142 17 16 15 12 551 550 276 275 274 273 272 270 267 264 259 541 206 208 380 540 777 545 284 334 713 606 0\n779 -92 0 686 573 775 749 689 688 265 266 267 270 272 273 275 767 774 569 566 571 557 555 556 549 550 551 552 773 776 538 11 12 13 14 16 37 43 106 142 214 313 321 403 547 542 561 559 228 562 778 543 416 185 186 347 540 712 713 136 206 285 545 546 541 608 0\n780 65 -73 -84 -36 0 689 688 686 691 775 573 779 52 72 31 11 547 561 565 569 571 556 551 214 555 550 142 12 185 540 206 541 137 136 187 186 319 229 228 227 321 576 403 579 594 599 596 583 566 558 562 559 101 33 17 16 14 13 285 545 242 255 410 728 544 293 546 609 0\n781 -73 -84 -36 0 689 686 779 228 52 72 31 11 547 561 565 566 558 559 186 187 780 191 544 256 257 712 0\n782 -65 -84 -36 0 689 775 686 573 779 52 72 31 11 547 561 565 569 571 555 550 142 12 556 551 214 37 566 557 43 781 543 259 541 206 540 558 261 728 101 415 260 319 228 559 403 321 106 16 15 148 191 286 544 180 346 546 619 0\n783 -84 -36 0 689 688 686 573 775 779 52 72 31 11 547 561 565 569 571 556 551 555 550 566 558 557 562 559 403 321 214 142 106 101 43 37 16 15 13 12 227 228 229 319 781 543 259 260 261 415 541 728 206 208 540 782 545 134 178 284 544 193 348 546 607 0\n784 -87 -91 -36 0 688 686 573 779 52 72 31 11 547 561 565 569 571 555 550 142 12 556 551 214 259 541 206 540 208 101 415 261 258 552 13 783 542 159 397 566 558 562 403 321 58 56 40 37 19 240 243 392 545 178 330 544 647 0\n785 -91 -36 0 689 686 573 779 52 72 31 11 547 561 565 569 571 556 552 13 783 542 156 551 566 558 559 214 259 260 261 541 728 207 784 546 180 193 544 0\n786 83 76 90 87 -36 0 688 691 689 573 779 686 52 72 31 11 547 561 565 566 558 728 569 571 556 552 13 783 542 156 559 37 557 43 785 543 186 546 321 576 403 579 594 599 596 583 187 33 17 555 550 142 12 185 540 293 544 551 214 206 541 137 159 397 595 585 581 438 562 311 545 362 645 0\n787 76 90 87 -36 0 689 779 573 686 691 31 321 576 403 579 594 599 596 583 37 52 72 11 547 561 565 566 557 43 785 543 187 33 17 569 571 555 550 142 12 185 540 558 728 293 544 556 551 214 206 541 186 552 13 783 542 156 397 559 101 16 15 546 786 411 375 657 0\n788 -76 -36 0 688 686 573 52 72 31 11 547 561 565 569 571 555 550 142 12 37 566 557 43 785 543 185 540 137 556 552 13 783 542 159 562 203 221 545 0\n789 87 -36 0 689 688 686 573 788 52 72 31 11 547 561 565 569 571 556 551 214 555 550 142 12 37 566 557 43 785 543 185 540 206 541 137 186 552 13 783 542 159 156 397 562 559 403 321 106 101 34 17 787 253 255 257 414 382 347 545 546 658 0\n790 -36 0 688 686 573 11 12 13 31 37 43 52 72 142 547 561 565 562 569 566 571 557 555 556 550 552 783 542 159 785 543 185 540 137 789 242 243 545 0\n791 156 -87 0 688 573 775 790 749 238 237 562 563 561 569 571 555 549 538 7 67 547 0\n792 -163 0 775 790 749 555 556 549 552 538 8 153 224 542 0\n793 170 0 792 573 571 0\n794 164 0 793 567 0\n795 168 0 793 569 0\n796 154 0 794 557 0\n797 155 0 794 558 0\n798 166 0 795 565 0\n799 158 0 798 561 0\n800 -61 -87 0 799 779 797 256 238 237 132 178 547 544 190 0\n801 80 -1 62 -50 -87 0 687 796 797 779 749 790 685 435 750 775 99 242 791 243 800 545 159 144 67 538 549 554 552 542 400 443 319 551 256 191 544 175 187 74 543 259 548 63 279 241 295 541 215 327 540 613 0\n802 -63 -80 -1 -50 -87 0 796 797 779 435 750 749 685 790 775 242 791 243 800 545 159 144 67 538 549 554 552 542 230 66 71 384 99 400 443 319 256 191 544 175 187 74 543 69 302 615 0\n803 62 22 -87 0 796 797 779 687 775 685 435 799 750 790 749 238 237 547 99 242 791 243 800 545 159 144 67 538 549 554 552 542 400 443 319 230 548 256 191 544 175 187 74 543 71 69 66 63 176 434 147 431 286 801 384 802 352 540 617 0\n804 22 -87 0 797 779 799 749 796 685 750 435 790 775 256 242 791 243 800 545 191 544 187 176 175 159 144 279 241 238 237 547 66 67 71 74 75 99 538 543 549 259 554 551 552 542 230 400 319 440 443 803 206 304 301 297 541 662 0\n805 -87 0 779 797 790 749 796 435 687 685 775 751 236 240 242 243 256 791 800 545 144 145 159 191 544 175 187 804 2 7 42 45 61 96 135 205 538 543 423 359 548 549 259 554 551 552 541 542 215 327 405 319 540 320 621 0\n806 156 0 795 563 0\n807 157 0 798 560 0\n808 -72 -22 -65 0 807 805 796 195 42 36 180 187 712 543 260 0\n809 -22 -65 0 779 797 807 805 796 191 167 148 36 42 195 808 544 257 261 546 543 186 0\n810 -90 -65 0 799 775 790 749 807 805 685 809 159 146 144 252 257 547 67 170 538 712 549 228 554 542 552 0\n811 -65 0 779 797 799 775 790 749 807 805 685 144 146 159 191 809 810 544 174 180 547 67 247 538 712 549 228 554 542 552 0\n812 -76 61 0 811 806 203 221 545 0\n813 -83 -72 22 0 799 775 790 749 807 805 685 178 812 180 179 174 217 218 229 547 67 247 538 546 549 156 554 542 552 0\n814 -50 -58 83 -72 0 806 811 805 790 749 796 687 685 775 751 156 136 129 178 545 208 204 187 179 177 175 63 67 74 75 99 358 422 538 543 548 549 259 554 551 552 541 542 215 327 405 319 540 320 611 0\n815 89 -72 22 0 806 811 807 805 799 790 749 796 687 685 775 751 178 813 545 208 204 812 176 434 187 180 179 175 174 546 129 136 156 814 547 346 47 50 54 55 98 421 538 543 548 549 259 554 551 552 541 542 215 327 405 319 540 320 610 0\n816 -72 22 0 799 796 174 175 187 815 247 260 547 543 54 0\n817 80 62 -40 -74 -89 0 685 806 811 435 750 796 775 687 749 773 548 246 260 44 543 185 22 540 325 215 250 249 290 97 59 133 200 545 229 24 549 554 552 542 317 398 315 551 280 251 295 541 651 0\n818 62 -40 -74 -89 0 687 796 775 685 806 811 435 750 749 97 59 133 200 545 229 24 773 549 554 552 542 317 398 315 246 260 44 543 185 548 46 22 248 433 250 249 290 540 325 817 387 622 0\n819 -15 -40 -74 -89 0 796 749 435 750 685 806 811 775 790 280 251 200 818 297 30 25 133 545 229 24 773 549 554 552 542 160 301 206 97 59 317 398 315 551 246 260 44 543 212 653 541 0\n820 -89 22 0 779 797 799 796 811 806 685 750 435 775 749 790 816 246 247 251 257 260 280 544 189 547 23 24 25 28 29 30 44 59 97 133 200 773 543 545 549 229 554 552 542 160 317 315 398 818 301 297 819 385 395 353 655 0\n821 -40 71 89 0 775 811 806 807 805 685 24 133 165 200 773 812 545 549 546 229 554 156 552 542 0\n822 -73 50 22 0 799 775 790 779 797 687 685 811 806 805 807 749 751 820 816 184 185 186 821 547 47 48 49 50 51 55 98 102 189 218 538 544 347 548 549 255 414 554 545 551 552 137 713 540 207 228 215 325 323 542 541 396 402 649 0\n823 -47 73 72 0 796 779 797 53 54 189 543 544 261 0\n824 -40 22 0 779 797 820 816 252 821 544 193 0\n825 50 22 0 799 824 816 822 547 823 0\n826 81 62 -83 22 0 805 807 435 750 685 797 779 796 790 775 687 749 825 67 538 548 73 74 816 190 544 261 543 185 63 540 325 215 69 549 554 552 65 229 542 220 68 287 99 77 317 398 221 820 170 156 546 315 551 353 541 623 0\n827 62 -83 22 0 687 797 779 796 805 807 790 775 685 435 750 749 825 99 77 67 538 549 554 552 65 229 542 317 398 221 820 170 156 546 315 220 73 74 816 190 544 261 543 185 255 254 548 69 68 64 63 62 60 287 540 325 826 370 652 0\n828 -15 -83 22 0 796 805 807 435 750 749 685 775 790 797 779 278 221 816 825 190 544 255 827 297 71 66 67 538 549 554 552 65 229 542 160 301 206 99 77 317 398 820 170 156 546 315 551 73 74 261 543 212 654 541 0\n829 -83 22 0 797 779 796 685 807 805 750 435 775 749 790 825 67 538 549 554 552 73 74 816 190 544 261 543 255 170 99 77 71 70 69 66 65 64 820 221 229 278 542 156 160 317 315 546 398 827 301 297 828 385 395 353 656 0\n830 22 0 775 790 779 797 687 685 796 811 806 805 807 749 751 816 820 825 63 64 65 67 70 73 74 75 76 99 103 170 190 538 544 548 549 254 255 261 554 543 551 552 185 829 545 422 137 713 334 540 207 228 215 325 323 542 541 396 402 650 0\n831 -23 0 830 1 0\n832 -25 0 830 2 0\n833 -27 0 830 3 0\n834 -31 0 830 7 0\n835 -38 0 830 18 0\n836 -40 0 830 21 0\n837 -43 0 830 36 0\n838 -45 0 830 42 0\n839 -49 0 830 57 0\n840 -50 0 830 61 0\n841 -54 0 830 96 0\n842 -55 0 830 100 0\n843 -56 0 830 105 0\n844 -58 0 830 128 0\n845 -61 0 830 132 0\n846 -62 0 830 135 0\n847 -76 0 830 195 0\n848 -79 0 830 199 0\n849 -80 0 830 205 0\n850 -150 0 834 749 790 775 538 0\n851 83 0 845 848 806 811 545 0\n852 151 0 850 687 548 0\n853 -160 0 850 549 0\n854 -59 0 851 219 0\n855 -84 0 851 229 0\n856 161 0 853 685 554 0\n857 152 0 856 551 0\n858 153 0 856 552 0\n859 66 0 858 833 855 542 0\n860 14 0 859 749 317 0\n861 75 0 859 435 841 750 315 0\n862 93 0 860 435 839 841 750 398 0\n863 -90 -73 0 749 832 846 852 849 857 843 840 842 847 807 805 844 862 851 861 859 830 860 185 540 215 541 325 186 253 257 414 347 546 660 0\n864 -73 0 852 846 832 749 857 849 779 797 842 845 854 831 835 836 847 807 805 844 862 851 861 859 830 860 185 186 187 540 215 325 541 863 728 544 411 332 546 659 0\n865 91 0 864 838 796 837 543 0\n866 -89 0 865 260 0\n867 -90 0 865 261 0\n868 -69 0 867 779 797 728 0\n869 71 0 868 844 805 807 866 847 546 0\n870 -72 0 869 180 0\n871 -74 0 869 193 0\n872 0 871 870 797 867 779 544 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record011.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record011.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record011.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record011.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record011 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeafTable : ConcreteGrowth.Table (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record011.l) :=
(.branch 39
 (.branch 19
 (.branch 9
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
 (.branch 8
 (.leaf (⟨7, by decide⟩))
 (.leaf (⟨8, by decide⟩))))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf (⟨9, by decide⟩))
 (.leaf (⟨10, by decide⟩)))
 (.branch 12
 (.leaf (⟨11, by decide⟩))
 (.branch 13
 (.leaf (⟨12, by decide⟩))
 (.leaf (⟨13, by decide⟩)))))
 (.branch 16
 (.branch 15
 (.leaf (⟨14, by decide⟩))
 (.leaf (⟨15, by decide⟩)))
 (.branch 17
 (.leaf (⟨16, by decide⟩))
 (.branch 18
 (.leaf (⟨17, by decide⟩))
 (.leaf (⟨18, by decide⟩)))))))
 (.branch 29
 (.branch 24
 (.branch 21
 (.branch 20
 (.leaf (⟨19, by decide⟩))
 (.leaf (⟨20, by decide⟩)))
 (.branch 22
 (.leaf (⟨21, by decide⟩))
 (.branch 23
 (.leaf (⟨22, by decide⟩))
 (.leaf (⟨23, by decide⟩)))))
 (.branch 26
 (.branch 25
 (.leaf (⟨24, by decide⟩))
 (.leaf (⟨25, by decide⟩)))
 (.branch 27
 (.leaf (⟨26, by decide⟩))
 (.branch 28
 (.leaf (⟨27, by decide⟩))
 (.leaf (⟨28, by decide⟩))))))
 (.branch 34
 (.branch 31
 (.branch 30
 (.leaf (⟨29, by decide⟩))
 (.leaf (⟨30, by decide⟩)))
 (.branch 32
 (.leaf (⟨31, by decide⟩))
 (.branch 33
 (.leaf (⟨32, by decide⟩))
 (.leaf (⟨33, by decide⟩)))))
 (.branch 36
 (.branch 35
 (.leaf (⟨34, by decide⟩))
 (.leaf (⟨35, by decide⟩)))
 (.branch 37
 (.leaf (⟨36, by decide⟩))
 (.branch 38
 (.leaf (⟨37, by decide⟩))
 (.leaf (⟨38, by decide⟩))))))))
 (.branch 58
 (.branch 48
 (.branch 43
 (.branch 41
 (.branch 40
 (.leaf (⟨0, by decide⟩))
 (.leaf (⟨1, by decide⟩)))
 (.branch 42
 (.leaf (⟨2, by decide⟩))
 (.leaf (⟨3, by decide⟩))))
 (.branch 45
 (.branch 44
 (.leaf (⟨4, by decide⟩))
 (.leaf (⟨5, by decide⟩)))
 (.branch 46
 (.leaf (⟨6, by decide⟩))
 (.branch 47
 (.leaf (⟨7, by decide⟩))
 (.leaf (⟨8, by decide⟩))))))
 (.branch 53
 (.branch 50
 (.branch 49
 (.leaf (⟨9, by decide⟩))
 (.leaf (⟨10, by decide⟩)))
 (.branch 51
 (.leaf (⟨11, by decide⟩))
 (.branch 52
 (.leaf (⟨12, by decide⟩))
 (.leaf (⟨13, by decide⟩)))))
 (.branch 55
 (.branch 54
 (.leaf (⟨14, by decide⟩))
 (.leaf (⟨15, by decide⟩)))
 (.branch 56
 (.leaf (⟨16, by decide⟩))
 (.branch 57
 (.leaf (⟨17, by decide⟩))
 (.leaf (⟨18, by decide⟩)))))))
 (.branch 68
 (.branch 63
 (.branch 60
 (.branch 59
 (.leaf (⟨19, by decide⟩))
 (.leaf (⟨20, by decide⟩)))
 (.branch 61
 (.leaf (⟨21, by decide⟩))
 (.branch 62
 (.leaf (⟨22, by decide⟩))
 (.leaf (⟨23, by decide⟩)))))
 (.branch 65
 (.branch 64
 (.leaf (⟨24, by decide⟩))
 (.leaf (⟨25, by decide⟩)))
 (.branch 66
 (.leaf (⟨26, by decide⟩))
 (.branch 67
 (.leaf (⟨27, by decide⟩))
 (.leaf (⟨28, by decide⟩))))))
 (.branch 73
 (.branch 70
 (.branch 69
 (.leaf (⟨29, by decide⟩))
 (.leaf (⟨30, by decide⟩)))
 (.branch 71
 (.leaf (⟨31, by decide⟩))
 (.branch 72
 (.leaf (⟨32, by decide⟩))
 (.leaf (⟨33, by decide⟩)))))
 (.branch 75
 (.branch 74
 (.leaf (⟨34, by decide⟩))
 (.leaf (⟨35, by decide⟩)))
 (.branch 76
 (.leaf (⟨36, by decide⟩))
 (.branch 77
 (.leaf (⟨37, by decide⟩))
 (.leaf (⟨38, by decide⟩)))))))))
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record011.l := originalLeafTable.get j.val
def orbitWordTable : ConcreteGrowth.Table (List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record011.g)) :=
(.branch 39
 (.branch 19
 (.branch 9
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
 (.branch 8
 (.leaf ([]))
 (.leaf ([]))))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ([]))
 (.leaf ([])))
 (.branch 12
 (.leaf ([]))
 (.branch 13
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 16
 (.branch 15
 (.leaf ([]))
 (.leaf ([])))
 (.branch 17
 (.leaf ([]))
 (.branch 18
 (.leaf ([]))
 (.leaf ([])))))))
 (.branch 29
 (.branch 24
 (.branch 21
 (.branch 20
 (.leaf ([]))
 (.leaf ([])))
 (.branch 22
 (.leaf ([]))
 (.branch 23
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 26
 (.branch 25
 (.leaf ([]))
 (.leaf ([])))
 (.branch 27
 (.leaf ([]))
 (.branch 28
 (.leaf ([]))
 (.leaf ([]))))))
 (.branch 34
 (.branch 31
 (.branch 30
 (.leaf ([]))
 (.leaf ([])))
 (.branch 32
 (.leaf ([]))
 (.branch 33
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 36
 (.branch 35
 (.leaf ([]))
 (.leaf ([])))
 (.branch 37
 (.leaf ([]))
 (.branch 38
 (.leaf ([]))
 (.leaf ([]))))))))
 (.branch 58
 (.branch 48
 (.branch 43
 (.branch 41
 (.branch 40
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 42
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))
 (.branch 45
 (.branch 44
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 46
 (.leaf ([⟨1, by decide⟩]))
 (.branch 47
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))))
 (.branch 53
 (.branch 50
 (.branch 49
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 51
 (.leaf ([⟨1, by decide⟩]))
 (.branch 52
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))
 (.branch 55
 (.branch 54
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 56
 (.leaf ([⟨1, by decide⟩]))
 (.branch 57
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))))
 (.branch 68
 (.branch 63
 (.branch 60
 (.branch 59
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 61
 (.leaf ([⟨1, by decide⟩]))
 (.branch 62
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))
 (.branch 65
 (.branch 64
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 66
 (.leaf ([⟨1, by decide⟩]))
 (.branch 67
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))))
 (.branch 73
 (.branch 70
 (.branch 69
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 71
 (.leaf ([⟨1, by decide⟩]))
 (.branch 72
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))
 (.branch 75
 (.branch 74
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 76
 (.leaf ([⟨1, by decide⟩]))
 (.branch 77
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))))))
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record011.g) := orbitWordTable.get j.val
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record011.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record011.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record011 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record011_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record011 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record011_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record011_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00022.record011

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00022.record008
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3983e31c8f0f23a8da2e87a718d61db0e4b83ee44f1e24e9c6699664d98e4b91e5c5c5595954d58d70d8b52d8751d0f5c338cd32cc73c2ccb4acab1ac9b16c3bc1d8751cc749c9715c3783d0f0bc1f1d18a198d11c7096261926439c1465854550d58330c6342c8b0ad0711c27"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db6db4db6934924934d249b4d249a49249a4924d2693249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record008 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record008 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record008.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record008.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record008.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 30), (facetIndex 58), (facetIndex 60)]))
 (.leaf ([(facetIndex 50), (facetIndex 71)])))
 (.branch 3
 (.leaf ([(facetIndex 76), (facetIndex 77)]))
 (.leaf ([(facetIndex 84), (facetIndex 86)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 37), (facetIndex 45), (facetIndex 68)]))
 (.leaf ([(facetIndex 78), (facetIndex 79), (facetIndex 81)])))
 (.branch 7
 (.leaf ([(facetIndex 80), (facetIndex 82), (facetIndex 85)]))
 (.branch 8
 (.leaf ([(facetIndex 24), (facetIndex 27), (facetIndex 52), (facetIndex 53)]))
 (.leaf ([(facetIndex 72), (facetIndex 73), (facetIndex 74), (facetIndex 83)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "363865655220888100400000000000000770100004000000040000000007007z18;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record008 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record008_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00022.record008" "{\"atoms\":[{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00022.record008" 75

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00022.record008" "{\"ridges\":[[2,261],[5,265],[7,194],[8,259],[11,532],[13,261],[13,772],[17,265],[18,265],[18,776],[20,208],[22,266],[27,526],[31,261],[32,194],[33,262],[34,262],[35,772],[41,265],[42,194],[43,776],[46,194],[47,194],[48,194],[48,259],[50,261],[50,265],[51,532],[53,556],[54,772],[55,532],[56,208],[57,532],[58,404],[59,772],[60,261],[64,152],[67,776],[69,776],[70,208],[71,912],[72,30],[73,300],[74,526],[77,262],[80,90],[82,178],[83,556],[84,284],[84,772],[84,776],[85,232]],\"owners\":[[8,259,[2,5,31,33,35,41,43],[48]],[48,259,[2,5,31,35,41,43],[8,33]],[33,262,[73,74],[2,26,31,34,35,77]],[34,262,[73,74],[2,26,31,33,35,77]],[77,262,[2,26,31,35,73,74],[33,34]],[22,266,[5,26,41,43,73,74],[]],[7,194,[76,77,80,81,82],[32,42,46,47,48]],[32,194,[80,81,82],[7,42,46,47,48,76,77]],[42,194,[76,77,82],[7,32,46,47,48,80,81]],[46,194,[77,81],[7,32,42,47,48,76,80,82]],[47,194,[76,77,80],[7,32,42,46,48,81,82]],[48,194,[76,80,81,82],[7,32,42,46,47,77]],[11,532,[83,84],[51,55,57,59]],[51,532,[],[11,55,57,59,83,84]],[55,532,[84],[11,51,57,59,83]],[57,532,[83,84],[11,51,55,59]],[13,772,[74,84],[35,54,59]],[35,772,[84],[13,54,59,74]],[54,772,[],[13,35,59,74,84]],[59,772,[74],[13,35,54,84]],[84,772,[13,35],[54,59,74]],[64,152,[79,86],[15,38,62,65,66,80,85]],[18,776,[74,84,86],[43,54,67,69]],[43,776,[84,86],[18,54,67,69,74]],[67,776,[74],[18,43,54,69,84,86]],[69,776,[74,84],[18,43,54,67,86]],[84,776,[18,43,69],[54,67,74,86]],[20,208,[76,80,82,85],[46,56,64,70]],[56,208,[80,82,85],[20,46,64,70,76]],[70,208,[76,80],[20,46,56,64,82,85]],[72,30,[24],[]],[27,526,[74],[]],[74,526,[27],[]],[80,90,[37,78],[]],[82,178,[45,79],[]],[84,284,[50],[]],[73,300,[52],[]],[53,556,[83],[]],[83,556,[53],[]],[58,404,[],[]],[85,232,[68,81],[]],[71,912,[86],[]]],\"edges\":[[23,[11,13,27,35,51,53,54,55,57,59,74,83,84]],[39,[7,20,32,42,46,47,48,56,60,64,68,70,76,77,80,81,82,85]],[42,[8,17,22,34,48,58,60,65,69,71,77,86]],[44,[13,18,35,43,54,59,67,69,71,74,84,86]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00022.record008" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00022.record008\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-27,-18],[-27,-22],[-42,-27],[-56,-12],[-56,-39],[-58,-56],[-4,1,2,14,16,18,20,22],[-26,1,2,14,18,20,22],[-1,-6,-27],[-6,-14,-27],[-6,-27,-37],[-16,46,47],[-17,46,47],[-49,1,12,14,18,46,47],[-2,-8,-27],[-7,-8,-27],[-8,-20,-27],[-10,2,12,20,22,46,47],[-3,48,49,52,53,54],[-15,52,53,54],[-21,48,49,54],[-24,49,53],[-25,48,49,52],[-26,48,52,53,54],[-5,55,56],[-28],[-32,56],[-34,55,56],[-6,47,56],[-18,56],[-31],[-36,47],[-56,6,18],[-38,51,58],[-8,47,56,58],[-22,56,58],[-40,47],[-42,47,56],[-56,8,22,42],[-9,48,52,54,57],[-33,52,54,57],[-43,48,52],[-45,11],[-13,47],[-47,13],[-52,19,50],[-54,23,51],[-56,27],[-46,29],[-30,55],[-55,30],[-35],[-57,41,53],[-44,58],[-37,59],[-44,60],[-48,61],[-49,61],[-56,62],[-58,62],[-19,63],[-23,63],[-41,63],[-50,64],[-51,64],[-53,64],[-11,65],[-13,65],[-29,65],[-30,65],[-66,45,46,47,55],[-46,66],[-47,66],[-55,66],[-60,67],[-59,67],[-62,68],[-61,68],[-68,69],[-67,69],[-64,70],[-63,70],[-65,-66,71],[-71,72],[-72,73],[-70,-72,74],[-74,75],[-69,-73,75],[-75],[5,6,13,18,28,30,31,32,34,36,47,55,56],[3,9,15,21,24,25,26,33,37,38,41,43,48,49,52,53,54,57],[4,7,10,17,26,35,37,39,42,44,49,58],[6,8,18,22,31,36,40,42,44,47,56,58]],\"atoms\":[{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":50,\"b\":35},{\"tag\":\"incompatible\",\"a\":50,\"b\":43},{\"tag\":\"incompatible\",\"a\":69,\"b\":50},{\"tag\":\"incompatible\",\"a\":84,\"b\":26},{\"tag\":\"incompatible\",\"a\":84,\"b\":65},{\"tag\":\"incompatible\",\"a\":86,\"b\":84},{\"tag\":\"mate\",\"ridge\":259,\"a\":8,\"owners\":[2,5,31,33,35,41,43]},{\"tag\":\"mate\",\"ridge\":259,\"a\":48,\"owners\":[2,5,31,35,41,43]},{\"tag\":\"three\",\"ridge\":261,\"vertices\":[2,13,50]},{\"tag\":\"three\",\"ridge\":261,\"vertices\":[13,31,50]},{\"tag\":\"three\",\"ridge\":261,\"vertices\":[13,50,60]},{\"tag\":\"mate\",\"ridge\":262,\"a\":33,\"owners\":[73,74]},{\"tag\":\"mate\",\"ridge\":262,\"a\":34,\"owners\":[73,74]},{\"tag\":\"mate\",\"ridge\":262,\"a\":77,\"owners\":[2,26,31,35,73,74]},{\"tag\":\"three\",\"ridge\":265,\"vertices\":[5,18,50]},{\"tag\":\"three\",\"ridge\":265,\"vertices\":[17,18,50]},{\"tag\":\"three\",\"ridge\":265,\"vertices\":[18,41,50]},{\"tag\":\"mate\",\"ridge\":266,\"a\":22,\"owners\":[5,26,41,43,73,74]},{\"tag\":\"mate\",\"ridge\":194,\"a\":7,\"owners\":[76,77,80,81,82]},{\"tag\":\"mate\",\"ridge\":194,\"a\":32,\"owners\":[80,81,82]},{\"tag\":\"mate\",\"ridge\":194,\"a\":42,\"owners\":[76,77,82]},{\"tag\":\"mate\",\"ridge\":194,\"a\":46,\"owners\":[77,81]},{\"tag\":\"mate\",\"ridge\":194,\"a\":47,\"owners\":[76,77,80]},{\"tag\":\"mate\",\"ridge\":194,\"a\":48,\"owners\":[76,80,81,82]},{\"tag\":\"mate\",\"ridge\":532,\"a\":11,\"owners\":[83,84]},{\"tag\":\"mate\",\"ridge\":532,\"a\":51,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":532,\"a\":55,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":532,\"a\":57,\"owners\":[83,84]},{\"tag\":\"mate\",\"ridge\":772,\"a\":13,\"owners\":[74,84]},{\"tag\":\"mate\",\"ridge\":772,\"a\":35,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":772,\"a\":54,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":772,\"a\":59,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":772,\"a\":84,\"owners\":[13,35]},{\"tag\":\"mate\",\"ridge\":152,\"a\":64,\"owners\":[79,86]},{\"tag\":\"mate\",\"ridge\":776,\"a\":18,\"owners\":[74,84,86]},{\"tag\":\"mate\",\"ridge\":776,\"a\":43,\"owners\":[84,86]},{\"tag\":\"mate\",\"ridge\":776,\"a\":67,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":776,\"a\":69,\"owners\":[74,84]},{\"tag\":\"mate\",\"ridge\":776,\"a\":84,\"owners\":[18,43,69]},{\"tag\":\"mate\",\"ridge\":208,\"a\":20,\"owners\":[76,80,82,85]},{\"tag\":\"mate\",\"ridge\":208,\"a\":56,\"owners\":[80,82,85]},{\"tag\":\"mate\",\"ridge\":208,\"a\":70,\"owners\":[76,80]},{\"tag\":\"mate\",\"ridge\":30,\"a\":72,\"owners\":[24]},{\"tag\":\"mate\",\"ridge\":526,\"a\":27,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":526,\"a\":74,\"owners\":[27]},{\"tag\":\"mate\",\"ridge\":90,\"a\":80,\"owners\":[37,78]},{\"tag\":\"mate\",\"ridge\":178,\"a\":82,\"owners\":[45,79]},{\"tag\":\"mate\",\"ridge\":284,\"a\":84,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":300,\"a\":73,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":556,\"a\":53,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":556,\"a\":83,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":404,\"a\":58,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":232,\"a\":85,\"owners\":[68,81]},{\"tag\":\"mate\",\"ridge\":912,\"a\":71,\"owners\":[86]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":60,\"full_literals\":[-37,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":71,\"full_literals\":[-44,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":76,\"full_literals\":[-48,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":77,\"full_literals\":[-49,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":84,\"full_literals\":[-56,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":86,\"full_literals\":[-58,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":37,\"full_literals\":[-19,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":45,\"full_literals\":[-23,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":68,\"full_literals\":[-41,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":78,\"full_literals\":[-50,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":79,\"full_literals\":[-51,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":81,\"full_literals\":[-53,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":24,\"full_literals\":[-11,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":27,\"full_literals\":[-13,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":52,\"full_literals\":[-29,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":53,\"full_literals\":[-30,65]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[72,73,74,83],\"full_literals\":[-66,45,46,47,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":73,\"full_literals\":[-46,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":74,\"full_literals\":[-47,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":83,\"full_literals\":[-55,66]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-60,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-59,false,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-62,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-61,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-68,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-67,false,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-64,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-65,-66,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-71,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-72,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-70,-72,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-74,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-69,-73,75],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":23,\"owners\":[11,13,27,35,51,53,54,55,57,59,74,83,84]},{\"tag\":\"edge\",\"edge\":39,\"owners\":[7,20,32,42,46,47,48,56,60,64,68,70,76,77,80,81,82,85]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[8,17,22,34,48,58,60,65,69,71,77,86]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[13,18,35,43,54,59,67,69,71,74,84,86]}]}"
  "94 -74 0 89 87 0\n95 5 6 13 18 30 32 34 36 47 55 56 0 26 31 90 0\n96 4 7 10 17 26 37 39 42 44 49 58 0 52 92 0\n97 6 8 18 22 36 40 42 44 47 56 58 0 31 93 0\n98 70 69 0 80 76 55 79 78 58 57 77 60 81 82 64 65 66 61 62 63 46 34 47 53 22 20 41 24 42 19 23 40 21 91 0\n99 47 69 0 79 77 59 60 36 30 80 75 56 32 37 29 35 38 97 0\n100 69 0 94 98 86 84 99 45 73 68 83 0\n101 -73 0 100 89 88 0\n102 -72 0 101 85 0\n103 -71 0 102 84 0\n104 -66 0 103 83 67 68 69 70 43 45 49 51 71 0\n105 -46 0 104 72 0\n106 -47 0 104 73 0\n107 -55 0 104 74 0\n108 -16 0 105 106 12 0\n109 -17 0 105 106 13 0\n110 -36 0 106 32 0\n111 -13 0 106 44 0\n112 -30 0 107 50 0\n113 56 0 110 107 106 112 111 27 30 29 25 28 95 0\n114 -12 0 113 4 0\n115 -39 0 113 5 0\n116 27 0 113 48 0\n117 -18 0 116 1 0\n118 -22 0 116 2 0\n119 -42 0 116 3 0\n120 6 0 117 113 33 0\n121 8 0 118 113 119 39 0\n122 -1 0 120 116 9 0\n123 -14 0 120 116 10 0\n124 -37 0 120 116 11 0\n125 -2 0 121 116 15 0\n126 -7 0 121 116 16 0\n127 -20 0 121 116 17 0\n128 -49 0 123 114 105 117 122 106 14 0\n129 -4 0 125 122 123 108 117 127 118 7 0\n130 -26 0 125 122 123 117 127 118 8 0\n131 -10 0 125 114 105 118 127 106 18 0\n132 58 0 126 128 131 119 115 124 130 109 129 54 96 0\n133 0 132 113 6 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record008.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record008.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record008.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record008.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record008 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record008.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record008.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record008.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record008.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record008 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record008_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record008 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record008_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record008_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00022.record008
