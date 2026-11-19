module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00018Data
public import GraphInputsRow29Part00018Frames
public import GraphInputsRow29Part00018Leaves
public import GraphInputsRow29Part00018Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00018.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record000
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨81, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 4433351142277120, (certNat% 4), (certNat% 5), 65970697666560]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record000_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00018.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00018.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record002
def vertexColumn : Fields := ⟨10, (certNat% 6)⟩
def kindColumn : Fields := ⟨3, (certNat% 7)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨80, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨101, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), (certNat% 9), (certNat% 10), 897201488265216, (certNat% 11), (certNat% 12)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 14), 844432446324736, (certNat% 11)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), (certNat% 16), (certNat% 17), (certNat% 18)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 20), (certNat% 16), (certNat% 14)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), (certNat% 22), (certNat% 23), 1941325217792, (certNat% 24)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 16), (certNat% 26), 897201488265216, 1927366574080, (certNat% 27), (certNat% 28)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record002_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00018.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00018.record004
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record004
def vertexColumn : Fields := ⟨10, (certNat% 29)⟩
def kindColumn : Fields := ⟨3, (certNat% 30)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨83, by decide⟩, ⟨86, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 32), (certNat% 33), (certNat% 34), 51677046505472, (certNat% 35)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 36), (certNat% 37), (certNat% 38), (certNat% 34), 52917295621603328, (certNat% 39)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), (certNat% 41), (certNat% 42), (certNat% 43), (certNat% 44), (certNat% 45)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), (certNat% 41), (certNat% 47), (certNat% 34), (certNat% 44), (certNat% 45)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), (certNat% 33), (certNat% 49), (certNat% 50), 16888498602639360]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 51), (certNat% 52), 16501264351232, (certNat% 53), (certNat% 54)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 55), (certNat% 56), 16888498602639360, (certNat% 57), 5497558138880]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 58), 16888498602639360, (certNat% 59), (certNat% 57), 5497558138880]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 60), (certNat% 34), (certNat% 61), 51677046505472, (certNat% 62), 5629499534213120]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 63), (certNat% 64), (certNat% 54), (certNat% 65), 16492674416640, 16888498602639360]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 66), 16501264351232, (certNat% 67), (certNat% 53), 16888498602639360, 4611686018427387904]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 68), (certNat% 69), 16492674416640, (certNat% 61), 5629499534213120]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 70), (certNat% 34), (certNat% 71), 51677046505472, 16888498602639360, (certNat% 72)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 73), (certNat% 41), (certNat% 34), (certNat% 53), (certNat% 74), 51677046505472, 16888507192573952]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c17 c12
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c18 c11
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c19 c10
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c20 c5
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c21 c4
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c22 c3
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c23 c2
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c24 c1
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c25 c1
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c26 c0
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c27 c0
  c28
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record004_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record004_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00018.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00018.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "e538c9723c1f392e2a5a8e87ae1b16a5996959568d9361db0ea398e938ce8b8ae1ba1e1783ee47891e785c5695655554d70da358d334ad8745d0f783c4e9364d534cf0ba2d8b32cab86c5b0ef07a1d8751cc749ca719e1745c9715c3783d0f23c4f0bc1fe13141d28c1b382c4872a286a1c46961465454550d48d1342d60c6344c530cc8b12c2b"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "49b4936926db6d34db6d36db4934934926924d24d249a4da6db4d349b493249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record005.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 60), (facetIndex 97), (facetIndex 101), (facetIndex 102)]))
 (.leaf ([(facetIndex 74), (facetIndex 106), (facetIndex 107)])))
 (.branch 3
 (.leaf ([(facetIndex 31), (facetIndex 50), (facetIndex 51), (facetIndex 52), (facetIndex 53)]))
 (.leaf ([(facetIndex 37), (facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 59)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 64), (facetIndex 65), (facetIndex 66), (facetIndex 67)]))
 (.leaf ([(facetIndex 69), (facetIndex 70), (facetIndex 71), (facetIndex 73)])))
 (.branch 7
 (.leaf ([(facetIndex 39), (facetIndex 47), (facetIndex 48), (facetIndex 61), (facetIndex 62), (facetIndex 75), (facetIndex 98), (facetIndex 103)]))
 (.leaf ([(facetIndex 29), (facetIndex 30), (facetIndex 34), (facetIndex 35), (facetIndex 44), (facetIndex 81), (facetIndex 87), (facetIndex 89), (facetIndex 96)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "240c00187000038e00038000c68b689241b061b612486c07000c18fc05f8z15;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 28), (facetIndex 49), (facetIndex 99), (facetIndex 100)]))
 (.leaf ([(facetIndex 63), (facetIndex 78), (facetIndex 104), (facetIndex 105)])))
 (.branch 3
 (.leaf ([(facetIndex 33), (facetIndex 54), (facetIndex 58)]))
 (.leaf ([(facetIndex 38), (facetIndex 68), (facetIndex 72)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 45), (facetIndex 76), (facetIndex 77)]))
 (.leaf ([(facetIndex 32), (facetIndex 36), (facetIndex 40), (facetIndex 41), (facetIndex 42), (facetIndex 43), (facetIndex 46), (facetIndex 79), (facetIndex 83), (facetIndex 85)])))
 (.branch 7
 (.leaf ([(facetIndex 80), (facetIndex 82), (facetIndex 84), (facetIndex 86), (facetIndex 90), (facetIndex 91), (facetIndex 92), (facetIndex 93), (facetIndex 94)]))
 (.leaf ([(facetIndex 88), (facetIndex 95)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "9000000fb6d871aeb86a64003003000200080080000160b6d0c5015z18;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
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
def grouped2_0010 : List Nat := [4, 5, 6, 7]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7]
def grouped2_0014 : List Nat := [7]
def grouped3_0015 : List Nat := [0]
def grouped3_0016 : List Nat := [0, 1]
def grouped3_0017 : List Nat := [0, 1, 2, 3]
def grouped3_0019 : List Nat := [1]
def grouped3_0020 : List Nat := [2]
def grouped3_0021 : List Nat := [2, 3]
def grouped3_0022 : List Nat := [3]
def grouped3_0023 : List Nat := [4]
def grouped3_0024 : List Nat := [4, 5]
def grouped3_0025 : List Nat := [4, 5, 6, 7]
def grouped3_0026 : List Nat := [5]
def grouped3_0027 : List Nat := [6]
def grouped3_0028 : List Nat := [6, 7]
def grouped3_0029 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record005_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00018.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00018.record005" 117

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00018.record005" "{\"ridges\":[[3,49],[4,81],[11,37],[12,69],[14,37],[14,69],[34,37],[35,69],[47,41],[47,49],[48,73],[48,81],[49,537],[53,522],[58,657],[64,37],[65,69],[81,44],[81,76],[91,550],[93,582],[98,50],[98,82],[99,568],[100,600],[101,522],[102,530],[103,44],[103,76],[107,532]],\"owners\":[[47,41,[8,16,64],[0,50,61,75]],[48,73,[9,16,65],[1,51,62,75]],[3,49,[11,17,61,69,75],[47,55]],[47,49,[11,17,69],[3,55,61,75]],[98,50,[3,34,55,90,91],[20,47,78,89,99]],[4,81,[12,17,62,70,75],[48,56]],[48,81,[12,17,70],[4,56,62,75]],[98,82,[4,35,56,92,93],[20,48,79,89,100]],[11,37,[8,14,29,39,40,41,64],[34,69]],[34,37,[8,14,64],[11,29,39,40,41,69]],[81,44,[8,61,64,104],[23,29,78,82,83,103]],[103,44,[8,29,64,82,83],[23,61,78,81,104]],[12,69,[9,14,30,39,42,43,65],[35,70]],[35,69,[9,14,65],[12,30,39,42,43,70]],[81,76,[9,62,65,105],[23,30,79,84,85,103]],[103,76,[9,30,65,84,85],[23,62,79,81,105]],[53,522,[80,83,85,88,99,100],[19,33,49,54,87,101]],[101,522,[33,49,80,83,85,99,100],[19,53,54,87,88]],[102,530,[38,49,80,91,93,99,100],[21,58,59,95,96]],[107,532,[38,63,80,91,93,104,105],[26,72,73,95,96]],[49,537,[63],[]],[58,657,[72,77],[]],[91,550,[83],[]],[93,582,[85],[]],[99,568,[104],[]],[100,600,[105],[]]],\"edges\":[],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00018.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00018.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-15,-11],[-15,-12],[-16,-9],[-16,-15],[-17,-9],[-17,-15],[-17,-16],[-21,-11],[-21,-12],[-21,-16],[-21,-17],[-22,-17],[-23,-17],[-24,-16],[-25,-16],[-26,-10],[-26,-14],[-26,-15],[-26,-18],[-26,-19],[-26,-20],[-26,-21],[-26,-22],[-26,-23],[-26,-24],[-26,-25],[-27,-26],[-28,-26],[-29,-16],[-30,-17],[-32,-29],[-32,-30],[-33,-29],[-33,-30],[-37,-17],[-37,-29],[-37,-30],[-38,-16],[-38,-29],[-38,-30],[-39,-26],[-42,-20],[-42,-26],[-42,-35],[-43,-16],[-44,-17],[-46,-4],[-46,-11],[-46,-12],[-46,-32],[-46,-43],[-46,-44],[-46,-45],[-47,-3],[-47,-11],[-47,-12],[-47,-33],[-47,-43],[-47,-44],[-47,-45],[-47,-46],[-49,-45],[-51,-17],[-51,-45],[-52,-16],[-52,-45],[-53,-48],[-55,-45],[-56,-20],[-56,-42],[-57,-16],[-57,-17],[-58,-26],[-59,-26],[-60,-26],[-61,-21],[-61,-29],[-61,-30],[-61,-43],[-61,-44],[-61,-57],[-62,-8],[-62,-15],[-62,-21],[-62,-57],[-63,-16],[-63,-17],[-63,-26],[-64,-11],[-64,-12],[-64,-16],[-64,-17],[-64,-26],[-64,-62],[-65,-16],[-65,-17],[-65,-26],[-66,-11],[-66,-12],[-66,-16],[-66,-17],[-66,-26],[-66,-62],[-67,-26],[-68,-15],[-68,-21],[-68,-64],[-68,-66],[-69,-26],[-70,-13],[-70,-15],[-70,-21],[-70,-57],[-70,-64],[-70,-66],[-71,-17],[-71,-26],[-72,-26],[-73,-16],[-73,-26],[-74,-26],[-75,-26],[-76,-26],[-77,-10],[-77,-13],[-77,-15],[-77,-18],[-77,-20],[-77,-21],[-77,-22],[-77,-23],[-77,-24],[-77,-25],[-77,-28],[-77,-59],[-77,-60],[-77,-63],[-77,-64],[-77,-65],[-77,-66],[-77,-71],[-77,-73],[-77,-75],[-78,-26],[-78,-56],[-79,-61],[-79,-62],[-79,-70],[-80,-29],[-80,-30],[-80,-57],[-80,-79],[-81,-29],[-81,-30],[-81,-57],[-81,-79],[-83,-41],[-83,-77],[-84,-61],[-84,-62],[-84,-70],[-84,-80],[-84,-81],[-85,-29],[-85,-30],[-85,-43],[-85,-44],[-85,-57],[-85,-79],[-85,-84],[-86,-29],[-86,-30],[-86,-43],[-86,-44],[-86,-57],[-86,-79],[-86,-84],[-87,-14],[-87,-27],[-87,-34],[-87,-36],[-87,-48],[-87,-49],[-87,-50],[-87,-54],[-87,-58],[-87,-67],[-87,-68],[-87,-69],[-87,-76],[-87,-78],[-87,-82],[-88,-78],[-88,-83],[-29,3,8,46],[-30,4,8,47],[-1,5,9,43,51,57],[-29,5,9,51],[-79,1,16,37,71,72],[-2,6,9,44,52,57],[-30,6,9,52],[-79,2,17,38,73,74],[-5,3,7,11,21,22,23,46],[-16,3,7,46],[-5,-7,-46],[-7,-16,-46],[-62,3,43,46,85],[-84,3,11,46,63,64],[-6,4,7,12,21,24,25,47],[-17,4,7,47],[-6,-7,-47],[-7,-17,-47],[-62,4,44,47,86],[-84,4,12,47,65,66],[-35,61,64,66,69,80,81],[-82,15,31,61,64,66,80,81],[-83,20,31,61,72,74,80,81],[-88,20,45,61,72,74,85,86],[-31,45],[-40,54,59],[-72,64],[-74,66],[-80,85],[-81,86],[-89,42,78,82,83],[-90,56,87,88],[-91,13,32,33,34,35],[-92,19,37,38,39,41],[-93,46,47,48,49],[-94,51,52,53,55],[-95,21,29,30,43,44,57,79,84],[-96,11,12,16,17,26,62,68,70,77],[-97,89],[-97,90],[-98,91],[-98,92],[-99,97],[-99,98],[-100,93],[-100,94],[-101,95],[-101,96],[-102,100],[-102,101],[-103,99],[-103,102],[103],[-104,10,31,80,81],[-105,15,36,40],[-106,20,50,54],[-107,27,58,59],[-108,14,18,22,23,24,25,28,60,64,66],[-109,61,63,65,67,71,72,73,74,75],[-110,69,76],[-111,104],[-112,105,106],[-113,111,112],[-114,107,108],[-115,109,110],[-116,114,115],[-117,113,116],[117]],\"atoms\":[{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":33,\"b\":29},{\"tag\":\"incompatible\",\"a\":33,\"b\":30},{\"tag\":\"incompatible\",\"a\":34,\"b\":17},{\"tag\":\"incompatible\",\"a\":34,\"b\":33},{\"tag\":\"incompatible\",\"a\":35,\"b\":17},{\"tag\":\"incompatible\",\"a\":35,\"b\":33},{\"tag\":\"incompatible\",\"a\":35,\"b\":34},{\"tag\":\"incompatible\",\"a\":39,\"b\":29},{\"tag\":\"incompatible\",\"a\":39,\"b\":30},{\"tag\":\"incompatible\",\"a\":39,\"b\":34},{\"tag\":\"incompatible\",\"a\":39,\"b\":35},{\"tag\":\"incompatible\",\"a\":40,\"b\":35},{\"tag\":\"incompatible\",\"a\":41,\"b\":35},{\"tag\":\"incompatible\",\"a\":42,\"b\":34},{\"tag\":\"incompatible\",\"a\":43,\"b\":34},{\"tag\":\"incompatible\",\"a\":44,\"b\":28},{\"tag\":\"incompatible\",\"a\":44,\"b\":32},{\"tag\":\"incompatible\",\"a\":44,\"b\":33},{\"tag\":\"incompatible\",\"a\":44,\"b\":36},{\"tag\":\"incompatible\",\"a\":44,\"b\":37},{\"tag\":\"incompatible\",\"a\":44,\"b\":38},{\"tag\":\"incompatible\",\"a\":44,\"b\":39},{\"tag\":\"incompatible\",\"a\":44,\"b\":40},{\"tag\":\"incompatible\",\"a\":44,\"b\":41},{\"tag\":\"incompatible\",\"a\":44,\"b\":42},{\"tag\":\"incompatible\",\"a\":44,\"b\":43},{\"tag\":\"incompatible\",\"a\":45,\"b\":44},{\"tag\":\"incompatible\",\"a\":46,\"b\":44},{\"tag\":\"incompatible\",\"a\":47,\"b\":34},{\"tag\":\"incompatible\",\"a\":48,\"b\":35},{\"tag\":\"incompatible\",\"a\":50,\"b\":47},{\"tag\":\"incompatible\",\"a\":50,\"b\":48},{\"tag\":\"incompatible\",\"a\":51,\"b\":47},{\"tag\":\"incompatible\",\"a\":51,\"b\":48},{\"tag\":\"incompatible\",\"a\":55,\"b\":35},{\"tag\":\"incompatible\",\"a\":55,\"b\":47},{\"tag\":\"incompatible\",\"a\":55,\"b\":48},{\"tag\":\"incompatible\",\"a\":56,\"b\":34},{\"tag\":\"incompatible\",\"a\":56,\"b\":47},{\"tag\":\"incompatible\",\"a\":56,\"b\":48},{\"tag\":\"incompatible\",\"a\":57,\"b\":44},{\"tag\":\"incompatible\",\"a\":60,\"b\":38},{\"tag\":\"incompatible\",\"a\":60,\"b\":44},{\"tag\":\"incompatible\",\"a\":60,\"b\":53},{\"tag\":\"incompatible\",\"a\":61,\"b\":34},{\"tag\":\"incompatible\",\"a\":62,\"b\":35},{\"tag\":\"incompatible\",\"a\":64,\"b\":9},{\"tag\":\"incompatible\",\"a\":64,\"b\":29},{\"tag\":\"incompatible\",\"a\":64,\"b\":30},{\"tag\":\"incompatible\",\"a\":64,\"b\":50},{\"tag\":\"incompatible\",\"a\":64,\"b\":61},{\"tag\":\"incompatible\",\"a\":64,\"b\":62},{\"tag\":\"incompatible\",\"a\":64,\"b\":63},{\"tag\":\"incompatible\",\"a\":65,\"b\":8},{\"tag\":\"incompatible\",\"a\":65,\"b\":29},{\"tag\":\"incompatible\",\"a\":65,\"b\":30},{\"tag\":\"incompatible\",\"a\":65,\"b\":51},{\"tag\":\"incompatible\",\"a\":65,\"b\":61},{\"tag\":\"incompatible\",\"a\":65,\"b\":62},{\"tag\":\"incompatible\",\"a\":65,\"b\":63},{\"tag\":\"incompatible\",\"a\":65,\"b\":64},{\"tag\":\"incompatible\",\"a\":67,\"b\":63},{\"tag\":\"incompatible\",\"a\":69,\"b\":35},{\"tag\":\"incompatible\",\"a\":69,\"b\":63},{\"tag\":\"incompatible\",\"a\":70,\"b\":34},{\"tag\":\"incompatible\",\"a\":70,\"b\":63},{\"tag\":\"incompatible\",\"a\":71,\"b\":66},{\"tag\":\"incompatible\",\"a\":73,\"b\":63},{\"tag\":\"incompatible\",\"a\":74,\"b\":38},{\"tag\":\"incompatible\",\"a\":74,\"b\":60},{\"tag\":\"incompatible\",\"a\":75,\"b\":34},{\"tag\":\"incompatible\",\"a\":75,\"b\":35},{\"tag\":\"incompatible\",\"a\":76,\"b\":44},{\"tag\":\"incompatible\",\"a\":77,\"b\":44},{\"tag\":\"incompatible\",\"a\":79,\"b\":44},{\"tag\":\"incompatible\",\"a\":80,\"b\":39},{\"tag\":\"incompatible\",\"a\":80,\"b\":47},{\"tag\":\"incompatible\",\"a\":80,\"b\":48},{\"tag\":\"incompatible\",\"a\":80,\"b\":61},{\"tag\":\"incompatible\",\"a\":80,\"b\":62},{\"tag\":\"incompatible\",\"a\":80,\"b\":75},{\"tag\":\"incompatible\",\"a\":81,\"b\":16},{\"tag\":\"incompatible\",\"a\":81,\"b\":33},{\"tag\":\"incompatible\",\"a\":81,\"b\":39},{\"tag\":\"incompatible\",\"a\":81,\"b\":75},{\"tag\":\"incompatible\",\"a\":82,\"b\":34},{\"tag\":\"incompatible\",\"a\":82,\"b\":35},{\"tag\":\"incompatible\",\"a\":82,\"b\":44},{\"tag\":\"incompatible\",\"a\":83,\"b\":29},{\"tag\":\"incompatible\",\"a\":83,\"b\":30},{\"tag\":\"incompatible\",\"a\":83,\"b\":34},{\"tag\":\"incompatible\",\"a\":83,\"b\":35},{\"tag\":\"incompatible\",\"a\":83,\"b\":44},{\"tag\":\"incompatible\",\"a\":83,\"b\":81},{\"tag\":\"incompatible\",\"a\":84,\"b\":34},{\"tag\":\"incompatible\",\"a\":84,\"b\":35},{\"tag\":\"incompatible\",\"a\":84,\"b\":44},{\"tag\":\"incompatible\",\"a\":85,\"b\":29},{\"tag\":\"incompatible\",\"a\":85,\"b\":30},{\"tag\":\"incompatible\",\"a\":85,\"b\":34},{\"tag\":\"incompatible\",\"a\":85,\"b\":35},{\"tag\":\"incompatible\",\"a\":85,\"b\":44},{\"tag\":\"incompatible\",\"a\":85,\"b\":81},{\"tag\":\"incompatible\",\"a\":86,\"b\":44},{\"tag\":\"incompatible\",\"a\":87,\"b\":33},{\"tag\":\"incompatible\",\"a\":87,\"b\":39},{\"tag\":\"incompatible\",\"a\":87,\"b\":83},{\"tag\":\"incompatible\",\"a\":87,\"b\":85},{\"tag\":\"incompatible\",\"a\":88,\"b\":44},{\"tag\":\"incompatible\",\"a\":89,\"b\":31},{\"tag\":\"incompatible\",\"a\":89,\"b\":33},{\"tag\":\"incompatible\",\"a\":89,\"b\":39},{\"tag\":\"incompatible\",\"a\":89,\"b\":75},{\"tag\":\"incompatible\",\"a\":89,\"b\":83},{\"tag\":\"incompatible\",\"a\":89,\"b\":85},{\"tag\":\"incompatible\",\"a\":90,\"b\":35},{\"tag\":\"incompatible\",\"a\":90,\"b\":44},{\"tag\":\"incompatible\",\"a\":91,\"b\":44},{\"tag\":\"incompatible\",\"a\":92,\"b\":34},{\"tag\":\"incompatible\",\"a\":92,\"b\":44},{\"tag\":\"incompatible\",\"a\":93,\"b\":44},{\"tag\":\"incompatible\",\"a\":94,\"b\":44},{\"tag\":\"incompatible\",\"a\":95,\"b\":44},{\"tag\":\"incompatible\",\"a\":96,\"b\":28},{\"tag\":\"incompatible\",\"a\":96,\"b\":31},{\"tag\":\"incompatible\",\"a\":96,\"b\":33},{\"tag\":\"incompatible\",\"a\":96,\"b\":36},{\"tag\":\"incompatible\",\"a\":96,\"b\":38},{\"tag\":\"incompatible\",\"a\":96,\"b\":39},{\"tag\":\"incompatible\",\"a\":96,\"b\":40},{\"tag\":\"incompatible\",\"a\":96,\"b\":41},{\"tag\":\"incompatible\",\"a\":96,\"b\":42},{\"tag\":\"incompatible\",\"a\":96,\"b\":43},{\"tag\":\"incompatible\",\"a\":96,\"b\":46},{\"tag\":\"incompatible\",\"a\":96,\"b\":77},{\"tag\":\"incompatible\",\"a\":96,\"b\":79},{\"tag\":\"incompatible\",\"a\":96,\"b\":82},{\"tag\":\"incompatible\",\"a\":96,\"b\":83},{\"tag\":\"incompatible\",\"a\":96,\"b\":84},{\"tag\":\"incompatible\",\"a\":96,\"b\":85},{\"tag\":\"incompatible\",\"a\":96,\"b\":90},{\"tag\":\"incompatible\",\"a\":96,\"b\":92},{\"tag\":\"incompatible\",\"a\":96,\"b\":94},{\"tag\":\"incompatible\",\"a\":97,\"b\":44},{\"tag\":\"incompatible\",\"a\":97,\"b\":74},{\"tag\":\"incompatible\",\"a\":98,\"b\":80},{\"tag\":\"incompatible\",\"a\":98,\"b\":81},{\"tag\":\"incompatible\",\"a\":98,\"b\":89},{\"tag\":\"incompatible\",\"a\":99,\"b\":47},{\"tag\":\"incompatible\",\"a\":99,\"b\":48},{\"tag\":\"incompatible\",\"a\":99,\"b\":75},{\"tag\":\"incompatible\",\"a\":99,\"b\":98},{\"tag\":\"incompatible\",\"a\":100,\"b\":47},{\"tag\":\"incompatible\",\"a\":100,\"b\":48},{\"tag\":\"incompatible\",\"a\":100,\"b\":75},{\"tag\":\"incompatible\",\"a\":100,\"b\":98},{\"tag\":\"incompatible\",\"a\":102,\"b\":59},{\"tag\":\"incompatible\",\"a\":102,\"b\":96},{\"tag\":\"incompatible\",\"a\":103,\"b\":80},{\"tag\":\"incompatible\",\"a\":103,\"b\":81},{\"tag\":\"incompatible\",\"a\":103,\"b\":89},{\"tag\":\"incompatible\",\"a\":103,\"b\":99},{\"tag\":\"incompatible\",\"a\":103,\"b\":100},{\"tag\":\"incompatible\",\"a\":104,\"b\":47},{\"tag\":\"incompatible\",\"a\":104,\"b\":48},{\"tag\":\"incompatible\",\"a\":104,\"b\":61},{\"tag\":\"incompatible\",\"a\":104,\"b\":62},{\"tag\":\"incompatible\",\"a\":104,\"b\":75},{\"tag\":\"incompatible\",\"a\":104,\"b\":98},{\"tag\":\"incompatible\",\"a\":104,\"b\":103},{\"tag\":\"incompatible\",\"a\":105,\"b\":47},{\"tag\":\"incompatible\",\"a\":105,\"b\":48},{\"tag\":\"incompatible\",\"a\":105,\"b\":61},{\"tag\":\"incompatible\",\"a\":105,\"b\":62},{\"tag\":\"incompatible\",\"a\":105,\"b\":75},{\"tag\":\"incompatible\",\"a\":105,\"b\":98},{\"tag\":\"incompatible\",\"a\":105,\"b\":103},{\"tag\":\"incompatible\",\"a\":106,\"b\":32},{\"tag\":\"incompatible\",\"a\":106,\"b\":45},{\"tag\":\"incompatible\",\"a\":106,\"b\":52},{\"tag\":\"incompatible\",\"a\":106,\"b\":54},{\"tag\":\"incompatible\",\"a\":106,\"b\":66},{\"tag\":\"incompatible\",\"a\":106,\"b\":67},{\"tag\":\"incompatible\",\"a\":106,\"b\":68},{\"tag\":\"incompatible\",\"a\":106,\"b\":72},{\"tag\":\"incompatible\",\"a\":106,\"b\":76},{\"tag\":\"incompatible\",\"a\":106,\"b\":86},{\"tag\":\"incompatible\",\"a\":106,\"b\":87},{\"tag\":\"incompatible\",\"a\":106,\"b\":88},{\"tag\":\"incompatible\",\"a\":106,\"b\":95},{\"tag\":\"incompatible\",\"a\":106,\"b\":97},{\"tag\":\"incompatible\",\"a\":106,\"b\":101},{\"tag\":\"incompatible\",\"a\":107,\"b\":97},{\"tag\":\"incompatible\",\"a\":107,\"b\":102},{\"tag\":\"mate\",\"ridge\":41,\"a\":47,\"owners\":[8,16,64]},{\"tag\":\"mate\",\"ridge\":73,\"a\":48,\"owners\":[9,16,65]},{\"tag\":\"mate\",\"ridge\":49,\"a\":3,\"owners\":[11,17,61,69,75]},{\"tag\":\"mate\",\"ridge\":49,\"a\":47,\"owners\":[11,17,69]},{\"tag\":\"mate\",\"ridge\":50,\"a\":98,\"owners\":[3,34,55,90,91]},{\"tag\":\"mate\",\"ridge\":81,\"a\":4,\"owners\":[12,17,62,70,75]},{\"tag\":\"mate\",\"ridge\":81,\"a\":48,\"owners\":[12,17,70]},{\"tag\":\"mate\",\"ridge\":82,\"a\":98,\"owners\":[4,35,56,92,93]},{\"tag\":\"mate\",\"ridge\":37,\"a\":11,\"owners\":[8,14,29,39,40,41,64]},{\"tag\":\"mate\",\"ridge\":37,\"a\":34,\"owners\":[8,14,64]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[11,14,64]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[14,34,64]},{\"tag\":\"mate\",\"ridge\":44,\"a\":81,\"owners\":[8,61,64,104]},{\"tag\":\"mate\",\"ridge\":44,\"a\":103,\"owners\":[8,29,64,82,83]},{\"tag\":\"mate\",\"ridge\":69,\"a\":12,\"owners\":[9,14,30,39,42,43,65]},{\"tag\":\"mate\",\"ridge\":69,\"a\":35,\"owners\":[9,14,65]},{\"tag\":\"three\",\"ridge\":69,\"vertices\":[12,14,65]},{\"tag\":\"three\",\"ridge\":69,\"vertices\":[14,35,65]},{\"tag\":\"mate\",\"ridge\":76,\"a\":81,\"owners\":[9,62,65,105]},{\"tag\":\"mate\",\"ridge\":76,\"a\":103,\"owners\":[9,30,65,84,85]},{\"tag\":\"mate\",\"ridge\":522,\"a\":53,\"owners\":[80,83,85,88,99,100]},{\"tag\":\"mate\",\"ridge\":522,\"a\":101,\"owners\":[33,49,80,83,85,99,100]},{\"tag\":\"mate\",\"ridge\":530,\"a\":102,\"owners\":[38,49,80,91,93,99,100]},{\"tag\":\"mate\",\"ridge\":532,\"a\":107,\"owners\":[38,63,80,91,93,104,105]},{\"tag\":\"mate\",\"ridge\":537,\"a\":49,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":657,\"a\":58,\"owners\":[72,77]},{\"tag\":\"mate\",\"ridge\":550,\"a\":91,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":582,\"a\":93,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":568,\"a\":99,\"owners\":[104]},{\"tag\":\"mate\",\"ridge\":600,\"a\":100,\"owners\":[105]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[60,97,101,102],\"full_literals\":[-89,42,78,82,83]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[74,106,107],\"full_literals\":[-90,56,87,88]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[31,50,51,52,53],\"full_literals\":[-91,13,32,33,34,35]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[37,55,56,57,59],\"full_literals\":[-92,19,37,38,39,41]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[64,65,66,67],\"full_literals\":[-93,46,47,48,49]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[69,70,71,73],\"full_literals\":[-94,51,52,53,55]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[39,47,48,61,62,75,98,103],\"full_literals\":[-95,21,29,30,43,44,57,79,84]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[29,30,34,35,44,81,87,89,96],\"full_literals\":[-96,11,12,16,17,26,62,68,70,77]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-97,89,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-97,false,90],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-98,91,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-98,false,92],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-99,97,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-99,false,98],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-100,93,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-100,false,94],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-101,95,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-101,false,96],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-102,100,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-102,false,101],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-103,99,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-103,false,102],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[28,49,99,100],\"full_literals\":[-104,10,31,80,81]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[33,54,58],\"full_literals\":[-105,15,36,40]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[38,68,72],\"full_literals\":[-106,20,50,54]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[45,76,77],\"full_literals\":[-107,27,58,59]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[32,36,40,41,42,43,46,79,83,85],\"full_literals\":[-108,14,18,22,23,24,25,28,60,64,66]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[80,82,84,86,90,91,92,93,94],\"full_literals\":[-109,61,63,65,67,71,72,73,74,75]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[88,95],\"full_literals\":[-110,69,76]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-111,104,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-112,105,106],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-113,111,112],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-114,107,108],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-115,109,110],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-116,114,115],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-117,113,116],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true}]}"
  "263 99 0 247 245 0\n264 102 0 247 246 0\n265 97 0 263 237 0\n266 98 0 263 238 0\n267 100 0 264 243 0\n268 101 0 264 244 0\n269 89 0 265 233 0\n270 90 0 265 234 0\n271 91 0 266 235 0\n272 92 0 266 236 0\n273 93 0 267 239 0\n274 94 0 267 240 0\n275 95 0 268 241 0\n276 96 0 268 242 0\n277 -61 0 275 76 77 78 79 80 81 146 159 231 0\n278 -88 82 45 85 86 72 74 0 277 269 193 194 218 225 42 0\n279 45 85 86 15 64 66 87 0 270 277 269 223 224 221 222 219 216 278 226 69 70 145 217 225 0\n280 -45 0 273 274 53 60 62 64 66 68 229 230 67 0\n281 -31 0 280 219 0\n282 -21 26 0 276 8 9 10 11 84 106 112 129 232 0\n283 -30 15 64 66 87 0 280 165 172 279 0\n284 -44 15 64 66 87 0 280 167 174 279 0\n285 -79 15 64 66 87 0 280 169 176 279 0\n286 -84 15 64 66 87 0 280 170 177 279 0\n287 -29 15 64 66 87 0 280 164 171 279 0\n288 -43 15 64 66 87 0 280 166 173 279 0\n289 15 64 66 87 21 0 275 280 283 284 285 286 287 288 231 168 175 279 0\n290 -15 26 0 276 1 2 4 6 83 105 111 126 232 0\n291 -64 26 0 276 89 90 91 92 94 107 114 138 232 0\n292 -66 26 0 276 98 99 100 101 103 108 115 140 232 0\n293 -11 -87 0 273 183 182 48 55 229 0\n294 -12 -87 0 273 183 182 49 56 229 0\n295 47 -16 17 26 0 273 275 119 95 71 65 45 38 29 15 14 3 282 291 290 292 289 294 183 182 222 229 47 52 206 214 209 200 201 202 231 0\n296 17 62 70 77 26 0 276 275 282 291 290 292 289 294 293 188 222 232 3 29 38 45 65 71 86 119 295 54 59 61 208 204 211 200 201 202 231 0\n297 -47 -17 26 0 275 116 87 72 63 46 35 30 13 12 7 5 282 291 290 292 289 293 221 54 58 61 212 208 203 197 198 199 231 0\n298 -17 26 0 273 275 282 291 290 292 289 294 183 182 221 5 7 30 35 46 63 72 96 116 297 229 47 51 214 210 205 197 198 199 231 0\n299 47 -62 26 0 273 275 160 147 85 82 282 291 290 292 289 183 182 229 47 51 52 196 231 213 171 0\n300 -62 26 0 275 282 82 85 147 160 299 54 58 59 61 195 207 231 165 0\n301 -30 33 13 26 0 271 277 282 291 290 292 289 189 180 32 150 154 227 215 0\n302 -47 -70 26 0 275 271 277 161 148 113 110 282 291 290 292 289 189 180 57 58 59 301 231 31 149 153 227 215 0\n303 -29 -70 26 0 273 271 277 282 291 290 292 289 182 183 302 229 50 110 189 180 33 149 153 227 215 0\n304 -70 26 0 273 275 282 291 290 292 289 183 182 110 113 148 161 302 229 51 52 303 231 34 301 0\n305 -30 26 0 300 298 304 296 125 34 301 0\n306 -57 26 0 277 262 281 282 291 290 292 289 185 184 300 298 304 296 128 250 181 135 220 249 256 189 190 254 187 222 142 221 141 137 143 139 253 259 131 130 133 132 136 127 178 134 252 186 179 251 258 260 261 257 255 124 151 155 248 0\n307 -29 26 0 269 271 282 291 290 292 289 192 191 300 298 304 296 158 225 44 125 180 31 33 227 0\n308 -43 -87 0 273 183 182 51 58 229 0\n309 -44 -87 0 273 183 182 52 59 229 0\n310 -79 26 0 277 262 281 282 291 290 292 289 185 184 300 298 304 296 128 250 181 135 220 249 256 189 190 254 187 222 142 221 141 137 143 139 253 259 131 130 133 132 136 127 178 134 252 186 179 251 258 260 261 257 255 124 152 156 248 0\n311 26 0 277 262 275 281 282 290 291 221 292 222 289 178 179 181 184 185 186 187 189 190 254 298 300 304 296 124 127 128 130 131 132 133 134 135 136 137 139 141 142 143 250 252 220 251 253 249 258 259 256 260 261 257 255 305 306 307 308 309 310 231 162 163 248 0\n312 -10 0 311 16 0\n313 -14 0 311 17 0\n314 -15 0 311 18 0\n315 -18 0 311 19 0\n316 -19 0 311 20 0\n317 -20 0 311 21 0\n318 -21 0 311 22 0\n319 -22 0 311 23 0\n320 -23 0 311 24 0\n321 -24 0 311 25 0\n322 -25 0 311 26 0\n323 -27 0 311 27 0\n324 -28 0 311 28 0\n325 -39 0 311 41 0\n326 -42 0 311 43 0\n327 -58 0 311 73 0\n328 -59 0 311 74 0\n329 -60 0 311 75 0\n330 -63 0 311 88 0\n331 -64 0 311 93 0\n332 -65 0 311 97 0\n333 -66 0 311 102 0\n334 -67 0 311 104 0\n335 -69 0 311 109 0\n336 -71 0 311 117 0\n337 -72 0 311 118 0\n338 -73 0 311 120 0\n339 -74 0 311 121 0\n340 -75 0 311 122 0\n341 -76 0 311 123 0\n342 -78 0 311 144 0\n343 -108 0 324 313 315 329 331 321 322 319 320 333 252 0\n344 -107 0 328 323 327 251 0\n345 -109 0 332 340 277 330 336 337 338 339 334 253 0\n346 87 0 333 314 331 318 289 0\n347 -110 0 341 335 254 0\n348 -114 0 344 343 258 0\n349 -115 0 345 347 259 0\n350 -36 0 346 181 0\n351 -50 0 346 184 0\n352 -54 0 346 185 0\n353 -82 0 346 192 0\n354 -43 0 346 308 0\n355 -44 0 346 309 0\n356 -116 0 348 349 260 0\n357 -106 0 351 317 352 250 0\n358 -40 0 352 328 220 0\n359 83 0 353 269 342 326 225 0\n360 113 0 356 262 261 0\n361 -105 0 358 314 350 249 0\n362 -41 0 359 157 0\n363 -112 0 361 357 256 0\n364 111 0 363 360 257 0\n365 104 0 364 255 0\n366 -84 0 365 312 281 162 163 248 0\n367 -29 0 362 325 316 272 36 39 228 0\n368 -57 0 365 312 281 151 155 248 0\n369 -79 0 365 312 281 152 156 248 0\n370 30 0 369 275 355 318 368 366 354 367 231 0\n371 -37 0 370 37 0\n372 -38 0 370 40 0\n373 0 372 371 272 316 325 362 228 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record005.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record005.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00018.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00018.record006
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "394e307ce495a4e87ae1b16a5996638ce2b91e1783ee4789565391e785c5695656558d70da358d334ad4745d0f783c4e9364d534cd4b32d2b2ad1b16c3bc1e8761cc729e1745c9743c1f1d06c1c98a1a866158362384e0bb81c447162469a1465854550d48d1342d60c6344c530cd0b22c4b0ac8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "369b69b6d24d249b4926934926924d2492492692492489249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record006 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record006 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record006.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record006.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record006.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 60), (facetIndex 74), (facetIndex 78), (facetIndex 79)]))
 (.leaf ([(facetIndex 42), (facetIndex 69), (facetIndex 70), (facetIndex 72), (facetIndex 73)])))
 (.branch 3
 (.leaf ([(facetIndex 39), (facetIndex 83), (facetIndex 84), (facetIndex 85)]))
 (.leaf ([(facetIndex 38), (facetIndex 48), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 52), (facetIndex 53), (facetIndex 54)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 41), (facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 59)]))
 (.leaf ([(facetIndex 61), (facetIndex 62), (facetIndex 75), (facetIndex 80), (facetIndex 81), (facetIndex 90), (facetIndex 94)])))
 (.branch 7
 (.leaf ([(facetIndex 46), (facetIndex 64), (facetIndex 65), (facetIndex 66), (facetIndex 67)]))
 (.leaf ([(facetIndex 40), (facetIndex 43), (facetIndex 44), (facetIndex 45)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "14014001242d000a09048db61688248db6db1bfe674cz1c;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 63), (facetIndex 76), (facetIndex 77)]))
 (.branch 2
 (.leaf ([(facetIndex 82), (facetIndex 91), (facetIndex 92)]))
 (.leaf ([(facetIndex 47), (facetIndex 58), (facetIndex 71)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 86), (facetIndex 87), (facetIndex 88)]))
 (.leaf ([(facetIndex 89), (facetIndex 93), (facetIndex 96)])))
 (.branch 6
 (.leaf ([(facetIndex 68)]))
 (.leaf ([(facetIndex 95)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "4c212236c00400000004050000000800000004z23;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
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
def grouped2_0008 : List Nat := [4, 5]
def grouped2_0009 : List Nat := [4, 5, 6, 7]
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7]
def grouped2_0012 : List Nat := [7]
def grouped3_0013 : List Nat := [0]
def grouped3_0014 : List Nat := [0, 1, 2]
def grouped3_0016 : List Nat := [1]
def grouped3_0017 : List Nat := [1, 2]
def grouped3_0018 : List Nat := [2]
def grouped3_0019 : List Nat := [3]
def grouped3_0020 : List Nat := [3, 4]
def grouped3_0021 : List Nat := [3, 4, 5, 6]
def grouped3_0022 : List Nat := [4]
def grouped3_0023 : List Nat := [5]
def grouped3_0024 : List Nat := [5, 6]
def grouped3_0025 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record006 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record006_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00018.record006" "{\"atoms\":[{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00018.record006" 75

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00018.record006" "{\"ridges\":[[7,138],[8,265],[8,266],[21,133],[23,385],[23,392],[34,138],[34,392],[39,265],[39,266],[40,131],[42,532],[43,133],[43,134],[44,131],[44,133],[44,134],[45,385],[46,644],[50,266],[51,138],[52,265],[52,266],[53,138],[54,265],[54,266],[60,896],[64,133],[65,133],[66,392],[69,532],[70,532],[72,532],[73,532],[74,133],[74,644],[74,896],[78,392],[78,896],[79,385],[79,784],[79,896],[83,134],[83,138],[84,138],[85,134],[85,392],[86,386],[87,134],[88,774],[89,134],[89,386],[89,644],[95,780],[96,404]],\"owners\":[[40,131,[7,13,51,53,60],[4,43,44,46,57,58]],[44,131,[7,13,51,57,58,60],[4,40,43,46,53]],[8,265,[23,63,66,68,76,77,78],[39,50,52,54]],[39,265,[23,76,77,78],[8,50,52,54,63,66,68]],[52,265,[23,63,66,68,77,78],[8,39,50,54,76]],[54,265,[23,63,66,68,76,78],[8,39,50,52,77]],[8,266,[34,82,85,91,92],[39,50,52,54]],[39,266,[34,91,92],[8,50,52,54,82,85]],[50,266,[34,85],[8,39,52,54,82,91,92]],[52,266,[34,82,85,92],[8,39,50,54,91]],[54,266,[34,82,85,91],[8,39,50,52,92]],[86,386,[13,34,60],[45,57,85,89,93]],[89,386,[13,34,57],[45,60,85,86,93]],[42,532,[96],[19,69,70,72,73,87,88]],[69,532,[87,88,96],[19,42,70,72,73]],[70,532,[87,88,96],[19,42,69,72,73]],[72,532,[88],[19,42,69,70,73,87,96]],[73,532,[87],[19,42,69,70,72,88,96]],[46,644,[95,96],[21,67,72,74,87,89]],[74,644,[87],[21,46,67,72,89,95,96]],[89,644,[21,67,72],[46,74,87,95,96]],[23,392,[34,85,95],[66,78]],[34,392,[23,66,78,95],[85]],[66,392,[34],[23,78,85,95]],[78,392,[34,85],[23,66,95]],[85,392,[23,78],[34,66,95]],[79,784,[88],[25,59,73,93,96]],[60,896,[95,96],[26,74,78,79,89,93]],[74,896,[93],[26,60,78,79,89,95,96]],[78,896,[89,93,96],[26,60,74,79,95]],[79,896,[89,95],[26,60,74,78,93,96]],[88,774,[47,89],[]],[95,780,[68],[]],[96,404,[71,86],[]]],\"edges\":[[28,[8,23,34,39,50,52,54,63,66,68,76,77,78,82,85,91,92,95]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00018.record006" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00018.record006\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-8,-7],[-10,-7],[-11,-7],[-13,-10],[-22,-5],[-22,-13],[-22,-15],[-24,-10],[-25,-11],[-26,-22],[-27,-10],[-28,-24],[-28,-25],[-28,-26],[-28,-27],[-31,-22],[-34,-12],[-34,-13],[-34,-26],[-34,-27],[-34,-28],[-37,-3],[-37,-12],[-37,-20],[-37,-22],[-37,-26],[-37,-27],[-37,-28],[-37,-31],[-38,-8],[-38,-28],[-38,-32],[-40,-10],[-40,-16],[-41,-11],[-41,-18],[-41,-25],[-42,-6],[-42,-34],[-44,-8],[-45,-7],[-45,-26],[-45,-42],[-51,-34],[-51,-38],[-8,1,3,16,18,22],[-11,1,3,16,20,21,22],[-4,-10,-25],[-10,-25,-34],[-11,-24,-34],[-10,-42,-44],[-11,-40,-46],[-11,-42,-44],[-1,-6,-40],[-1,-6,-41],[-6,-16,-41],[-6,-18,-40],[-2,5,23,26,28,35,36,37],[-7,5,35,36,37],[-17,5,23,26,28,36,37],[-19,5,23,26,28,35,37],[-2,6,39,42,47,48],[-7,6,47,48],[-15,6,42],[-17,6,39,42,48],[-19,6,39,42,47],[-5,-12,-38],[-43,3,6,22],[-46,3,6,20],[-9,51],[-29,44,45,51],[-30,44,45,51],[-32,45],[-33,44],[-13,50,51],[-34,44],[-46,4,27,32],[-5,6,42,50],[-6,5,26,37,50],[-26,6],[-37,6,42],[-42,5,37],[-38,45],[-22,50,51],[-34,49],[-37,46,49,51],[-38,46,50],[-45,14,46],[-50,28],[-51,31,43],[-52,22,34,37,38],[-53,9,29,30,32,33],[-54,7,40,41,42],[-55,13,24,25,26,27],[-56,8,10,11,12],[-57,52],[-57,53],[-58,54],[-59,57],[-59,58],[-60,55],[-60,56],[-61,60],[-62,59],[-62,61],[62],[-23,63],[-35,63],[-36,63],[-39,64],[-47,64],[-48,64],[-14,65],[-21,65],[-66,43,44,45],[-43,66],[-44,66],[-45,66],[-46,67],[-49,67],[-51,67],[-68,28],[-69,50],[-65,70],[-64,70],[-70,71],[-63,71],[-72,66],[-66,-67,72],[-73,68,69],[-74,72,73],[-72,74],[-71,-74,75],[-75],[2,5,6,7,15,17,19,23,26,28,35,36,37,39,42,47,48,50]],\"atoms\":[{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":40,\"b\":39},{\"tag\":\"incompatible\",\"a\":43,\"b\":39},{\"tag\":\"incompatible\",\"a\":44,\"b\":39},{\"tag\":\"incompatible\",\"a\":46,\"b\":43},{\"tag\":\"incompatible\",\"a\":60,\"b\":23},{\"tag\":\"incompatible\",\"a\":60,\"b\":46},{\"tag\":\"incompatible\",\"a\":60,\"b\":50},{\"tag\":\"incompatible\",\"a\":64,\"b\":43},{\"tag\":\"incompatible\",\"a\":65,\"b\":44},{\"tag\":\"incompatible\",\"a\":66,\"b\":60},{\"tag\":\"incompatible\",\"a\":67,\"b\":43},{\"tag\":\"incompatible\",\"a\":68,\"b\":64},{\"tag\":\"incompatible\",\"a\":68,\"b\":65},{\"tag\":\"incompatible\",\"a\":68,\"b\":66},{\"tag\":\"incompatible\",\"a\":68,\"b\":67},{\"tag\":\"incompatible\",\"a\":71,\"b\":60},{\"tag\":\"incompatible\",\"a\":74,\"b\":45},{\"tag\":\"incompatible\",\"a\":74,\"b\":46},{\"tag\":\"incompatible\",\"a\":74,\"b\":66},{\"tag\":\"incompatible\",\"a\":74,\"b\":67},{\"tag\":\"incompatible\",\"a\":74,\"b\":68},{\"tag\":\"incompatible\",\"a\":78,\"b\":13},{\"tag\":\"incompatible\",\"a\":78,\"b\":45},{\"tag\":\"incompatible\",\"a\":78,\"b\":57},{\"tag\":\"incompatible\",\"a\":78,\"b\":60},{\"tag\":\"incompatible\",\"a\":78,\"b\":66},{\"tag\":\"incompatible\",\"a\":78,\"b\":67},{\"tag\":\"incompatible\",\"a\":78,\"b\":68},{\"tag\":\"incompatible\",\"a\":78,\"b\":71},{\"tag\":\"incompatible\",\"a\":79,\"b\":40},{\"tag\":\"incompatible\",\"a\":79,\"b\":68},{\"tag\":\"incompatible\",\"a\":79,\"b\":72},{\"tag\":\"incompatible\",\"a\":83,\"b\":43},{\"tag\":\"incompatible\",\"a\":83,\"b\":51},{\"tag\":\"incompatible\",\"a\":84,\"b\":44},{\"tag\":\"incompatible\",\"a\":84,\"b\":53},{\"tag\":\"incompatible\",\"a\":84,\"b\":65},{\"tag\":\"incompatible\",\"a\":85,\"b\":34},{\"tag\":\"incompatible\",\"a\":85,\"b\":74},{\"tag\":\"incompatible\",\"a\":87,\"b\":40},{\"tag\":\"incompatible\",\"a\":88,\"b\":39},{\"tag\":\"incompatible\",\"a\":88,\"b\":66},{\"tag\":\"incompatible\",\"a\":88,\"b\":85},{\"tag\":\"incompatible\",\"a\":96,\"b\":74},{\"tag\":\"incompatible\",\"a\":96,\"b\":79},{\"tag\":\"mate\",\"ridge\":131,\"a\":40,\"owners\":[7,13,51,53,60]},{\"tag\":\"mate\",\"ridge\":131,\"a\":44,\"owners\":[7,13,51,57,58,60]},{\"tag\":\"three\",\"ridge\":133,\"vertices\":[21,43,65]},{\"tag\":\"three\",\"ridge\":133,\"vertices\":[43,65,74]},{\"tag\":\"three\",\"ridge\":133,\"vertices\":[44,64,74]},{\"tag\":\"three\",\"ridge\":134,\"vertices\":[43,85,87]},{\"tag\":\"three\",\"ridge\":134,\"vertices\":[44,83,89]},{\"tag\":\"three\",\"ridge\":134,\"vertices\":[44,85,87]},{\"tag\":\"three\",\"ridge\":138,\"vertices\":[7,34,83]},{\"tag\":\"three\",\"ridge\":138,\"vertices\":[7,34,84]},{\"tag\":\"three\",\"ridge\":138,\"vertices\":[34,51,84]},{\"tag\":\"three\",\"ridge\":138,\"vertices\":[34,53,83]},{\"tag\":\"mate\",\"ridge\":265,\"a\":8,\"owners\":[23,63,66,68,76,77,78]},{\"tag\":\"mate\",\"ridge\":265,\"a\":39,\"owners\":[23,76,77,78]},{\"tag\":\"mate\",\"ridge\":265,\"a\":52,\"owners\":[23,63,66,68,77,78]},{\"tag\":\"mate\",\"ridge\":265,\"a\":54,\"owners\":[23,63,66,68,76,78]},{\"tag\":\"mate\",\"ridge\":266,\"a\":8,\"owners\":[34,82,85,91,92]},{\"tag\":\"mate\",\"ridge\":266,\"a\":39,\"owners\":[34,91,92]},{\"tag\":\"mate\",\"ridge\":266,\"a\":50,\"owners\":[34,85]},{\"tag\":\"mate\",\"ridge\":266,\"a\":52,\"owners\":[34,82,85,92]},{\"tag\":\"mate\",\"ridge\":266,\"a\":54,\"owners\":[34,82,85,91]},{\"tag\":\"three\",\"ridge\":385,\"vertices\":[23,45,79]},{\"tag\":\"mate\",\"ridge\":386,\"a\":86,\"owners\":[13,34,60]},{\"tag\":\"mate\",\"ridge\":386,\"a\":89,\"owners\":[13,34,57]},{\"tag\":\"mate\",\"ridge\":532,\"a\":42,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":532,\"a\":69,\"owners\":[87,88,96]},{\"tag\":\"mate\",\"ridge\":532,\"a\":70,\"owners\":[87,88,96]},{\"tag\":\"mate\",\"ridge\":532,\"a\":72,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":532,\"a\":73,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":644,\"a\":46,\"owners\":[95,96]},{\"tag\":\"mate\",\"ridge\":644,\"a\":74,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":644,\"a\":89,\"owners\":[21,67,72]},{\"tag\":\"mate\",\"ridge\":392,\"a\":23,\"owners\":[34,85,95]},{\"tag\":\"mate\",\"ridge\":392,\"a\":34,\"owners\":[23,66,78,95]},{\"tag\":\"mate\",\"ridge\":392,\"a\":66,\"owners\":[34]},{\"tag\":\"mate\",\"ridge\":392,\"a\":78,\"owners\":[34,85]},{\"tag\":\"mate\",\"ridge\":392,\"a\":85,\"owners\":[23,78]},{\"tag\":\"mate\",\"ridge\":784,\"a\":79,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":896,\"a\":60,\"owners\":[95,96]},{\"tag\":\"mate\",\"ridge\":896,\"a\":74,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":896,\"a\":78,\"owners\":[89,93,96]},{\"tag\":\"mate\",\"ridge\":896,\"a\":79,\"owners\":[89,95]},{\"tag\":\"mate\",\"ridge\":774,\"a\":88,\"owners\":[47,89]},{\"tag\":\"mate\",\"ridge\":780,\"a\":95,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":404,\"a\":96,\"owners\":[71,86]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[60,74,78,79],\"full_literals\":[-52,22,34,37,38]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[42,69,70,72,73],\"full_literals\":[-53,9,29,30,32,33]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[39,83,84,85],\"full_literals\":[-54,7,40,41,42]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[46,64,65,66,67],\"full_literals\":[-55,13,24,25,26,27]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[40,43,44,45],\"full_literals\":[-56,8,10,11,12]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-57,52,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-57,false,53],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-58,54,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-59,57,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-59,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-60,55,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-60,false,56],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-61,false,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-62,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-62,false,61],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":63,\"full_literals\":[-23,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":76,\"full_literals\":[-35,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":77,\"full_literals\":[-36,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":82,\"full_literals\":[-39,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":91,\"full_literals\":[-47,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":92,\"full_literals\":[-48,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":47,\"full_literals\":[-14,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":58,\"full_literals\":[-21,65]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[86,87,88],\"full_literals\":[-66,43,44,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":86,\"full_literals\":[-43,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":87,\"full_literals\":[-44,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":88,\"full_literals\":[-45,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":89,\"full_literals\":[-46,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":93,\"full_literals\":[-49,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":96,\"full_literals\":[-51,67]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[68],\"full_literals\":[-68,28]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[95],\"full_literals\":[-69,50]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-65,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-64,false,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-70,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-72,66,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-66,-67,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-73,68,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-74,72,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-72,false,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-71,-74,75],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":28,\"owners\":[8,23,34,39,50,52,54,63,66,68,76,77,78,82,85,91,92,95]}]}"
  "136 59 0 106 104 0\n137 61 0 106 105 0\n138 57 0 136 99 0\n139 58 0 136 100 0\n140 60 0 137 103 0\n141 52 0 138 96 0\n142 53 0 138 97 0\n143 54 0 139 98 0\n144 55 0 140 101 0\n145 56 0 140 102 0\n146 -28 0 144 141 12 13 14 15 21 28 31 94 91 6 0\n147 -50 0 146 89 0\n148 -68 0 146 122 0\n149 -69 0 147 123 0\n150 -73 0 148 149 130 0\n151 27 -10 26 13 -46 32 0 144 8 77 48 94 0\n152 -10 32 26 13 -46 0 151 11 0\n153 -10 42 -37 0 144 143 27 26 2 4 8 33 94 93 37 0\n154 -40 -6 -37 22 21 0 145 38 153 24 23 22 34 57 54 47 46 95 0\n155 -41 -6 -37 22 0 145 38 153 23 22 35 36 56 55 95 46 0\n156 -6 -37 22 21 0 143 145 23 38 153 154 155 93 1 3 95 0\n157 -37 22 -74 0 150 134 145 133 126 124 114 113 131 128 22 23 24 156 69 68 81 88 115 51 40 53 95 0\n158 -42 37 22 0 141 39 43 91 83 0\n159 6 42 37 71 0 147 146 126 125 112 111 110 127 109 108 107 63 80 65 66 62 64 78 135 0\n160 -11 -34 26 0 144 20 18 9 50 94 0\n161 -34 26 0 145 144 17 18 20 76 40 160 95 8 49 94 0\n162 26 7 -6 37 22 0 141 147 145 143 158 79 161 91 30 32 45 87 67 75 152 95 35 52 93 0\n163 -26 37 22 0 141 19 42 91 83 0\n164 22 -74 0 134 141 133 157 158 159 163 161 162 91 41 83 0\n165 -74 0 134 147 146 133 126 127 125 107 108 109 110 111 112 164 5 7 10 25 58 82 59 61 60 79 135 0\n166 -72 0 165 132 0\n167 -51 31 0 166 90 121 116 129 0\n168 -22 0 147 16 84 167 0\n169 -38 0 147 166 83 87 118 119 129 0\n170 67 51 0 168 169 141 119 120 85 86 91 0\n171 51 0 166 142 70 170 129 117 118 74 73 71 72 92 0\n172 -34 0 171 44 0\n173 31 0 171 167 0\n174 37 0 172 141 169 168 91 0\n175 0 174 173 29 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record006.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record006.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record006.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record006.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record006 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record006.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record006.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record006.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record006.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record006 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record006_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record006 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record006_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record006_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00018.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00018.record007
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1f392e295a4e87aa5996638ce2b91e1783ee4789565391e6956558d334ad4745d0f69364e5354e334cf0ba2d4b32d2b2ad1b16c3ba1d8731ca785d1725d0f07c741b382c48726286a198560d88e1382ee07111c5891a465154352344d0b703a0d8318e1344c530cd0b22c4b0ac8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "49369b4934926d3692692492492492492492491249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record007 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record007 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record007.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 43), (facetIndex 63), (facetIndex 64), (facetIndex 77), (facetIndex 90)]))
 (.leaf ([(facetIndex 48), (facetIndex 57), (facetIndex 58), (facetIndex 76), (facetIndex 89)])))
 (.branch 3
 (.leaf ([(facetIndex 42), (facetIndex 68), (facetIndex 69), (facetIndex 70)]))
 (.leaf ([(facetIndex 81), (facetIndex 82), (facetIndex 83)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 41), (facetIndex 50), (facetIndex 51), (facetIndex 52), (facetIndex 65), (facetIndex 66), (facetIndex 73), (facetIndex 78), (facetIndex 79), (facetIndex 86), (facetIndex 91)]))
 (.leaf ([(facetIndex 45), (facetIndex 46), (facetIndex 47), (facetIndex 49)])))
 (.branch 7
 (.leaf ([(facetIndex 53), (facetIndex 54), (facetIndex 55), (facetIndex 56)]))
 (.leaf ([(facetIndex 44), (facetIndex 59), (facetIndex 60), (facetIndex 61), (facetIndex 62)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "8081006d89010200921201ffe4edb4929b6f0az1f;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 71), (facetIndex 72)]))
 (.leaf ([(facetIndex 84), (facetIndex 85)])))
 (.branch 3
 (.leaf ([(facetIndex 67), (facetIndex 74), (facetIndex 75)]))
 (.leaf ([(facetIndex 80), (facetIndex 87), (facetIndex 88)]))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨2, sparse_nat% "3c50300a0008z21;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 4
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
def grouped2_0008 : List Nat := [4, 5, 6, 7]
def grouped2_0009 : List Nat := [5]
def grouped2_0010 : List Nat := [6, 7]
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1]
def grouped3_0014 : List Nat := [1]
def grouped3_0015 : List Nat := [2]
def grouped3_0016 : List Nat := [2, 3]
def grouped3_0017 : List Nat := [3]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record007 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record007_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00018.record007" "{\"atoms\":[{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00018.record007" 37

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00018.record007" "{\"ridges\":[[80,284],[87,312],[88,344]],\"owners\":[[80,284,[67],[]],[87,312,[74],[]],[88,344,[75],[]]],\"edges\":[],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00018.record007" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00018.record007\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-10,-1],[-10,-3],[-10,-4],[-10,-5],[-10,-8],[-10,-9],[-11,-2],[-11,-6],[-11,-7],[-12,-2],[-12,-6],[-12,-7],[-13,-10],[-14,-1],[-14,-3],[-14,-4],[-14,-5],[-14,-8],[-14,-9],[-14,-13],[-15,-1],[-15,-3],[-15,-4],[-15,-5],[-15,-8],[-15,-9],[-15,-13],[-16,-11],[-16,-12],[-17,-10],[-17,-14],[-17,-15],[-18,-10],[-18,-14],[-18,-15],[-20,-10],[-20,-14],[-20,-15],[-23,-11],[-23,-12],[-24,-10],[-24,-14],[-24,-15],[-19,10],[-21,14],[-22,15],[-25,2,6,7,16,23],[-26,1,3,4,5,8,9,13,17,18,20,24],[-27,25],[-28,27],[-29,26],[-30,29],[-31,28],[-31,30],[31],[-32,11,12],[-33,10,14,15],[-34,19,21,22],[-35,32],[-36,33,34],[-37,35,36],[37]],\"atoms\":[{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":67,\"b\":41},{\"tag\":\"incompatible\",\"a\":67,\"b\":50},{\"tag\":\"incompatible\",\"a\":67,\"b\":51},{\"tag\":\"incompatible\",\"a\":67,\"b\":52},{\"tag\":\"incompatible\",\"a\":67,\"b\":65},{\"tag\":\"incompatible\",\"a\":67,\"b\":66},{\"tag\":\"incompatible\",\"a\":71,\"b\":43},{\"tag\":\"incompatible\",\"a\":71,\"b\":63},{\"tag\":\"incompatible\",\"a\":71,\"b\":64},{\"tag\":\"incompatible\",\"a\":72,\"b\":43},{\"tag\":\"incompatible\",\"a\":72,\"b\":63},{\"tag\":\"incompatible\",\"a\":72,\"b\":64},{\"tag\":\"incompatible\",\"a\":73,\"b\":67},{\"tag\":\"incompatible\",\"a\":74,\"b\":41},{\"tag\":\"incompatible\",\"a\":74,\"b\":50},{\"tag\":\"incompatible\",\"a\":74,\"b\":51},{\"tag\":\"incompatible\",\"a\":74,\"b\":52},{\"tag\":\"incompatible\",\"a\":74,\"b\":65},{\"tag\":\"incompatible\",\"a\":74,\"b\":66},{\"tag\":\"incompatible\",\"a\":74,\"b\":73},{\"tag\":\"incompatible\",\"a\":75,\"b\":41},{\"tag\":\"incompatible\",\"a\":75,\"b\":50},{\"tag\":\"incompatible\",\"a\":75,\"b\":51},{\"tag\":\"incompatible\",\"a\":75,\"b\":52},{\"tag\":\"incompatible\",\"a\":75,\"b\":65},{\"tag\":\"incompatible\",\"a\":75,\"b\":66},{\"tag\":\"incompatible\",\"a\":75,\"b\":73},{\"tag\":\"incompatible\",\"a\":77,\"b\":71},{\"tag\":\"incompatible\",\"a\":77,\"b\":72},{\"tag\":\"incompatible\",\"a\":78,\"b\":67},{\"tag\":\"incompatible\",\"a\":78,\"b\":74},{\"tag\":\"incompatible\",\"a\":78,\"b\":75},{\"tag\":\"incompatible\",\"a\":79,\"b\":67},{\"tag\":\"incompatible\",\"a\":79,\"b\":74},{\"tag\":\"incompatible\",\"a\":79,\"b\":75},{\"tag\":\"incompatible\",\"a\":86,\"b\":67},{\"tag\":\"incompatible\",\"a\":86,\"b\":74},{\"tag\":\"incompatible\",\"a\":86,\"b\":75},{\"tag\":\"incompatible\",\"a\":90,\"b\":71},{\"tag\":\"incompatible\",\"a\":90,\"b\":72},{\"tag\":\"incompatible\",\"a\":91,\"b\":67},{\"tag\":\"incompatible\",\"a\":91,\"b\":74},{\"tag\":\"incompatible\",\"a\":91,\"b\":75},{\"tag\":\"mate\",\"ridge\":284,\"a\":80,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":312,\"a\":87,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":344,\"a\":88,\"owners\":[75]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[43,63,64,77,90],\"full_literals\":[-25,2,6,7,16,23]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[41,50,51,52,65,66,73,78,79,86,91],\"full_literals\":[-26,1,3,4,5,8,9,13,17,18,20,24]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-27,25,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-28,27,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-29,26,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-30,29,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-31,28,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-31,false,30],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[71,72],\"full_literals\":[-32,11,12]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[67,74,75],\"full_literals\":[-33,10,14,15]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[80,87,88],\"full_literals\":[-34,19,21,22]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-35,32,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-36,33,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-37,35,36],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true}]}"
  "63 28 0 55 53 0\n64 30 0 55 54 0\n65 27 0 63 50 0\n66 29 0 64 52 0\n67 25 0 65 49 0\n68 26 0 66 51 0\n69 -14 8 4 0 68 14 15 17 19 20 31 34 37 42 48 0\n70 -15 9 0 68 21 22 23 24 25 27 32 35 38 43 48 0\n71 -14 0 16 18 69 0\n72 -21 0 71 45 0\n73 -15 0 26 70 0\n74 -22 0 73 46 0\n75 -10 0 68 1 2 3 4 5 6 13 30 33 36 41 48 0\n76 -19 0 75 44 0\n77 -33 0 75 73 71 57 0\n78 -34 0 76 74 72 58 0\n79 -36 0 77 78 60 0\n80 35 0 79 62 61 0\n81 32 0 80 59 0\n82 -11 0 67 7 8 9 28 39 47 0\n83 12 0 82 81 56 0\n84 -2 0 83 10 0\n85 -6 0 83 11 0\n86 -7 0 83 12 0\n87 -16 0 83 29 0\n88 -23 0 83 40 0\n89 0 87 85 67 84 86 88 47 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record007.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record007.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record007.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record007.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record007 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record007.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record007.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record007.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record007.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record007 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record007_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record007 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record007_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record007_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00018.record007
