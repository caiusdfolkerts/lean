module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00173Data
public import GraphInputsRow24Part00173Frames
public import GraphInputsRow24Part00173Leaves
public import GraphInputsRow24Part00173Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00173.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record001
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨87, by decide⟩, ⟨93, by decide⟩, ⟨95, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), (certNat% 6), 15187004358656, 7775746231631872]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record001_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00173.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00173.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record003
def vertexColumn : Fields := ⟨10, (certNat% 7)⟩
def kindColumn : Fields := ⟨3, (certNat% 8)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨100, by decide⟩, ⟨104, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), (certNat% 10), (certNat% 11), 8787503087616, 17996806323437568, (certNat% 12), (certNat% 13)]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record003_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00173.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00173.record009
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record009
def vertexColumn : Fields := ⟨10, (certNat% 14)⟩
def kindColumn : Fields := ⟨3, (certNat% 15)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨73, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨96, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), (certNat% 17), (certNat% 18), 8786429345792, 16879702509617152, 9205357638345293824]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record009_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record009_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00173.record009

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00173.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record010
def vertexColumn : Fields := ⟨10, (certNat% 19)⟩
def kindColumn : Fields := ⟨3, (certNat% 20)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨69, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨97, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), (certNat% 22), (certNat% 23), (certNat% 24), 4389456576512, 35958428274786304]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record010_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00173.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00173.record000
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "370da4eb26a5a5635a362d8766394e3392e8789e1783e36539c9695954d58d4b51d58d534cd4b61d2745d0f723a4e5334d332cc7362d4b32d2b86d1b0ef07a1d8791d4731ca719e1725c570de0f0bc1f8c89a16a264990e2384e8c499166254950d2344d88d2384c9314c3342c8b12c1b81d0721c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "69a6da6d249a4d34db4da49349a492492492492492492492249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record000 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record000 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record000.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record000.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record000.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 33), (facetIndex 35), (facetIndex 39), (facetIndex 40), (facetIndex 46), (facetIndex 60), (facetIndex 75), (facetIndex 92)]))
 (.leaf ([(facetIndex 65), (facetIndex 66), (facetIndex 67), (facetIndex 68)])))
 (.branch 3
 (.leaf ([(facetIndex 82), (facetIndex 83), (facetIndex 84), (facetIndex 85)]))
 (.leaf ([(facetIndex 32), (facetIndex 47), (facetIndex 48), (facetIndex 49), (facetIndex 51), (facetIndex 57), (facetIndex 77), (facetIndex 94)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 36), (facetIndex 37), (facetIndex 38), (facetIndex 62), (facetIndex 63), (facetIndex 71), (facetIndex 79), (facetIndex 80), (facetIndex 88)]))
 (.leaf ([(facetIndex 54), (facetIndex 55), (facetIndex 56), (facetIndex 58), (facetIndex 59)])))
 (.branch 7
 (.leaf ([(facetIndex 34), (facetIndex 41), (facetIndex 42), (facetIndex 43), (facetIndex 44), (facetIndex 45)]))
 (.leaf ([(facetIndex 50), (facetIndex 52), (facetIndex 53)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "c0004012484818000801248900b5db7f7db636db0124183z18;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 61), (facetIndex 76)]))
 (.leaf ([(facetIndex 78), (facetIndex 93)])))
 (.branch 3
 (.leaf ([(facetIndex 64), (facetIndex 69), (facetIndex 70), (facetIndex 72), (facetIndex 73), (facetIndex 74)]))
 (.branch 4
 (.leaf ([(facetIndex 81), (facetIndex 86), (facetIndex 87), (facetIndex 89), (facetIndex 90), (facetIndex 91)]))
 (.leaf ([(facetIndex 95)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "8086d86c0018040092090002z30;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 5
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
def grouped3_0018 : List Nat := [1]
def grouped3_0019 : List Nat := [2]
def grouped3_0020 : List Nat := [2, 3, 4]
def grouped3_0021 : List Nat := [3]
def grouped3_0022 : List Nat := [3, 4]
def grouped3_0023 : List Nat := [4]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record000 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record000_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00173.record000" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00173.record000" 75

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00173.record000" "{\"ridges\":[[11,81],[12,145],[21,25],[22,25],[23,49],[29,88],[30,152],[31,50],[54,49],[54,50],[55,49],[55,50],[57,81],[57,145],[58,81],[59,145],[71,560],[76,25],[76,49],[81,540],[86,116],[87,180],[88,560],[89,212],[90,596],[91,660],[93,50]],\"owners\":[[11,81,[21,62,69,72,73,77],[36,54,57,58]],[57,81,[21,62,69,73],[11,36,54,58,72,77]],[58,81,[21,62,69,72,77],[11,36,54,57,73]],[12,145,[22,63,70,72,74,77],[37,55,57,59]],[57,145,[22,63,70,74],[12,37,55,59,72,77]],[59,145,[22,63,70,72,77],[12,37,55,57,74]],[29,88,[21,62,77,95],[79,94]],[30,152,[22,63,77,95],[80,94]],[71,560,[31],[23,88]],[88,560,[23],[31,71]],[81,540,[64],[]],[86,116,[69],[]],[87,180,[70],[]],[89,212,[72,95],[]],[90,596,[73],[]],[91,660,[74],[]]],\"edges\":[[31,[11,21,29,36,54,57,58,62,69,72,73,77,79,86,89,90,94,95]],[32,[12,22,30,37,55,57,59,63,70,72,74,77,80,87,89,91,94,95]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00173.record000" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00173.record000\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-10,-9],[-11,-9],[-12,-9],[-13,-10],[-13,-11],[-13,-12],[-14,-10],[-14,-11],[-14,-12],[-15,-10],[-15,-11],[-15,-12],[-16,-10],[-16,-11],[-16,-12],[-17,-10],[-17,-11],[-17,-12],[-24,-23],[-25,-23],[-26,-10],[-26,-11],[-26,-12],[-26,-24],[-26,-25],[-28,-24],[-28,-25],[-29,-24],[-29,-25],[-30,-24],[-30,-25],[-31,-10],[-31,-11],[-31,-12],[-31,-24],[-31,-25],[-32,-10],[-32,-11],[-32,-12],[-32,-24],[-32,-25],[-33,-23],[-33,-26],[-33,-31],[-33,-32],[-34,-10],[-34,-11],[-34,-12],[-34,-24],[-34,-25],[-34,-33],[-35,-10],[-35,-11],[-35,-12],[-35,-24],[-35,-25],[-35,-33],[-36,-10],[-36,-11],[-36,-12],[-36,-24],[-36,-25],[-36,-33],[-37,-27],[-38,-37],[-39,-33],[-40,-23],[-40,-26],[-40,-31],[-40,-32],[-40,-34],[-40,-35],[-40,-36],[-41,-23],[-41,-26],[-41,-31],[-41,-32],[-41,-34],[-41,-35],[-41,-36],[-43,-37],[-44,-40],[-44,-41],[-45,-40],[-45,-41],[-46,-40],[-46,-41],[-49,-23],[-49,-26],[-49,-31],[-49,-32],[-49,-34],[-49,-35],[-49,-36],[-49,-39],[-54,-53],[-55,-10],[-55,-11],[-55,-12],[-55,-24],[-55,-25],[-55,-33],[-55,-40],[-55,-41],[-55,-49],[-3,-4,-37],[-5,-18,-37],[-5,-19,-37],[-8,-18,-53],[-8,-19,-53],[-1,3,24,31,34,35,38],[-20,3,24,31,35],[-21,3,24,31,34,38],[-2,4,25,32,34,36,38],[-20,4,25,32,36],[-22,4,25,32,34,38],[-6,3,24,38,55],[-7,4,25,38,55],[-33,8],[-49,5],[-42,26],[-47,31],[-48,32],[-50,34,55],[-51,35],[-52,36],[-56,27,28,29,30],[-57,43,44,45,46],[-58,10,11,12,24,25,33,40,41,49],[-59,9,13,14,15,16,17],[-60,56],[-61,57],[-62,60],[-62,61],[-63,58],[-64,59],[-65,63],[-65,64],[-66,62],[-66,65],[66],[-67,23,37],[-68,39,53],[-69,26,31,32,34,35,36],[-26,69],[-31,69],[-32,69],[-34,69],[-35,69],[-36,69],[-70,42,47,48,50,51,52],[-71,55],[-72,67],[-72,68],[-73,70,71],[-74,69,73],[-75,72,74],[75],[1,3,6,10,18,20,21,24,31,34,35,38,40,47,50,51,54,55],[2,4,7,11,19,20,22,25,32,34,36,38,41,48,50,52,54,55]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":36,\"b\":34},{\"tag\":\"incompatible\",\"a\":37,\"b\":34},{\"tag\":\"incompatible\",\"a\":38,\"b\":34},{\"tag\":\"incompatible\",\"a\":41,\"b\":36},{\"tag\":\"incompatible\",\"a\":41,\"b\":37},{\"tag\":\"incompatible\",\"a\":41,\"b\":38},{\"tag\":\"incompatible\",\"a\":42,\"b\":36},{\"tag\":\"incompatible\",\"a\":42,\"b\":37},{\"tag\":\"incompatible\",\"a\":42,\"b\":38},{\"tag\":\"incompatible\",\"a\":43,\"b\":36},{\"tag\":\"incompatible\",\"a\":43,\"b\":37},{\"tag\":\"incompatible\",\"a\":43,\"b\":38},{\"tag\":\"incompatible\",\"a\":44,\"b\":36},{\"tag\":\"incompatible\",\"a\":44,\"b\":37},{\"tag\":\"incompatible\",\"a\":44,\"b\":38},{\"tag\":\"incompatible\",\"a\":45,\"b\":36},{\"tag\":\"incompatible\",\"a\":45,\"b\":37},{\"tag\":\"incompatible\",\"a\":45,\"b\":38},{\"tag\":\"incompatible\",\"a\":62,\"b\":61},{\"tag\":\"incompatible\",\"a\":63,\"b\":61},{\"tag\":\"incompatible\",\"a\":64,\"b\":36},{\"tag\":\"incompatible\",\"a\":64,\"b\":37},{\"tag\":\"incompatible\",\"a\":64,\"b\":38},{\"tag\":\"incompatible\",\"a\":64,\"b\":62},{\"tag\":\"incompatible\",\"a\":64,\"b\":63},{\"tag\":\"incompatible\",\"a\":66,\"b\":62},{\"tag\":\"incompatible\",\"a\":66,\"b\":63},{\"tag\":\"incompatible\",\"a\":67,\"b\":62},{\"tag\":\"incompatible\",\"a\":67,\"b\":63},{\"tag\":\"incompatible\",\"a\":68,\"b\":62},{\"tag\":\"incompatible\",\"a\":68,\"b\":63},{\"tag\":\"incompatible\",\"a\":69,\"b\":36},{\"tag\":\"incompatible\",\"a\":69,\"b\":37},{\"tag\":\"incompatible\",\"a\":69,\"b\":38},{\"tag\":\"incompatible\",\"a\":69,\"b\":62},{\"tag\":\"incompatible\",\"a\":69,\"b\":63},{\"tag\":\"incompatible\",\"a\":70,\"b\":36},{\"tag\":\"incompatible\",\"a\":70,\"b\":37},{\"tag\":\"incompatible\",\"a\":70,\"b\":38},{\"tag\":\"incompatible\",\"a\":70,\"b\":62},{\"tag\":\"incompatible\",\"a\":70,\"b\":63},{\"tag\":\"incompatible\",\"a\":71,\"b\":61},{\"tag\":\"incompatible\",\"a\":71,\"b\":64},{\"tag\":\"incompatible\",\"a\":71,\"b\":69},{\"tag\":\"incompatible\",\"a\":71,\"b\":70},{\"tag\":\"incompatible\",\"a\":72,\"b\":36},{\"tag\":\"incompatible\",\"a\":72,\"b\":37},{\"tag\":\"incompatible\",\"a\":72,\"b\":38},{\"tag\":\"incompatible\",\"a\":72,\"b\":62},{\"tag\":\"incompatible\",\"a\":72,\"b\":63},{\"tag\":\"incompatible\",\"a\":72,\"b\":71},{\"tag\":\"incompatible\",\"a\":73,\"b\":36},{\"tag\":\"incompatible\",\"a\":73,\"b\":37},{\"tag\":\"incompatible\",\"a\":73,\"b\":38},{\"tag\":\"incompatible\",\"a\":73,\"b\":62},{\"tag\":\"incompatible\",\"a\":73,\"b\":63},{\"tag\":\"incompatible\",\"a\":73,\"b\":71},{\"tag\":\"incompatible\",\"a\":74,\"b\":36},{\"tag\":\"incompatible\",\"a\":74,\"b\":37},{\"tag\":\"incompatible\",\"a\":74,\"b\":38},{\"tag\":\"incompatible\",\"a\":74,\"b\":62},{\"tag\":\"incompatible\",\"a\":74,\"b\":63},{\"tag\":\"incompatible\",\"a\":74,\"b\":71},{\"tag\":\"incompatible\",\"a\":76,\"b\":65},{\"tag\":\"incompatible\",\"a\":77,\"b\":76},{\"tag\":\"incompatible\",\"a\":78,\"b\":71},{\"tag\":\"incompatible\",\"a\":79,\"b\":61},{\"tag\":\"incompatible\",\"a\":79,\"b\":64},{\"tag\":\"incompatible\",\"a\":79,\"b\":69},{\"tag\":\"incompatible\",\"a\":79,\"b\":70},{\"tag\":\"incompatible\",\"a\":79,\"b\":72},{\"tag\":\"incompatible\",\"a\":79,\"b\":73},{\"tag\":\"incompatible\",\"a\":79,\"b\":74},{\"tag\":\"incompatible\",\"a\":80,\"b\":61},{\"tag\":\"incompatible\",\"a\":80,\"b\":64},{\"tag\":\"incompatible\",\"a\":80,\"b\":69},{\"tag\":\"incompatible\",\"a\":80,\"b\":70},{\"tag\":\"incompatible\",\"a\":80,\"b\":72},{\"tag\":\"incompatible\",\"a\":80,\"b\":73},{\"tag\":\"incompatible\",\"a\":80,\"b\":74},{\"tag\":\"incompatible\",\"a\":82,\"b\":76},{\"tag\":\"incompatible\",\"a\":83,\"b\":79},{\"tag\":\"incompatible\",\"a\":83,\"b\":80},{\"tag\":\"incompatible\",\"a\":84,\"b\":79},{\"tag\":\"incompatible\",\"a\":84,\"b\":80},{\"tag\":\"incompatible\",\"a\":85,\"b\":79},{\"tag\":\"incompatible\",\"a\":85,\"b\":80},{\"tag\":\"incompatible\",\"a\":88,\"b\":61},{\"tag\":\"incompatible\",\"a\":88,\"b\":64},{\"tag\":\"incompatible\",\"a\":88,\"b\":69},{\"tag\":\"incompatible\",\"a\":88,\"b\":70},{\"tag\":\"incompatible\",\"a\":88,\"b\":72},{\"tag\":\"incompatible\",\"a\":88,\"b\":73},{\"tag\":\"incompatible\",\"a\":88,\"b\":74},{\"tag\":\"incompatible\",\"a\":88,\"b\":78},{\"tag\":\"incompatible\",\"a\":94,\"b\":93},{\"tag\":\"incompatible\",\"a\":95,\"b\":36},{\"tag\":\"incompatible\",\"a\":95,\"b\":37},{\"tag\":\"incompatible\",\"a\":95,\"b\":38},{\"tag\":\"incompatible\",\"a\":95,\"b\":62},{\"tag\":\"incompatible\",\"a\":95,\"b\":63},{\"tag\":\"incompatible\",\"a\":95,\"b\":71},{\"tag\":\"incompatible\",\"a\":95,\"b\":79},{\"tag\":\"incompatible\",\"a\":95,\"b\":80},{\"tag\":\"incompatible\",\"a\":95,\"b\":88},{\"tag\":\"three\",\"ridge\":25,\"vertices\":[21,22,76]},{\"tag\":\"three\",\"ridge\":49,\"vertices\":[23,54,76]},{\"tag\":\"three\",\"ridge\":49,\"vertices\":[23,55,76]},{\"tag\":\"three\",\"ridge\":50,\"vertices\":[31,54,93]},{\"tag\":\"three\",\"ridge\":50,\"vertices\":[31,55,93]},{\"tag\":\"mate\",\"ridge\":81,\"a\":11,\"owners\":[21,62,69,72,73,77]},{\"tag\":\"mate\",\"ridge\":81,\"a\":57,\"owners\":[21,62,69,73]},{\"tag\":\"mate\",\"ridge\":81,\"a\":58,\"owners\":[21,62,69,72,77]},{\"tag\":\"mate\",\"ridge\":145,\"a\":12,\"owners\":[22,63,70,72,74,77]},{\"tag\":\"mate\",\"ridge\":145,\"a\":57,\"owners\":[22,63,70,74]},{\"tag\":\"mate\",\"ridge\":145,\"a\":59,\"owners\":[22,63,70,72,77]},{\"tag\":\"mate\",\"ridge\":88,\"a\":29,\"owners\":[21,62,77,95]},{\"tag\":\"mate\",\"ridge\":152,\"a\":30,\"owners\":[22,63,77,95]},{\"tag\":\"mate\",\"ridge\":560,\"a\":71,\"owners\":[31]},{\"tag\":\"mate\",\"ridge\":560,\"a\":88,\"owners\":[23]},{\"tag\":\"mate\",\"ridge\":540,\"a\":81,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":116,\"a\":86,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":180,\"a\":87,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":212,\"a\":89,\"owners\":[72,95]},{\"tag\":\"mate\",\"ridge\":596,\"a\":90,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":660,\"a\":91,\"owners\":[74]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[65,66,67,68],\"full_literals\":[-56,27,28,29,30]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[82,83,84,85],\"full_literals\":[-57,43,44,45,46]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[36,37,38,62,63,71,79,80,88],\"full_literals\":[-58,10,11,12,24,25,33,40,41,49]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[34,41,42,43,44,45],\"full_literals\":[-59,9,13,14,15,16,17]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-60,false,56],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-61,57,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-62,60,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-62,false,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-63,58,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-64,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-65,63,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-65,false,64],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-66,62,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-66,false,65],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[61,76],\"full_literals\":[-67,23,37]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[78,93],\"full_literals\":[-68,39,53]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[64,69,70,72,73,74],\"full_literals\":[-69,26,31,32,34,35,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":64,\"full_literals\":[-26,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":69,\"full_literals\":[-31,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":70,\"full_literals\":[-32,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":72,\"full_literals\":[-34,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":73,\"full_literals\":[-35,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":74,\"full_literals\":[-36,69]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[81,86,87,89,90,91],\"full_literals\":[-70,42,47,48,50,51,52]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[95],\"full_literals\":[-71,55]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-72,67,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-72,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-73,70,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-74,69,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-75,72,74],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":31,\"owners\":[11,21,29,36,54,57,58,62,69,72,73,77,79,86,89,90,94,95]},{\"tag\":\"edge\",\"edge\":32,\"owners\":[12,22,30,37,55,57,59,63,70,72,74,77,80,87,89,91,94,95]}]}"
  "161 62 0 141 139 0\n162 65 0 141 140 0\n163 60 0 161 133 0\n164 61 0 161 134 0\n165 63 0 162 137 0\n166 64 0 162 138 0\n167 56 0 163 131 0\n168 57 0 164 132 0\n169 58 0 165 135 0\n170 59 0 166 136 0\n171 -55 0 169 97 98 99 100 101 102 103 104 105 129 0\n172 -71 0 171 152 0\n173 -24 35 34 36 -69 0 24 35 40 144 0\n174 -25 35 34 36 -69 0 25 36 41 144 0\n175 -40 35 34 36 -69 0 68 69 70 144 0\n176 -33 -69 0 43 44 45 51 57 63 144 0\n177 -26 40 25 24 33 0 169 21 22 23 75 89 129 0\n178 -31 40 25 24 33 0 169 32 33 34 76 90 129 0\n179 34 35 36 -69 0 169 176 173 174 175 177 178 144 37 38 39 77 91 129 0\n180 -34 33 0 169 46 47 48 49 50 71 78 92 129 0\n181 -35 33 0 169 52 53 54 55 56 72 79 93 129 0\n182 -69 0 169 176 180 181 179 58 59 60 61 62 73 80 94 129 0\n183 -26 0 182 145 0\n184 -31 0 182 146 0\n185 -32 0 182 147 0\n186 -34 0 182 148 0\n187 -35 0 182 149 0\n188 -36 0 182 150 0\n189 -42 0 183 121 0\n190 -47 0 184 122 0\n191 -48 0 185 123 0\n192 -50 0 186 171 124 0\n193 -51 0 187 125 0\n194 -52 0 188 126 0\n195 -70 0 191 192 193 190 189 194 151 0\n196 -73 0 195 172 155 0\n197 -74 0 196 182 156 0\n198 72 0 197 158 157 0\n199 67 0 198 153 0\n200 68 0 198 154 0\n201 -10 0 170 1 4 7 10 13 16 130 0\n202 -11 0 170 2 5 8 11 14 17 130 0\n203 -12 0 170 3 6 9 12 15 18 130 0\n204 -24 0 199 167 19 26 28 30 142 127 64 0\n205 -25 0 199 167 20 27 29 31 142 127 64 0\n206 -40 0 199 168 67 82 84 86 142 128 81 0\n207 -41 0 199 168 74 83 85 87 142 128 81 0\n208 4 -49 0 199 200 171 194 192 191 207 188 186 185 205 202 95 143 96 88 142 65 120 108 114 115 116 118 160 0\n209 -49 0 199 200 171 193 192 190 206 187 186 184 204 201 88 95 120 142 143 107 65 96 208 106 111 112 113 117 159 0\n210 33 0 209 169 206 205 201 207 202 203 204 129 0\n211 -23 0 210 42 0\n212 -39 0 210 66 0\n213 8 0 210 119 0\n214 37 0 211 199 142 0\n215 53 0 212 200 143 0\n216 -18 0 213 215 109 0\n217 -19 0 213 215 110 0\n218 -38 0 214 65 0\n219 -54 0 215 96 0\n220 3 0 171 219 193 192 190 206 218 187 186 184 204 201 216 111 112 113 117 159 0\n221 -4 0 220 214 106 0\n222 -2 0 221 205 185 186 188 218 114 0\n223 -20 0 221 205 185 188 115 0\n224 -22 0 221 205 185 186 218 116 0\n225 -7 0 221 218 205 171 118 0\n226 0 224 222 217 202 221 223 225 205 185 186 188 218 207 191 192 194 219 171 160 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record000.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record000.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record000.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record000.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record000 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record000.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record000.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record000.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record000.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record000 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record000_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record000 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record000_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record000_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00173.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00173.record004
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "cb0dcca8da2e87ac98d68d936c3a8e63a4e538ce8b92e2785e0fb29364b91e725356354d70da358d9354d3362d4b49d1743dc8cd38cd332cc73c2e8b62e4b52ccb2ac6b26c5b0ef07a1d8791d4731e2749e1745c370bc1f8a92a258568390e2384e8a529254558350d2344d88d2324c530ce0b42c8b12c2b81d0721c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b4db69b49249249a6db4da4924924d2492492492492492492492249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record004 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record004 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record004.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record004.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record004.data.quota

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
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 32), (facetIndex 39), (facetIndex 50), (facetIndex 60), (facetIndex 67), (facetIndex 75), (facetIndex 86), (facetIndex 94)]))
 (.leaf ([(facetIndex 33), (facetIndex 44), (facetIndex 55), (facetIndex 61), (facetIndex 72), (facetIndex 80), (facetIndex 91), (facetIndex 99)])))
 (.branch 3
 (.leaf ([(facetIndex 34), (facetIndex 45), (facetIndex 56), (facetIndex 57), (facetIndex 58), (facetIndex 59)]))
 (.leaf ([(facetIndex 63), (facetIndex 64), (facetIndex 68), (facetIndex 69), (facetIndex 70), (facetIndex 71)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 82), (facetIndex 83), (facetIndex 87), (facetIndex 88), (facetIndex 89), (facetIndex 90)]))
 (.leaf ([(facetIndex 35), (facetIndex 36), (facetIndex 37), (facetIndex 38), (facetIndex 40), (facetIndex 41), (facetIndex 42), (facetIndex 43)])))
 (.branch 7
 (.leaf ([(facetIndex 46), (facetIndex 47), (facetIndex 48), (facetIndex 49), (facetIndex 51), (facetIndex 52), (facetIndex 53), (facetIndex 54)]))
 (.leaf ([(facetIndex 65), (facetIndex 66), (facetIndex 84), (facetIndex 85)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "20000032483f9010000016db1fb6084923b6c36d91b6d16da88z18;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 62), (facetIndex 73), (facetIndex 74), (facetIndex 76)]))
 (.branch 2
 (.leaf ([(facetIndex 77), (facetIndex 78), (facetIndex 79), (facetIndex 81)]))
 (.leaf ([(facetIndex 92), (facetIndex 93), (facetIndex 95)]))))
 (.branch 4
 (.leaf ([(facetIndex 96), (facetIndex 97), (facetIndex 98)]))
 (.branch 5
 (.leaf ([(facetIndex 100)]))
 (.leaf ([(facetIndex 101)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "2c0db412000000008248z39;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped1_0000 : List Nat := [14]
def grouped1_0001 : List Nat := [14, 15]
def grouped1_0002 : List Nat := [15]
def grouped2_0003 : List Nat := [0, 1]
def grouped2_0004 : List Nat := [0, 1, 2, 3]
def grouped2_0006 : List Nat := [2]
def grouped2_0007 : List Nat := [2, 3]
def grouped2_0008 : List Nat := [3]
def grouped2_0009 : List Nat := [4]
def grouped2_0010 : List Nat := [4, 5]
def grouped2_0011 : List Nat := [4, 5, 6, 7]
def grouped2_0012 : List Nat := [5]
def grouped2_0013 : List Nat := [6]
def grouped2_0014 : List Nat := [6, 7]
def grouped2_0015 : List Nat := [7]
def grouped3_0016 : List Nat := [0]
def grouped3_0017 : List Nat := [0, 1, 2]
def grouped3_0019 : List Nat := [1]
def grouped3_0020 : List Nat := [1, 2]
def grouped3_0021 : List Nat := [2]
def grouped3_0022 : List Nat := [3]
def grouped3_0023 : List Nat := [3, 4, 5]
def grouped3_0024 : List Nat := [4]
def grouped3_0025 : List Nat := [4, 5]
def grouped3_0026 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record004 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record004_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00173.record004" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"group\",\"kind\":1,\"index\":14},{\"tag\":\"group\",\"kind\":1,\"index\":15},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0014\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00173.record004" 65

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00173.record004" "{\"ridges\":[[11,49],[11,50],[14,35],[15,35],[22,289],[23,545],[30,290],[31,546],[34,49],[34,50],[37,35],[38,35],[45,49],[45,50],[56,35],[56,49],[56,50],[57,35],[57,49],[57,50],[58,49],[58,50],[59,49],[59,50],[62,60],[65,289],[66,545],[73,308],[74,564],[76,804],[77,120],[78,184],[81,60],[84,290],[85,546],[92,308],[93,564],[95,804],[96,120],[97,184]],\"owners\":[[11,49,[62,73,74,77,78],[34,45,56,57,58,59]],[34,49,[77,78],[11,45,56,57,58,59,62,73,74]],[45,49,[73,74],[11,34,56,57,58,59,62,77,78]],[56,49,[62,73,74,78],[11,34,45,57,58,59,77]],[57,49,[62,73,74,77],[11,34,45,56,58,59,78]],[58,49,[62,74,77,78],[11,34,45,56,57,59,73]],[59,49,[62,73,77,78],[11,34,45,56,57,58,74]],[11,50,[81,92,93,96,97],[34,45,56,57,58,59]],[34,50,[96,97],[11,45,56,57,58,59,81,92,93]],[45,50,[92,93],[11,34,56,57,58,59,81,96,97]],[56,50,[81,92,93,97],[11,34,45,57,58,59,96]],[57,50,[81,92,93,96],[11,34,45,56,58,59,97]],[58,50,[81,93,96,97],[11,34,45,56,57,59,92]],[59,50,[81,92,96,97],[11,34,45,56,57,58,93]],[22,289,[14,37,58,61,73,76],[65,80]],[65,289,[14,58,61],[22,37,73,76,80]],[30,290,[14,37,58,61,92,95],[84,99]],[84,290,[14,58,61],[30,37,92,95,99]],[23,545,[15,38,59,61,74,76],[66,80]],[66,545,[15,59,61],[23,38,74,76,80]],[31,546,[15,38,59,61,93,95],[85,99]],[85,546,[15,59,61],[31,38,93,95,99]],[62,60,[81],[]],[81,60,[62],[]],[73,308,[92],[]],[92,308,[73],[]],[74,564,[93],[]],[93,564,[74],[]],[76,804,[95,101],[]],[95,804,[76,101],[]],[77,120,[96],[]],[96,120,[77],[]],[78,184,[97],[]],[97,184,[78],[]]],\"edges\":[[30,[11,34,45,56,57,58,59,62,73,74,77,78,81,92,93,96,97]],[37,[14,22,30,37,58,61,65,73,76,80,84,92,95,99,101]],[38,[15,23,31,38,59,61,66,74,76,80,85,93,95,99,101]]],\"groupings\":[1,2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00173.record004" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00173.record004\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-9,-8],[-10,-8],[-11,-8],[-12,-8],[-13,-8],[-14,-8],[-15,-8],[-16,-8],[-20,-3],[-20,-12],[-21,-2],[-21,-11],[-21,-20],[-22,-18],[-22,-19],[-22,-20],[-22,-21],[-24,-23],[-25,-23],[-26,-24],[-26,-25],[-27,-24],[-27,-25],[-28,-24],[-28,-25],[-31,-29],[-31,-30],[-33,-23],[-33,-26],[-33,-27],[-33,-28],[-34,-23],[-34,-26],[-34,-27],[-34,-28],[-39,-19],[-40,-38],[-40,-39],[-2,-3,-18],[-2,-3,-19],[-2,-12,-18],[-2,-12,-19],[-3,-11,-18],[-3,-11,-19],[-1,23,26,27,29,30],[-8,29,30],[-17,26,27],[-18,23,26,27,30],[-19,23,26,27,29],[-20,23,27,29,30],[-21,23,26,29,30],[-1,32,35,36,38,39],[-8,38,39],[-17,35,36],[-18,32,35,36,39],[-19,32,35,36,38],[-20,32,36,38,39],[-21,32,35,38,39],[-4,2,11,20,22,26,28],[-24,2,20,22],[-6,2,11,20,22,35,37],[-33,2,20,22],[-5,3,12,21,22,27,28],[-25,3,21,22],[-7,3,12,21,22,36,37],[-34,3,21,22],[-23,32],[-32,23],[-26,35],[-35,26],[-27,36],[-36,27],[-28,37,41],[-37,28,41],[-29,38],[-38,29],[-30,39],[-39,30],[-42,2],[-2,42],[-43,3],[-3,43],[-44,42,43],[-43,44],[-42,44],[-45,8,17,18,19,20,21],[-46,9,10,11,12,13,14,15,16],[-47,24,25,33,34],[-48,45],[-49,48],[-50,46],[-51,47],[-52,50],[-52,51],[-53,49],[-53,52],[53],[-54,23,26,27,28],[-23,54],[-26,54],[-27,54],[-28,54],[-29,55],[-30,55],[-32,55],[-35,56],[-36,56],[-37,56],[-38,57],[-39,57],[-41,58],[-56,59],[-55,59],[-59,60],[-54,60],[-54,-59,61],[-58,62],[-57,63],[-57,-62,64],[-60,-64,65],[-61,-63,65],[-65],[1,8,17,18,19,20,21,23,26,27,29,30,32,35,36,38,39],[2,4,6,11,20,22,24,26,28,31,33,35,37,40,41],[3,5,7,12,21,22,25,27,28,31,34,36,37,40,41]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"group\",\"index\":14,\"kind\":1},{\"tag\":\"group\",\"index\":15,\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":35,\"b\":34},{\"tag\":\"incompatible\",\"a\":36,\"b\":34},{\"tag\":\"incompatible\",\"a\":37,\"b\":34},{\"tag\":\"incompatible\",\"a\":38,\"b\":34},{\"tag\":\"incompatible\",\"a\":40,\"b\":34},{\"tag\":\"incompatible\",\"a\":41,\"b\":34},{\"tag\":\"incompatible\",\"a\":42,\"b\":34},{\"tag\":\"incompatible\",\"a\":43,\"b\":34},{\"tag\":\"incompatible\",\"a\":58,\"b\":15},{\"tag\":\"incompatible\",\"a\":58,\"b\":38},{\"tag\":\"incompatible\",\"a\":59,\"b\":14},{\"tag\":\"incompatible\",\"a\":59,\"b\":37},{\"tag\":\"incompatible\",\"a\":59,\"b\":58},{\"tag\":\"incompatible\",\"a\":61,\"b\":56},{\"tag\":\"incompatible\",\"a\":61,\"b\":57},{\"tag\":\"incompatible\",\"a\":61,\"b\":58},{\"tag\":\"incompatible\",\"a\":61,\"b\":59},{\"tag\":\"incompatible\",\"a\":65,\"b\":62},{\"tag\":\"incompatible\",\"a\":66,\"b\":62},{\"tag\":\"incompatible\",\"a\":73,\"b\":65},{\"tag\":\"incompatible\",\"a\":73,\"b\":66},{\"tag\":\"incompatible\",\"a\":74,\"b\":65},{\"tag\":\"incompatible\",\"a\":74,\"b\":66},{\"tag\":\"incompatible\",\"a\":76,\"b\":65},{\"tag\":\"incompatible\",\"a\":76,\"b\":66},{\"tag\":\"incompatible\",\"a\":80,\"b\":77},{\"tag\":\"incompatible\",\"a\":80,\"b\":78},{\"tag\":\"incompatible\",\"a\":84,\"b\":62},{\"tag\":\"incompatible\",\"a\":84,\"b\":73},{\"tag\":\"incompatible\",\"a\":84,\"b\":74},{\"tag\":\"incompatible\",\"a\":84,\"b\":76},{\"tag\":\"incompatible\",\"a\":85,\"b\":62},{\"tag\":\"incompatible\",\"a\":85,\"b\":73},{\"tag\":\"incompatible\",\"a\":85,\"b\":74},{\"tag\":\"incompatible\",\"a\":85,\"b\":76},{\"tag\":\"incompatible\",\"a\":97,\"b\":57},{\"tag\":\"incompatible\",\"a\":99,\"b\":96},{\"tag\":\"incompatible\",\"a\":99,\"b\":97},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[14,15,56]},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[14,15,57]},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[14,38,56]},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[14,38,57]},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[15,37,56]},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[15,37,57]},{\"tag\":\"mate\",\"ridge\":49,\"a\":11,\"owners\":[62,73,74,77,78]},{\"tag\":\"mate\",\"ridge\":49,\"a\":34,\"owners\":[77,78]},{\"tag\":\"mate\",\"ridge\":49,\"a\":45,\"owners\":[73,74]},{\"tag\":\"mate\",\"ridge\":49,\"a\":56,\"owners\":[62,73,74,78]},{\"tag\":\"mate\",\"ridge\":49,\"a\":57,\"owners\":[62,73,74,77]},{\"tag\":\"mate\",\"ridge\":49,\"a\":58,\"owners\":[62,74,77,78]},{\"tag\":\"mate\",\"ridge\":49,\"a\":59,\"owners\":[62,73,77,78]},{\"tag\":\"mate\",\"ridge\":50,\"a\":11,\"owners\":[81,92,93,96,97]},{\"tag\":\"mate\",\"ridge\":50,\"a\":34,\"owners\":[96,97]},{\"tag\":\"mate\",\"ridge\":50,\"a\":45,\"owners\":[92,93]},{\"tag\":\"mate\",\"ridge\":50,\"a\":56,\"owners\":[81,92,93,97]},{\"tag\":\"mate\",\"ridge\":50,\"a\":57,\"owners\":[81,92,93,96]},{\"tag\":\"mate\",\"ridge\":50,\"a\":58,\"owners\":[81,93,96,97]},{\"tag\":\"mate\",\"ridge\":50,\"a\":59,\"owners\":[81,92,96,97]},{\"tag\":\"mate\",\"ridge\":289,\"a\":22,\"owners\":[14,37,58,61,73,76]},{\"tag\":\"mate\",\"ridge\":289,\"a\":65,\"owners\":[14,58,61]},{\"tag\":\"mate\",\"ridge\":290,\"a\":30,\"owners\":[14,37,58,61,92,95]},{\"tag\":\"mate\",\"ridge\":290,\"a\":84,\"owners\":[14,58,61]},{\"tag\":\"mate\",\"ridge\":545,\"a\":23,\"owners\":[15,38,59,61,74,76]},{\"tag\":\"mate\",\"ridge\":545,\"a\":66,\"owners\":[15,59,61]},{\"tag\":\"mate\",\"ridge\":546,\"a\":31,\"owners\":[15,38,59,61,93,95]},{\"tag\":\"mate\",\"ridge\":546,\"a\":85,\"owners\":[15,59,61]},{\"tag\":\"mate\",\"ridge\":60,\"a\":62,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":60,\"a\":81,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":308,\"a\":73,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":308,\"a\":92,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":564,\"a\":74,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":564,\"a\":93,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":804,\"a\":76,\"owners\":[95,101]},{\"tag\":\"mate\",\"ridge\":804,\"a\":95,\"owners\":[76,101]},{\"tag\":\"mate\",\"ridge\":120,\"a\":77,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":120,\"a\":96,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":184,\"a\":78,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":184,\"a\":97,\"owners\":[78]},{\"tag\":\"group_or\",\"kind\":1,\"index\":14,\"members\":[14],\"full_literals\":[-42,2]},{\"tag\":\"group_take\",\"kind\":1,\"index\":14,\"member\":14,\"full_literals\":[-2,42]},{\"tag\":\"group_or\",\"kind\":1,\"index\":15,\"members\":[15],\"full_literals\":[-43,3]},{\"tag\":\"group_take\",\"kind\":1,\"index\":15,\"member\":15,\"full_literals\":[-3,43]},{\"tag\":\"merge\",\"left\":[14],\"right\":[15],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0002\",\"joined_name\":\"grouped1_0001\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-44,42,43],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14],\"right\":[15],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0002\",\"joined_name\":\"grouped1_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,44],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14],\"right\":[15],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0002\",\"joined_name\":\"grouped1_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,44],\"grouped\":true,\"kind\":1},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[34,45,56,57,58,59],\"full_literals\":[-45,8,17,18,19,20,21]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[35,36,37,38,40,41,42,43],\"full_literals\":[-46,9,10,11,12,13,14,15,16]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[65,66,84,85],\"full_literals\":[-47,24,25,33,34]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-48,45,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-49,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-50,false,46],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0013\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0014\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-51,false,47],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-52,50,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0011\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-52,false,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0004\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-53,49,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0004\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-53,false,52],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[62,73,74,76],\"full_literals\":[-54,23,26,27,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":62,\"full_literals\":[-23,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":73,\"full_literals\":[-26,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":74,\"full_literals\":[-27,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":76,\"full_literals\":[-28,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":77,\"full_literals\":[-29,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":78,\"full_literals\":[-30,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":81,\"full_literals\":[-32,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":92,\"full_literals\":[-35,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":93,\"full_literals\":[-36,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":95,\"full_literals\":[-37,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":96,\"full_literals\":[-38,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":97,\"full_literals\":[-39,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":101,\"full_literals\":[-41,58]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-56,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-55,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-59,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-54,false,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-54,-59,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0025\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-58,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-57,false,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-57,-62,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-60,-64,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-61,-63,65],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":30,\"owners\":[11,34,45,56,57,58,59,62,73,74,77,78,81,92,93,96,97]},{\"tag\":\"edge\",\"edge\":37,\"owners\":[14,22,30,37,58,61,65,73,76,80,84,92,95,99,101]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[15,23,31,38,59,61,66,74,76,80,85,93,95,99,101]}]}"
  "126 49 0 97 95 0\n127 52 0 97 96 0\n128 48 0 126 90 0\n129 50 0 127 93 0\n130 51 0 127 94 0\n131 45 0 128 89 0\n132 46 0 129 91 0\n133 47 0 130 92 0\n134 60 0 114 115 112 113 99 100 101 106 107 103 104 105 45 47 48 49 51 50 46 76 78 123 0\n135 -64 0 134 122 120 0\n136 59 57 0 110 77 109 75 53 112 113 106 107 105 54 69 55 56 58 71 57 52 67 123 0\n137 57 61 0 109 110 53 75 77 136 116 99 100 101 45 68 47 70 48 49 51 72 50 123 0\n138 38 39 54 0 100 70 101 72 99 68 55 77 47 53 75 52 56 58 57 123 0\n139 -8 0 132 1 2 3 4 5 6 7 8 87 0\n140 44 22 20 21 0 133 84 85 82 80 64 66 60 62 88 0\n141 43 -44 -19 21 -38 54 41 0 15 76 26 37 102 74 101 72 82 83 64 66 79 42 65 63 125 0\n142 20 21 39 54 41 0 139 131 138 76 26 37 100 70 101 72 99 68 55 102 74 47 86 15 140 141 81 40 44 60 62 61 59 124 0\n143 21 39 54 41 0 138 76 26 37 102 74 101 72 142 9 10 16 64 66 65 63 125 0\n144 39 54 41 0 102 74 100 70 138 37 76 26 143 11 12 13 17 60 62 61 59 124 0\n145 -21 54 41 0 144 78 27 38 102 74 100 70 11 12 13 17 60 62 61 59 124 0\n146 2 20 54 41 0 131 139 145 101 100 47 144 36 86 14 140 78 27 38 102 74 70 79 60 62 83 81 43 61 59 124 0\n147 20 54 41 0 139 131 145 144 78 27 38 36 102 74 101 72 100 47 86 14 146 39 41 64 66 65 63 125 0\n148 54 41 0 101 102 72 74 144 38 78 27 145 147 9 10 16 64 66 65 63 125 0\n149 61 0 135 137 119 117 111 148 116 112 113 106 107 108 105 69 71 73 67 98 0\n150 -63 0 149 122 121 0\n151 -57 0 150 118 0\n152 -38 0 151 109 0\n153 -39 0 151 110 0\n154 54 0 153 152 138 0\n155 -25 0 154 19 21 23 25 98 0\n156 -24 0 154 18 20 22 24 98 0\n157 -33 0 154 28 29 30 31 98 0\n158 34 0 157 133 156 155 88 0\n159 -23 0 158 32 0\n160 -26 0 158 33 0\n161 -27 0 158 34 0\n162 -28 0 158 35 0\n163 0 161 160 154 162 159 98 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record004.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record004.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record004.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record004.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record004 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record004.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record004.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record004.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record004.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record004 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record004_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record004 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record004_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record004_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00173.record004
