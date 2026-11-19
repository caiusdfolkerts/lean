module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00024Data
public import GraphInputsRow24Part00024Frames
public import GraphInputsRow24Part00024Leaves
public import GraphInputsRow24Part00024Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00024.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record000
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨80, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 161078453469184, 651333096108457984, (certNat% 3), 68679894317400064, (certNat% 4)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), (certNat% 6), (certNat% 7), (certNat% 8), 193514046488576, (certNat% 9)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), 70932793642713088, (certNat% 11), 648527142434373632, (certNat% 12), (certNat% 13), 194338680209408]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record000_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00024.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00024.record019
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record019
def vertexColumn : Fields := ⟨10, (certNat% 14)⟩
def kindColumn : Fields := ⟨3, (certNat% 15)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), (certNat% 17), (certNat% 18), 8162774324609024]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 20), (certNat% 21), 586734588953362432, 6755399441055744]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), (certNat% 23), (certNat% 24), 72171943247216640, 1882522236426911744, 4362862139015168, 40538443960287232]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record019_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record019_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record019_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record019_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record019_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record019_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record019_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record019_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record019_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00024.record019

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00024.record023
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record023
def vertexColumn : Fields := ⟨10, (certNat% 25)⟩
def kindColumn : Fields := ⟨3, (certNat% 26)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), (certNat% 28), (certNat% 29), (certNat% 30), (certNat% 31)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 32), (certNat% 33), (certNat% 34), (certNat% 35), 19509734323257344]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 36), 22517998136852480, (certNat% 37), (certNat% 29), (certNat% 38)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 39), 22517998136852480, (certNat% 40), (certNat% 29), (certNat% 38)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 41), (certNat% 42), (certNat% 43), 19509734323257344, (certNat% 44), (certNat% 38), 5118258839552]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record023_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record023_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record023_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record023_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record023_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record023_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record023_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record023_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record023_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00024.record023

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00024.record024
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record024
def vertexColumn : Fields := ⟨10, (certNat% 45)⟩
def kindColumn : Fields := ⟨3, (certNat% 46)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 47), 36424621204963328, (certNat% 48), (certNat% 49), 374520048699572224]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 50), (certNat% 51), (certNat% 52), (certNat% 53), 145566543424520192, 302462454661644288, 151129161728]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record024_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record024_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record024_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record024_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record024_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record024_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record024_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record024_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record024_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00024.record024

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00024.record015
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3b0dc2f2e2d2b2a9a8ea368ba998e6358b6338ae1b91e2785e0fae1d27299a4e9364b9994e5354b5334ad1b51d2745d0f743b0f23a8e6338f1364cd32cf0b92d4b32e2b4acab1ac9b16c3b91e2719d1715c3743c8f468c6298961382e07919314a52544d0b41dc0e4330e2328d1324d0b12c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6db6924924936db6da492492492492492492492492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record015 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record015 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record015.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record015.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record015.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 73), (facetIndex 74), (facetIndex 75)]))
 (.branch 2
 (.leaf ([(facetIndex 91), (facetIndex 92), (facetIndex 93)]))
 (.leaf ([(facetIndex 70), (facetIndex 71), (facetIndex 72)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 88), (facetIndex 89), (facetIndex 90)]))
 (.leaf ([(facetIndex 95), (facetIndex 96), (facetIndex 97)])))
 (.branch 6
 (.leaf ([(facetIndex 69), (facetIndex 76)]))
 (.leaf ([(facetIndex 87), (facetIndex 94)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "249892dbc000000050024a8z33;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0003 : List Nat := [1]
def grouped3_0004 : List Nat := [1, 2]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [3, 4]
def grouped3_0007 : List Nat := [3, 4, 5, 6]
def grouped3_0008 : List Nat := [5]
def grouped3_0009 : List Nat := [5, 6]
def grouped3_0010 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record015 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record015_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00024.record015" "{\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00024.record015" 34

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00024.record015" "{\"ridges\":[[12,545],[14,577],[15,769],[36,545],[37,577],[44,546],[47,578],[48,769],[52,769],[54,545],[54,578],[55,545],[56,545],[56,769],[57,577],[58,577],[58,769],[73,616],[74,808],[75,840],[92,808],[93,840]],\"owners\":[[12,545,[69,73,74,76],[36,44,54,55,56]],[36,545,[73,74,76],[12,44,54,55,56,69]],[54,545,[74],[12,36,44,55,56,69,73,76]],[55,545,[69,73,74],[12,36,44,54,56,76]],[56,545,[69,73,76],[12,36,44,54,55,74]],[44,546,[87,94],[12,36,54,55,56,91,92]],[14,577,[69,73,75,76],[37,47,54,57,58]],[37,577,[73,75,76],[14,47,54,57,58,69]],[57,577,[69,73,75],[14,37,47,54,58,76]],[58,577,[69,73,76],[14,37,47,54,57,75]],[47,578,[87,94],[14,37,54,57,58,91,93]],[54,578,[93],[14,37,47,57,58,87,91,94]],[15,769,[74,75],[48,52,56,58]],[48,769,[],[15,52,56,58,74,75]],[52,769,[74,75],[15,48,56,58]],[56,769,[75],[15,48,52,58,74]],[58,769,[74],[15,48,52,56,75]],[73,616,[91],[]],[74,808,[92],[]],[92,808,[74],[]],[75,840,[93],[]],[93,840,[75],[]]],\"edges\":[[38,[12,36,44,54,55,56,69,73,74,76,87,91,92,94]],[41,[14,37,47,54,57,58,69,73,75,76,87,91,93,94]],[44,[15,48,52,56,58,74,75,92,93]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00024.record015" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00024.record015\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-17,-16],[-21,-17],[-23,-16],[-23,-17],[-23,-21],[-23,-22],[-1,15,16,17,19],[-4,16,17,19],[-10,17],[-11,15,16,17],[-12,15,16,19],[-6,20,24],[-2,15,16,18,19],[-5,16,18,19],[-13,15,16,18],[-14,15,16,19],[-7,20,24],[-10,23],[-3,17,18],[-8],[-9,17,18],[-12,18],[-14,17],[-16,21],[-17,22],[-22,17],[-18,23],[-23,18],[-25,16,17,18],[-17,25],[-18,25],[-21,26],[-22,26],[-23,26],[-15,27],[-19,27],[-20,28],[-24,28],[-26,29],[-30,25,29],[-29,30],[-25,30],[-25,-29,31],[-28,32],[-27,32],[-32,33],[-31,-33,34],[-34],[1,4,6,10,11,12,15,16,17,19,20,21,22,24],[2,5,7,10,13,14,15,16,18,19,20,21,23,24],[3,8,9,12,14,17,18,22,23]],\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":74,\"b\":73},{\"tag\":\"incompatible\",\"a\":91,\"b\":74},{\"tag\":\"incompatible\",\"a\":93,\"b\":73},{\"tag\":\"incompatible\",\"a\":93,\"b\":74},{\"tag\":\"incompatible\",\"a\":93,\"b\":91},{\"tag\":\"incompatible\",\"a\":93,\"b\":92},{\"tag\":\"mate\",\"ridge\":545,\"a\":12,\"owners\":[69,73,74,76]},{\"tag\":\"mate\",\"ridge\":545,\"a\":36,\"owners\":[73,74,76]},{\"tag\":\"mate\",\"ridge\":545,\"a\":54,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":545,\"a\":55,\"owners\":[69,73,74]},{\"tag\":\"mate\",\"ridge\":545,\"a\":56,\"owners\":[69,73,76]},{\"tag\":\"mate\",\"ridge\":546,\"a\":44,\"owners\":[87,94]},{\"tag\":\"mate\",\"ridge\":577,\"a\":14,\"owners\":[69,73,75,76]},{\"tag\":\"mate\",\"ridge\":577,\"a\":37,\"owners\":[73,75,76]},{\"tag\":\"mate\",\"ridge\":577,\"a\":57,\"owners\":[69,73,75]},{\"tag\":\"mate\",\"ridge\":577,\"a\":58,\"owners\":[69,73,76]},{\"tag\":\"mate\",\"ridge\":578,\"a\":47,\"owners\":[87,94]},{\"tag\":\"mate\",\"ridge\":578,\"a\":54,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":769,\"a\":15,\"owners\":[74,75]},{\"tag\":\"mate\",\"ridge\":769,\"a\":48,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":769,\"a\":52,\"owners\":[74,75]},{\"tag\":\"mate\",\"ridge\":769,\"a\":56,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":769,\"a\":58,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":616,\"a\":73,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":808,\"a\":74,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":808,\"a\":92,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":840,\"a\":75,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":840,\"a\":93,\"owners\":[75]},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[73,74,75],\"full_literals\":[-25,16,17,18]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":74,\"full_literals\":[-17,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":75,\"full_literals\":[-18,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":91,\"full_literals\":[-21,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":92,\"full_literals\":[-22,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":93,\"full_literals\":[-23,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":69,\"full_literals\":[-15,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":76,\"full_literals\":[-19,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":87,\"full_literals\":[-20,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":94,\"full_literals\":[-24,28]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-26,false,29],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-30,25,29],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-29,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-25,false,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-25,-29,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-28,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-27,false,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-32,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-31,-33,34],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":38,\"owners\":[12,36,44,54,55,56,69,73,74,76,87,91,92,94]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[14,37,47,54,57,58,69,73,75,76,87,91,93,94]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[15,48,52,56,58,74,75,92,93]}]}"
  "52 3 9 12 14 17 18 22 23 0 20 51 0\n53 30 0 41 42 39 30 31 33 34 19 23 22 21 52 0\n54 29 0 53 39 40 32 33 34 24 25 27 29 0\n55 17 18 0 19 23 26 22 28 21 52 0\n56 25 0 30 31 55 0\n57 31 0 56 54 43 0\n58 -33 0 57 48 47 0\n59 -32 0 58 46 0\n60 -28 0 59 44 0\n61 -27 0 59 45 0\n62 -20 0 60 37 0\n63 -24 0 60 38 0\n64 -15 0 61 35 0\n65 -19 0 61 36 0\n66 -6 0 62 63 12 0\n67 -7 0 62 63 17 0\n68 23 0 63 62 65 64 67 18 27 55 1 2 13 15 16 14 50 0\n69 -16 0 68 3 0\n70 -17 0 68 4 0\n71 -21 0 68 5 0\n72 -22 0 68 6 0\n73 -1 0 69 64 70 65 7 0\n74 -11 0 69 64 70 10 0\n75 -12 0 69 64 65 11 0\n76 -4 0 69 70 65 8 0\n77 -10 0 70 9 0\n78 0 73 74 76 66 77 75 64 69 70 65 62 71 72 63 49 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record015.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record015.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record015.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record015.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record015 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record015.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record015.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record015.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record015.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record015 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record015_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record015_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record015_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record015_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record015_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record015_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record015_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record015 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record015_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record015_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record015_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00024.record015

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00024.record016
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "26c3b0dc2f0ea368bad1b26998e6358b6338ae1b91e2785e0fae19a4e9364b9d1725994e5c54d52d64d3362d2b46d4749d1743dd0f2398ce364cd32cc6b46c5b0ef0791d4731e2749ca719c9715c3743c8f328aa269161382e078c92a499c1645895151342d074c328d1324c8b12c2b06d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6926db6d24924da4924d369249249b692492492492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record016 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record016 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record016.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record016.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record016.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 51), (facetIndex 52), (facetIndex 53)]))
 (.branch 2
 (.leaf ([(facetIndex 85), (facetIndex 86), (facetIndex 87)]))
 (.leaf ([(facetIndex 63), (facetIndex 64), (facetIndex 66)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 73), (facetIndex 74), (facetIndex 84)]))
 (.leaf ([(facetIndex 82), (facetIndex 83), (facetIndex 93)])))
 (.branch 6
 (.leaf ([(facetIndex 91), (facetIndex 92)]))
 (.leaf ([(facetIndex 94)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1a5a0024b9000000d80000824z2f;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0003 : List Nat := [1]
def grouped3_0004 : List Nat := [1, 2]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [3]
def grouped3_0007 : List Nat := [3, 4]
def grouped3_0008 : List Nat := [3, 4, 5, 6]
def grouped3_0009 : List Nat := [4]
def grouped3_0010 : List Nat := [5]
def grouped3_0011 : List Nat := [5, 6]
def grouped3_0012 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record016 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record016_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00024.record016" "{\"atoms\":[{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00024.record016" 43

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00024.record016" "{\"ridges\":[[17,545],[18,577],[18,580],[19,769],[19,772],[38,548],[41,577],[41,580],[42,769],[51,610],[52,802],[53,834],[60,545],[62,577],[62,580],[65,769],[65,772],[67,545],[67,548],[67,580],[68,545],[68,548],[68,769],[68,772],[69,577],[69,580],[69,769],[73,616],[74,736],[85,610],[87,834],[91,180],[92,212],[94,616]],\"owners\":[[17,545,[51,52,73,74],[38,60,67,68]],[60,545,[51,52,74],[17,38,67,68,73]],[67,545,[52],[17,38,51,60,68,73,74]],[68,545,[51,73,74],[17,38,52,60,67]],[38,548,[94],[17,60,67,68,85,86]],[67,548,[86],[17,38,60,68,85,94]],[68,548,[85,94],[17,38,60,67,86]],[18,577,[51,53,73,74],[41,62,67,69]],[41,577,[73,74],[18,51,53,62,67,69]],[62,577,[51,53,74],[18,41,67,69,73]],[69,577,[51,73,74],[18,41,53,62,67]],[18,580,[85,87,94],[41,62,67,69]],[41,580,[94],[18,62,67,69,85,87]],[62,580,[85,87],[18,41,67,69,94]],[67,580,[87],[18,41,62,69,85,94]],[69,580,[85,94],[18,41,62,67,87]],[19,769,[52,53],[42,65,68,69]],[42,769,[],[19,52,53,65,68,69]],[65,769,[52,53],[19,42,68,69]],[68,769,[53],[19,42,52,65,69]],[69,769,[52],[19,42,53,65,68]],[19,772,[86,87],[42,65,68,69]],[65,772,[86,87],[19,42,68,69]],[68,772,[87],[19,42,65,69,86]],[51,610,[85],[]],[85,610,[51],[]],[52,802,[86],[]],[53,834,[87],[]],[87,834,[53],[]],[91,180,[63,82],[]],[92,212,[64,83],[]],[73,616,[94],[]],[94,616,[73],[]],[74,736,[],[]]],\"edges\":[[38,[17,38,51,52,60,67,68,73,74,85,86,94]],[41,[18,41,51,53,62,67,69,73,74,85,87,94]],[44,[19,42,52,53,65,68,69,86,87]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00024.record016" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00024.record016\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-22,-8],[-23,-22],[-24,-7],[-24,-8],[-24,-22],[-24,-23],[-1,7,8,18,19],[-10,7,8,19],[-15,8],[-16,7,18,19],[-4,27],[-15,23],[-16,22,27],[-2,7,9,18,19],[-5,18,19],[-11,7,9,19],[-17,7,18,19],[-2,22,24,27],[-5,27],[-11,22,24],[-15,24],[-17,22,27],[-3,8,9],[-6],[-14,8,9],[-16,9],[-17,8],[-3,23,24],[-14,23,24],[-16,24],[-7,22],[-22,7],[-8,23],[-9,24],[-24,9],[-25,12,20],[-26,13,21],[-18,27],[-27,18],[-19],[-7,28],[-8,28],[-9,28],[-22,29],[-23,29],[-24,29],[-12,30],[-13,30],[-18,31],[-20,32],[-21,32],[-33,25,26],[-34,27],[-27,34],[-30,35],[-29,35],[-29,-30,36],[-35,37],[-36,38],[-28,37],[-28,-35,38],[-32,39],[-31,39],[-40,33,34],[-34,40],[-40,41],[-39,41],[-39,-40,42],[-37,-42,43],[-38,-41,43],[-43],[1,4,7,8,10,15,16,18,19,22,23,27],[2,5,7,9,11,15,17,18,19,22,24,27],[3,6,8,9,14,16,17,23,24]],\"atoms\":[{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":85,\"b\":52},{\"tag\":\"incompatible\",\"a\":86,\"b\":85},{\"tag\":\"incompatible\",\"a\":87,\"b\":51},{\"tag\":\"incompatible\",\"a\":87,\"b\":52},{\"tag\":\"incompatible\",\"a\":87,\"b\":85},{\"tag\":\"incompatible\",\"a\":87,\"b\":86},{\"tag\":\"mate\",\"ridge\":545,\"a\":17,\"owners\":[51,52,73,74]},{\"tag\":\"mate\",\"ridge\":545,\"a\":60,\"owners\":[51,52,74]},{\"tag\":\"mate\",\"ridge\":545,\"a\":67,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":545,\"a\":68,\"owners\":[51,73,74]},{\"tag\":\"mate\",\"ridge\":548,\"a\":38,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":548,\"a\":67,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":548,\"a\":68,\"owners\":[85,94]},{\"tag\":\"mate\",\"ridge\":577,\"a\":18,\"owners\":[51,53,73,74]},{\"tag\":\"mate\",\"ridge\":577,\"a\":41,\"owners\":[73,74]},{\"tag\":\"mate\",\"ridge\":577,\"a\":62,\"owners\":[51,53,74]},{\"tag\":\"mate\",\"ridge\":577,\"a\":69,\"owners\":[51,73,74]},{\"tag\":\"mate\",\"ridge\":580,\"a\":18,\"owners\":[85,87,94]},{\"tag\":\"mate\",\"ridge\":580,\"a\":41,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":580,\"a\":62,\"owners\":[85,87]},{\"tag\":\"mate\",\"ridge\":580,\"a\":67,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":580,\"a\":69,\"owners\":[85,94]},{\"tag\":\"mate\",\"ridge\":769,\"a\":19,\"owners\":[52,53]},{\"tag\":\"mate\",\"ridge\":769,\"a\":42,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":769,\"a\":65,\"owners\":[52,53]},{\"tag\":\"mate\",\"ridge\":769,\"a\":68,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":769,\"a\":69,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":772,\"a\":19,\"owners\":[86,87]},{\"tag\":\"mate\",\"ridge\":772,\"a\":65,\"owners\":[86,87]},{\"tag\":\"mate\",\"ridge\":772,\"a\":68,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":610,\"a\":51,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":610,\"a\":85,\"owners\":[51]},{\"tag\":\"mate\",\"ridge\":802,\"a\":52,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":834,\"a\":53,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":834,\"a\":87,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":180,\"a\":91,\"owners\":[63,82]},{\"tag\":\"mate\",\"ridge\":212,\"a\":92,\"owners\":[64,83]},{\"tag\":\"mate\",\"ridge\":616,\"a\":73,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":616,\"a\":94,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":736,\"a\":74,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":51,\"full_literals\":[-7,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":52,\"full_literals\":[-8,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":53,\"full_literals\":[-9,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":85,\"full_literals\":[-22,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":86,\"full_literals\":[-23,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":87,\"full_literals\":[-24,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":63,\"full_literals\":[-12,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":64,\"full_literals\":[-13,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":73,\"full_literals\":[-18,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":82,\"full_literals\":[-20,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":83,\"full_literals\":[-21,32]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[91,92],\"full_literals\":[-33,25,26]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[94],\"full_literals\":[-34,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":94,\"full_literals\":[-27,34]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-30,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-29,false,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-29,-30,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-35,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-36,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-28,false,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-28,-35,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-32,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-31,false,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-40,33,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-34,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-40,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-39,false,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-39,-40,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-37,-42,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-38,-41,43],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":38,\"owners\":[17,38,51,52,60,67,68,73,74,85,86,94]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[18,41,51,53,62,67,69,73,74,85,87,94]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[19,42,52,53,65,68,69,86,87]}]}"
  "75 1 4 7 8 10 15 16 18 22 23 27 0 40 72 0\n76 2 5 7 9 11 15 17 18 22 24 27 0 40 73 0\n77 3 8 9 14 16 17 23 24 0 24 74 0\n78 37 0 58 60 56 42 43 45 46 27 26 23 25 77 0\n79 -42 0 78 71 69 0\n80 30 -40 0 79 68 63 49 39 53 64 62 51 50 47 48 36 37 52 0\n81 -40 38 0 79 40 59 68 63 49 15 39 80 55 57 61 44 45 46 41 43 22 12 20 18 76 0\n82 9 7 5 27 11 15 17 18 22 24 0 40 76 14 0\n83 28 27 0 40 38 19 41 42 43 32 17 9 35 16 82 0\n84 38 0 81 65 54 83 61 56 44 45 46 13 22 28 29 33 34 77 0\n85 -41 0 84 71 70 0\n86 -40 0 85 66 0\n87 -39 0 85 67 0\n88 -34 0 86 65 0\n89 -31 0 87 63 0\n90 -27 0 88 54 0\n91 -18 0 89 49 0\n92 -4 0 90 11 0\n93 -5 0 90 19 0\n94 22 24 0 91 90 93 34 21 22 31 20 82 0\n95 24 0 30 34 94 1 2 27 23 25 77 0\n96 -7 0 95 3 0\n97 -8 0 95 4 0\n98 -22 0 95 5 0\n99 -23 0 95 6 0\n100 -16 0 96 91 40 10 0\n101 -15 0 97 9 0\n102 -10 0 97 96 40 8 0\n103 -1 0 97 91 96 40 7 0\n104 0 103 98 92 96 102 101 97 91 100 99 90 75 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record016.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record016.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record016.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record016.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record016 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record016.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record016.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record016.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record016.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record016 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record016_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record016_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record016_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record016_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record016_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record016_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record016_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record016 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record016_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record016_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record016_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00024.record016

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00024.record028
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "370bcc68da2e8e6958d62d8ce4b8ae2785e0fad16a719364b9396552d4cd4b45d0f743c8ce3c4cd32cf0b32cab86d1b26c5b0ee4731d2729c6785c970dd0f23c4f350ac272524a8560b81e944d14a4a9264c5294951548d0b41dc0e4348e1314d0b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "49b6d26d24924d24924924d269a492492492492249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record028 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record028 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record028.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record028.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record028.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 43), (facetIndex 48), (facetIndex 57), (facetIndex 59), (facetIndex 64), (facetIndex 67)]))
 (.leaf ([(facetIndex 44), (facetIndex 52), (facetIndex 58), (facetIndex 62), (facetIndex 65), (facetIndex 68)])))
 (.branch 3
 (.leaf ([(facetIndex 34), (facetIndex 40), (facetIndex 50), (facetIndex 55)]))
 (.branch 4
 (.leaf ([(facetIndex 33), (facetIndex 36), (facetIndex 39), (facetIndex 41), (facetIndex 60), (facetIndex 61), (facetIndex 63)]))
 (.leaf ([(facetIndex 69), (facetIndex 72), (facetIndex 73)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 70), (facetIndex 76), (facetIndex 77)]))
 (.leaf ([(facetIndex 71), (facetIndex 82), (facetIndex 83)])))
 (.branch 8
 (.leaf ([(facetIndex 37), (facetIndex 47), (facetIndex 53), (facetIndex 56)]))
 (.branch 9
 (.leaf ([(facetIndex 32), (facetIndex 35), (facetIndex 38), (facetIndex 42)]))
 (.leaf ([(facetIndex 45), (facetIndex 46)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "6600005500446541001031330107207102007991083238738238z20;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 66)]))
 (.leaf ([(facetIndex 81)])))
 (.branch 3
 (.leaf ([(facetIndex 49), (facetIndex 51), (facetIndex 54)]))
 (.branch 4
 (.leaf ([(facetIndex 74), (facetIndex 75), (facetIndex 78)]))
 (.leaf ([(facetIndex 79), (facetIndex 80)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "c8c06c000000000000008041z25;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 5
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3, 4]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [3, 4]
def grouped2_0009 : List Nat := [4]
def grouped2_0010 : List Nat := [5]
def grouped2_0011 : List Nat := [5, 6]
def grouped2_0012 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0013 : List Nat := [6]
def grouped2_0014 : List Nat := [7]
def grouped2_0015 : List Nat := [7, 8, 9]
def grouped2_0016 : List Nat := [8]
def grouped2_0017 : List Nat := [8, 9]
def grouped2_0018 : List Nat := [9]
def grouped3_0019 : List Nat := [0]
def grouped3_0020 : List Nat := [0, 1]
def grouped3_0022 : List Nat := [1]
def grouped3_0023 : List Nat := [2]
def grouped3_0024 : List Nat := [2, 3, 4]
def grouped3_0025 : List Nat := [3]
def grouped3_0026 : List Nat := [3, 4]
def grouped3_0027 : List Nat := [4]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record028 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record028_matrix_checked

def leafCount : Nat := 8
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaf0000 : List (Fin data.count) := [(facetIndex 2), (facetIndex 19), (facetIndex 24), (facetIndex 28), (facetIndex 42), (facetIndex 55), (facetIndex 63), (facetIndex 66), (facetIndex 67), (facetIndex 68), (facetIndex 73), (facetIndex 76), (facetIndex 81), (facetIndex 82)]
theorem leaf0000_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0000 = true := by
  decide +kernel
theorem leaf0000_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0000 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0000_counts_checked
def leaf0001 : List (Fin data.count) := [(facetIndex 2), (facetIndex 19), (facetIndex 28), (facetIndex 31), (facetIndex 42), (facetIndex 55), (facetIndex 63), (facetIndex 66), (facetIndex 67), (facetIndex 68), (facetIndex 70), (facetIndex 73), (facetIndex 81), (facetIndex 82)]
theorem leaf0001_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0001 = true := by
  decide +kernel
theorem leaf0001_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0001 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0001_counts_checked
def leaf0002 : List (Fin data.count) := [(facetIndex 17), (facetIndex 19), (facetIndex 27), (facetIndex 30), (facetIndex 40), (facetIndex 41), (facetIndex 56), (facetIndex 66), (facetIndex 67), (facetIndex 68), (facetIndex 69), (facetIndex 77), (facetIndex 81), (facetIndex 83)]
theorem leaf0002_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0002 = true := by
  decide +kernel
theorem leaf0002_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0002 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0002_counts_checked
def leaf0003 : List (Fin data.count) := [(facetIndex 2), (facetIndex 23), (facetIndex 24), (facetIndex 28), (facetIndex 42), (facetIndex 55), (facetIndex 63), (facetIndex 65), (facetIndex 66), (facetIndex 67), (facetIndex 73), (facetIndex 76), (facetIndex 81), (facetIndex 82)]
theorem leaf0003_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0003 = true := by
  decide +kernel
theorem leaf0003_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0003 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0003_counts_checked
def leaf0004 : List (Fin data.count) := [(facetIndex 3), (facetIndex 19), (facetIndex 24), (facetIndex 27), (facetIndex 40), (facetIndex 56), (facetIndex 63), (facetIndex 66), (facetIndex 67), (facetIndex 68), (facetIndex 72), (facetIndex 77), (facetIndex 81), (facetIndex 83)]
theorem leaf0004_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0004 = true := by
  decide +kernel
theorem leaf0004_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0004 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0004_counts_checked
def leaf0005 : List (Fin data.count) := [(facetIndex 3), (facetIndex 19), (facetIndex 27), (facetIndex 30), (facetIndex 40), (facetIndex 56), (facetIndex 63), (facetIndex 66), (facetIndex 67), (facetIndex 68), (facetIndex 69), (facetIndex 77), (facetIndex 81), (facetIndex 83)]
theorem leaf0005_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0005 = true := by
  decide +kernel
theorem leaf0005_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0005 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0005_counts_checked
def leaf0006 : List (Fin data.count) := [(facetIndex 18), (facetIndex 19), (facetIndex 28), (facetIndex 31), (facetIndex 39), (facetIndex 42), (facetIndex 55), (facetIndex 66), (facetIndex 67), (facetIndex 68), (facetIndex 70), (facetIndex 73), (facetIndex 81), (facetIndex 82)]
theorem leaf0006_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0006 = true := by
  decide +kernel
theorem leaf0006_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0006 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0006_counts_checked
def leaf0007 : List (Fin data.count) := [(facetIndex 3), (facetIndex 21), (facetIndex 24), (facetIndex 27), (facetIndex 40), (facetIndex 56), (facetIndex 63), (facetIndex 64), (facetIndex 66), (facetIndex 68), (facetIndex 72), (facetIndex 77), (facetIndex 81), (facetIndex 83)]
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

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00024.record028" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0017\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0017\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00024.record028" 113

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00024.record028" "{\"ridges\":[[0,7],[1,7],[2,7],[2,37],[3,7],[6,259],[10,67],[10,515],[11,770],[14,137],[15,69],[19,137],[20,161],[22,193],[23,529],[28,530],[28,592],[30,164],[31,196],[33,7],[34,7],[36,7],[36,22],[37,515],[37,529],[37,530],[38,67],[39,7],[40,7],[40,259],[40,290],[41,7],[41,133],[42,7],[42,69],[42,577],[42,578],[43,26],[48,161],[49,202],[50,769],[51,178],[52,67],[53,769],[54,226],[55,515],[55,770],[56,67],[56,259],[56,770],[57,37],[58,69],[63,37],[63,69],[66,265],[66,529],[67,137],[67,161],[67,168],[68,145],[68,193],[68,208],[68,529],[69,22],[69,38],[70,26],[70,84],[72,14],[72,38],[72,164],[73,38],[74,202],[75,178],[76,22],[76,70],[76,196],[77,22],[77,70],[78,226],[79,178],[80,202],[81,26],[81,530],[82,152],[83,152]],\"owners\":[[72,14,[0,24,32,34,70],[25,33,71,73,74]],[76,22,[1,24,35,37,69],[26,36,71,75,77]],[69,38,[2,38,39,40,78],[25,35,72,73,75]],[72,38,[2,35,38,40],[25,39,69,73,75,78]],[73,38,[2,35,38,39,75,78],[25,40,69,72]],[76,70,[3,32,38,42],[26,41,70,74,77,78]],[77,70,[3,32,38,41,74,78],[26,42,70,76]],[66,265,[6,21,34,59,67],[46,50]],[40,290,[27],[9,55,73]],[42,577,[23,68],[10,56,62]],[42,578,[28],[10,56,77]],[50,769,[],[11,53,55,56,66]],[53,769,[],[11,50,55,56,66]],[11,770,[81],[50,53,55,56]],[55,770,[81],[11,50,53,56]],[56,770,[81],[11,50,53,55]],[41,133,[14,16,17],[18,33,36,39]],[67,137,[14,19,33,45,49,60,65],[20,48]],[70,84,[15,31,62],[26,58,77,83]],[68,145,[16,19,36,45,51,61,64],[22,52]],[20,161,[17,39,51,54,61,63],[48,64,67]],[48,161,[17,61,63],[20,39,51,54,64,67]],[67,161,[17,39,51,54,61,63],[20,48,64]],[30,164,[17,39,61,63,75,78],[72,82]],[72,164,[17,61,63],[30,39,75,78,82]],[22,193,[18,41,49,54,60,63],[52,65,68]],[68,193,[18,41,49,54,60,63],[22,52,65]],[31,196,[18,41,60,63,74,78],[76,83]],[76,196,[18,60,63],[31,41,74,78,83]],[82,152,[19,45,65,80],[29,64,71,79,83]],[83,152,[19,45,64,79],[29,65,71,80,82]],[67,168,[30,72,79,82],[20,48,64]],[68,208,[31,76,80,83],[22,52,65]],[28,592,[23,62,68],[77]],[49,202,[74,80],[]],[74,202,[49,80],[]],[80,202,[49,74],[]],[51,178,[75,79],[]],[75,178,[51,79],[]],[79,178,[51,75],[]],[54,226,[78],[]],[78,226,[54],[]]],\"edges\":[[36,[17,20,30,39,48,51,54,61,63,64,67,72,75,78,79,82]],[39,[18,22,31,41,49,52,54,60,63,65,68,74,76,78,80,83]],[41,[10,23,28,42,56,62,68,77]],[44,[11,50,53,55,56,66,81]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00024.record028" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00024.record028\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-23,-3],[-25,-23],[-26,-4],[-26,-23],[-26,-25],[-28,-23],[-28,-26],[-29,-24],[-29,-25],[-29,-27],[-29,-28],[-30,-23],[-30,-26],[-30,-29],[-31,-3],[-31,-23],[-31,-25],[-31,-26],[-31,-29],[-31,-30],[-32,-23],[-32,-26],[-32,-29],[-32,-30],[-33,-26],[-33,-28],[-33,-29],[-33,-32],[-34,-31],[-35,-33],[-39,-30],[-39,-31],[-43,-17],[-43,-30],[-43,-33],[-47,-33],[-47,-46],[-48,-30],[-50,-30],[-50,-31],[-51,-11],[-51,-30],[-52,-12],[-52,-51],[-53,-28],[-53,-33],[-53,-43],[-54,-8],[-54,-10],[-54,-29],[-54,-30],[-54,-51],[-54,-52],[-55,-51],[-56,-52],[-57,-36],[-57,-37],[-57,-38],[-59,-43],[-60,-23],[-60,-24],[-60,-34],[-60,-48],[-60,-55],[-61,-26],[-61,-28],[-61,-35],[-61,-49],[-61,-56],[-61,-60],[-62,-30],[-62,-60],[-62,-61],[-63,-24],[-63,-27],[-63,-30],[-63,-32],[-63,-39],[-63,-43],[-63,-48],[-63,-50],[-63,-62],[-64,-25],[-64,-31],[-64,-34],[-64,-39],[-64,-50],[-67,-30],[-67,-62],[-67,-63],[-68,-28],[-68,-33],[-68,-35],[-68,-43],[-68,-53],[-73,-51],[-73,-55],[-73,-60],[-73,-63],[-74,-10],[-74,-35],[-74,-49],[-74,-52],[-74,-56],[-74,-61],[-74,-67],[-1,-4,-31],[-2,-3,-33],[-3,-4,-25],[-3,-24,-33],[-3,-25,-32],[-3,-27,-33],[-4,-25,-30],[-63,1,18,23,25,61],[-67,2,18,26,28,60],[-27,-60,-68],[-3,-48,-54],[-60,3,29,30,31,69],[-63,3,26,29,31],[-64,3,26,29,30,66,69],[-6,-29,-43],[-29,-43,-47],[-9,-33,-54],[-33,-49,-54],[-67,4,23,29,33],[-68,4,23,29,32,65,69],[-34,-61,-72],[-5,-31,-47],[-57,5,15,25,50,58],[-6,-28,-46],[-17,-28,-57],[-28,-57,-59],[-20,-28,-72],[-31,19],[-33,17,59],[-33,20],[-41],[-44],[-7,72],[-46,72],[-47,72],[-32,8,10,11],[-58,8,13,24,36,40,51,56],[-8,-13,-58],[-61,9,22,53],[-59,10,13,27,36,42,52,55],[-14,11,30,42,45,52,54],[-39,11,52,54],[-58,11,30,42,45,52,54],[-21,11,30,52,54,66,69],[-63,11,52,54],[-16,12,32,40,45,51,54],[-59,12,32,40,45,51,54],[-22,12,32,51,54,65,69],[-67,12,51,54],[-73,13,36,56,71],[-74,13,36,55,70],[-58,21,63,70,73],[-59,22,67,71,74],[-20,17,53,59],[-40,65,71],[-65,40,71],[-71,40,65],[-42,66,70],[-66,42,70],[-70,42,66],[-45,69],[-69,45],[-75,34,39,48,50,55,58],[-76,35,43,49,53,56,59],[-77,25,31,41,46],[-31,77],[-78,24,27,30,32,51,52,54],[-79,60,63,64],[-80,61,67,68],[-81,62,73,74],[-82,28,38,44,47],[-83,23,26,29,33],[-23,83],[-26,83],[-33,83],[-84,36,37],[-85,75],[-85,76],[-86,78],[-86,79],[-87,77,86],[-88,77],[-88,86],[-90,85],[-89,87],[-90,88],[-91,80],[-91,81],[-92,83,84],[-93,84],[-94,82,92],[-95,82,93],[-95,92],[-96,93],[-97,91,95],[-98,91,96],[-97,94],[-98,95],[-99,96],[-100,89,99],[-100,90,98],[-100,97],[100],[-101,57],[-57,101],[-102,72],[-72,102],[-103,40,42,45],[-40,103],[-42,103],[-45,103],[-104,65,66,69],[-65,104],[-66,104],[-69,104],[-105,70,71],[-70,105],[-71,105],[-102,106],[-107,101],[-101,106],[-107,102],[-108,104,105],[-105,108],[-104,108],[-104,-105,109],[-110,103,108],[-109,111],[-103,-108,111],[-112,107,110],[-106,-111,113],[112],[-113],[-3,-13,-18,-20,-33,-46,-54,-57,-58,-59,-64,-67,-72,-73],[-3,-13,-20,-22,-33,-46,-54,-57,-58,-59,-61,-64,-72,-73],[-11,-13,-19,-21,-31,-32,-47,-57,-58,-59,-60,-68,-72,-74],[-3,-17,-18,-20,-33,-46,-54,-56,-57,-58,-64,-67,-72,-73],[-4,-13,-18,-19,-31,-47,-54,-57,-58,-59,-63,-68,-72,-74],[-4,-13,-19,-21,-31,-47,-54,-57,-58,-59,-60,-68,-72,-74],[-12,-13,-20,-22,-30,-33,-46,-57,-58,-59,-61,-64,-72,-73],[-4,-15,-18,-19,-31,-47,-54,-55,-57,-59,-63,-68,-72,-74],[11,14,21,30,39,42,45,52,54,55,58,63,66,69,70,73],[12,16,22,32,40,43,45,51,54,56,59,65,67,69,71,74],[6,17,20,33,47,53,59,68],[7,41,44,46,47,57,72]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":32,\"b\":2},{\"tag\":\"incompatible\",\"a\":34,\"b\":32},{\"tag\":\"incompatible\",\"a\":35,\"b\":3},{\"tag\":\"incompatible\",\"a\":35,\"b\":32},{\"tag\":\"incompatible\",\"a\":35,\"b\":34},{\"tag\":\"incompatible\",\"a\":37,\"b\":32},{\"tag\":\"incompatible\",\"a\":37,\"b\":35},{\"tag\":\"incompatible\",\"a\":38,\"b\":33},{\"tag\":\"incompatible\",\"a\":38,\"b\":34},{\"tag\":\"incompatible\",\"a\":38,\"b\":36},{\"tag\":\"incompatible\",\"a\":38,\"b\":37},{\"tag\":\"incompatible\",\"a\":39,\"b\":32},{\"tag\":\"incompatible\",\"a\":39,\"b\":35},{\"tag\":\"incompatible\",\"a\":39,\"b\":38},{\"tag\":\"incompatible\",\"a\":40,\"b\":2},{\"tag\":\"incompatible\",\"a\":40,\"b\":32},{\"tag\":\"incompatible\",\"a\":40,\"b\":34},{\"tag\":\"incompatible\",\"a\":40,\"b\":35},{\"tag\":\"incompatible\",\"a\":40,\"b\":38},{\"tag\":\"incompatible\",\"a\":40,\"b\":39},{\"tag\":\"incompatible\",\"a\":41,\"b\":32},{\"tag\":\"incompatible\",\"a\":41,\"b\":35},{\"tag\":\"incompatible\",\"a\":41,\"b\":38},{\"tag\":\"incompatible\",\"a\":41,\"b\":39},{\"tag\":\"incompatible\",\"a\":42,\"b\":35},{\"tag\":\"incompatible\",\"a\":42,\"b\":37},{\"tag\":\"incompatible\",\"a\":42,\"b\":38},{\"tag\":\"incompatible\",\"a\":42,\"b\":41},{\"tag\":\"incompatible\",\"a\":43,\"b\":40},{\"tag\":\"incompatible\",\"a\":44,\"b\":42},{\"tag\":\"incompatible\",\"a\":48,\"b\":39},{\"tag\":\"incompatible\",\"a\":48,\"b\":40},{\"tag\":\"incompatible\",\"a\":52,\"b\":23},{\"tag\":\"incompatible\",\"a\":52,\"b\":39},{\"tag\":\"incompatible\",\"a\":52,\"b\":42},{\"tag\":\"incompatible\",\"a\":56,\"b\":42},{\"tag\":\"incompatible\",\"a\":56,\"b\":55},{\"tag\":\"incompatible\",\"a\":57,\"b\":39},{\"tag\":\"incompatible\",\"a\":59,\"b\":39},{\"tag\":\"incompatible\",\"a\":59,\"b\":40},{\"tag\":\"incompatible\",\"a\":60,\"b\":17},{\"tag\":\"incompatible\",\"a\":60,\"b\":39},{\"tag\":\"incompatible\",\"a\":61,\"b\":18},{\"tag\":\"incompatible\",\"a\":61,\"b\":60},{\"tag\":\"incompatible\",\"a\":62,\"b\":37},{\"tag\":\"incompatible\",\"a\":62,\"b\":42},{\"tag\":\"incompatible\",\"a\":62,\"b\":52},{\"tag\":\"incompatible\",\"a\":63,\"b\":14},{\"tag\":\"incompatible\",\"a\":63,\"b\":16},{\"tag\":\"incompatible\",\"a\":63,\"b\":38},{\"tag\":\"incompatible\",\"a\":63,\"b\":39},{\"tag\":\"incompatible\",\"a\":63,\"b\":60},{\"tag\":\"incompatible\",\"a\":63,\"b\":61},{\"tag\":\"incompatible\",\"a\":64,\"b\":60},{\"tag\":\"incompatible\",\"a\":65,\"b\":61},{\"tag\":\"incompatible\",\"a\":66,\"b\":45},{\"tag\":\"incompatible\",\"a\":66,\"b\":46},{\"tag\":\"incompatible\",\"a\":66,\"b\":47},{\"tag\":\"incompatible\",\"a\":68,\"b\":52},{\"tag\":\"incompatible\",\"a\":69,\"b\":32},{\"tag\":\"incompatible\",\"a\":69,\"b\":33},{\"tag\":\"incompatible\",\"a\":69,\"b\":43},{\"tag\":\"incompatible\",\"a\":69,\"b\":57},{\"tag\":\"incompatible\",\"a\":69,\"b\":64},{\"tag\":\"incompatible\",\"a\":70,\"b\":35},{\"tag\":\"incompatible\",\"a\":70,\"b\":37},{\"tag\":\"incompatible\",\"a\":70,\"b\":44},{\"tag\":\"incompatible\",\"a\":70,\"b\":58},{\"tag\":\"incompatible\",\"a\":70,\"b\":65},{\"tag\":\"incompatible\",\"a\":70,\"b\":69},{\"tag\":\"incompatible\",\"a\":71,\"b\":39},{\"tag\":\"incompatible\",\"a\":71,\"b\":69},{\"tag\":\"incompatible\",\"a\":71,\"b\":70},{\"tag\":\"incompatible\",\"a\":72,\"b\":33},{\"tag\":\"incompatible\",\"a\":72,\"b\":36},{\"tag\":\"incompatible\",\"a\":72,\"b\":39},{\"tag\":\"incompatible\",\"a\":72,\"b\":41},{\"tag\":\"incompatible\",\"a\":72,\"b\":48},{\"tag\":\"incompatible\",\"a\":72,\"b\":52},{\"tag\":\"incompatible\",\"a\":72,\"b\":57},{\"tag\":\"incompatible\",\"a\":72,\"b\":59},{\"tag\":\"incompatible\",\"a\":72,\"b\":71},{\"tag\":\"incompatible\",\"a\":73,\"b\":34},{\"tag\":\"incompatible\",\"a\":73,\"b\":40},{\"tag\":\"incompatible\",\"a\":73,\"b\":43},{\"tag\":\"incompatible\",\"a\":73,\"b\":48},{\"tag\":\"incompatible\",\"a\":73,\"b\":59},{\"tag\":\"incompatible\",\"a\":76,\"b\":39},{\"tag\":\"incompatible\",\"a\":76,\"b\":71},{\"tag\":\"incompatible\",\"a\":76,\"b\":72},{\"tag\":\"incompatible\",\"a\":77,\"b\":37},{\"tag\":\"incompatible\",\"a\":77,\"b\":42},{\"tag\":\"incompatible\",\"a\":77,\"b\":44},{\"tag\":\"incompatible\",\"a\":77,\"b\":52},{\"tag\":\"incompatible\",\"a\":77,\"b\":62},{\"tag\":\"incompatible\",\"a\":82,\"b\":60},{\"tag\":\"incompatible\",\"a\":82,\"b\":64},{\"tag\":\"incompatible\",\"a\":82,\"b\":69},{\"tag\":\"incompatible\",\"a\":82,\"b\":72},{\"tag\":\"incompatible\",\"a\":83,\"b\":16},{\"tag\":\"incompatible\",\"a\":83,\"b\":44},{\"tag\":\"incompatible\",\"a\":83,\"b\":58},{\"tag\":\"incompatible\",\"a\":83,\"b\":61},{\"tag\":\"incompatible\",\"a\":83,\"b\":65},{\"tag\":\"incompatible\",\"a\":83,\"b\":70},{\"tag\":\"incompatible\",\"a\":83,\"b\":76},{\"tag\":\"three\",\"ridge\":7,\"vertices\":[0,3,40]},{\"tag\":\"three\",\"ridge\":7,\"vertices\":[1,2,42]},{\"tag\":\"three\",\"ridge\":7,\"vertices\":[2,3,34]},{\"tag\":\"three\",\"ridge\":7,\"vertices\":[2,33,42]},{\"tag\":\"three\",\"ridge\":7,\"vertices\":[2,34,41]},{\"tag\":\"three\",\"ridge\":7,\"vertices\":[2,36,42]},{\"tag\":\"three\",\"ridge\":7,\"vertices\":[3,34,39]},{\"tag\":\"mate\",\"ridge\":14,\"a\":72,\"owners\":[0,24,32,34,70]},{\"tag\":\"mate\",\"ridge\":22,\"a\":76,\"owners\":[1,24,35,37,69]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[36,69,77]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[2,57,63]},{\"tag\":\"mate\",\"ridge\":38,\"a\":69,\"owners\":[2,38,39,40,78]},{\"tag\":\"mate\",\"ridge\":38,\"a\":72,\"owners\":[2,35,38,40]},{\"tag\":\"mate\",\"ridge\":38,\"a\":73,\"owners\":[2,35,38,39,75,78]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[10,38,52]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[38,52,56]},{\"tag\":\"three\",\"ridge\":69,\"vertices\":[15,42,63]},{\"tag\":\"three\",\"ridge\":69,\"vertices\":[42,58,63]},{\"tag\":\"mate\",\"ridge\":70,\"a\":76,\"owners\":[3,32,38,42]},{\"tag\":\"mate\",\"ridge\":70,\"a\":77,\"owners\":[3,32,38,41,74,78]},{\"tag\":\"three\",\"ridge\":26,\"vertices\":[43,70,81]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[6,40,56]},{\"tag\":\"mate\",\"ridge\":265,\"a\":66,\"owners\":[6,21,34,59,67]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[10,37,55]},{\"tag\":\"three\",\"ridge\":529,\"vertices\":[23,37,66]},{\"tag\":\"three\",\"ridge\":529,\"vertices\":[37,66,68]},{\"tag\":\"three\",\"ridge\":530,\"vertices\":[28,37,81]},{\"tag\":\"mate\",\"ridge\":290,\"a\":40,\"owners\":[27]},{\"tag\":\"mate\",\"ridge\":577,\"a\":42,\"owners\":[23,68]},{\"tag\":\"mate\",\"ridge\":578,\"a\":42,\"owners\":[28]},{\"tag\":\"mate\",\"ridge\":769,\"a\":50,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":769,\"a\":53,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":770,\"a\":11,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":770,\"a\":55,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":770,\"a\":56,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":133,\"a\":41,\"owners\":[14,16,17]},{\"tag\":\"mate\",\"ridge\":137,\"a\":67,\"owners\":[14,19,33,45,49,60,65]},{\"tag\":\"three\",\"ridge\":137,\"vertices\":[14,19,67]},{\"tag\":\"mate\",\"ridge\":84,\"a\":70,\"owners\":[15,31,62]},{\"tag\":\"mate\",\"ridge\":145,\"a\":68,\"owners\":[16,19,36,45,51,61,64]},{\"tag\":\"mate\",\"ridge\":161,\"a\":20,\"owners\":[17,39,51,54,61,63]},{\"tag\":\"mate\",\"ridge\":161,\"a\":48,\"owners\":[17,61,63]},{\"tag\":\"mate\",\"ridge\":161,\"a\":67,\"owners\":[17,39,51,54,61,63]},{\"tag\":\"mate\",\"ridge\":164,\"a\":30,\"owners\":[17,39,61,63,75,78]},{\"tag\":\"mate\",\"ridge\":164,\"a\":72,\"owners\":[17,61,63]},{\"tag\":\"mate\",\"ridge\":193,\"a\":22,\"owners\":[18,41,49,54,60,63]},{\"tag\":\"mate\",\"ridge\":193,\"a\":68,\"owners\":[18,41,49,54,60,63]},{\"tag\":\"mate\",\"ridge\":196,\"a\":31,\"owners\":[18,41,60,63,74,78]},{\"tag\":\"mate\",\"ridge\":196,\"a\":76,\"owners\":[18,60,63]},{\"tag\":\"mate\",\"ridge\":152,\"a\":82,\"owners\":[19,45,65,80]},{\"tag\":\"mate\",\"ridge\":152,\"a\":83,\"owners\":[19,45,64,79]},{\"tag\":\"mate\",\"ridge\":168,\"a\":67,\"owners\":[30,72,79,82]},{\"tag\":\"mate\",\"ridge\":208,\"a\":68,\"owners\":[31,76,80,83]},{\"tag\":\"mate\",\"ridge\":592,\"a\":28,\"owners\":[23,62,68]},{\"tag\":\"mate\",\"ridge\":202,\"a\":49,\"owners\":[74,80]},{\"tag\":\"mate\",\"ridge\":202,\"a\":74,\"owners\":[49,80]},{\"tag\":\"mate\",\"ridge\":202,\"a\":80,\"owners\":[49,74]},{\"tag\":\"mate\",\"ridge\":178,\"a\":51,\"owners\":[75,79]},{\"tag\":\"mate\",\"ridge\":178,\"a\":75,\"owners\":[51,79]},{\"tag\":\"mate\",\"ridge\":178,\"a\":79,\"owners\":[51,75]},{\"tag\":\"mate\",\"ridge\":226,\"a\":54,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":226,\"a\":78,\"owners\":[54]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[43,48,57,59,64,67],\"full_literals\":[-75,34,39,48,50,55,58]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[44,52,58,62,65,68],\"full_literals\":[-76,35,43,49,53,56,59]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[34,40,50,55],\"full_literals\":[-77,25,31,41,46]},{\"tag\":\"group_take\",\"kind\":2,\"index\":2,\"member\":40,\"full_literals\":[-31,77]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[33,36,39,41,60,61,63],\"full_literals\":[-78,24,27,30,32,51,52,54]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[69,72,73],\"full_literals\":[-79,60,63,64]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[70,76,77],\"full_literals\":[-80,61,67,68]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[71,82,83],\"full_literals\":[-81,62,73,74]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[37,47,53,56],\"full_literals\":[-82,28,38,44,47]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[32,35,38,42],\"full_literals\":[-83,23,26,29,33]},{\"tag\":\"group_take\",\"kind\":2,\"index\":8,\"member\":32,\"full_literals\":[-23,83]},{\"tag\":\"group_take\",\"kind\":2,\"index\":8,\"member\":35,\"full_literals\":[-26,83]},{\"tag\":\"group_take\",\"kind\":2,\"index\":8,\"member\":42,\"full_literals\":[-33,83]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[45,46],\"full_literals\":[-84,36,37]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-85,75,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-85,false,76],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0008\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-86,78,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-86,false,79],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-87,77,86],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-88,77,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-88,false,86],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-90,85,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-89,false,87],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-90,false,88],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-91,80,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-91,false,81],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0018\",\"joined_name\":\"grouped2_0017\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-92,83,84],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0018\",\"joined_name\":\"grouped2_0017\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-93,false,84],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-94,82,92],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-95,82,93],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-95,false,92],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-96,false,93],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-97,91,95],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-98,91,96],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-97,false,94],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-98,false,95],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-99,false,96],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-100,89,99],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-100,90,98],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-100,false,97],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[66],\"full_literals\":[-101,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":66,\"full_literals\":[-57,101]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[81],\"full_literals\":[-102,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":81,\"full_literals\":[-72,102]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[49,51,54],\"full_literals\":[-103,40,42,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":49,\"full_literals\":[-40,103]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":51,\"full_literals\":[-42,103]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":54,\"full_literals\":[-45,103]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[74,75,78],\"full_literals\":[-104,65,66,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":74,\"full_literals\":[-65,104]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":75,\"full_literals\":[-66,104]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":78,\"full_literals\":[-69,104]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[79,80],\"full_literals\":[-105,70,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":79,\"full_literals\":[-70,105]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":80,\"full_literals\":[-71,105]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-102,106],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-107,101,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-101,false,106],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-107,false,102],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-108,104,105],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-105,108],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-104,false,108],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-104,-105,109],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-110,103,108],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-109,111],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-103,-108,111],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-112,107,110],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-106,-111,113],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"block\",\"leaf\":0,\"vertices\":[2,19,24,28,42,55,63,66,67,68,73,76,81,82]},{\"tag\":\"block\",\"leaf\":1,\"vertices\":[2,19,28,31,42,55,63,66,67,68,70,73,81,82]},{\"tag\":\"block\",\"leaf\":2,\"vertices\":[17,19,27,30,40,41,56,66,67,68,69,77,81,83]},{\"tag\":\"block\",\"leaf\":3,\"vertices\":[2,23,24,28,42,55,63,65,66,67,73,76,81,82]},{\"tag\":\"block\",\"leaf\":4,\"vertices\":[3,19,24,27,40,56,63,66,67,68,72,77,81,83]},{\"tag\":\"block\",\"leaf\":5,\"vertices\":[3,19,27,30,40,56,63,66,67,68,69,77,81,83]},{\"tag\":\"block\",\"leaf\":6,\"vertices\":[18,19,28,31,39,42,55,66,67,68,70,73,81,82]},{\"tag\":\"block\",\"leaf\":7,\"vertices\":[3,21,24,27,40,56,63,64,66,68,72,77,81,83]},{\"tag\":\"edge\",\"edge\":36,\"owners\":[17,20,30,39,48,51,54,61,63,64,67,72,75,78,79,82]},{\"tag\":\"edge\",\"edge\":39,\"owners\":[18,22,31,41,49,52,54,60,63,65,68,74,76,78,80,83]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[10,23,28,42,56,62,68,77]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[11,50,53,55,56,66,81]}]}"
  "252 -77 25 31 46 0 137 171 0\n253 -82 28 38 47 0 138 177 0\n254 97 0 209 208 0\n255 94 0 254 203 0\n256 7 46 47 57 72 0 137 138 251 0\n257 106 0 225 227 213 211 139 140 141 256 0\n258 -111 0 257 239 237 0\n259 -109 0 258 234 0\n260 -105 103 0 259 216 215 232 219 220 163 166 222 0\n261 -108 0 258 235 215 216 217 168 260 223 224 229 165 162 218 0\n262 -105 0 261 230 0\n263 -104 0 261 231 0\n264 -70 0 262 223 0\n265 -71 0 262 224 0\n266 -65 0 263 219 0\n267 -66 0 263 220 0\n268 -69 0 263 221 0\n269 -40 0 266 265 161 0\n270 -42 0 267 264 164 0\n271 -45 0 268 167 0\n272 -103 0 269 270 271 214 0\n273 -110 0 272 261 233 0\n274 107 0 273 238 236 0\n275 101 0 274 226 0\n276 102 0 274 228 0\n277 57 0 275 210 0\n278 72 0 276 212 0\n279 -36 0 277 56 0\n280 -37 0 277 57 0\n281 -38 0 277 58 0\n282 -84 0 280 279 182 0\n283 -93 0 282 196 0\n284 -96 0 283 200 0\n285 -99 0 284 205 0\n286 89 0 285 209 206 0\n287 87 0 286 191 0\n288 -28 -83 0 6 7 11 26 178 0\n289 -23 -77 46 0 2 16 252 0\n290 -26 -77 46 0 5 18 252 0\n291 -77 -95 0 282 281 283 198 199 195 288 253 37 36 289 290 178 9 19 252 0\n292 51 43 54 32 30 27 24 -78 0 265 268 266 271 269 173 43 55 103 152 154 155 153 249 0\n293 43 54 -78 32 30 27 24 0 270 271 267 268 264 292 41 44 96 54 151 150 147 148 149 248 0\n294 -29 -95 0 282 281 283 287 291 187 185 198 199 195 288 253 8 10 14 23 50 122 293 0\n295 -30 -95 0 282 281 283 294 198 199 195 288 253 36 12 13 178 0\n296 -32 -95 0 282 281 283 294 198 199 195 288 253 36 21 22 178 0\n297 26 -95 0 282 281 283 287 268 267 295 294 291 187 186 172 198 199 195 288 253 36 178 1 60 119 120 174 0\n298 -98 0 284 283 282 281 268 266 202 204 193 198 199 195 288 253 36 294 296 297 3 4 65 125 126 175 0\n299 90 0 298 209 207 0\n300 85 0 299 190 0\n301 88 0 299 192 0\n302 75 0 300 183 0\n303 76 0 300 184 0\n304 77 0 301 188 0\n305 86 0 301 189 0\n306 -95 0 304 291 0\n307 78 0 305 185 0\n308 79 0 305 186 0\n309 91 0 306 254 201 0\n310 80 0 309 193 0\n311 81 0 309 194 0\n312 -26 33 29 0 268 266 310 3 4 22 65 125 126 175 0\n313 33 -83 29 30 0 268 267 308 312 178 1 16 60 119 120 174 0\n314 -60 68 0 310 311 70 72 98 175 176 106 0\n315 59 -18 -67 -54 -3 -64 -33 0 304 311 302 303 278 277 117 86 87 85 89 106 176 97 169 124 84 83 252 136 46 35 30 135 170 243 0\n316 -67 -54 -3 -64 -33 28 0 304 311 302 270 279 278 277 117 53 49 112 108 84 83 252 87 86 85 92 314 136 25 89 106 115 176 97 169 315 146 240 0\n317 -64 -83 29 30 0 268 267 304 307 310 303 311 265 279 302 278 277 313 136 92 46 35 30 28 25 288 83 84 85 86 87 120 252 110 112 293 123 124 117 316 175 69 73 105 145 170 176 97 156 169 241 0\n318 -83 29 30 0 311 310 308 313 92 314 317 174 82 90 99 175 176 105 0\n319 -3 46 -4 0 304 15 109 252 0\n320 -58 -18 -31 -47 -4 -54 -63 0 310 303 311 269 279 278 277 134 82 99 176 104 79 102 101 90 105 175 95 170 52 48 74 143 244 0\n321 -63 29 30 0 282 255 307 311 310 268 266 281 303 302 278 277 318 195 197 180 179 74 75 77 78 79 80 81 82 90 99 293 176 101 102 104 105 175 91 95 126 253 170 37 319 119 17 29 128 134 107 114 320 129 169 247 0\n322 32 3 -68 29 30 0 281 282 255 279 311 303 302 264 267 308 268 266 307 278 277 321 318 180 120 174 98 63 118 32 64 62 40 169 158 95 94 72 176 102 93 104 170 157 134 116 61 195 197 91 253 179 126 293 245 0\n323 3 -68 29 30 0 281 282 255 267 308 268 311 279 302 303 264 278 277 318 195 197 91 253 95 94 93 321 180 120 174 62 63 64 72 98 118 176 32 40 134 100 102 104 157 169 170 144 158 322 142 242 0\n324 -68 29 30 0 282 255 281 304 268 266 318 195 197 179 91 253 37 323 15 319 252 126 111 0\n325 29 30 0 278 277 281 304 308 255 282 318 181 195 197 321 324 314 174 83 84 252 37 253 45 130 131 132 133 250 0\n326 17 68 6 33 47 53 59 0 250 160 0\n327 30 0 304 307 325 8 9 10 19 23 27 50 252 293 37 33 47 59 94 121 326 0\n328 -23 0 327 12 0\n329 -26 0 327 13 0\n330 -29 0 327 14 0\n331 -31 0 327 20 0\n332 -32 0 327 24 0\n333 -39 0 327 31 0\n334 -43 0 327 34 0\n335 -48 0 327 38 0\n336 -50 0 327 39 0\n337 -51 0 327 42 0\n338 -54 0 327 51 0\n339 -62 0 327 71 0\n340 -63 0 327 76 0\n341 -67 0 327 88 0\n342 68 0 310 308 340 339 311 304 331 279 335 333 302 336 281 255 282 328 330 329 334 303 265 341 338 271 269 337 332 278 277 327 314 175 174 66 67 68 69 105 127 83 176 252 97 156 37 169 253 197 195 178 46 136 170 159 153 246 0\n343 -28 0 342 91 0\n344 -33 0 342 92 0\n345 4 0 342 328 330 332 266 268 126 0\n346 -83 0 344 329 330 328 178 0\n347 -25 0 345 327 113 0\n348 -92 0 346 282 195 0\n349 46 0 347 331 304 252 0\n350 82 0 348 255 197 0\n351 -47 0 349 37 0\n352 0 351 350 281 343 253 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record028.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record028.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record028.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record028.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record028 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeafTable : ConcreteGrowth.Table (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record028.l) :=
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
 (.leaf (⟨0, by decide⟩))
 (.leaf (⟨1, by decide⟩)))
 (.branch 7
 (.leaf (⟨2, by decide⟩))
 (.leaf (⟨3, by decide⟩)))))
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record028.l := originalLeafTable.get j.val
def orbitWordTable : ConcreteGrowth.Table (List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record028.g)) :=
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
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 7
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record028.g) := orbitWordTable.get j.val
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record028.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record028.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record028 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record028_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record028_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record028_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record028_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record028_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record028_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record028_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record028 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record028_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record028_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record028_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00024.record028
