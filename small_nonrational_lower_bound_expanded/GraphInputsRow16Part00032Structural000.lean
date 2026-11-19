module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow16Part00032Data
public import GraphInputsRow16Part00032Frames
public import GraphInputsRow16Part00032Leaves
public import GraphInputsRow16Part00032Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00032.record007
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record007
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨58, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨70, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 27021597764222976, (certNat% 3), (certNat% 4), 72292889526272, 7885697394409472]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), 574082508652544, (certNat% 6), (certNat% 7), 72018011619328]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), 985162418487296, (certNat% 9), (certNat% 10), 80264348827648]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), 3395361162919936, (certNat% 12), (certNat% 13), 72293963268096, (certNat% 14)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), (certNat% 16), 27021598032658432, (certNat% 4), 145685290680320, 8162845191569408, 115724672565248]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record007_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record007_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00032.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00032.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record008
def vertexColumn : Fields := ⟨10, (certNat% 17)⟩
def kindColumn : Fields := ⟨3, (certNat% 18)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [17732907753799680, (certNat% 19), 15569256448, 90071992547409920, (certNat% 20), 281474976710656]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), (certNat% 22), (certNat% 23), 246428043575296, 2533287675297792, 1690224249798656, 13526194200772608]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record008_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00032.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00032.record029
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record029
def vertexColumn : Fields := ⟨10, (certNat% 24)⟩
def kindColumn : Fields := ⟨3, (certNat% 25)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [63050394783186944, (certNat% 26), 377132488327168, 738880403800064, 7890099735887872, 261657460736, 824935710720]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record029_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record029_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record029_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record029_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record029_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record029_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record029_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record029_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record029_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00032.record029

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00032.record040
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record040
def vertexColumn : Fields := ⟨10, (certNat% 27)⟩
def kindColumn : Fields := ⟨3, (certNat% 28)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), 9232379511524294656, 346777172381270016, (certNat% 30), 289171558105088, 4204532464615424, 255953207296]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record040_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record040_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record040_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record040_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record040_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record040_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record040_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record040_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record040_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00032.record040

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00032.record015
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "d8a5a7195635a2e4b89e0fb61965c5554d58b52d2743dd0ec370f2398d6394d5392d2b86c9b16c3b61d4731e2729d1715c3783d0f23cd28a9262582e078d18a5252542d0764350cc388d2324c5382c2b06d0721c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6d24936da492492492492492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record015 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record015 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record015.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record015.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record015.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 31), (facetIndex 35), (facetIndex 36), (facetIndex 56), (facetIndex 65)]))
 (.leaf ([(facetIndex 52), (facetIndex 54), (facetIndex 55)])))
 (.branch 3
 (.leaf ([(facetIndex 27), (facetIndex 30), (facetIndex 32), (facetIndex 40), (facetIndex 53), (facetIndex 62)]))
 (.leaf ([(facetIndex 61), (facetIndex 63), (facetIndex 64)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 46), (facetIndex 47), (facetIndex 48), (facetIndex 51)]))
 (.leaf ([(facetIndex 28), (facetIndex 29), (facetIndex 38), (facetIndex 41), (facetIndex 42)])))
 (.branch 7
 (.leaf ([(facetIndex 39), (facetIndex 43), (facetIndex 44), (facetIndex 45), (facetIndex 49), (facetIndex 50)]))
 (.leaf ([(facetIndex 33), (facetIndex 34), (facetIndex 37)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36980002519b4936d6ad781fa0ad4z14;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 59)]))
 (.branch 2
 (.leaf ([(facetIndex 60)]))
 (.leaf ([(facetIndex 68)]))))
 (.branch 4
 (.leaf ([(facetIndex 69)]))
 (.branch 5
 (.leaf ([(facetIndex 57), (facetIndex 58)]))
 (.leaf ([(facetIndex 66), (facetIndex 67)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1ab4000112z2b;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4]
def grouped2_0003 : List Nat := [4, 5]
def grouped2_0004 : List Nat := [4, 5, 6, 7]
def grouped2_0005 : List Nat := [5]
def grouped2_0006 : List Nat := [6, 7]
def grouped3_0007 : List Nat := [0]
def grouped3_0008 : List Nat := [0, 1, 2]
def grouped3_0010 : List Nat := [1]
def grouped3_0011 : List Nat := [1, 2]
def grouped3_0012 : List Nat := [2]
def grouped3_0013 : List Nat := [3]
def grouped3_0014 : List Nat := [3, 4, 5]
def grouped3_0015 : List Nat := [4]
def grouped3_0016 : List Nat := [4, 5]
def grouped3_0017 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record015 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record015_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00032.record015" "{\"atoms\":[{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00032.record015" 37

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00032.record015" "{\"ridges\":[[13,322],[14,577],[36,321],[43,577],[44,322],[45,577],[46,322],[47,577],[49,322],[50,577],[51,322],[51,577],[59,600],[68,600],[69,864]],\"owners\":[[36,321,[60],[13,44,46,49,51,57,58]],[13,322,[66,67,69],[36,44,46,49,51]],[44,322,[67,69],[13,36,46,49,51,66]],[46,322,[66,67],[13,36,44,49,51,69]],[49,322,[66,69],[13,36,44,46,51,67]],[51,322,[66,67],[13,36,44,46,49,69]],[14,577,[59,60],[43,45,47,50,51]],[43,577,[60],[14,45,47,50,51,59]],[45,577,[60],[14,43,47,50,51,59]],[47,577,[59],[14,43,45,50,51,60]],[50,577,[59,60],[14,43,45,47,51]],[51,577,[59],[14,43,45,47,50,60]],[59,600,[68],[]],[68,600,[59],[]],[69,864,[60],[]]],\"edges\":[[40,[13,36,44,46,49,51,57,58,60,66,67,69]],[41,[14,43,45,47,50,51,59,60,68,69]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00032.record015" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00032.record015\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-16,-7],[-16,-9],[-3,16],[-1,17,18,20],[-5,18,20],[-7,17,18],[-10,17,20],[-12,17,18],[-2,15,16],[-4,16],[-6,16],[-8,15],[-11,15,16],[-12,15],[-15,19],[-19,15],[-20,16],[-21,7,8,9,12],[-22,21],[-23,22],[-24,23],[24],[-25,15],[-15,25],[-26,16],[-16,26],[-27,19],[-19,27],[-13,28],[-14,28],[-17,29],[-18,29],[-30,26,27],[-27,30],[-26,30],[-26,-27,31],[-32,25,30],[-30,32],[-25,32],[-25,-30,33],[-25,-31,34],[-29,35],[-28,35],[-35,36],[-33,-36,37],[-34,37],[-37],[1,3,5,7,10,12,13,14,16,17,18,20],[2,4,6,8,11,12,15,16,19,20]],\"atoms\":[{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":60,\"b\":46},{\"tag\":\"incompatible\",\"a\":60,\"b\":48},{\"tag\":\"mate\",\"ridge\":321,\"a\":36,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":322,\"a\":13,\"owners\":[66,67,69]},{\"tag\":\"mate\",\"ridge\":322,\"a\":44,\"owners\":[67,69]},{\"tag\":\"mate\",\"ridge\":322,\"a\":46,\"owners\":[66,67]},{\"tag\":\"mate\",\"ridge\":322,\"a\":49,\"owners\":[66,69]},{\"tag\":\"mate\",\"ridge\":322,\"a\":51,\"owners\":[66,67]},{\"tag\":\"mate\",\"ridge\":577,\"a\":14,\"owners\":[59,60]},{\"tag\":\"mate\",\"ridge\":577,\"a\":43,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":577,\"a\":45,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":577,\"a\":47,\"owners\":[59]},{\"tag\":\"mate\",\"ridge\":577,\"a\":50,\"owners\":[59,60]},{\"tag\":\"mate\",\"ridge\":577,\"a\":51,\"owners\":[59]},{\"tag\":\"mate\",\"ridge\":600,\"a\":59,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":600,\"a\":68,\"owners\":[59]},{\"tag\":\"mate\",\"ridge\":864,\"a\":69,\"owners\":[60]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[46,47,48,51],\"full_literals\":[-21,7,8,9,12]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-22,21,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-23,22,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-24,false,23],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[59],\"full_literals\":[-25,15]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":59,\"full_literals\":[-15,25]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[60],\"full_literals\":[-26,16]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":60,\"full_literals\":[-16,26]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[68],\"full_literals\":[-27,19]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":68,\"full_literals\":[-19,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":57,\"full_literals\":[-13,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":58,\"full_literals\":[-14,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":66,\"full_literals\":[-17,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":67,\"full_literals\":[-18,29]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-30,26,27],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-27,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-26,false,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-26,-27,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-32,25,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-30,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-25,false,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-25,-30,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-25,-31,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-29,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-28,false,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-35,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-33,-36,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-34,false,37],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":40,\"owners\":[13,36,44,46,49,51,57,58,60,66,67,69]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[14,43,45,47,50,51,59,60,68,69]}]}"
  "50 23 0 22 21 0\n51 22 0 50 20 0\n52 21 0 51 19 0\n53 -34 0 47 46 0\n54 32 0 38 39 34 35 24 28 26 9 12 13 14 10 11 17 49 0\n55 30 0 54 34 37 28 23 15 0\n56 15 0 55 52 12 14 16 27 33 25 1 2 18 0\n57 19 0 56 15 0\n58 25 0 56 24 0\n59 27 0 57 28 0\n60 33 0 58 55 40 0\n61 -31 0 58 53 41 0\n62 -26 0 59 61 36 0\n63 -36 0 60 47 45 0\n64 -16 0 62 26 0\n65 -35 0 63 44 0\n66 -3 0 64 3 0\n67 -20 0 64 17 0\n68 -29 0 65 42 0\n69 -28 0 65 43 0\n70 -17 0 68 31 0\n71 -18 0 68 32 0\n72 -13 0 69 29 0\n73 -14 0 69 30 0\n74 -1 0 70 71 67 4 0\n75 -7 0 70 71 6 0\n76 -10 0 70 67 7 0\n77 -12 0 70 71 8 0\n78 -5 0 71 67 5 0\n79 0 78 71 74 75 76 77 72 73 64 70 66 67 48 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record015.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record015.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record015.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record015.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record015 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record015.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record015.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record015.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record015.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record015 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record015_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record015_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record015_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record015_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record015_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record015_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record015_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record015 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record015_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record015_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record015_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00032.record015

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00032.record045
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "d8a5a699568d94e2b89e17b61965a555635534ad2745dd0f23a8da398d6354e3392d4b32cab86c9b61d4789e1745c9715c3743c4f0be52169262988e07a51165252948d0764350e2348ca384c5322c4b06d0721c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1a4db49349b692492492492492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record045 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record045 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record045.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record045.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record045.data.quota

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
 (.leaf ([(facetIndex 31), (facetIndex 39), (facetIndex 43), (facetIndex 45), (facetIndex 59), (facetIndex 68)]))
 (.leaf ([(facetIndex 27), (facetIndex 32), (facetIndex 53), (facetIndex 54)])))
 (.branch 3
 (.leaf ([(facetIndex 30), (facetIndex 35), (facetIndex 37), (facetIndex 48), (facetIndex 58), (facetIndex 67)]))
 (.branch 4
 (.leaf ([(facetIndex 28), (facetIndex 38), (facetIndex 61), (facetIndex 62)]))
 (.leaf ([(facetIndex 44), (facetIndex 47), (facetIndex 49), (facetIndex 50)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 41), (facetIndex 42), (facetIndex 51)]))
 (.leaf ([(facetIndex 29), (facetIndex 33), (facetIndex 34)])))
 (.branch 8
 (.leaf ([(facetIndex 40), (facetIndex 63)]))
 (.branch 9
 (.leaf ([(facetIndex 36), (facetIndex 52)]))
 (.leaf ([(facetIndex 46)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "20007330020001185442490405570328266102631z1b;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 56)]))
 (.branch 2
 (.leaf ([(facetIndex 60)]))
 (.leaf ([(facetIndex 65)]))))
 (.branch 4
 (.leaf ([(facetIndex 69)]))
 (.branch 5
 (.leaf ([(facetIndex 55), (facetIndex 57)]))
 (.leaf ([(facetIndex 64), (facetIndex 66)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "181550010208z29;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

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
def grouped1_0019 : List Nat := [11, 12]
def grouped1_0020 : List Nat := [13]
def grouped1_0021 : List Nat := [13, 14, 15]
def grouped1_0022 : List Nat := [13, 14, 15, 16, 17, 18, 19]
def grouped1_0023 : List Nat := [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]
def grouped1_0024 : List Nat := [14]
def grouped1_0025 : List Nat := [14, 15]
def grouped1_0026 : List Nat := [15]
def grouped1_0027 : List Nat := [16]
def grouped1_0028 : List Nat := [16, 17]
def grouped1_0029 : List Nat := [16, 17, 18, 19]
def grouped1_0030 : List Nat := [17]
def grouped1_0031 : List Nat := [18]
def grouped1_0032 : List Nat := [18, 19]
def grouped1_0033 : List Nat := [19]
def grouped1_0034 : List Nat := [20]
def grouped1_0035 : List Nat := [20, 21, 22]
def grouped1_0036 : List Nat := [20, 21, 22, 23, 24, 25, 26]
def grouped1_0037 : List Nat := [21]
def grouped1_0038 : List Nat := [21, 22]
def grouped1_0039 : List Nat := [22]
def grouped1_0040 : List Nat := [23]
def grouped1_0041 : List Nat := [23, 24]
def grouped1_0042 : List Nat := [23, 24, 25, 26]
def grouped1_0043 : List Nat := [24]
def grouped1_0044 : List Nat := [25]
def grouped1_0045 : List Nat := [25, 26]
def grouped1_0046 : List Nat := [26]
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
def grouped3_0073 : List Nat := [3, 4, 5]
def grouped3_0074 : List Nat := [4]
def grouped3_0075 : List Nat := [4, 5]
def grouped3_0076 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record045 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record045_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00032.record045" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"group\",\"kind\":1,\"index\":4},{\"tag\":\"group\",\"kind\":1,\"index\":7},{\"tag\":\"group\",\"kind\":1,\"index\":9},{\"tag\":\"group\",\"kind\":1,\"index\":10},{\"tag\":\"group\",\"kind\":1,\"index\":13},{\"tag\":\"group\",\"kind\":1,\"index\":15},{\"tag\":\"group\",\"kind\":1,\"index\":16},{\"tag\":\"group\",\"kind\":1,\"index\":17},{\"tag\":\"group\",\"kind\":1,\"index\":18},{\"tag\":\"group\",\"kind\":1,\"index\":19},{\"tag\":\"group\",\"kind\":1,\"index\":20},{\"tag\":\"group\",\"kind\":1,\"index\":21},{\"tag\":\"group\",\"kind\":1,\"index\":22},{\"tag\":\"group\",\"kind\":1,\"index\":23},{\"tag\":\"group\",\"kind\":1,\"index\":24},{\"tag\":\"group\",\"kind\":1,\"index\":25},{\"tag\":\"group\",\"kind\":1,\"index\":26},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0007\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0005\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0013\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0010\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0016\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0017\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0011\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0011\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0002\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0002\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0025\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0021\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0028\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0028\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0032\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0032\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0029\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0029\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0029\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0022\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0022\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0022\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0038\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0035\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0035\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0041\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0041\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0045\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0045\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0042\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0042\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0042\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0036\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0036\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0036\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":4,\"list_name\":\"grouped1_0036\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":4,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":4,\"list_name\":\"groupKind1\"},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0048\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0055\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0053\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0049\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0049\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0058\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0064\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0064\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0062\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0062\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0062\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0059\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0059\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0059\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0070\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0070\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0067\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0067\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0067\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0075\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0073\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0073\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00032.record045" 166

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00032.record045" "{\"ridges\":[[2,7],[2,38],[8,81],[8,82],[9,529],[9,530],[10,131],[11,35],[11,289],[11,290],[12,545],[13,322],[14,67],[14,577],[14,578],[18,289],[20,81],[20,577],[20,592],[24,38],[24,262],[24,290],[26,82],[26,578],[33,19],[33,261],[34,7],[34,529],[34,530],[35,545],[36,7],[36,67],[36,261],[36,321],[37,262],[40,35],[40,137],[40,138],[40,162],[41,67],[41,74],[42,11],[42,322],[43,578],[44,35],[44,529],[44,530],[44,545],[45,82],[45,322],[46,322],[47,545],[49,545],[50,545],[51,322],[52,81],[53,28],[54,37],[56,564],[58,292],[59,529],[59,592],[60,289],[60,321],[60,577],[60,864],[61,82],[62,28],[62,138],[63,38],[63,140],[65,564],[67,134],[67,164],[67,292],[68,88],[68,530],[68,592],[69,290],[69,578],[69,864]],\"owners\":[[34,7,[0,2,3,4,28,36],[1,31,35]],[42,11,[0,5,7,27,39,40],[6,29,43]],[33,19,[5,8,9,38,44],[1,30,32,45]],[44,35,[2,10,11,27,40,46],[12,30,47]],[54,37,[2,18,30,35,56],[17,27]],[63,38,[2,24,30,35,65],[23,27]],[10,131,[3,7,32,37,38,41],[48,49]],[67,134,[3,22,32,62],[23,37]],[33,261,[18,55,58],[4,29,36,37,57]],[36,261,[18,58],[4,29,33,37,55,57]],[24,262,[4,29,33,36,37,64,66],[67]],[37,262,[24,64,66],[4,29,33,36,67]],[41,67,[8,13,14,31,36,46,47],[6,28]],[41,74,[25,61,64,68],[6,28,42,43]],[40,137,[16,53],[7,38,41,54]],[40,138,[22,62],[7,38,41,63]],[62,138,[7,40,41],[22,38,63]],[52,81,[8,20,45],[19,31,57]],[26,82,[8,25,31,45,61,66],[]],[9,529,[20,56,59],[34,39,44]],[34,529,[20,59],[9,39,44,56]],[44,529,[20,59],[9,34,39,56]],[59,529,[9,34,44,56],[20,39]],[9,530,[26,65,68],[34,39,44]],[34,530,[26,68],[9,39,44,65]],[44,530,[26,68],[9,34,39,65]],[68,530,[9,34,44,65],[26,39]],[40,162,[23,67],[10,48,49,63]],[69,290,[11,24,48,67],[46,50]],[12,545,[56,60],[35,44,47,49,50]],[35,545,[60],[12,44,47,49,50,56]],[44,545,[60],[12,35,47,49,50,56]],[47,545,[56],[12,35,44,49,50,60]],[49,545,[56,60],[12,35,44,47,50]],[50,545,[56],[12,35,44,47,49,60]],[36,321,[60],[13,42,45,46,51,55,57]],[60,321,[13,36,42,45,55,57],[46,51]],[13,322,[64,66,69],[36,42,45,46,51]],[42,322,[66,69],[13,36,45,46,51,64]],[45,322,[64,69],[13,36,42,46,51,66]],[46,322,[64,66],[13,36,42,45,51,69]],[51,322,[64,66],[13,36,42,45,46,69]],[69,578,[14,26,43,68],[47,51]],[53,28,[21,61],[15,52,62]],[62,28,[15,52],[21,53,61]],[63,140,[16,53],[22,54,62]],[67,164,[17,54],[23,58,63]],[58,292,[24],[18,67]],[67,292,[18],[24,58]],[68,88,[19,52],[25,59,61]],[20,592,[26,68],[59]],[59,592,[26],[20,68]],[68,592,[20],[26,59]],[56,564,[65],[]],[65,564,[56],[]],[60,864,[69],[]],[69,864,[60],[]]],\"edges\":[[34,[9,20,26,34,39,44,56,59,65,68]],[38,[12,35,44,47,49,50,56,60,65,69]],[40,[13,36,42,45,46,51,55,57,60,64,66,69]]],\"groupings\":[1,2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00032.record045" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00032.record045\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-32,-2],[-32,-3],[-33,-7],[-33,-29],[-34,-33],[-35,-26],[-35,-27],[-35,-28],[-35,-29],[-35,-30],[-35,-31],[-35,-32],[-39,-26],[-39,-31],[-40,-37],[-40,-39],[-41,-7],[-41,-35],[-42,-35],[-43,-29],[-43,-33],[-43,-34],[-44,-32],[-44,-33],[-44,-35],[-44,-41],[-47,-39],[-47,-43],[-48,-2],[-48,-29],[-48,-34],[-48,-39],[-51,-5],[-51,-27],[-51,-30],[-51,-35],[-51,-37],[-51,-38],[-52,-1],[-52,-26],[-52,-27],[-52,-28],[-52,-31],[-52,-37],[-52,-51],[-53,-3],[-53,-15],[-53,-52],[-57,-53],[-58,-51],[-59,-45],[-59,-50],[-60,-5],[-60,-30],[-60,-35],[-60,-38],[-60,-51],[-61,-1],[-61,-20],[-61,-21],[-61,-26],[-61,-28],[-61,-31],[-61,-52],[-62,-3],[-62,-22],[-62,-26],[-62,-31],[-62,-36],[-62,-61],[-66,-22],[-66,-23],[-67,-25],[-67,-60],[-33,1,2,3,4,27,35],[-2,-33,-35],[-41,1,5,6,26,38,39],[-32,5,7,8,37,43],[-43,2,9,10,26,39,45],[-10,-39,-43],[-53,2,17,29,34,55],[-62,2,23,29,34,64],[-2,-23,-62],[-9,3,6,31,36,37,40],[-66,3,21,31,61],[-32,17,54,57],[-35,17,57],[-23,4,28,32,35,36,63,65],[-36,23,63,65],[-40,7,12,13,30,35,45,46],[-13,-35,-40],[-40,24,60,63,67],[-39,15,52],[-39,21,61],[-61,6,39,40],[-51,7,19,44],[-7,-19,-51],[-25,7,24,30,44,60,65],[-7,-25,-60],[-25,-44,-60],[-8,19,55,58],[-33,19,58],[-43,19,58],[-58,8,33,43,55],[-8,25,64,67],[-33,25,67],[-43,25,67],[-67,8,33,43,64],[-39,22,66],[-10,-17,-59],[-68,10,23,47,66],[-10,-23,-68],[-11,55,59],[-34,59],[-43,59],[-46,55],[-48,55,59],[-49,55],[-35,59],[-59,12,35,41,44,54,56],[-12,63,65,68],[-41,65,68],[-44,63,68],[-45,63,65],[-50,63,65],[-13,-19,-59],[-68,13,25,42,67],[-13,-25,-68],[-25,-42,-68],[-52,20,60],[-61,14,51],[-62,15,52],[-66,16,53],[-57,23],[-66,17],[-67,18,51],[-19,25,67],[-58,25],[-67,19],[-55,64],[-64,55],[-59,68],[-68,59],[-4,69],[-6,70],[-8,71],[-9,72],[-12,73],[-14,74],[-15,75],[-16,76],[-17,77],[-18,78],[-79,19],[-19,79],[-80,20],[-20,80],[-81,21],[-21,81],[-82,22],[-22,82],[-83,23],[-23,83],[-24,84],[-25,85],[-69,86],[-86,87],[-87,88],[-70,89],[-89,90],[-72,91],[-71,91],[-91,92],[-92,93],[-90,93],[-90,-92,94],[-93,95],[-94,96],[-88,95],[-88,-93,96],[-74,97],[-97,98],[-73,98],[-76,99],[-75,99],[-75,-76,100],[-78,101],[-77,101],[-77,-78,102],[-101,103],[-102,104],[-99,103],[-99,-101,104],[-100,-101,105],[-103,106],[-104,107],[-105,108],[-98,106],[-98,-103,107],[-98,-104,108],[-109,80,81],[-81,109],[-80,109],[-110,79,109],[-109,110],[-79,110],[-79,-109,111],[-112,82,83],[-83,112],[-82,-83,113],[-85,114],[-84,-85,115],[-114,116],[-115,117],[-112,116],[-112,-114,117],[-112,-115,118],[-113,117],[-113,-114,118],[-117,120],[-110,119],[-110,-116,120],[-110,-117,121],[-110,-118,122],[-111,-116,121],[-120,123],[-122,125],[-106,-119,123],[-106,-120,124],[-106,-121,125],[-107,-119,124],[-107,-120,125],[-108,-119,125],[-125,126],[-95,-124,126],[-96,-123,126],[-126],[-127,30,38,42,44,58,67],[-128,26,31,52,53],[-129,29,34,36,47,57,66],[-130,27,37,60,61],[-131,43,46,48,49],[-132,40,41,50],[-133,28,32,33],[-134,39,62],[-39,134],[-135,35,51],[-35,135],[-136,45],[-137,127],[-137,128],[-138,130],[-138,131],[-139,129],[-139,138],[-140,137,139],[-141,137],[-141,139],[-142,132],[-142,133],[-143,135,136],[-144,136],[-145,134,143],[-146,134,144],[-146,143],[-147,144],[-148,142,146],[-149,142,147],[-148,145],[-149,146],[-150,147],[-151,140,150],[-151,141,149],[-151,148],[151],[-152,55],[-55,152],[-153,59],[-59,153],[-154,64],[-64,154],[-68,155],[-54,156],[-56,156],[-63,157],[-65,157],[-158,153,154],[-154,158],[-153,158],[-153,-154,159],[-160,152,158],[-158,160],[-152,160],[-152,-158,161],[-152,-159,162],[-157,163],[-156,163],[-163,164],[-155,-163,165],[-160,-165,166],[-161,-164,166],[-162,166],[-166],[8,19,25,33,38,43,55,58,64,67],[11,34,43,46,48,49,55,59,64,68],[12,35,41,44,45,50,54,56,59,63,65,68]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"group\",\"index\":4,\"kind\":1},{\"tag\":\"group\",\"index\":7,\"kind\":1},{\"tag\":\"group\",\"index\":9,\"kind\":1},{\"tag\":\"group\",\"index\":10,\"kind\":1},{\"tag\":\"group\",\"index\":13,\"kind\":1},{\"tag\":\"group\",\"index\":15,\"kind\":1},{\"tag\":\"group\",\"index\":16,\"kind\":1},{\"tag\":\"group\",\"index\":17,\"kind\":1},{\"tag\":\"group\",\"index\":18,\"kind\":1},{\"tag\":\"group\",\"index\":19,\"kind\":1},{\"tag\":\"group\",\"index\":20,\"kind\":1},{\"tag\":\"group\",\"index\":21,\"kind\":1},{\"tag\":\"group\",\"index\":22,\"kind\":1},{\"tag\":\"group\",\"index\":23,\"kind\":1},{\"tag\":\"group\",\"index\":24,\"kind\":1},{\"tag\":\"group\",\"index\":25,\"kind\":1},{\"tag\":\"group\",\"index\":26,\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":33,\"b\":2},{\"tag\":\"incompatible\",\"a\":33,\"b\":3},{\"tag\":\"incompatible\",\"a\":34,\"b\":8},{\"tag\":\"incompatible\",\"a\":34,\"b\":30},{\"tag\":\"incompatible\",\"a\":35,\"b\":34},{\"tag\":\"incompatible\",\"a\":36,\"b\":27},{\"tag\":\"incompatible\",\"a\":36,\"b\":28},{\"tag\":\"incompatible\",\"a\":36,\"b\":29},{\"tag\":\"incompatible\",\"a\":36,\"b\":30},{\"tag\":\"incompatible\",\"a\":36,\"b\":31},{\"tag\":\"incompatible\",\"a\":36,\"b\":32},{\"tag\":\"incompatible\",\"a\":36,\"b\":33},{\"tag\":\"incompatible\",\"a\":40,\"b\":27},{\"tag\":\"incompatible\",\"a\":40,\"b\":32},{\"tag\":\"incompatible\",\"a\":41,\"b\":38},{\"tag\":\"incompatible\",\"a\":41,\"b\":40},{\"tag\":\"incompatible\",\"a\":42,\"b\":8},{\"tag\":\"incompatible\",\"a\":42,\"b\":36},{\"tag\":\"incompatible\",\"a\":43,\"b\":36},{\"tag\":\"incompatible\",\"a\":44,\"b\":30},{\"tag\":\"incompatible\",\"a\":44,\"b\":34},{\"tag\":\"incompatible\",\"a\":44,\"b\":35},{\"tag\":\"incompatible\",\"a\":45,\"b\":33},{\"tag\":\"incompatible\",\"a\":45,\"b\":34},{\"tag\":\"incompatible\",\"a\":45,\"b\":36},{\"tag\":\"incompatible\",\"a\":45,\"b\":42},{\"tag\":\"incompatible\",\"a\":48,\"b\":40},{\"tag\":\"incompatible\",\"a\":48,\"b\":44},{\"tag\":\"incompatible\",\"a\":49,\"b\":2},{\"tag\":\"incompatible\",\"a\":49,\"b\":30},{\"tag\":\"incompatible\",\"a\":49,\"b\":35},{\"tag\":\"incompatible\",\"a\":49,\"b\":40},{\"tag\":\"incompatible\",\"a\":52,\"b\":5},{\"tag\":\"incompatible\",\"a\":52,\"b\":28},{\"tag\":\"incompatible\",\"a\":52,\"b\":31},{\"tag\":\"incompatible\",\"a\":52,\"b\":36},{\"tag\":\"incompatible\",\"a\":52,\"b\":38},{\"tag\":\"incompatible\",\"a\":52,\"b\":39},{\"tag\":\"incompatible\",\"a\":53,\"b\":0},{\"tag\":\"incompatible\",\"a\":53,\"b\":27},{\"tag\":\"incompatible\",\"a\":53,\"b\":28},{\"tag\":\"incompatible\",\"a\":53,\"b\":29},{\"tag\":\"incompatible\",\"a\":53,\"b\":32},{\"tag\":\"incompatible\",\"a\":53,\"b\":38},{\"tag\":\"incompatible\",\"a\":53,\"b\":52},{\"tag\":\"incompatible\",\"a\":54,\"b\":3},{\"tag\":\"incompatible\",\"a\":54,\"b\":16},{\"tag\":\"incompatible\",\"a\":54,\"b\":53},{\"tag\":\"incompatible\",\"a\":58,\"b\":54},{\"tag\":\"incompatible\",\"a\":59,\"b\":52},{\"tag\":\"incompatible\",\"a\":60,\"b\":46},{\"tag\":\"incompatible\",\"a\":60,\"b\":51},{\"tag\":\"incompatible\",\"a\":61,\"b\":5},{\"tag\":\"incompatible\",\"a\":61,\"b\":31},{\"tag\":\"incompatible\",\"a\":61,\"b\":36},{\"tag\":\"incompatible\",\"a\":61,\"b\":39},{\"tag\":\"incompatible\",\"a\":61,\"b\":52},{\"tag\":\"incompatible\",\"a\":62,\"b\":0},{\"tag\":\"incompatible\",\"a\":62,\"b\":21},{\"tag\":\"incompatible\",\"a\":62,\"b\":22},{\"tag\":\"incompatible\",\"a\":62,\"b\":27},{\"tag\":\"incompatible\",\"a\":62,\"b\":29},{\"tag\":\"incompatible\",\"a\":62,\"b\":32},{\"tag\":\"incompatible\",\"a\":62,\"b\":53},{\"tag\":\"incompatible\",\"a\":63,\"b\":3},{\"tag\":\"incompatible\",\"a\":63,\"b\":23},{\"tag\":\"incompatible\",\"a\":63,\"b\":27},{\"tag\":\"incompatible\",\"a\":63,\"b\":32},{\"tag\":\"incompatible\",\"a\":63,\"b\":37},{\"tag\":\"incompatible\",\"a\":63,\"b\":62},{\"tag\":\"incompatible\",\"a\":67,\"b\":23},{\"tag\":\"incompatible\",\"a\":67,\"b\":24},{\"tag\":\"incompatible\",\"a\":68,\"b\":26},{\"tag\":\"incompatible\",\"a\":68,\"b\":61},{\"tag\":\"mate\",\"ridge\":7,\"a\":34,\"owners\":[0,2,3,4,28,36]},{\"tag\":\"three\",\"ridge\":7,\"vertices\":[2,34,36]},{\"tag\":\"mate\",\"ridge\":11,\"a\":42,\"owners\":[0,5,7,27,39,40]},{\"tag\":\"mate\",\"ridge\":19,\"a\":33,\"owners\":[5,8,9,38,44]},{\"tag\":\"mate\",\"ridge\":35,\"a\":44,\"owners\":[2,10,11,27,40,46]},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[11,40,44]},{\"tag\":\"mate\",\"ridge\":37,\"a\":54,\"owners\":[2,18,30,35,56]},{\"tag\":\"mate\",\"ridge\":38,\"a\":63,\"owners\":[2,24,30,35,65]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[2,24,63]},{\"tag\":\"mate\",\"ridge\":131,\"a\":10,\"owners\":[3,7,32,37,38,41]},{\"tag\":\"mate\",\"ridge\":134,\"a\":67,\"owners\":[3,22,32,62]},{\"tag\":\"mate\",\"ridge\":261,\"a\":33,\"owners\":[18,55,58]},{\"tag\":\"mate\",\"ridge\":261,\"a\":36,\"owners\":[18,58]},{\"tag\":\"mate\",\"ridge\":262,\"a\":24,\"owners\":[4,29,33,36,37,64,66]},{\"tag\":\"mate\",\"ridge\":262,\"a\":37,\"owners\":[24,64,66]},{\"tag\":\"mate\",\"ridge\":67,\"a\":41,\"owners\":[8,13,14,31,36,46,47]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[14,36,41]},{\"tag\":\"mate\",\"ridge\":74,\"a\":41,\"owners\":[25,61,64,68]},{\"tag\":\"mate\",\"ridge\":137,\"a\":40,\"owners\":[16,53]},{\"tag\":\"mate\",\"ridge\":138,\"a\":40,\"owners\":[22,62]},{\"tag\":\"mate\",\"ridge\":138,\"a\":62,\"owners\":[7,40,41]},{\"tag\":\"mate\",\"ridge\":81,\"a\":52,\"owners\":[8,20,45]},{\"tag\":\"three\",\"ridge\":81,\"vertices\":[8,20,52]},{\"tag\":\"mate\",\"ridge\":82,\"a\":26,\"owners\":[8,25,31,45,61,66]},{\"tag\":\"three\",\"ridge\":82,\"vertices\":[8,26,61]},{\"tag\":\"three\",\"ridge\":82,\"vertices\":[26,45,61]},{\"tag\":\"mate\",\"ridge\":529,\"a\":9,\"owners\":[20,56,59]},{\"tag\":\"mate\",\"ridge\":529,\"a\":34,\"owners\":[20,59]},{\"tag\":\"mate\",\"ridge\":529,\"a\":44,\"owners\":[20,59]},{\"tag\":\"mate\",\"ridge\":529,\"a\":59,\"owners\":[9,34,44,56]},{\"tag\":\"mate\",\"ridge\":530,\"a\":9,\"owners\":[26,65,68]},{\"tag\":\"mate\",\"ridge\":530,\"a\":34,\"owners\":[26,68]},{\"tag\":\"mate\",\"ridge\":530,\"a\":44,\"owners\":[26,68]},{\"tag\":\"mate\",\"ridge\":530,\"a\":68,\"owners\":[9,34,44,65]},{\"tag\":\"mate\",\"ridge\":162,\"a\":40,\"owners\":[23,67]},{\"tag\":\"three\",\"ridge\":289,\"vertices\":[11,18,60]},{\"tag\":\"mate\",\"ridge\":290,\"a\":69,\"owners\":[11,24,48,67]},{\"tag\":\"three\",\"ridge\":290,\"vertices\":[11,24,69]},{\"tag\":\"mate\",\"ridge\":545,\"a\":12,\"owners\":[56,60]},{\"tag\":\"mate\",\"ridge\":545,\"a\":35,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":545,\"a\":44,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":545,\"a\":47,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":545,\"a\":49,\"owners\":[56,60]},{\"tag\":\"mate\",\"ridge\":545,\"a\":50,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":321,\"a\":36,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":321,\"a\":60,\"owners\":[13,36,42,45,55,57]},{\"tag\":\"mate\",\"ridge\":322,\"a\":13,\"owners\":[64,66,69]},{\"tag\":\"mate\",\"ridge\":322,\"a\":42,\"owners\":[66,69]},{\"tag\":\"mate\",\"ridge\":322,\"a\":45,\"owners\":[64,69]},{\"tag\":\"mate\",\"ridge\":322,\"a\":46,\"owners\":[64,66]},{\"tag\":\"mate\",\"ridge\":322,\"a\":51,\"owners\":[64,66]},{\"tag\":\"three\",\"ridge\":577,\"vertices\":[14,20,60]},{\"tag\":\"mate\",\"ridge\":578,\"a\":69,\"owners\":[14,26,43,68]},{\"tag\":\"three\",\"ridge\":578,\"vertices\":[14,26,69]},{\"tag\":\"three\",\"ridge\":578,\"vertices\":[26,43,69]},{\"tag\":\"mate\",\"ridge\":28,\"a\":53,\"owners\":[21,61]},{\"tag\":\"mate\",\"ridge\":28,\"a\":62,\"owners\":[15,52]},{\"tag\":\"mate\",\"ridge\":140,\"a\":63,\"owners\":[16,53]},{\"tag\":\"mate\",\"ridge\":164,\"a\":67,\"owners\":[17,54]},{\"tag\":\"mate\",\"ridge\":292,\"a\":58,\"owners\":[24]},{\"tag\":\"mate\",\"ridge\":292,\"a\":67,\"owners\":[18]},{\"tag\":\"mate\",\"ridge\":88,\"a\":68,\"owners\":[19,52]},{\"tag\":\"mate\",\"ridge\":592,\"a\":20,\"owners\":[26,68]},{\"tag\":\"mate\",\"ridge\":592,\"a\":59,\"owners\":[26]},{\"tag\":\"mate\",\"ridge\":592,\"a\":68,\"owners\":[20]},{\"tag\":\"mate\",\"ridge\":564,\"a\":56,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":564,\"a\":65,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":864,\"a\":60,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":864,\"a\":69,\"owners\":[60]},{\"tag\":\"group_take\",\"kind\":1,\"index\":4,\"member\":4,\"full_literals\":[-4,69]},{\"tag\":\"group_take\",\"kind\":1,\"index\":7,\"member\":7,\"full_literals\":[-6,70]},{\"tag\":\"group_take\",\"kind\":1,\"index\":9,\"member\":9,\"full_literals\":[-8,71]},{\"tag\":\"group_take\",\"kind\":1,\"index\":10,\"member\":10,\"full_literals\":[-9,72]},{\"tag\":\"group_take\",\"kind\":1,\"index\":13,\"member\":13,\"full_literals\":[-12,73]},{\"tag\":\"group_take\",\"kind\":1,\"index\":15,\"member\":15,\"full_literals\":[-14,74]},{\"tag\":\"group_take\",\"kind\":1,\"index\":16,\"member\":16,\"full_literals\":[-15,75]},{\"tag\":\"group_take\",\"kind\":1,\"index\":17,\"member\":17,\"full_literals\":[-16,76]},{\"tag\":\"group_take\",\"kind\":1,\"index\":18,\"member\":18,\"full_literals\":[-17,77]},{\"tag\":\"group_take\",\"kind\":1,\"index\":19,\"member\":19,\"full_literals\":[-18,78]},{\"tag\":\"group_or\",\"kind\":1,\"index\":20,\"members\":[20],\"full_literals\":[-79,19]},{\"tag\":\"group_take\",\"kind\":1,\"index\":20,\"member\":20,\"full_literals\":[-19,79]},{\"tag\":\"group_or\",\"kind\":1,\"index\":21,\"members\":[21],\"full_literals\":[-80,20]},{\"tag\":\"group_take\",\"kind\":1,\"index\":21,\"member\":21,\"full_literals\":[-20,80]},{\"tag\":\"group_or\",\"kind\":1,\"index\":22,\"members\":[22],\"full_literals\":[-81,21]},{\"tag\":\"group_take\",\"kind\":1,\"index\":22,\"member\":22,\"full_literals\":[-21,81]},{\"tag\":\"group_or\",\"kind\":1,\"index\":23,\"members\":[23],\"full_literals\":[-82,22]},{\"tag\":\"group_take\",\"kind\":1,\"index\":23,\"member\":23,\"full_literals\":[-22,82]},{\"tag\":\"group_or\",\"kind\":1,\"index\":24,\"members\":[24],\"full_literals\":[-83,23]},{\"tag\":\"group_take\",\"kind\":1,\"index\":24,\"member\":24,\"full_literals\":[-23,83]},{\"tag\":\"group_take\",\"kind\":1,\"index\":25,\"member\":25,\"full_literals\":[-24,84]},{\"tag\":\"group_take\",\"kind\":1,\"index\":26,\"member\":26,\"full_literals\":[-25,85]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped1_0006\",\"right_name\":\"grouped1_0008\",\"joined_name\":\"grouped1_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-69,false,86],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped1_0004\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0005\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-86,87],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0005\",\"joined_name\":\"grouped1_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-87,88],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0014\",\"joined_name\":\"grouped1_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-70,false,89],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped1_0009\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-89,90],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-72,91],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-71,false,91],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[9,10],\"right\":[11,12],\"left_name\":\"grouped1_0016\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-91,false,92],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11,12],\"left_name\":\"grouped1_0010\",\"right_name\":\"grouped1_0017\",\"joined_name\":\"grouped1_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-92,93],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11,12],\"left_name\":\"grouped1_0010\",\"right_name\":\"grouped1_0017\",\"joined_name\":\"grouped1_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-90,false,93],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11,12],\"left_name\":\"grouped1_0010\",\"right_name\":\"grouped1_0017\",\"joined_name\":\"grouped1_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-90,-92,94],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11,12],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0011\",\"joined_name\":\"grouped1_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-93,95],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11,12],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0011\",\"joined_name\":\"grouped1_0002\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-94,96],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11,12],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0011\",\"joined_name\":\"grouped1_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-88,false,95],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11,12],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0011\",\"joined_name\":\"grouped1_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-88,-93,96],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14],\"right\":[15],\"left_name\":\"grouped1_0024\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0025\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-74,97],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13],\"right\":[14,15],\"left_name\":\"grouped1_0020\",\"right_name\":\"grouped1_0025\",\"joined_name\":\"grouped1_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-97,98],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13],\"right\":[14,15],\"left_name\":\"grouped1_0020\",\"right_name\":\"grouped1_0025\",\"joined_name\":\"grouped1_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-73,false,98],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16],\"right\":[17],\"left_name\":\"grouped1_0027\",\"right_name\":\"grouped1_0030\",\"joined_name\":\"grouped1_0028\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-76,99],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16],\"right\":[17],\"left_name\":\"grouped1_0027\",\"right_name\":\"grouped1_0030\",\"joined_name\":\"grouped1_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-75,false,99],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16],\"right\":[17],\"left_name\":\"grouped1_0027\",\"right_name\":\"grouped1_0030\",\"joined_name\":\"grouped1_0028\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-75,-76,100],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[18],\"right\":[19],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0033\",\"joined_name\":\"grouped1_0032\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-78,101],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[18],\"right\":[19],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0033\",\"joined_name\":\"grouped1_0032\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-77,false,101],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[18],\"right\":[19],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0033\",\"joined_name\":\"grouped1_0032\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-77,-78,102],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17],\"right\":[18,19],\"left_name\":\"grouped1_0028\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0029\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-101,103],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17],\"right\":[18,19],\"left_name\":\"grouped1_0028\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0029\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-102,104],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17],\"right\":[18,19],\"left_name\":\"grouped1_0028\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0029\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-99,false,103],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17],\"right\":[18,19],\"left_name\":\"grouped1_0028\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0029\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-99,-101,104],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17],\"right\":[18,19],\"left_name\":\"grouped1_0028\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0029\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-100,-101,105],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13,14,15],\"right\":[16,17,18,19],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-103,106],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13,14,15],\"right\":[16,17,18,19],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0022\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-104,107],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13,14,15],\"right\":[16,17,18,19],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0022\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-105,108],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13,14,15],\"right\":[16,17,18,19],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-98,false,106],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13,14,15],\"right\":[16,17,18,19],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-98,-103,107],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13,14,15],\"right\":[16,17,18,19],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0022\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-98,-104,108],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[21],\"right\":[22],\"left_name\":\"grouped1_0037\",\"right_name\":\"grouped1_0039\",\"joined_name\":\"grouped1_0038\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-109,80,81],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[21],\"right\":[22],\"left_name\":\"grouped1_0037\",\"right_name\":\"grouped1_0039\",\"joined_name\":\"grouped1_0038\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-81,109],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[21],\"right\":[22],\"left_name\":\"grouped1_0037\",\"right_name\":\"grouped1_0039\",\"joined_name\":\"grouped1_0038\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-80,false,109],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20],\"right\":[21,22],\"left_name\":\"grouped1_0034\",\"right_name\":\"grouped1_0038\",\"joined_name\":\"grouped1_0035\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-110,79,109],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20],\"right\":[21,22],\"left_name\":\"grouped1_0034\",\"right_name\":\"grouped1_0038\",\"joined_name\":\"grouped1_0035\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-109,110],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20],\"right\":[21,22],\"left_name\":\"grouped1_0034\",\"right_name\":\"grouped1_0038\",\"joined_name\":\"grouped1_0035\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-79,false,110],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20],\"right\":[21,22],\"left_name\":\"grouped1_0034\",\"right_name\":\"grouped1_0038\",\"joined_name\":\"grouped1_0035\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-79,-109,111],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[23],\"right\":[24],\"left_name\":\"grouped1_0040\",\"right_name\":\"grouped1_0043\",\"joined_name\":\"grouped1_0041\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-112,82,83],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[23],\"right\":[24],\"left_name\":\"grouped1_0040\",\"right_name\":\"grouped1_0043\",\"joined_name\":\"grouped1_0041\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-83,112],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[23],\"right\":[24],\"left_name\":\"grouped1_0040\",\"right_name\":\"grouped1_0043\",\"joined_name\":\"grouped1_0041\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-82,-83,113],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[25],\"right\":[26],\"left_name\":\"grouped1_0044\",\"right_name\":\"grouped1_0046\",\"joined_name\":\"grouped1_0045\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-85,114],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[25],\"right\":[26],\"left_name\":\"grouped1_0044\",\"right_name\":\"grouped1_0046\",\"joined_name\":\"grouped1_0045\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-84,-85,115],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[23,24],\"right\":[25,26],\"left_name\":\"grouped1_0041\",\"right_name\":\"grouped1_0045\",\"joined_name\":\"grouped1_0042\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-114,116],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[23,24],\"right\":[25,26],\"left_name\":\"grouped1_0041\",\"right_name\":\"grouped1_0045\",\"joined_name\":\"grouped1_0042\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-115,117],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[23,24],\"right\":[25,26],\"left_name\":\"grouped1_0041\",\"right_name\":\"grouped1_0045\",\"joined_name\":\"grouped1_0042\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-112,false,116],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[23,24],\"right\":[25,26],\"left_name\":\"grouped1_0041\",\"right_name\":\"grouped1_0045\",\"joined_name\":\"grouped1_0042\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-112,-114,117],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[23,24],\"right\":[25,26],\"left_name\":\"grouped1_0041\",\"right_name\":\"grouped1_0045\",\"joined_name\":\"grouped1_0042\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-112,-115,118],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[23,24],\"right\":[25,26],\"left_name\":\"grouped1_0041\",\"right_name\":\"grouped1_0045\",\"joined_name\":\"grouped1_0042\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-113,false,117],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[23,24],\"right\":[25,26],\"left_name\":\"grouped1_0041\",\"right_name\":\"grouped1_0045\",\"joined_name\":\"grouped1_0042\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-113,-114,118],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20,21,22],\"right\":[23,24,25,26],\"left_name\":\"grouped1_0035\",\"right_name\":\"grouped1_0042\",\"joined_name\":\"grouped1_0036\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-117,120],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20,21,22],\"right\":[23,24,25,26],\"left_name\":\"grouped1_0035\",\"right_name\":\"grouped1_0042\",\"joined_name\":\"grouped1_0036\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-110,false,119],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20,21,22],\"right\":[23,24,25,26],\"left_name\":\"grouped1_0035\",\"right_name\":\"grouped1_0042\",\"joined_name\":\"grouped1_0036\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-110,-116,120],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20,21,22],\"right\":[23,24,25,26],\"left_name\":\"grouped1_0035\",\"right_name\":\"grouped1_0042\",\"joined_name\":\"grouped1_0036\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-110,-117,121],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20,21,22],\"right\":[23,24,25,26],\"left_name\":\"grouped1_0035\",\"right_name\":\"grouped1_0042\",\"joined_name\":\"grouped1_0036\",\"a\":1,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-110,-118,122],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20,21,22],\"right\":[23,24,25,26],\"left_name\":\"grouped1_0035\",\"right_name\":\"grouped1_0042\",\"joined_name\":\"grouped1_0036\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-111,-116,121],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13,14,15,16,17,18,19],\"right\":[20,21,22,23,24,25,26],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0036\",\"joined_name\":\"grouped1_0023\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-120,123],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13,14,15,16,17,18,19],\"right\":[20,21,22,23,24,25,26],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0036\",\"joined_name\":\"grouped1_0023\",\"a\":0,\"b\":4,\"direction\":\"forward\",\"full_literals\":[false,-122,125],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13,14,15,16,17,18,19],\"right\":[20,21,22,23,24,25,26],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0036\",\"joined_name\":\"grouped1_0023\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-106,-119,123],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13,14,15,16,17,18,19],\"right\":[20,21,22,23,24,25,26],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0036\",\"joined_name\":\"grouped1_0023\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-106,-120,124],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13,14,15,16,17,18,19],\"right\":[20,21,22,23,24,25,26],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0036\",\"joined_name\":\"grouped1_0023\",\"a\":1,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-106,-121,125],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13,14,15,16,17,18,19],\"right\":[20,21,22,23,24,25,26],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0036\",\"joined_name\":\"grouped1_0023\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-107,-119,124],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13,14,15,16,17,18,19],\"right\":[20,21,22,23,24,25,26],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0036\",\"joined_name\":\"grouped1_0023\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-107,-120,125],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13,14,15,16,17,18,19],\"right\":[20,21,22,23,24,25,26],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0036\",\"joined_name\":\"grouped1_0023\",\"a\":3,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-108,-119,125],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10,11,12],\"right\":[13,14,15,16,17,18,19,20,21,22,23,24,25,26],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"groupKind1\",\"a\":0,\"b\":4,\"direction\":\"forward\",\"full_literals\":[false,-125,126],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10,11,12],\"right\":[13,14,15,16,17,18,19,20,21,22,23,24,25,26],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"groupKind1\",\"a\":1,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-95,-124,126],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10,11,12],\"right\":[13,14,15,16,17,18,19,20,21,22,23,24,25,26],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"groupKind1\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-96,-123,126],\"grouped\":true,\"kind\":1},{\"tag\":\"quota_upper\",\"kind\":1,\"quota\":3,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[31,39,43,45,59,68],\"full_literals\":[-127,30,38,42,44,58,67]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[27,32,53,54],\"full_literals\":[-128,26,31,52,53]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[30,35,37,48,58,67],\"full_literals\":[-129,29,34,36,47,57,66]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[28,38,61,62],\"full_literals\":[-130,27,37,60,61]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[44,47,49,50],\"full_literals\":[-131,43,46,48,49]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[41,42,51],\"full_literals\":[-132,40,41,50]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[29,33,34],\"full_literals\":[-133,28,32,33]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[40,63],\"full_literals\":[-134,39,62]},{\"tag\":\"group_take\",\"kind\":2,\"index\":7,\"member\":40,\"full_literals\":[-39,134]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[36,52],\"full_literals\":[-135,35,51]},{\"tag\":\"group_take\",\"kind\":2,\"index\":8,\"member\":36,\"full_literals\":[-35,135]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[46],\"full_literals\":[-136,45]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0047\",\"right_name\":\"grouped2_0051\",\"joined_name\":\"grouped2_0048\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-137,127,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0047\",\"right_name\":\"grouped2_0051\",\"joined_name\":\"grouped2_0048\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-137,false,128],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0054\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0055\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-138,130,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0054\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0055\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-138,false,131],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0055\",\"joined_name\":\"grouped2_0053\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-139,129,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0055\",\"joined_name\":\"grouped2_0053\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-139,false,138],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0048\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"grouped2_0049\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-140,137,139],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0048\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"grouped2_0049\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-141,137,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0048\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"grouped2_0049\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-141,false,139],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0060\",\"joined_name\":\"grouped2_0058\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-142,132,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0060\",\"joined_name\":\"grouped2_0058\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-142,false,133],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0063\",\"right_name\":\"grouped2_0065\",\"joined_name\":\"grouped2_0064\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-143,135,136],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0063\",\"right_name\":\"grouped2_0065\",\"joined_name\":\"grouped2_0064\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-144,false,136],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0061\",\"right_name\":\"grouped2_0064\",\"joined_name\":\"grouped2_0062\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-145,134,143],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0061\",\"right_name\":\"grouped2_0064\",\"joined_name\":\"grouped2_0062\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-146,134,144],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0061\",\"right_name\":\"grouped2_0064\",\"joined_name\":\"grouped2_0062\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-146,false,143],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0061\",\"right_name\":\"grouped2_0064\",\"joined_name\":\"grouped2_0062\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-147,false,144],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0058\",\"right_name\":\"grouped2_0062\",\"joined_name\":\"grouped2_0059\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-148,142,146],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0058\",\"right_name\":\"grouped2_0062\",\"joined_name\":\"grouped2_0059\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-149,142,147],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0058\",\"right_name\":\"grouped2_0062\",\"joined_name\":\"grouped2_0059\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-148,false,145],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0058\",\"right_name\":\"grouped2_0062\",\"joined_name\":\"grouped2_0059\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-149,false,146],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0058\",\"right_name\":\"grouped2_0062\",\"joined_name\":\"grouped2_0059\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-150,false,147],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0049\",\"right_name\":\"grouped2_0059\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-151,140,150],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0049\",\"right_name\":\"grouped2_0059\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-151,141,149],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0049\",\"right_name\":\"grouped2_0059\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-151,false,148],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[56],\"full_literals\":[-152,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":56,\"full_literals\":[-55,152]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[60],\"full_literals\":[-153,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":60,\"full_literals\":[-59,153]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[65],\"full_literals\":[-154,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":65,\"full_literals\":[-64,154]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":69,\"full_literals\":[-68,155]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":55,\"full_literals\":[-54,156]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":57,\"full_literals\":[-56,156]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":64,\"full_literals\":[-63,157]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":66,\"full_literals\":[-65,157]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0069\",\"right_name\":\"grouped3_0071\",\"joined_name\":\"grouped3_0070\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-158,153,154],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0069\",\"right_name\":\"grouped3_0071\",\"joined_name\":\"grouped3_0070\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-154,158],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0069\",\"right_name\":\"grouped3_0071\",\"joined_name\":\"grouped3_0070\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-153,false,158],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0069\",\"right_name\":\"grouped3_0071\",\"joined_name\":\"grouped3_0070\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-153,-154,159],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0066\",\"right_name\":\"grouped3_0070\",\"joined_name\":\"grouped3_0067\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-160,152,158],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0066\",\"right_name\":\"grouped3_0070\",\"joined_name\":\"grouped3_0067\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-158,160],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0066\",\"right_name\":\"grouped3_0070\",\"joined_name\":\"grouped3_0067\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-152,false,160],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0066\",\"right_name\":\"grouped3_0070\",\"joined_name\":\"grouped3_0067\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-152,-158,161],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0066\",\"right_name\":\"grouped3_0070\",\"joined_name\":\"grouped3_0067\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-152,-159,162],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0074\",\"right_name\":\"grouped3_0076\",\"joined_name\":\"grouped3_0075\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-157,163],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0074\",\"right_name\":\"grouped3_0076\",\"joined_name\":\"grouped3_0075\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-156,false,163],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0072\",\"right_name\":\"grouped3_0075\",\"joined_name\":\"grouped3_0073\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-163,164],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0072\",\"right_name\":\"grouped3_0075\",\"joined_name\":\"grouped3_0073\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-155,-163,165],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0067\",\"right_name\":\"grouped3_0073\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-160,-165,166],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0067\",\"right_name\":\"grouped3_0073\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-161,-164,166],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0067\",\"right_name\":\"grouped3_0073\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-162,false,166],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":34,\"owners\":[9,20,26,34,39,44,56,59,65,68]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[12,35,44,47,49,50,56,60,65,69]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[13,36,42,45,46,51,55,57,60,64,66,69]}]}"
  "307 -125 0 237 234 0\n308 -122 0 307 227 0\n309 148 0 275 274 0\n310 145 0 309 269 0\n311 -162 0 303 302 0\n312 160 0 292 293 288 289 277 281 279 113 116 118 114 115 143 117 305 0\n313 -165 0 312 303 300 0\n314 158 0 312 288 291 281 276 140 0\n315 15 52 -134 0 93 132 245 0\n316 -39 53 52 -128 0 13 14 239 0\n317 52 -128 -134 0 315 47 316 245 67 68 239 0\n318 -52 -130 -135 0 41 44 45 64 247 241 55 0\n319 -60 -135 0 55 57 247 0\n320 -35 61 -130 60 -132 50 0 7 18 241 243 15 0\n321 61 -130 -135 -132 50 0 319 320 247 34 37 241 0\n322 66 113 10 -39 -68 0 27 111 109 163 161 210 0\n323 -138 -149 55 0 314 307 141 280 287 278 51 249 270 265 261 262 264 266 268 259 142 52 118 116 252 253 318 315 47 150 185 192 195 230 321 70 245 16 32 243 242 17 18 26 80 247 96 155 206 221 223 233 218 197 322 133 135 151 152 186 188 194 0\n324 -67 -116 -109 51 0 307 136 139 153 155 187 207 190 225 195 230 0\n325 -149 55 0 313 314 275 308 141 280 287 278 51 249 262 266 271 272 142 282 299 296 285 52 268 270 259 260 265 264 261 319 323 255 256 251 317 42 45 130 247 157 9 12 18 19 203 244 243 205 5 76 16 91 224 245 82 163 209 215 217 324 127 92 165 164 212 0\n326 -66 -112 0 71 72 160 162 208 0\n327 -39 66 -52 55 0 314 275 308 41 325 273 258 255 252 64 44 241 74 253 141 280 287 278 142 118 116 32 94 242 159 80 107 202 322 165 205 211 224 219 0\n328 -9 -120 13 7 -62 -52 55 0 314 275 237 226 236 178 69 65 41 325 273 258 255 252 64 44 241 54 318 248 43 141 280 287 278 51 116 147 171 173 174 176 177 170 235 169 229 145 198 84 183 90 148 0\n329 95 43 7 -23 36 5 35 37 28 157 0 286 285 177 179 174 168 173 167 172 166 146 144 78 88 0\n330 -25 -112 -52 55 0 313 275 310 314 237 141 280 287 278 142 51 249 325 273 258 255 252 318 261 263 326 327 245 66 160 208 162 112 83 69 65 41 64 44 241 74 56 54 53 248 42 40 39 257 250 282 299 297 284 283 296 99 100 128 129 165 238 211 216 220 226 236 178 328 79 329 235 229 198 183 148 120 77 145 169 170 175 176 180 173 168 172 167 146 166 104 144 75 0\n331 25 -60 55 0 74 56 141 105 106 107 137 138 304 0\n332 -48 23 -134 64 0 29 30 31 32 82 245 0\n333 -52 55 0 314 313 275 310 309 307 325 273 258 255 253 252 254 141 280 287 278 142 282 299 297 283 296 286 285 51 249 118 116 41 42 43 44 48 64 318 241 261 265 263 267 260 331 165 330 211 209 163 89 134 332 242 20 21 22 28 244 240 2 86 85 133 152 159 151 188 202 184 205 193 196 232 213 222 0\n334 -25 51 55 0 313 310 275 309 314 307 141 280 287 278 52 51 249 262 325 273 257 251 333 317 264 267 259 263 261 319 258 255 252 247 320 131 149 181 182 6 11 239 49 87 152 188 190 199 232 220 214 260 8 12 244 3 25 10 142 282 299 296 286 98 165 164 212 0\n335 51 55 0 310 275 314 309 307 141 280 287 278 51 249 262 325 273 257 251 333 317 264 267 260 259 263 261 319 258 255 252 52 247 6 8 11 12 320 239 244 131 49 149 87 181 152 182 334 106 136 139 153 155 189 206 191 221 200 233 0\n336 -33 55 0 313 309 310 314 275 237 333 325 273 257 251 141 280 287 278 52 51 249 317 263 261 258 255 252 262 264 267 259 321 61 63 239 46 58 335 50 38 36 34 33 246 253 142 282 299 297 284 283 118 116 4 5 21 24 102 242 155 29 206 75 81 221 144 152 166 188 167 190 168 195 179 228 235 236 231 180 199 175 183 170 148 169 120 145 77 0\n337 91 -67 55 0 313 309 310 275 314 141 280 287 278 333 325 273 257 251 52 51 249 317 263 261 258 255 252 262 264 267 259 321 61 63 239 49 142 282 299 297 283 260 62 336 244 86 110 1 246 171 172 147 146 79 108 0\n338 -110 25 55 0 313 309 310 314 275 237 333 325 273 257 251 141 280 287 278 52 51 249 317 263 261 258 255 252 262 264 267 259 321 61 63 239 49 142 282 299 297 283 260 62 336 244 86 152 188 190 195 59 156 60 158 201 335 36 35 246 116 204 221 154 228 97 126 137 236 178 337 173 174 176 177 170 235 169 231 145 199 95 183 90 148 0\n339 19 67 8 25 38 33 55 58 64 0 304 103 0\n340 25 55 0 336 335 50 38 141 338 206 155 101 139 339 0\n341 55 0 314 275 310 309 141 280 287 278 51 52 142 249 262 325 273 257 258 250 251 255 252 333 317 263 264 261 267 259 260 335 321 35 38 50 62 336 244 23 340 73 129 238 0\n342 64 0 341 140 0\n343 152 0 341 277 0\n344 154 0 342 281 0\n345 161 0 343 314 294 0\n346 -159 0 343 311 295 0\n347 -153 0 344 346 290 0\n348 -164 0 345 303 301 0\n349 -59 0 347 279 0\n350 -163 0 348 298 0\n351 -35 0 349 119 0\n352 -68 0 349 143 0\n353 -157 0 350 296 0\n354 -156 0 350 297 0\n355 -63 0 353 285 0\n356 -65 0 353 286 0\n357 -54 0 354 283 0\n358 -56 0 354 284 0\n359 -44 0 355 352 123 0\n360 -45 0 355 356 124 0\n361 -50 0 355 356 125 0\n362 -12 0 355 356 352 121 0\n363 -41 0 356 352 122 0\n364 0 362 357 351 363 359 360 361 358 349 355 356 352 306 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record045.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record045.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record045.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record045.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record045 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record045.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record045.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record045.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record045.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record045 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record045_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record045_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record045_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record045_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record045_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record045_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record045_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record045 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record045_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record045_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record045_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00032.record045
