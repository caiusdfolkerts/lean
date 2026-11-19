module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow26Part00063Data
public import GraphInputsRow26Part00063Frames
public import GraphInputsRow26Part00063Leaves
public import GraphInputsRow26Part00063Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00063.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record003
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨31, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨54, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [635990638592, (certNat% 2), (certNat% 3), 2324490726420774912, (certNat% 4)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [569418645504, (certNat% 2), (certNat% 5), 2324490726420774912, (certNat% 4)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2324490726423003136, 22347776, (certNat% 6), 100663296, (certNat% 7), 2837094334464]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨17, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨21, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record003_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00063.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00063.record017
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record017
def vertexColumn : Fields := ⟨10, (certNat% 8)⟩
def kindColumn : Fields := ⟨3, (certNat% 9)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨61, by decide⟩, ⟨64, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), 3321888768, (certNat% 11), (certNat% 12)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 14), 34360262656, 1085276160, 621019136, 2449473536]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨17, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record017_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record017_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record017_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record017_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record017_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record017_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record017_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record017_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record017_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00063.record017

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00063.record022
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record022
def vertexColumn : Fields := ⟨10, (certNat% 15)⟩
def kindColumn : Fields := ⟨3, (certNat% 16)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨18, by decide⟩, ⟨19, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨25, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨39, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨60, by decide⟩, ⟨69, by decide⟩, ⟨73, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨84, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), (certNat% 18), (certNat% 19), 9663938560, (certNat% 20)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), (certNat% 22), 805830656, 1155173854176346112, 6192449491828736]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), 1155173304957403136, (certNat% 24), (certNat% 19), 8589934592]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), 1155173854176346112, (certNat% 26), 5981343255101440, (certNat% 27)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1155173864389476352, (certNat% 19), (certNat% 28), 269221888, 6473924464345088, (certNat% 20)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record022_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record022_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record022_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record022_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record022_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record022_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record022_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record022_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record022_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00063.record022

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00063.record000
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1e8ce334cb26c5b31c8f13c789b23c9ca6a96a3a93a719963594e8791eac5b13c5a99a4e98e53999595356354d4759362d4b46d8751d0f5a338d9334d332cc7362ccb4acab1ae1b46c3b61cc785d1725c5783d0f07db0649164384e386312c6291a6158344d30c9312c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db6da6db6da69a4934936da6d26936d24d369b4db692492449249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record000 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record000 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record000.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record000.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record000.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 19), (facetIndex 20), (facetIndex 64), (facetIndex 66)]))
 (.leaf ([(facetIndex 37), (facetIndex 61), (facetIndex 62), (facetIndex 63)])))
 (.branch 3
 (.leaf ([(facetIndex 31), (facetIndex 46), (facetIndex 58), (facetIndex 59)]))
 (.leaf ([(facetIndex 40), (facetIndex 68), (facetIndex 76)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 22), (facetIndex 23), (facetIndex 24), (facetIndex 25)]))
 (.leaf ([(facetIndex 45), (facetIndex 48), (facetIndex 52), (facetIndex 57)])))
 (.branch 7
 (.leaf ([(facetIndex 26), (facetIndex 34), (facetIndex 39), (facetIndex 41)]))
 (.leaf ([(facetIndex 21), (facetIndex 49)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "30000030002484a800503d0a8033c081804001a4938000000000000000"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

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

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record000 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record000_matrix_checked

def leafCount : Nat := 4
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaf0000 : List (Fin data.count) := [(facetIndex 2), (facetIndex 14), (facetIndex 15), (facetIndex 25), (facetIndex 39), (facetIndex 49), (facetIndex 57), (facetIndex 58), (facetIndex 62), (facetIndex 68), (facetIndex 72), (facetIndex 77), (facetIndex 83), (facetIndex 84)]
theorem leaf0000_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0000 = true := by
  decide +kernel
theorem leaf0000_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0000 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0000_counts_checked
def leaf0001 : List (Fin data.count) := [(facetIndex 2), (facetIndex 9), (facetIndex 13), (facetIndex 25), (facetIndex 39), (facetIndex 49), (facetIndex 57), (facetIndex 62), (facetIndex 66), (facetIndex 68), (facetIndex 71), (facetIndex 73), (facetIndex 83), (facetIndex 84)]
theorem leaf0001_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0001 = true := by
  decide +kernel
theorem leaf0001_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0001 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0001_counts_checked
def leaf0002 : List (Fin data.count) := [(facetIndex 10), (facetIndex 14), (facetIndex 18), (facetIndex 25), (facetIndex 26), (facetIndex 40), (facetIndex 49), (facetIndex 58), (facetIndex 63), (facetIndex 64), (facetIndex 72), (facetIndex 77), (facetIndex 83), (facetIndex 84)]
theorem leaf0002_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0002 = true := by
  decide +kernel
theorem leaf0002_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0002 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0002_counts_checked
def leaf0003 : List (Fin data.count) := [(facetIndex 9), (facetIndex 16), (facetIndex 18), (facetIndex 25), (facetIndex 26), (facetIndex 40), (facetIndex 49), (facetIndex 57), (facetIndex 61), (facetIndex 66), (facetIndex 71), (facetIndex 73), (facetIndex 83), (facetIndex 84)]
theorem leaf0003_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0003 = true := by
  decide +kernel
theorem leaf0003_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0003 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0003_counts_checked
def leavesTable : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf (leaf0000))
 (.leaf (leaf0001)))
 (.branch 3
 (.leaf (leaf0002))
 (.leaf (leaf0003))))
def leaves (j : Fin leafCount) : List (Fin data.count) := leavesTable.get j.val

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00063.record000" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00063.record000" 89

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00063.record000" "{\"ridges\":[[2,7],[3,73],[6,13],[6,73],[7,13],[13,97],[14,14],[14,70],[15,14],[20,7],[20,13],[21,7],[21,14],[23,7],[24,7],[24,262],[25,7],[26,7],[26,70],[29,11],[31,104],[34,73],[34,74],[39,193],[39,194],[40,274],[40,386],[40,400],[41,224],[45,524],[48,13],[48,524],[49,69],[49,73],[49,76],[49,521],[49,524],[50,116],[52,532],[53,212],[55,69],[55,612],[57,521],[57,552],[57,560],[58,73],[58,104],[58,224],[59,73],[64,14],[66,74],[66,76],[67,212],[69,452],[71,170],[72,266],[75,114],[76,386],[76,416],[81,356],[82,76],[82,612],[83,804]],\"owners\":[[23,7,[0,2,20,21],[1,24,25,26,27]],[24,7,[0,2,21,26],[1,20,23,25,27]],[29,11,[0,3,21,31,32,34],[19,20,28,30,33,35]],[49,69,[2,22,26,50,53],[6,46,55]],[55,69,[2,6,22,26,53],[46,49,50]],[14,70,[2,22,26,67,69],[66]],[26,70,[14,66],[2,22,67,69]],[49,73,[3,9,34,58],[6,59]],[34,74,[14,66,72],[3,31,71,74]],[66,74,[3,31,34,71],[14,72,74]],[39,193,[13,58],[5,26,34,53,61]],[39,194,[69,71,74,77],[5,26,34,41,67,75]],[49,76,[14,66,81],[6,46,82]],[66,76,[6,46,49,82],[14,81]],[82,76,[6,14,66],[46,49,81]],[49,521,[10,30,57],[7,21,45,59]],[57,521,[7,21,49],[10,30,45,59]],[45,524,[82,83],[7,21,48,49,65,79,80]],[48,524,[65,80],[7,21,45,49,79,82,83]],[49,524,[65,79,80,83],[7,21,45,48,82]],[52,532,[65,80],[8,25,45,79,84]],[13,97,[9,31,36,46,50,55,59],[41,61]],[31,104,[81,82,86],[9,46,58,59,71,72]],[58,104,[72,81,82],[9,31,46,59,71,86]],[57,552,[82,83],[10,48,59,79,85]],[57,560,[84],[12,52,63,79,85]],[41,224,[86],[13,58,61,71,75,77]],[58,224,[75,77],[13,41,61,71,86]],[24,262,[15,66,69],[16,20,27,68]],[72,266,[15,20,29,35,64],[33,66,70,73,74]],[40,274,[16,64,70],[17,24,29,38,76]],[40,386,[69,73,74,77],[17,27,35,42,68,76]],[76,386,[27,35,69,74],[17,40,42,68,73,77]],[40,400,[18],[17,54,62,68]],[76,416,[60,86],[18,42,62,73,77]],[71,170,[32,73],[]],[75,114,[36],[]],[50,116,[],[]],[53,212,[67],[]],[67,212,[53],[]],[55,612,[82],[]],[82,612,[55],[]],[69,452,[],[]],[81,356,[],[]],[83,804,[84],[]]],\"edges\":[[20,[2,6,14,22,26,46,49,50,53,55,66,67,69,81,82]]],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00063.record000" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00063.record000\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-14,-9],[-15,-4],[-15,-13],[-15,-14],[-16,-13],[-16,-14],[-16,-15],[-17,-13],[-18,-13],[-18,-14],[-19,-13],[-19,-15],[-20,-3],[-20,-16],[-20,-17],[-24,-20],[-26,-2],[-26,-16],[-26,-20],[-30,-16],[-30,-17],[-30,-21],[-30,-25],[-30,-27],[-30,-28],[-30,-29],[-31,-14],[-31,-17],[-31,-18],[-31,-30],[-33,-19],[-34,-15],[-35,-34],[-36,-1],[-36,-13],[-36,-14],[-36,-15],[-36,-24],[-36,-33],[-36,-34],[-36,-35],[-38,-19],[-38,-34],[-39,-17],[-39,-19],[-39,-30],[-40,-33],[-40,-36],[-41,-40],[-42,-25],[-42,-26],[-42,-27],[-42,-28],[-42,-32],[-43,-35],[-43,-36],[-43,-41],[-44,-42],[-44,-43],[-45,-30],[-45,-42],[-46,-31],[-47,-41],[-48,-18],[-48,-21],[-48,-23],[-48,-33],[-48,-41],[-49,-48],[-50,-1],[-50,-14],[-50,-15],[-50,-48],[-51,-17],[-51,-18],[-52,-17],[-52,-18],[-52,-20],[-52,-48],[-55,-29],[-55,-42],[-55,-54],[-56,-29],[-56,-50],[-58,-42],[-58,-50],[-60,-32],[-60,-55],[-60,-56],[-61,-50],[-62,-48],[-63,-48],[-65,-34],[-65,-35],[-65,-36],[-65,-38],[-66,-34],[-68,-42],[-68,-50],[-17,1,2,14,15],[-18,1,2,15,20],[-2,-14,-19],[-2,-15,-17],[-2,-15,-18],[-15,-18,-20],[-22,1,3,15,24,25,26],[-4,-5,-14],[-4,-14,-35],[-9,-10,-15],[-9,-15,-48],[-36,2,16,20,37,39],[-40,2,4,16,20,39],[-9,2,16,20,51,53],[-20,9,50],[-36,3,6,26,42],[-3,-36,-42],[-4,-26,-43],[-26,9,50,56],[-50,3,24,26,55],[-30,8,42],[-30,53,55,58,61],[-36,9,50,64],[-50,4,34,36,65],[-65,4,9,50],[-36,7,23,41],[-41,5,15,36],[-33,65,66],[-35,49,63],[-36,49,62,63,66],[-38,49,63],[-8,6,24,28,34,37,40,43],[-24,64,65,68],[-42,56,64,65],[-41,65,66],[-41,67],[-32,68],[-42,59,61],[-18,10,50,53],[-56,10,14,22,27,48],[-31,11,48,54],[-31,53,57,58,61],[-60,21,27,53,58],[-31,12],[-60,44,68],[-55,25,57],[-59,28],[-37],[-39,51],[-51,39],[-40,65],[-65,40],[-53],[-64],[-66,67],[-69,13,14,48,50],[-70,29,45,46,47],[-71,24,34,42,43],[-72,31,52,60],[-73,16,17,18,19],[-74,33,35,38,41],[-75,20,26,30,32],[-76,15,36],[-15,76],[-36,76],[-77,69,70],[-78,69],[-78,70],[-79,71,72],[-80,71],[-80,72],[-81,77],[-81,78,80],[-82,78],[-81,79],[-82,80],[-83,73,74],[-84,73],[-84,74],[-85,75,76],[-86,75],[-86,76],[-87,83],[-87,84,86],[-88,84],[-87,85],[-88,86],[-89,81],[-89,82,88],[-89,87],[89],[-2,-9,-10,-19,-30,-36,-41,-42,-46,-52,-56,-61,-66,-67],[-2,-6,-8,-19,-30,-36,-41,-46,-50,-52,-55,-57,-66,-67],[-7,-9,-12,-19,-20,-31,-36,-42,-47,-48,-56,-61,-66,-67],[-6,-11,-12,-19,-20,-31,-36,-41,-45,-50,-55,-57,-66,-67],[2,4,9,16,20,34,36,37,39,40,50,51,53,64,65]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":20,\"b\":14},{\"tag\":\"incompatible\",\"a\":21,\"b\":6},{\"tag\":\"incompatible\",\"a\":21,\"b\":19},{\"tag\":\"incompatible\",\"a\":21,\"b\":20},{\"tag\":\"incompatible\",\"a\":22,\"b\":19},{\"tag\":\"incompatible\",\"a\":22,\"b\":20},{\"tag\":\"incompatible\",\"a\":22,\"b\":21},{\"tag\":\"incompatible\",\"a\":23,\"b\":19},{\"tag\":\"incompatible\",\"a\":24,\"b\":19},{\"tag\":\"incompatible\",\"a\":24,\"b\":20},{\"tag\":\"incompatible\",\"a\":25,\"b\":19},{\"tag\":\"incompatible\",\"a\":25,\"b\":21},{\"tag\":\"incompatible\",\"a\":26,\"b\":3},{\"tag\":\"incompatible\",\"a\":26,\"b\":22},{\"tag\":\"incompatible\",\"a\":26,\"b\":23},{\"tag\":\"incompatible\",\"a\":31,\"b\":26},{\"tag\":\"incompatible\",\"a\":34,\"b\":2},{\"tag\":\"incompatible\",\"a\":34,\"b\":22},{\"tag\":\"incompatible\",\"a\":34,\"b\":26},{\"tag\":\"incompatible\",\"a\":39,\"b\":22},{\"tag\":\"incompatible\",\"a\":39,\"b\":23},{\"tag\":\"incompatible\",\"a\":39,\"b\":27},{\"tag\":\"incompatible\",\"a\":39,\"b\":32},{\"tag\":\"incompatible\",\"a\":39,\"b\":35},{\"tag\":\"incompatible\",\"a\":39,\"b\":36},{\"tag\":\"incompatible\",\"a\":39,\"b\":37},{\"tag\":\"incompatible\",\"a\":40,\"b\":20},{\"tag\":\"incompatible\",\"a\":40,\"b\":23},{\"tag\":\"incompatible\",\"a\":40,\"b\":24},{\"tag\":\"incompatible\",\"a\":40,\"b\":39},{\"tag\":\"incompatible\",\"a\":45,\"b\":25},{\"tag\":\"incompatible\",\"a\":46,\"b\":21},{\"tag\":\"incompatible\",\"a\":48,\"b\":46},{\"tag\":\"incompatible\",\"a\":49,\"b\":0},{\"tag\":\"incompatible\",\"a\":49,\"b\":19},{\"tag\":\"incompatible\",\"a\":49,\"b\":20},{\"tag\":\"incompatible\",\"a\":49,\"b\":21},{\"tag\":\"incompatible\",\"a\":49,\"b\":31},{\"tag\":\"incompatible\",\"a\":49,\"b\":45},{\"tag\":\"incompatible\",\"a\":49,\"b\":46},{\"tag\":\"incompatible\",\"a\":49,\"b\":48},{\"tag\":\"incompatible\",\"a\":52,\"b\":25},{\"tag\":\"incompatible\",\"a\":52,\"b\":46},{\"tag\":\"incompatible\",\"a\":53,\"b\":23},{\"tag\":\"incompatible\",\"a\":53,\"b\":25},{\"tag\":\"incompatible\",\"a\":53,\"b\":39},{\"tag\":\"incompatible\",\"a\":55,\"b\":45},{\"tag\":\"incompatible\",\"a\":55,\"b\":49},{\"tag\":\"incompatible\",\"a\":57,\"b\":55},{\"tag\":\"incompatible\",\"a\":58,\"b\":32},{\"tag\":\"incompatible\",\"a\":58,\"b\":34},{\"tag\":\"incompatible\",\"a\":58,\"b\":35},{\"tag\":\"incompatible\",\"a\":58,\"b\":36},{\"tag\":\"incompatible\",\"a\":58,\"b\":41},{\"tag\":\"incompatible\",\"a\":59,\"b\":48},{\"tag\":\"incompatible\",\"a\":59,\"b\":49},{\"tag\":\"incompatible\",\"a\":59,\"b\":57},{\"tag\":\"incompatible\",\"a\":60,\"b\":58},{\"tag\":\"incompatible\",\"a\":60,\"b\":59},{\"tag\":\"incompatible\",\"a\":61,\"b\":39},{\"tag\":\"incompatible\",\"a\":61,\"b\":58},{\"tag\":\"incompatible\",\"a\":62,\"b\":40},{\"tag\":\"incompatible\",\"a\":63,\"b\":57},{\"tag\":\"incompatible\",\"a\":64,\"b\":24},{\"tag\":\"incompatible\",\"a\":64,\"b\":27},{\"tag\":\"incompatible\",\"a\":64,\"b\":30},{\"tag\":\"incompatible\",\"a\":64,\"b\":45},{\"tag\":\"incompatible\",\"a\":64,\"b\":57},{\"tag\":\"incompatible\",\"a\":65,\"b\":64},{\"tag\":\"incompatible\",\"a\":66,\"b\":0},{\"tag\":\"incompatible\",\"a\":66,\"b\":20},{\"tag\":\"incompatible\",\"a\":66,\"b\":21},{\"tag\":\"incompatible\",\"a\":66,\"b\":64},{\"tag\":\"incompatible\",\"a\":67,\"b\":23},{\"tag\":\"incompatible\",\"a\":67,\"b\":24},{\"tag\":\"incompatible\",\"a\":68,\"b\":23},{\"tag\":\"incompatible\",\"a\":68,\"b\":24},{\"tag\":\"incompatible\",\"a\":68,\"b\":26},{\"tag\":\"incompatible\",\"a\":68,\"b\":64},{\"tag\":\"incompatible\",\"a\":71,\"b\":37},{\"tag\":\"incompatible\",\"a\":71,\"b\":58},{\"tag\":\"incompatible\",\"a\":71,\"b\":70},{\"tag\":\"incompatible\",\"a\":72,\"b\":37},{\"tag\":\"incompatible\",\"a\":72,\"b\":66},{\"tag\":\"incompatible\",\"a\":74,\"b\":58},{\"tag\":\"incompatible\",\"a\":74,\"b\":66},{\"tag\":\"incompatible\",\"a\":76,\"b\":41},{\"tag\":\"incompatible\",\"a\":76,\"b\":71},{\"tag\":\"incompatible\",\"a\":76,\"b\":72},{\"tag\":\"incompatible\",\"a\":77,\"b\":66},{\"tag\":\"incompatible\",\"a\":79,\"b\":64},{\"tag\":\"incompatible\",\"a\":80,\"b\":64},{\"tag\":\"incompatible\",\"a\":82,\"b\":46},{\"tag\":\"incompatible\",\"a\":82,\"b\":48},{\"tag\":\"incompatible\",\"a\":82,\"b\":49},{\"tag\":\"incompatible\",\"a\":82,\"b\":52},{\"tag\":\"incompatible\",\"a\":83,\"b\":46},{\"tag\":\"incompatible\",\"a\":86,\"b\":58},{\"tag\":\"incompatible\",\"a\":86,\"b\":66},{\"tag\":\"mate\",\"ridge\":7,\"a\":23,\"owners\":[0,2,20,21]},{\"tag\":\"mate\",\"ridge\":7,\"a\":24,\"owners\":[0,2,21,26]},{\"tag\":\"three\",\"ridge\":7,\"vertices\":[2,20,25]},{\"tag\":\"three\",\"ridge\":7,\"vertices\":[2,21,23]},{\"tag\":\"three\",\"ridge\":7,\"vertices\":[2,21,24]},{\"tag\":\"three\",\"ridge\":7,\"vertices\":[21,24,26]},{\"tag\":\"mate\",\"ridge\":11,\"a\":29,\"owners\":[0,3,21,31,32,34]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[6,7,20]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[6,20,48]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[14,15,21]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[14,21,64]},{\"tag\":\"mate\",\"ridge\":69,\"a\":49,\"owners\":[2,22,26,50,53]},{\"tag\":\"mate\",\"ridge\":69,\"a\":55,\"owners\":[2,6,22,26,53]},{\"tag\":\"mate\",\"ridge\":70,\"a\":14,\"owners\":[2,22,26,67,69]},{\"tag\":\"mate\",\"ridge\":70,\"a\":26,\"owners\":[14,66]},{\"tag\":\"mate\",\"ridge\":73,\"a\":49,\"owners\":[3,9,34,58]},{\"tag\":\"three\",\"ridge\":73,\"vertices\":[3,49,58]},{\"tag\":\"three\",\"ridge\":73,\"vertices\":[6,34,59]},{\"tag\":\"mate\",\"ridge\":74,\"a\":34,\"owners\":[14,66,72]},{\"tag\":\"mate\",\"ridge\":74,\"a\":66,\"owners\":[3,31,34,71]},{\"tag\":\"mate\",\"ridge\":193,\"a\":39,\"owners\":[13,58]},{\"tag\":\"mate\",\"ridge\":194,\"a\":39,\"owners\":[69,71,74,77]},{\"tag\":\"mate\",\"ridge\":76,\"a\":49,\"owners\":[14,66,81]},{\"tag\":\"mate\",\"ridge\":76,\"a\":66,\"owners\":[6,46,49,82]},{\"tag\":\"mate\",\"ridge\":76,\"a\":82,\"owners\":[6,14,66]},{\"tag\":\"mate\",\"ridge\":521,\"a\":49,\"owners\":[10,30,57]},{\"tag\":\"mate\",\"ridge\":521,\"a\":57,\"owners\":[7,21,49]},{\"tag\":\"mate\",\"ridge\":524,\"a\":45,\"owners\":[82,83]},{\"tag\":\"mate\",\"ridge\":524,\"a\":48,\"owners\":[65,80]},{\"tag\":\"mate\",\"ridge\":524,\"a\":49,\"owners\":[65,79,80,83]},{\"tag\":\"mate\",\"ridge\":532,\"a\":52,\"owners\":[65,80]},{\"tag\":\"mate\",\"ridge\":97,\"a\":13,\"owners\":[9,31,36,46,50,55,59]},{\"tag\":\"mate\",\"ridge\":104,\"a\":31,\"owners\":[81,82,86]},{\"tag\":\"mate\",\"ridge\":104,\"a\":58,\"owners\":[72,81,82]},{\"tag\":\"mate\",\"ridge\":552,\"a\":57,\"owners\":[82,83]},{\"tag\":\"mate\",\"ridge\":560,\"a\":57,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":224,\"a\":41,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":224,\"a\":58,\"owners\":[75,77]},{\"tag\":\"mate\",\"ridge\":262,\"a\":24,\"owners\":[15,66,69]},{\"tag\":\"mate\",\"ridge\":266,\"a\":72,\"owners\":[15,20,29,35,64]},{\"tag\":\"mate\",\"ridge\":274,\"a\":40,\"owners\":[16,64,70]},{\"tag\":\"mate\",\"ridge\":386,\"a\":40,\"owners\":[69,73,74,77]},{\"tag\":\"mate\",\"ridge\":386,\"a\":76,\"owners\":[27,35,69,74]},{\"tag\":\"mate\",\"ridge\":400,\"a\":40,\"owners\":[18]},{\"tag\":\"mate\",\"ridge\":416,\"a\":76,\"owners\":[60,86]},{\"tag\":\"mate\",\"ridge\":170,\"a\":71,\"owners\":[32,73]},{\"tag\":\"mate\",\"ridge\":114,\"a\":75,\"owners\":[36]},{\"tag\":\"mate\",\"ridge\":116,\"a\":50,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":212,\"a\":53,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":212,\"a\":67,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":612,\"a\":55,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":612,\"a\":82,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":452,\"a\":69,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":356,\"a\":81,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":804,\"a\":83,\"owners\":[84]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[19,20,64,66],\"full_literals\":[-69,13,14,48,50]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[37,61,62,63],\"full_literals\":[-70,29,45,46,47]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[31,46,58,59],\"full_literals\":[-71,24,34,42,43]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[40,68,76],\"full_literals\":[-72,31,52,60]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[22,23,24,25],\"full_literals\":[-73,16,17,18,19]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[45,48,52,57],\"full_literals\":[-74,33,35,38,41]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[26,34,39,41],\"full_literals\":[-75,20,26,30,32]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[21,49],\"full_literals\":[-76,15,36]},{\"tag\":\"group_take\",\"kind\":2,\"index\":7,\"member\":21,\"full_literals\":[-15,76]},{\"tag\":\"group_take\",\"kind\":2,\"index\":7,\"member\":49,\"full_literals\":[-36,76]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-77,69,70],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-78,69,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-78,false,70],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-79,71,72],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-80,71,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-80,false,72],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-81,77,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-81,78,80],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-82,78,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-81,false,79],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-82,false,80],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-83,73,74],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-84,73,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-84,false,74],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-85,75,76],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-86,75,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-86,false,76],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-87,83,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-87,84,86],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-88,84,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-87,false,85],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-88,false,86],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-89,81,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-89,82,88],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-89,false,87],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"block\",\"leaf\":0,\"vertices\":[2,14,15,25,39,49,57,58,62,68,72,77,83,84]},{\"tag\":\"block\",\"leaf\":1,\"vertices\":[2,9,13,25,39,49,57,62,66,68,71,73,83,84]},{\"tag\":\"block\",\"leaf\":2,\"vertices\":[10,14,18,25,26,40,49,58,63,64,72,77,83,84]},{\"tag\":\"block\",\"leaf\":3,\"vertices\":[9,16,18,25,26,40,49,57,61,66,71,73,83,84]},{\"tag\":\"edge\",\"edge\":20,\"owners\":[2,6,14,22,26,46,49,50,53,55,66,67,69,81,82]}]}"
  "196 81 0 190 187 0\n197 87 0 190 189 0\n198 77 0 196 171 0\n199 79 0 196 174 0\n200 83 0 197 182 0\n201 85 0 197 185 0\n202 2 4 9 16 20 34 36 39 40 50 51 65 0 147 152 153 195 0\n203 -43 -19 -74 0 42 31 55 57 160 0\n204 -20 -50 86 0 197 190 186 188 175 170 169 183 178 177 13 14 15 16 19 78 119 81 88 158 29 159 31 42 203 157 33 93 97 160 134 0\n205 -34 -74 0 33 43 93 97 127 134 160 0\n206 -33 -50 76 0 201 190 197 153 181 204 99 136 84 183 178 205 186 188 175 170 169 177 179 164 31 47 151 133 132 123 157 117 59 161 144 20 21 30 159 158 77 0\n207 -35 -50 86 0 190 197 153 99 84 183 178 205 186 188 175 169 55 94 133 132 157 0\n208 -38 -50 76 0 201 190 197 153 181 204 99 136 84 183 178 205 186 188 175 170 169 177 179 164 42 96 133 132 123 157 117 59 161 144 20 21 30 159 158 77 0\n209 -50 76 0 190 197 153 181 183 178 205 186 188 175 169 84 99 206 207 208 160 49 57 151 133 132 157 0\n210 -13 -73 0 5 8 9 11 159 0\n211 -17 -14 76 0 201 190 209 1 114 27 181 186 188 175 170 179 21 76 158 87 89 161 118 0\n212 -42 61 0 53 137 146 0\n213 4 -14 76 0 197 10 181 183 177 6 211 159 45 149 102 209 1 114 178 205 164 112 124 202 0\n214 -14 76 0 197 181 183 178 177 164 163 6 10 211 159 31 42 213 107 108 126 160 0\n215 76 0 197 190 181 186 183 188 177 178 173 166 209 210 214 155 67 68 69 92 128 130 160 0\n216 36 -48 16 50 0 200 215 67 68 69 92 128 130 160 176 64 162 2 12 32 110 124 159 114 150 44 74 103 202 0\n217 -48 16 50 0 200 197 190 153 152 64 65 66 67 68 69 79 91 92 128 130 160 178 176 183 184 180 188 173 175 167 169 170 216 38 40 56 95 122 125 129 157 154 51 52 54 61 85 133 212 142 83 158 28 30 62 143 159 161 156 193 0\n218 -19 -10 -75 -74 -42 -72 -70 -9 -36 16 0 153 147 95 133 83 58 98 144 212 61 54 51 41 39 42 45 160 63 135 134 156 62 158 78 111 161 191 0\n219 -30 19 60 -73 -72 16 0 21 30 159 158 77 0\n220 -36 16 50 0 198 196 190 153 217 34 35 36 37 38 40 56 95 122 155 165 166 172 173 169 170 188 157 184 186 50 51 52 54 58 98 133 116 177 178 180 106 144 139 218 219 161 15 78 159 158 29 0\n221 -20 -73 -15 16 0 12 15 105 159 0\n222 -17 16 50 0 190 215 152 220 162 217 3 4 155 166 173 188 184 177 221 32 2 44 74 103 112 113 151 202 0\n223 16 50 0 152 190 215 217 220 162 2 3 4 12 32 155 166 173 188 184 177 221 222 159 75 138 104 148 109 112 124 202 0\n224 78 -16 0 215 196 190 7 162 56 40 38 20 18 14 172 173 169 188 157 186 54 180 161 0\n225 50 0 215 197 190 223 5 6 7 14 18 20 162 38 39 40 41 56 224 166 155 68 69 92 130 160 178 183 184 180 188 161 175 54 169 157 0\n226 -1 0 225 70 0\n227 -14 0 225 71 0\n228 -15 0 225 72 0\n229 -48 0 225 73 0\n230 -58 0 225 86 0\n231 -61 0 225 90 0\n232 -68 0 225 99 0\n233 36 0 228 215 162 0\n234 -42 0 231 212 0\n235 -32 0 232 136 0\n236 -24 0 233 38 0\n237 -33 0 233 39 0\n238 -34 0 233 40 0\n239 -35 0 233 41 0\n240 -40 0 233 48 0\n241 -43 0 233 56 0\n242 -65 0 233 95 0\n243 -71 0 234 236 238 241 157 0\n244 72 0 243 199 168 0\n245 -80 0 243 169 0\n246 -82 0 245 175 0\n247 78 0 245 196 172 0\n248 88 0 246 190 188 0\n249 70 0 247 167 0\n250 84 0 248 184 0\n251 86 0 248 186 0\n252 73 0 250 177 0\n253 74 0 250 178 0\n254 75 0 251 180 0\n255 -16 0 254 235 14 18 20 161 0\n256 -30 20 0 234 231 230 152 238 240 147 236 241 255 252 244 237 253 239 242 249 225 233 22 23 24 25 26 30 46 60 120 121 145 142 111 131 219 158 42 160 63 135 134 156 192 0\n257 30 20 0 255 252 233 147 226 228 227 235 254 161 17 100 101 111 159 45 0\n258 20 0 256 257 0\n259 -3 0 258 13 0\n260 -17 0 258 15 0\n261 -26 0 258 19 0\n262 -52 0 258 78 0\n263 55 0 259 225 236 261 119 0\n264 6 0 259 261 233 234 115 0\n265 -29 0 263 80 0\n266 -54 0 263 82 0\n267 -60 0 263 88 0\n268 31 0 267 244 262 158 0\n269 -18 0 268 29 0\n270 -46 0 268 62 0\n271 11 0 268 229 266 140 0\n272 57 0 268 152 230 231 141 0\n273 12 0 268 143 0\n274 19 0 269 255 252 260 159 0\n275 -38 0 274 42 0\n276 41 0 275 239 253 237 160 0\n277 -47 0 276 63 0\n278 67 0 276 135 0\n279 66 0 276 242 134 0\n280 45 0 277 249 270 265 156 0\n281 0 280 279 264 273 258 268 233 271 274 225 263 272 276 278 194 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record000.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record000.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record000.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record000.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record000 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeafTable : ConcreteGrowth.Table (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record000.l) :=
(.branch 2
 (.branch 1
 (.leaf (⟨0, by decide⟩))
 (.leaf (⟨1, by decide⟩)))
 (.branch 3
 (.leaf (⟨2, by decide⟩))
 (.leaf (⟨3, by decide⟩))))
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record000.l := originalLeafTable.get j.val
def orbitWordTable : ConcreteGrowth.Table (List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record000.g)) :=
(.branch 2
 (.branch 1
 (.leaf ([]))
 (.leaf ([])))
 (.branch 3
 (.leaf ([]))
 (.leaf ([]))))
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record000.g) := orbitWordTable.get j.val
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record000.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record000.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record000 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record000_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record000 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record000_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record000_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00063.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00063.record014
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "75174c713c789d26a8eac6a9a668da71966c59969595635b0e8b92e8791e6a4e9a6599365391e595954d54d4758b52d8751d0f5a338e9364e5334e8b62ccb8ad2b2ac6b86d1b26c5b61e4731e2749e1745c9715e0f43c2f07d986292a4986634619264658545530c6382c8b0ae0711c27"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db4db4da6db6da6db4936d269b4db4db4924924d369249b49a649249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record014 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record014 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record014.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record014.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record014.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 20), (facetIndex 27), (facetIndex 68), (facetIndex 76)]))
 (.leaf ([(facetIndex 23), (facetIndex 54), (facetIndex 56), (facetIndex 57)])))
 (.branch 3
 (.leaf ([(facetIndex 33), (facetIndex 61), (facetIndex 62), (facetIndex 63)]))
 (.leaf ([(facetIndex 41), (facetIndex 79), (facetIndex 83)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 22), (facetIndex 26), (facetIndex 35), (facetIndex 51)]))
 (.leaf ([(facetIndex 29), (facetIndex 40), (facetIndex 43), (facetIndex 47)])))
 (.branch 7
 (.leaf ([(facetIndex 28), (facetIndex 30)]))
 (.leaf ([(facetIndex 36), (facetIndex 37), (facetIndex 38), (facetIndex 39), (facetIndex 42)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "600600000000000490009040800a00bddfff8101ae1003z11;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 32), (facetIndex 59), (facetIndex 64)]))
 (.leaf ([(facetIndex 48), (facetIndex 82), (facetIndex 85)])))
 (.branch 3
 (.leaf ([(facetIndex 72), (facetIndex 77), (facetIndex 88)]))
 (.branch 4
 (.leaf ([(facetIndex 24), (facetIndex 31), (facetIndex 89)]))
 (.leaf ([(facetIndex 19), (facetIndex 21), (facetIndex 49), (facetIndex 53), (facetIndex 70)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 50), (facetIndex 66), (facetIndex 69), (facetIndex 86), (facetIndex 87)]))
 (.leaf ([(facetIndex 25), (facetIndex 52), (facetIndex 55), (facetIndex 58), (facetIndex 65)])))
 (.branch 8
 (.leaf ([(facetIndex 34), (facetIndex 60)]))
 (.branch 9
 (.leaf ([(facetIndex 44), (facetIndex 45), (facetIndex 46), (facetIndex 67), (facetIndex 71), (facetIndex 75), (facetIndex 78), (facetIndex 84)]))
 (.leaf ([(facetIndex 73), (facetIndex 74), (facetIndex 80), (facetIndex 81)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "32551801990820899284508560000706006046054108880000000007003000006300404z13;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
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
def grouped3_0015 : List Nat := [0, 1]
def grouped3_0016 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0018 : List Nat := [2]
def grouped3_0019 : List Nat := [2, 3, 4]
def grouped3_0020 : List Nat := [3]
def grouped3_0021 : List Nat := [3, 4]
def grouped3_0022 : List Nat := [4]
def grouped3_0023 : List Nat := [5]
def grouped3_0024 : List Nat := [5, 6]
def grouped3_0025 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0026 : List Nat := [6]
def grouped3_0027 : List Nat := [7]
def grouped3_0028 : List Nat := [7, 8, 9]
def grouped3_0029 : List Nat := [8]
def grouped3_0030 : List Nat := [8, 9]
def grouped3_0031 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record014 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record014_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00063.record014" "{\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0030\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":5,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00063.record014" 92

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00063.record014" "{\"ridges\":[[9,21],[9,532],[10,69],[12,529],[12,536],[15,292],[16,290],[17,386],[18,400],[22,518],[23,84],[26,21],[26,518],[26,532],[27,292],[30,69],[35,522],[35,529],[35,536],[38,296],[48,417],[51,21],[51,532],[55,21],[55,276],[55,305],[56,21],[56,69],[56,208],[57,532],[60,305],[63,536],[65,417],[66,276],[67,30],[67,532],[68,292],[73,594],[74,276],[75,276],[75,532],[76,100],[76,292],[77,452],[78,90],[79,386],[79,400],[81,786],[83,296],[83,386],[85,480],[86,60],[87,276],[87,532],[88,368],[89,276],[89,452]],\"owners\":[[22,518,[73,75],[2,26,28,30,67,69,70]],[26,518,[69,70],[2,22,28,30,67,73,75]],[35,522,[69,70],[5,22,39,42,67,80,81]],[23,84,[88,89],[8,54,56,57,71,72,73]],[12,529,[9,26,44,46,57],[35,63]],[35,529,[9,57],[12,26,44,46,63]],[9,532,[67,73,75,87],[26,51,57]],[26,532,[87],[9,51,57,67,73,75]],[51,532,[73,75],[9,26,57,67,87]],[57,532,[67,75,87],[9,26,51,73]],[67,532,[9,57],[26,51,73,75,87]],[75,532,[9,51,57],[26,67,73,87]],[87,532,[9,26,57,73],[51,67,75]],[76,100,[10,54],[14,88]],[12,536,[67,80,81,87],[35,51,63]],[35,536,[87],[12,51,63,67,80,81]],[63,536,[67,81,87],[12,35,51,80]],[56,208,[78,84],[13,43,61,71,89]],[16,290,[15,27,48,76,85],[38,83]],[15,292,[52,55,86,88],[27,68,76]],[27,292,[86,88],[15,52,55,68,76]],[68,292,[55,88],[15,27,52,76,86]],[76,292,[52,55,86],[15,27,68,88]],[38,296,[86],[16,52,60,65,68,83]],[83,296,[52,60,86],[16,38,65,68]],[17,386,[31,45,48,74,77,84,85],[41,79,83]],[79,386,[31,48,77,85],[17,41,45,74,83,84]],[83,386,[31,45,74,77,84],[17,41,48,79,85]],[18,400,[45,58,74,84,89],[62,79]],[79,400,[58,89],[18,45,62,74,84]],[67,30,[19,66],[]],[78,90,[32],[]],[73,594,[44],[]],[48,417,[65],[]],[65,417,[48],[]],[86,60,[49],[]],[55,305,[60],[]],[60,305,[55],[]],[81,786,[75],[]],[77,452,[89],[]],[89,452,[77],[]],[85,480,[],[]],[88,368,[],[]]],\"edges\":[[34,[9,12,26,35,44,46,51,57,63,67,73,75,80,81,87]],[37,[15,16,27,38,48,52,55,60,65,68,76,83,85,86,88]],[42,[17,18,31,41,45,48,58,62,65,74,77,79,83,84,85,89]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00063.record014" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00063.record014\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-10,-9],[-14,-13],[-15,-13],[-24,-9],[-24,-20],[-26,-9],[-27,-9],[-27,-10],[-27,-16],[-27,-20],[-27,-22],[-27,-24],[-27,-26],[-30,-17],[-30,-21],[-31,-25],[-31,-29],[-32,-27],[-33,-13],[-33,-16],[-33,-20],[-33,-22],[-33,-24],[-33,-28],[-33,-32],[-34,-27],[-34,-33],[-35,-33],[-36,-27],[-36,-33],[-40,-27],[-41,-27],[-43,-12],[-43,-18],[-43,-21],[-43,-23],[-43,-38],[-43,-42],[-44,-43],[-45,-14],[-46,-45],[-48,-36],[-49,-43],[-50,-43],[-51,-39],[-52,-12],[-52,-18],[-52,-23],[-52,-45],[-52,-49],[-54,-9],[-54,-10],[-54,-26],[-54,-28],[-54,-40],[-54,-41],[-55,-9],[-55,-27],[-55,-54],[-57,-45],[-2,-15,-30],[-10,42,44],[-12,40,41],[-18,40,41],[-1,-29,-30],[-12,-29,-30],[-26,-29,-30],[-11,56,57],[-3,1,12,21,23,31],[-18,1,31],[-1,38,42,44,55],[-12,55],[-26,42,44],[-31,38,44,55],[-38,1,31],[-44,1,26,31],[-55,1,12,31,42],[-45,2,28],[-3,38,49,50,55],[-18,55],[-35,38,50,55],[-30,47,52],[-5,4,13,24,45,53],[-4,27,29,54,56],[-13,54,56],[-39,29,56],[-45,27,29,54],[-19,54],[-51,27,33,54],[-6,16,22,24,43,46,52,53],[-48,16,24,46,53],[-51,16,22,43,46,52],[-7,22,32,43,52,57],[-48,32,57],[-38,8,37],[-29,-37,-57],[-29,-43,-55],[-29,-44,-57],[-29,-55,-57],[-47,17],[-42,21],[-24,36],[-36,24],[-54,25],[-29,33],[-33,29],[-50,44],[-46,57],[-57,46],[-53],[-56],[-58,9,13,39,45],[-59,11,28,30,31],[-60,20,48,51],[-61,10,12,18,26],[-62,14,15],[-63,58,59],[-64,58],[-64,59],[-65,60],[-66,63],[-66,64,65],[-67,64],[-68,61],[-69,62],[-70,68,69],[-71,68],[-72,66],[-72,67,71],[-72,70],[72],[-46,73],[-57,74],[-8,75],[-29,76],[-33,77],[-21,78],[-23,78],[-42,79],[-49,79],[-74,80],[-74,-75,81],[-73,-80,82],[-73,-81,83],[-82,84],[-83,85],[-76,86],[-79,87],[-78,87],[-77,88],[-77,-87,89],[-86,-88,90],[-86,-89,91],[-84,-91,92],[-85,-90,92],[-92],[1,3,12,18,21,23,26,31,35,38,42,44,49,50,55],[4,5,13,19,24,27,29,33,36,39,45,51,53,54,56],[6,7,16,20,22,24,32,34,36,43,46,48,51,52,53,57]],\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":22,\"b\":20},{\"tag\":\"incompatible\",\"a\":28,\"b\":27},{\"tag\":\"incompatible\",\"a\":30,\"b\":27},{\"tag\":\"incompatible\",\"a\":48,\"b\":20},{\"tag\":\"incompatible\",\"a\":48,\"b\":41},{\"tag\":\"incompatible\",\"a\":51,\"b\":20},{\"tag\":\"incompatible\",\"a\":52,\"b\":20},{\"tag\":\"incompatible\",\"a\":52,\"b\":22},{\"tag\":\"incompatible\",\"a\":52,\"b\":31},{\"tag\":\"incompatible\",\"a\":52,\"b\":41},{\"tag\":\"incompatible\",\"a\":52,\"b\":45},{\"tag\":\"incompatible\",\"a\":52,\"b\":48},{\"tag\":\"incompatible\",\"a\":52,\"b\":51},{\"tag\":\"incompatible\",\"a\":56,\"b\":32},{\"tag\":\"incompatible\",\"a\":56,\"b\":44},{\"tag\":\"incompatible\",\"a\":57,\"b\":49},{\"tag\":\"incompatible\",\"a\":57,\"b\":55},{\"tag\":\"incompatible\",\"a\":58,\"b\":52},{\"tag\":\"incompatible\",\"a\":60,\"b\":27},{\"tag\":\"incompatible\",\"a\":60,\"b\":31},{\"tag\":\"incompatible\",\"a\":60,\"b\":41},{\"tag\":\"incompatible\",\"a\":60,\"b\":45},{\"tag\":\"incompatible\",\"a\":60,\"b\":48},{\"tag\":\"incompatible\",\"a\":60,\"b\":54},{\"tag\":\"incompatible\",\"a\":60,\"b\":58},{\"tag\":\"incompatible\",\"a\":62,\"b\":52},{\"tag\":\"incompatible\",\"a\":62,\"b\":60},{\"tag\":\"incompatible\",\"a\":63,\"b\":60},{\"tag\":\"incompatible\",\"a\":65,\"b\":52},{\"tag\":\"incompatible\",\"a\":65,\"b\":60},{\"tag\":\"incompatible\",\"a\":69,\"b\":52},{\"tag\":\"incompatible\",\"a\":70,\"b\":52},{\"tag\":\"incompatible\",\"a\":74,\"b\":26},{\"tag\":\"incompatible\",\"a\":74,\"b\":35},{\"tag\":\"incompatible\",\"a\":74,\"b\":44},{\"tag\":\"incompatible\",\"a\":74,\"b\":46},{\"tag\":\"incompatible\",\"a\":74,\"b\":67},{\"tag\":\"incompatible\",\"a\":74,\"b\":73},{\"tag\":\"incompatible\",\"a\":75,\"b\":74},{\"tag\":\"incompatible\",\"a\":76,\"b\":28},{\"tag\":\"incompatible\",\"a\":77,\"b\":76},{\"tag\":\"incompatible\",\"a\":79,\"b\":65},{\"tag\":\"incompatible\",\"a\":80,\"b\":74},{\"tag\":\"incompatible\",\"a\":81,\"b\":74},{\"tag\":\"incompatible\",\"a\":83,\"b\":68},{\"tag\":\"incompatible\",\"a\":84,\"b\":26},{\"tag\":\"incompatible\",\"a\":84,\"b\":35},{\"tag\":\"incompatible\",\"a\":84,\"b\":46},{\"tag\":\"incompatible\",\"a\":84,\"b\":76},{\"tag\":\"incompatible\",\"a\":84,\"b\":80},{\"tag\":\"incompatible\",\"a\":86,\"b\":20},{\"tag\":\"incompatible\",\"a\":86,\"b\":22},{\"tag\":\"incompatible\",\"a\":86,\"b\":51},{\"tag\":\"incompatible\",\"a\":86,\"b\":54},{\"tag\":\"incompatible\",\"a\":86,\"b\":69},{\"tag\":\"incompatible\",\"a\":86,\"b\":70},{\"tag\":\"incompatible\",\"a\":87,\"b\":20},{\"tag\":\"incompatible\",\"a\":87,\"b\":52},{\"tag\":\"incompatible\",\"a\":87,\"b\":86},{\"tag\":\"incompatible\",\"a\":89,\"b\":76},{\"tag\":\"three\",\"ridge\":69,\"vertices\":[10,30,56]},{\"tag\":\"mate\",\"ridge\":518,\"a\":22,\"owners\":[73,75]},{\"tag\":\"mate\",\"ridge\":518,\"a\":26,\"owners\":[69,70]},{\"tag\":\"mate\",\"ridge\":522,\"a\":35,\"owners\":[69,70]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[9,55,56]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[26,55,56]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[51,55,56]},{\"tag\":\"mate\",\"ridge\":84,\"a\":23,\"owners\":[88,89]},{\"tag\":\"mate\",\"ridge\":529,\"a\":12,\"owners\":[9,26,44,46,57]},{\"tag\":\"mate\",\"ridge\":529,\"a\":35,\"owners\":[9,57]},{\"tag\":\"mate\",\"ridge\":532,\"a\":9,\"owners\":[67,73,75,87]},{\"tag\":\"mate\",\"ridge\":532,\"a\":26,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":532,\"a\":51,\"owners\":[73,75]},{\"tag\":\"mate\",\"ridge\":532,\"a\":57,\"owners\":[67,75,87]},{\"tag\":\"mate\",\"ridge\":532,\"a\":67,\"owners\":[9,57]},{\"tag\":\"mate\",\"ridge\":532,\"a\":75,\"owners\":[9,51,57]},{\"tag\":\"mate\",\"ridge\":532,\"a\":87,\"owners\":[9,26,57,73]},{\"tag\":\"mate\",\"ridge\":100,\"a\":76,\"owners\":[10,54]},{\"tag\":\"mate\",\"ridge\":536,\"a\":12,\"owners\":[67,80,81,87]},{\"tag\":\"mate\",\"ridge\":536,\"a\":35,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":536,\"a\":63,\"owners\":[67,81,87]},{\"tag\":\"mate\",\"ridge\":208,\"a\":56,\"owners\":[78,84]},{\"tag\":\"mate\",\"ridge\":290,\"a\":16,\"owners\":[15,27,48,76,85]},{\"tag\":\"mate\",\"ridge\":292,\"a\":15,\"owners\":[52,55,86,88]},{\"tag\":\"mate\",\"ridge\":292,\"a\":27,\"owners\":[86,88]},{\"tag\":\"mate\",\"ridge\":292,\"a\":68,\"owners\":[55,88]},{\"tag\":\"mate\",\"ridge\":292,\"a\":76,\"owners\":[52,55,86]},{\"tag\":\"mate\",\"ridge\":296,\"a\":38,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":296,\"a\":83,\"owners\":[52,60,86]},{\"tag\":\"mate\",\"ridge\":386,\"a\":17,\"owners\":[31,45,48,74,77,84,85]},{\"tag\":\"mate\",\"ridge\":386,\"a\":79,\"owners\":[31,48,77,85]},{\"tag\":\"mate\",\"ridge\":386,\"a\":83,\"owners\":[31,45,74,77,84]},{\"tag\":\"mate\",\"ridge\":400,\"a\":18,\"owners\":[45,58,74,84,89]},{\"tag\":\"mate\",\"ridge\":400,\"a\":79,\"owners\":[58,89]},{\"tag\":\"mate\",\"ridge\":30,\"a\":67,\"owners\":[19,66]},{\"tag\":\"three\",\"ridge\":276,\"vertices\":[55,66,89]},{\"tag\":\"three\",\"ridge\":276,\"vertices\":[55,74,87]},{\"tag\":\"three\",\"ridge\":276,\"vertices\":[55,75,89]},{\"tag\":\"three\",\"ridge\":276,\"vertices\":[55,87,89]},{\"tag\":\"mate\",\"ridge\":90,\"a\":78,\"owners\":[32]},{\"tag\":\"mate\",\"ridge\":594,\"a\":73,\"owners\":[44]},{\"tag\":\"mate\",\"ridge\":417,\"a\":48,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":417,\"a\":65,\"owners\":[48]},{\"tag\":\"mate\",\"ridge\":60,\"a\":86,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":305,\"a\":55,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":305,\"a\":60,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":786,\"a\":81,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":452,\"a\":77,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":452,\"a\":89,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":480,\"a\":85,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":368,\"a\":88,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[20,27,68,76],\"full_literals\":[-58,9,13,39,45]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[23,54,56,57],\"full_literals\":[-59,11,28,30,31]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[41,79,83],\"full_literals\":[-60,20,48,51]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[22,26,35,51],\"full_literals\":[-61,10,12,18,26]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[28,30],\"full_literals\":[-62,14,15]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-63,58,59],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-64,58,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-64,false,59],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-65,false,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-66,63,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-66,64,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-67,64,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-68,61,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-69,62,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-70,68,69],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-71,68,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-72,66,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-72,67,71],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-72,false,70],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":77,\"full_literals\":[-46,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":89,\"full_literals\":[-57,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":19,\"full_literals\":[-8,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":55,\"full_literals\":[-29,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":60,\"full_literals\":[-33,77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":44,\"full_literals\":[-21,78]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":46,\"full_literals\":[-23,78]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":73,\"full_literals\":[-42,79]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":80,\"full_literals\":[-49,79]},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-74,false,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-74,-75,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-73,-80,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-73,-81,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-82,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-83,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-76,86],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0030\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-79,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0030\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-78,false,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-77,false,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-77,-87,89],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-86,-88,90],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-86,-89,91],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-84,-91,92],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-85,-90,92],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":4,\"grouped\":true},{\"tag\":\"edge\",\"edge\":34,\"owners\":[9,12,26,35,44,46,51,57,63,67,73,75,80,81,87]},{\"tag\":\"edge\",\"edge\":37,\"owners\":[15,16,27,38,48,52,55,60,65,68,76,83,85,86,88]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[17,18,31,41,45,48,58,62,65,74,77,79,83,84,85,89]}]}"
  "160 66 0 131 128 0\n161 70 0 131 130 0\n162 63 0 160 121 0\n163 4 5 13 19 24 27 29 33 36 39 45 51 54 0 110 111 158 0\n164 6 7 16 20 22 24 32 34 36 43 46 48 51 52 57 0 110 159 0\n165 55 -43 0 39 38 73 44 43 37 36 35 34 33 71 74 79 81 157 0\n166 29 -43 0 131 111 165 58 59 85 57 34 33 39 38 62 73 115 124 127 129 123 118 86 112 87 0\n167 -43 0 165 166 97 0\n168 24 27 54 33 0 111 110 89 105 84 87 88 85 86 103 83 163 0\n169 27 54 33 0 111 160 85 105 86 87 89 168 4 5 102 112 42 118 114 122 120 0\n170 54 33 0 111 131 110 167 105 86 85 169 7 8 9 10 11 12 13 18 26 29 31 32 63 64 115 124 127 129 123 118 112 41 49 60 90 91 92 93 164 0\n171 -45 -54 0 161 131 111 55 56 64 53 52 63 115 124 127 129 123 119 126 125 104 16 54 40 60 78 116 68 61 113 0\n172 33 0 111 161 131 105 86 170 51 52 53 55 56 63 64 115 124 126 127 125 129 123 118 171 112 2 3 116 0\n173 -13 0 172 19 0\n174 -16 0 172 20 0\n175 -20 0 172 21 0\n176 -22 0 172 22 0\n177 -24 0 172 23 0\n178 -28 0 172 24 0\n179 -32 0 172 25 0\n180 -34 0 172 27 0\n181 -35 0 172 28 0\n182 -36 0 172 30 0\n183 29 0 172 106 0\n184 77 0 172 136 0\n185 -31 0 183 17 0\n186 76 0 183 135 0\n187 88 0 184 150 0\n188 86 0 186 147 0\n189 90 0 187 188 152 0\n190 -85 0 189 156 155 0\n191 -83 0 190 146 0\n192 -30 0 183 181 185 14 15 65 67 66 100 101 77 76 70 75 82 107 48 50 69 157 0\n193 57 45 0 111 179 178 192 185 162 160 131 175 176 167 174 173 108 68 94 113 119 117 122 123 120 129 114 127 45 92 124 112 46 47 1 6 115 0\n194 -57 0 183 191 156 188 184 181 185 109 133 98 96 99 132 141 107 72 80 143 144 145 142 154 134 153 95 151 148 149 139 140 137 138 73 71 79 157 0\n195 -46 0 194 108 0\n196 -48 0 194 179 94 0\n197 45 0 194 193 0\n198 -52 0 197 49 0\n199 -7 0 198 179 167 176 194 93 0\n200 -6 0 198 174 177 167 176 195 110 90 0\n201 -51 0 198 174 167 176 195 92 0\n202 0 200 199 174 175 176 177 179 180 182 167 195 196 201 198 194 164 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record014.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record014.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record014.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record014.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record014 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record014.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record014.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record014.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record014.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record014 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record014_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record014_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record014_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record014_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record014_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record014_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record014_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record014 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record014_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record014_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record014_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00063.record014
