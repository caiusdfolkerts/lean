module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00074Data
public import GraphInputsRow24Part00074Frames
public import GraphInputsRow24Part00074Leaves
public import GraphInputsRow24Part00074Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00074.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record012
def vertexColumn : Fields := ⟨10, hexnat% "b329c9713cb2a9a9693a3392e2b86e4789e17ac9a66598e539b16959568d934cd4b4ad1b61d4749d176c3a4e53a2e4b32d2b2ac6b86d1b26c5b61d4731ca719c9715d0f4d03c4c83a499160d88e1382e07931a264986439495150d48d1342d0752344c3322c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b69b69249249249b6924924936d2492492492492249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [17523466567680, hexnat% "4520408804400000000000", hexnat% "2d8000000000000000000", hexnat% "7801000800000000000", 16659800184061952, hexnat% "76600000000000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record012_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00074.record012

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00074.record016
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record016
def vertexColumn : Fields := ⟨10, hexnat% "2d8370bc1f2ca3693a2e87ab1996558d64d8b61d8ce2b86e2785e0fad1b2699964d94e4b91e6c565555354b51d4cd2b46d2745d0f6c364d5334d332cc7332e2b4acab1ad1b26c5b0ee8761e4751cc729c6745c9715c3723c4f0bc1f4d28a929264c689924991643949515254550d68390d2382c8b12c2b41c8711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "db69b6db6d36db6db4924934924db4926da6d24934924924924924c9249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨85, by decide⟩, ⟨94, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400008000103000000000000", hexnat% "20000000100e03c0000000", hexnat% "800000800000000000", hexnat% "7600000000000000000", 2181843386368, hexnat% "f8e00000000000000", 105554055790592]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record016_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record016_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record016_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record016_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record016_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record016_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record016_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record016_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record016_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00074.record016

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00074.record018
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record018
def vertexColumn : Fields := ⟨10, hexnat% "2cc4f2ca4eac6a3a4e3392e2b86e4789e17ac94e6c5a364d3352d2b46d4749d176c332e2b4acab1ae1b46c9b16e8761e4751cc729c6725c5783d0f4d03c4ca8a9283a499160d88e1382e07931a26490e525454352344d0b41da0e4348d130ce0b22c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "d24d24924924d2492492492492492492492249249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2848848220010000000000", 2249600790429696, hexnat% "1001001c40000000000000", hexnat% "3b6000000000000000", hexnat% "3b6000000000000000000", 114841790497947648]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record018_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record018_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record018_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record018_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record018_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record018_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record018_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record018_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record018_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00074.record018

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00074.record000
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "274b329c9713c1f16a4e87ab1a96959361d8ce4b86e4789e1783e9c6c95a699965391e6c599695956354d475a364d3352d1b61d4749d1743db0d63a4e531cd8b52ccb4ac6b26c5b0ee8791cc749ca785d1725c5743c2f4c91a198362384e079314668591465854352344d0752318d130cd0b22c4b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db4db69269249b6da69249249349249a6d2492492492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record000 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record000 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record000.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record000.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record000.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 60), (facetIndex 71), (facetIndex 75)]))
 (.leaf ([(facetIndex 83), (facetIndex 90), (facetIndex 92)])))
 (.branch 3
 (.leaf ([(facetIndex 93), (facetIndex 94)]))
 (.leaf ([(facetIndex 50), (facetIndex 51), (facetIndex 53)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 73), (facetIndex 74), (facetIndex 76)]))
 (.leaf ([(facetIndex 87), (facetIndex 88), (facetIndex 89)])))
 (.branch 7
 (.leaf ([(facetIndex 95), (facetIndex 96), (facetIndex 97)]))
 (.branch 8
 (.leaf ([(facetIndex 77)]))
 (.leaf ([(facetIndex 98)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "86662210155500010000074044z13;3033z32;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record000 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record000_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00074.record000" "{\"atoms\":[{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00074.record000" 43

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00074.record000" "{\"ridges\":[[17,532],[19,580],[20,641],[20,644],[35,532],[39,580],[40,641],[40,644],[50,594],[51,658],[53,706],[58,532],[62,580],[63,641],[66,529],[67,529],[67,580],[68,532],[68,641],[69,577],[69,580],[70,580],[70,641],[70,644],[73,600],[74,664],[76,712],[87,594],[88,658],[89,706],[95,600],[96,664],[97,712]],\"owners\":[[66,529,[50,51,73,74],[17,35,58,67,68,77]],[67,529,[51,74],[17,35,50,58,66,68,73,77]],[17,532,[87,88,95,96,98],[35,58,66,67,68]],[35,532,[95,96,98],[17,58,66,67,68,87,88]],[58,532,[87,88,98],[17,35,66,67,68,95,96]],[68,532,[87,95,98],[17,35,58,66,67,88,96]],[69,577,[50,53,73,76],[19,39,62,67,70,77]],[19,580,[87,89,95,97,98],[39,62,67,69,70]],[39,580,[95,97,98],[19,62,67,69,70,87,89]],[62,580,[87,89,98],[19,39,67,69,70,95,97]],[67,580,[89,97],[19,39,62,69,70,87,95,98]],[69,580,[87,89,95,97],[19,39,62,67,70,98]],[70,580,[87,95,98],[19,39,62,67,69,89,97]],[20,641,[51,53,74,76],[40,63,68,70]],[40,641,[74,76],[20,51,53,63,68,70]],[63,641,[51,53],[20,40,68,70,74,76]],[68,641,[53,76],[20,40,51,63,70,74]],[70,641,[51,74],[20,40,53,63,68,76]],[20,644,[88,89,96,97],[40,63,68,70]],[40,644,[96,97],[20,63,68,70,88,89]],[70,644,[88,96],[20,40,63,68,89,97]],[50,594,[87],[]],[87,594,[50],[]],[51,658,[88],[]],[88,658,[51],[]],[53,706,[89],[]],[89,706,[53],[]],[73,600,[95],[]],[95,600,[73],[]],[74,664,[96],[]],[96,664,[74],[]],[76,712,[97],[]],[97,712,[76],[]]],\"edges\":[[34,[17,35,50,51,58,66,67,68,73,74,77,87,88,95,96,98]],[41,[19,39,50,53,62,67,69,70,73,76,77,87,89,95,97,98]],[43,[20,40,51,53,63,68,70,74,76,88,89,96,97]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00074.record000" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00074.record000\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-22,-8],[-23,-22],[-24,-4],[-24,-7],[-24,-8],[-24,-22],[-24,-23],[-26,-11],[-26,-18],[-26,-25],[-27,-10],[-27,-18],[-27,-19],[-27,-25],[-27,-26],[-13,7,8,18,19],[-14,8,19],[-1,22,23,25,26,28],[-4,25,26,28],[-10,22,23,28],[-15,22,25,28],[-16,7,9,18,20],[-2,22,24,25,27,28],[-5,25,27,28],[-11,22,24,28],[-14,24,27],[-16,22,24,25,27],[-17,22,25,28],[-3,8,9,19,20],[-6,19,20],[-12,8,9],[-15,9,20],[-17,8,19],[-3,23,24,26,27],[-6,26,27],[-17,23,26],[-7,22],[-22,7],[-8,23],[-23,8],[-9,24],[-24,9],[-18,25],[-25,18],[-19,26],[-26,19],[-20,27],[-27,20],[-29,7,8,9],[-7,29],[-8,29],[-9,29],[-18,30],[-19,30],[-20,30],[-22,31],[-23,31],[-24,31],[-32,25,26,27],[-25,32],[-26,32],[-27,32],[-21,33],[-28,34],[-29,35],[-35,36],[-31,37],[-30,37],[-34,38],[-33,38],[-38,39],[-32,39],[-32,-38,40],[-37,-39,41],[-37,-40,42],[-42,43],[-36,-41,43],[-43],[1,4,7,8,10,13,14,15,18,19,21,22,23,25,26,28],[2,5,7,9,11,14,16,17,18,20,21,22,24,25,27,28],[3,6,8,9,12,15,17,19,20,23,24,26,27]],\"atoms\":[{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":87,\"b\":51},{\"tag\":\"incompatible\",\"a\":88,\"b\":87},{\"tag\":\"incompatible\",\"a\":89,\"b\":35},{\"tag\":\"incompatible\",\"a\":89,\"b\":50},{\"tag\":\"incompatible\",\"a\":89,\"b\":51},{\"tag\":\"incompatible\",\"a\":89,\"b\":87},{\"tag\":\"incompatible\",\"a\":89,\"b\":88},{\"tag\":\"incompatible\",\"a\":96,\"b\":62},{\"tag\":\"incompatible\",\"a\":96,\"b\":73},{\"tag\":\"incompatible\",\"a\":96,\"b\":95},{\"tag\":\"incompatible\",\"a\":97,\"b\":58},{\"tag\":\"incompatible\",\"a\":97,\"b\":73},{\"tag\":\"incompatible\",\"a\":97,\"b\":74},{\"tag\":\"incompatible\",\"a\":97,\"b\":95},{\"tag\":\"incompatible\",\"a\":97,\"b\":96},{\"tag\":\"mate\",\"ridge\":529,\"a\":66,\"owners\":[50,51,73,74]},{\"tag\":\"mate\",\"ridge\":529,\"a\":67,\"owners\":[51,74]},{\"tag\":\"mate\",\"ridge\":532,\"a\":17,\"owners\":[87,88,95,96,98]},{\"tag\":\"mate\",\"ridge\":532,\"a\":35,\"owners\":[95,96,98]},{\"tag\":\"mate\",\"ridge\":532,\"a\":58,\"owners\":[87,88,98]},{\"tag\":\"mate\",\"ridge\":532,\"a\":68,\"owners\":[87,95,98]},{\"tag\":\"mate\",\"ridge\":577,\"a\":69,\"owners\":[50,53,73,76]},{\"tag\":\"mate\",\"ridge\":580,\"a\":19,\"owners\":[87,89,95,97,98]},{\"tag\":\"mate\",\"ridge\":580,\"a\":39,\"owners\":[95,97,98]},{\"tag\":\"mate\",\"ridge\":580,\"a\":62,\"owners\":[87,89,98]},{\"tag\":\"mate\",\"ridge\":580,\"a\":67,\"owners\":[89,97]},{\"tag\":\"mate\",\"ridge\":580,\"a\":69,\"owners\":[87,89,95,97]},{\"tag\":\"mate\",\"ridge\":580,\"a\":70,\"owners\":[87,95,98]},{\"tag\":\"mate\",\"ridge\":641,\"a\":20,\"owners\":[51,53,74,76]},{\"tag\":\"mate\",\"ridge\":641,\"a\":40,\"owners\":[74,76]},{\"tag\":\"mate\",\"ridge\":641,\"a\":63,\"owners\":[51,53]},{\"tag\":\"mate\",\"ridge\":641,\"a\":68,\"owners\":[53,76]},{\"tag\":\"mate\",\"ridge\":641,\"a\":70,\"owners\":[51,74]},{\"tag\":\"mate\",\"ridge\":644,\"a\":20,\"owners\":[88,89,96,97]},{\"tag\":\"mate\",\"ridge\":644,\"a\":40,\"owners\":[96,97]},{\"tag\":\"mate\",\"ridge\":644,\"a\":70,\"owners\":[88,96]},{\"tag\":\"mate\",\"ridge\":594,\"a\":50,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":594,\"a\":87,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":658,\"a\":51,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":658,\"a\":88,\"owners\":[51]},{\"tag\":\"mate\",\"ridge\":706,\"a\":53,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":706,\"a\":89,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":600,\"a\":73,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":600,\"a\":95,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":664,\"a\":74,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":664,\"a\":96,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":712,\"a\":76,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":712,\"a\":97,\"owners\":[76]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[50,51,53],\"full_literals\":[-29,7,8,9]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":50,\"full_literals\":[-7,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":51,\"full_literals\":[-8,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":53,\"full_literals\":[-9,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":73,\"full_literals\":[-18,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":74,\"full_literals\":[-19,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":76,\"full_literals\":[-20,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":87,\"full_literals\":[-22,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":88,\"full_literals\":[-23,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":89,\"full_literals\":[-24,31]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[95,96,97],\"full_literals\":[-32,25,26,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":95,\"full_literals\":[-25,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":96,\"full_literals\":[-26,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":97,\"full_literals\":[-27,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":77,\"full_literals\":[-21,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":98,\"full_literals\":[-28,34]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-29,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-35,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-31,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-30,false,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-34,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-33,false,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-38,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-32,false,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-32,-38,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-37,-39,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-37,-40,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-42,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-36,-41,43],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":34,\"owners\":[17,35,50,51,58,66,67,68,73,74,77,87,88,95,96,98]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[19,39,50,53,62,67,69,70,73,76,77,87,89,95,97,98]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[20,40,51,53,63,68,70,74,76,88,89,96,97]}]}"
  "p cnf 43 81\n-22 -8 0\n-23 -22 0\n-24 -4 0\n-24 -7 0\n-24 -8 0\n-24 -22 0\n-24 -23 0\n-26 -11 0\n-26 -18 0\n-26 -25 0\n-27 -10 0\n-27 -18 0\n-27 -19 0\n-27 -25 0\n-27 -26 0\n-13 7 8 18 19 0\n-14 8 19 0\n-1 22 23 25 26 28 0\n-4 25 26 28 0\n-10 22 23 28 0\n-15 22 25 28 0\n-16 7 9 18 20 0\n-2 22 24 25 27 28 0\n-5 25 27 28 0\n-11 22 24 28 0\n-14 24 27 0\n-16 22 24 25 27 0\n-17 22 25 28 0\n-3 8 9 19 20 0\n-6 19 20 0\n-12 8 9 0\n-15 9 20 0\n-17 8 19 0\n-3 23 24 26 27 0\n-6 26 27 0\n-17 23 26 0\n-7 22 0\n-22 7 0\n-8 23 0\n-23 8 0\n-9 24 0\n-24 9 0\n-18 25 0\n-25 18 0\n-19 26 0\n-26 19 0\n-20 27 0\n-27 20 0\n-29 7 8 9 0\n-7 29 0\n-8 29 0\n-9 29 0\n-18 30 0\n-19 30 0\n-20 30 0\n-22 31 0\n-23 31 0\n-24 31 0\n-32 25 26 27 0\n-25 32 0\n-26 32 0\n-27 32 0\n-21 33 0\n-28 34 0\n-29 35 0\n-35 36 0\n-31 37 0\n-30 37 0\n-34 38 0\n-33 38 0\n-38 39 0\n-32 39 0\n-32 -38 40 0\n-37 -39 41 0\n-37 -40 42 0\n-42 43 0\n-36 -41 43 0\n-43 0\n1 4 7 8 10 13 14 15 18 19 21 22 23 25 26 28 0\n2 5 7 9 11 14 16 17 18 20 21 22 24 25 27 28 0\n3 6 8 9 12 15 17 19 20 23 24 26 27 0\n"
  "82 -42 0 78 76 0\n83 20 27 6 9 12 3 17 19 8 23 24 26 0 81 32 0\n84 30 29 0 51 52 31 42 40 54 55 30 46 29 33 48 83 0\n85 26 27 29 0 47 51 52 31 42 40 35 45 34 36 83 0\n86 27 29 0 82 84 68 75 52 42 50 38 47 26 85 8 9 10 61 22 73 69 70 64 63 24 23 28 80 0\n87 29 0 82 50 51 38 40 84 68 75 86 11 12 13 14 15 62 16 17 73 69 70 64 63 21 19 18 79 0\n88 35 0 87 65 0\n89 36 0 88 66 0\n90 -41 0 89 78 77 0\n91 -27 0 90 48 62 55 72 68 74 0\n92 -20 0 91 47 0\n93 -32 26 0 90 91 59 72 44 74 53 68 0\n94 31 9 0 87 56 57 37 39 49 0\n95 22 38 17 24 25 0 91 92 69 64 24 70 63 26 41 43 37 25 27 23 80 0\n96 -22 17 24 26 0 91 92 41 45 35 1 2 31 29 83 0\n97 22 24 25 0 90 41 94 67 74 71 69 64 95 28 0\n98 24 26 0 93 60 45 97 1 96 33 0\n99 26 0 90 45 93 60 43 98 3 4 5 6 7 58 16 17 67 74 71 69 70 64 63 21 18 20 79 0\n100 19 0 99 46 0\n101 32 0 99 61 0\n102 30 0 100 54 0\n103 39 0 101 72 0\n104 37 0 102 68 0\n105 0 104 103 90 74 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record000.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record000.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record000.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record000.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record000 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record000.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record000.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record000.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record000.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record000 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record000_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record000 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record000_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record000_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00074.record000
