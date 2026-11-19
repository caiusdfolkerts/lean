module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00002Data
public import GraphInputsRow24Part00002Frames
public import GraphInputsRow24Part00002Leaves
public import GraphInputsRow24Part00002Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00002.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record006
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 962877980672, 10414681512476672, (certNat% 3), (certNat% 4)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), 864691129528877056, (certNat% 6), 6896139076894720, 10414681512476672]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), 864691128723570688, (certNat% 6), 123145839181824, 9020423459045376]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), (certNat% 9), (certNat% 10), 9007285154086912, 2392545891975168, 1407374883553280]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), (certNat% 12), (certNat% 13), (certNat% 14), 9020423459045376, 2570108429926400, 1143595172102144]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record006_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00002.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00002.record013
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record013
def vertexColumn : Fields := ⟨10, (certNat% 15)⟩
def kindColumn : Fields := ⟨3, (certNat% 16)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), 5531917877248, (certNat% 18), 4538852718936064, (certNat% 19)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), 844424955297792, (certNat% 21), 16492674416640, (certNat% 22), 35218731827200]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9241404027952955392, (certNat% 23), 16492674416640, (certNat% 24), 10836786607554560, (certNat% 25), 281483633754112]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c3 c2
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record013_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record013_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00002.record013

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00002.record020
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record020
def vertexColumn : Fields := ⟨10, (certNat% 26)⟩
def kindColumn : Fields := ⟨3, (certNat% 27)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), (certNat% 29), 197568495616, 720576009098756096, (certNat% 30)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 32), 43981270417408, (certNat% 33), (certNat% 34)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [728036943031435264, (certNat% 32), (certNat% 29), 13194407968768, (certNat% 35), (certNat% 36)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), 2882304311272931328, 8942390345728, (certNat% 38), (certNat% 39), 35184372088832]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), 4423820509184, (certNat% 41), 721138890332700672, 6896136929411072, 9223372036854775808]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), 2305844109262192640, (certNat% 43), (certNat% 44), (certNat% 45), 8796093022208]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [721174177859502080, (certNat% 46), 6896137063628800, (certNat% 30), (certNat% 43), (certNat% 45), 8813272891392]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record020_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record020_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record020_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record020_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record020_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record020_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record020_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record020_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record020_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00002.record020

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00002.record004
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3a8cb13c6a99a3693ab1a663385e0fbc1e875174789ca6a96a59936539b17259971595535c368d3362d4b51d1743db0ea368e6364cd34cd8b32d2b2ad1b26c5b0ee8791cc789c670dc8f13c560b81ee06c1c85894a519916251542d074c314c8b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db6da49369349a4934db6924936da6924924d2492449249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record004 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record004 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record004.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record004.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record004.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 56), (facetIndex 68)]))
 (.branch 2
 (.leaf ([(facetIndex 30), (facetIndex 42), (facetIndex 44)]))
 (.leaf ([(facetIndex 74), (facetIndex 75)]))))
 (.branch 4
 (.leaf ([(facetIndex 51), (facetIndex 61)]))
 (.branch 5
 (.leaf ([(facetIndex 39), (facetIndex 54)]))
 (.leaf ([(facetIndex 73), (facetIndex 77)])))))
 (.branch 9
 (.branch 7
 (.leaf ([(facetIndex 76), (facetIndex 80)]))
 (.branch 8
 (.leaf ([(facetIndex 52), (facetIndex 53), (facetIndex 64)]))
 (.leaf ([(facetIndex 81), (facetIndex 82)]))))
 (.branch 10
 (.leaf ([(facetIndex 41), (facetIndex 67)]))
 (.branch 11
 (.leaf ([(facetIndex 43), (facetIndex 78)]))
 (.leaf ([(facetIndex 79)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "886ba5622500000900700300000047730000001a1904000000001z1e;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 12
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0002 : List Nat := [0, 1, 2, 3, 4, 5]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [1, 2]
def grouped3_0006 : List Nat := [2]
def grouped3_0007 : List Nat := [3, 4, 5]
def grouped3_0008 : List Nat := [6]
def grouped3_0009 : List Nat := [6, 7, 8]
def grouped3_0010 : List Nat := [6, 7, 8, 9, 10, 11]
def grouped3_0011 : List Nat := [7]
def grouped3_0012 : List Nat := [7, 8]
def grouped3_0013 : List Nat := [8]
def grouped3_0014 : List Nat := [9]
def grouped3_0015 : List Nat := [9, 10, 11]
def grouped3_0016 : List Nat := [10]
def grouped3_0017 : List Nat := [10, 11]
def grouped3_0018 : List Nat := [11]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record004 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record004_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00002.record004" "{\"atoms\":[{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":10},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0005\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00002.record004" 51

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00002.record004" "{\"ridges\":[[13,580],[14,273],[17,800],[18,704],[19,896],[29,580],[34,280],[39,306],[45,704],[48,273],[54,308],[55,580],[56,788],[57,580],[58,800],[59,704],[60,273],[62,280],[65,800],[66,896],[67,464],[68,848],[69,896],[70,704],[70,896]],\"owners\":[[13,580,[74,75],[29,55,57,59]],[29,580,[],[13,55,57,59,74,75]],[55,580,[74,75],[13,29,57,59]],[57,580,[75],[13,29,55,59,74]],[14,273,[39,41,54,56,67,68],[34,48,60,62]],[48,273,[39,41,67,68],[14,34,54,56,60,62]],[60,273,[41,56,67,68],[14,34,39,48,54,62]],[34,280,[80],[14,48,60,62,76,78]],[62,280,[76,80],[14,34,48,60,78]],[17,800,[81,82],[58,65,69]],[58,800,[82],[17,65,69,81]],[65,800,[],[17,58,69,81,82]],[18,704,[75],[45,59,70]],[45,704,[],[18,59,70,75]],[59,704,[],[18,45,70,75]],[70,704,[75],[18,45,59]],[19,896,[82],[66,69,70]],[66,896,[],[19,69,70,82]],[69,896,[],[19,66,70,82]],[70,896,[82],[19,66,69]],[39,306,[76],[]],[54,308,[80],[]],[56,788,[],[]],[67,464,[],[]],[68,848,[],[]]],\"edges\":[[33,[14,34,39,41,48,54,56,60,62,67,68,76,78,80]],[41,[13,18,29,42,45,55,57,59,68,70,74,75]],[44,[17,19,53,56,58,65,66,68,69,70,81,82]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00002.record004" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00002.record004\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,28,29],[-6],[-15,28,29],[-17,29],[-2,8,9,14,16,24,25],[-12,8,9,24,25],[-20,9,16,24,25],[-7,32],[-21,30,32],[-3,33,34],[-18,34],[-22],[-4,29],[-11],[-19],[-27,29],[-5,34],[-23],[-26],[-27,34],[-8,30],[-14,32],[-16],[-24],[-25],[-10,35],[-28,36],[-29,36],[-30,37],[-32,37],[-13,38],[-33,39],[-34,39],[-9,40],[-31,41],[-36,42],[-35,42],[-42,43],[-43,44],[-39,45],[-38,45],[-45,46],[-37,-45,47],[-41,48],[-48,49],[-40,49],[-46,-49,50],[-47,50],[-44,-50,51],[-51],[2,7,8,9,12,14,16,20,21,24,25,30,31,32],[1,4,6,10,11,15,17,19,25,27,28,29],[3,5,13,16,18,22,23,25,26,27,33,34]],\"atoms\":[{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":10,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":580,\"a\":13,\"owners\":[74,75]},{\"tag\":\"mate\",\"ridge\":580,\"a\":29,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":580,\"a\":55,\"owners\":[74,75]},{\"tag\":\"mate\",\"ridge\":580,\"a\":57,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":273,\"a\":14,\"owners\":[39,41,54,56,67,68]},{\"tag\":\"mate\",\"ridge\":273,\"a\":48,\"owners\":[39,41,67,68]},{\"tag\":\"mate\",\"ridge\":273,\"a\":60,\"owners\":[41,56,67,68]},{\"tag\":\"mate\",\"ridge\":280,\"a\":34,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":280,\"a\":62,\"owners\":[76,80]},{\"tag\":\"mate\",\"ridge\":800,\"a\":17,\"owners\":[81,82]},{\"tag\":\"mate\",\"ridge\":800,\"a\":58,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":800,\"a\":65,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":704,\"a\":18,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":704,\"a\":45,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":704,\"a\":59,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":704,\"a\":70,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":896,\"a\":19,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":896,\"a\":66,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":896,\"a\":69,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":896,\"a\":70,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":306,\"a\":39,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":308,\"a\":54,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":788,\"a\":56,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":464,\"a\":67,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":848,\"a\":68,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":42,\"full_literals\":[-10,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":74,\"full_literals\":[-28,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":75,\"full_literals\":[-29,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":76,\"full_literals\":[-30,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":80,\"full_literals\":[-32,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":53,\"full_literals\":[-13,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":81,\"full_literals\":[-33,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":82,\"full_literals\":[-34,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":41,\"full_literals\":[-9,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":78,\"full_literals\":[-31,41]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-36,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-35,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-42,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-43,false,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-39,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-45,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-37,-45,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-41,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-48,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-46,-49,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0010\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-47,false,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-44,-50,51],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":33,\"owners\":[14,34,39,41,48,54,56,60,62,67,68,76,78,80]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[13,18,29,42,45,55,57,59,68,70,74,75]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[17,19,53,56,58,65,66,68,69,70,81,82]}]}"
  "54 2 7 8 9 12 14 20 21 30 31 32 0 23 24 25 51 0\n55 1 4 10 15 17 27 28 29 0 2 14 15 25 52 0\n56 3 5 13 18 27 33 34 0 23 12 18 25 19 53 0\n57 42 0 36 37 27 28 26 1 3 4 13 16 55 0\n58 43 0 57 38 0\n59 44 0 58 39 0\n60 -50 0 59 50 49 0\n61 -47 0 60 48 0\n62 45 0 40 41 32 33 31 10 11 17 20 56 0\n63 46 0 62 42 0\n64 -37 0 62 61 43 0\n65 -49 0 63 60 47 0\n66 -30 0 64 29 0\n67 -32 0 64 30 0\n68 -48 0 65 45 0\n69 -40 0 65 46 0\n70 -21 0 66 67 9 0\n71 -8 0 66 21 0\n72 -7 0 67 8 0\n73 -14 0 67 22 0\n74 -41 0 68 44 0\n75 -9 0 69 34 0\n76 -31 0 74 35 0\n77 -20 0 75 23 24 25 7 0\n78 -2 0 75 71 73 23 24 25 5 0\n79 -12 0 75 71 24 25 6 0\n80 0 78 79 72 71 75 73 77 70 66 76 67 54 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record004.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record004.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record004.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record004.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record004 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record004.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record004.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record004.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record004.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record004 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record004_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record004 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record004_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record004_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00002.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00002.record018
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3c24eac6699964d8ce1b85ef0539b15a5655353346d1774370f2368f1364e4b32d2b1ad1b16e8761e4749ca719d1725c5723c3ce0ac24c83a318361382e07b81b05310e4c50d44d0b41dc0e8360e4330d2344c3312c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "926d24924da492492492492492492449249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record018 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record018 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record018.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 46), (facetIndex 48), (facetIndex 64), (facetIndex 73)]))
 (.leaf ([(facetIndex 44), (facetIndex 55), (facetIndex 56), (facetIndex 65), (facetIndex 74)])))
 (.branch 3
 (.leaf ([(facetIndex 38), (facetIndex 41), (facetIndex 43), (facetIndex 60), (facetIndex 69)]))
 (.leaf ([(facetIndex 35), (facetIndex 57), (facetIndex 58), (facetIndex 59)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 66), (facetIndex 67), (facetIndex 68)]))
 (.leaf ([(facetIndex 42), (facetIndex 49), (facetIndex 63), (facetIndex 72)])))
 (.branch 7
 (.leaf ([(facetIndex 45), (facetIndex 47), (facetIndex 50)]))
 (.branch 8
 (.leaf ([(facetIndex 51), (facetIndex 52), (facetIndex 53), (facetIndex 54)]))
 (.leaf ([(facetIndex 36), (facetIndex 37), (facetIndex 39), (facetIndex 40)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "1050024441050023331177776506061252882883z23;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 1
 (.leaf ([(facetIndex 61), (facetIndex 62)]))
 (.leaf ([(facetIndex 70), (facetIndex 71)])))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨1, sparse_nat% "cz11;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 2
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [4]
def grouped2_0007 : List Nat := [4, 5]
def grouped2_0008 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0009 : List Nat := [5]
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7, 8]
def grouped2_0012 : List Nat := [7]
def grouped2_0013 : List Nat := [7, 8]
def grouped2_0014 : List Nat := [8]
def grouped3_0015 : List Nat := [0]
def grouped3_0017 : List Nat := [1]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record018 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record018_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00002.record018" "{\"atoms\":[{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00002.record018" 49

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00002.record018" "{\"ridges\":[[20,133],[37,133],[40,133],[57,69],[58,69],[59,133],[61,133],[62,133],[63,133]],\"owners\":[[57,69,[3,20,39,42,63],[18,36,58]],[58,69,[3,20,36,42,63],[18,39,57]]],\"edges\":[],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00002.record018" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00002.record018\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-5,-1],[-5,-3],[-6,-4],[-6,-5],[-7,-6],[-8,-1],[-8,-3],[-8,-4],[-8,-6],[-8,-7],[-9,-4],[-9,-5],[-9,-7],[-9,-8],[-10,-5],[-10,-8],[-11,-4],[-11,-5],[-11,-7],[-11,-8],[-12,-4],[-13,-7],[-14,-4],[-14,-7],[-15,-9],[-16,-9],[-17,-9],[-18,-9],[-23,-5],[-23,-6],[-23,-11],[-23,-22],[-24,-6],[-24,-8],[-24,-11],[-24,-22],[-26,-4],[-26,-12],[-27,-7],[-27,-13],[-28,-4],[-28,-7],[-29,-23],[-29,-24],[-19,1,2,7,10,25],[-20,1,2,4,10,25],[-2,-5,-24],[-2,-8,-23],[-5,-21,-24],[-5,-24,-25],[-8,-21,-23],[-8,-23,-25],[-30,6,9,11,22,29],[-31,3,19,20,21],[-32,26,27,28],[-33,12,13,14],[-34,15,16,17,18],[-35,4,5,7,8],[-36,30,31],[-37,30],[-38,36],[-39,37],[-40,32],[-41,34,35],[-42,35],[-44,33],[-43,41],[-44,42],[-46,40],[-45,43],[-46,44],[-47,38],[-47,39,46],[-47,45],[47],[-48,23,24],[-49,48],[49]],\"atoms\":[{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":37,\"b\":3},{\"tag\":\"incompatible\",\"a\":37,\"b\":35},{\"tag\":\"incompatible\",\"a\":38,\"b\":36},{\"tag\":\"incompatible\",\"a\":38,\"b\":37},{\"tag\":\"incompatible\",\"a\":39,\"b\":38},{\"tag\":\"incompatible\",\"a\":40,\"b\":3},{\"tag\":\"incompatible\",\"a\":40,\"b\":35},{\"tag\":\"incompatible\",\"a\":40,\"b\":36},{\"tag\":\"incompatible\",\"a\":40,\"b\":38},{\"tag\":\"incompatible\",\"a\":40,\"b\":39},{\"tag\":\"incompatible\",\"a\":41,\"b\":36},{\"tag\":\"incompatible\",\"a\":41,\"b\":37},{\"tag\":\"incompatible\",\"a\":41,\"b\":39},{\"tag\":\"incompatible\",\"a\":41,\"b\":40},{\"tag\":\"incompatible\",\"a\":42,\"b\":37},{\"tag\":\"incompatible\",\"a\":42,\"b\":40},{\"tag\":\"incompatible\",\"a\":43,\"b\":36},{\"tag\":\"incompatible\",\"a\":43,\"b\":37},{\"tag\":\"incompatible\",\"a\":43,\"b\":39},{\"tag\":\"incompatible\",\"a\":43,\"b\":40},{\"tag\":\"incompatible\",\"a\":45,\"b\":36},{\"tag\":\"incompatible\",\"a\":47,\"b\":39},{\"tag\":\"incompatible\",\"a\":50,\"b\":36},{\"tag\":\"incompatible\",\"a\":50,\"b\":39},{\"tag\":\"incompatible\",\"a\":51,\"b\":41},{\"tag\":\"incompatible\",\"a\":52,\"b\":41},{\"tag\":\"incompatible\",\"a\":53,\"b\":41},{\"tag\":\"incompatible\",\"a\":54,\"b\":41},{\"tag\":\"incompatible\",\"a\":61,\"b\":37},{\"tag\":\"incompatible\",\"a\":61,\"b\":38},{\"tag\":\"incompatible\",\"a\":61,\"b\":43},{\"tag\":\"incompatible\",\"a\":61,\"b\":60},{\"tag\":\"incompatible\",\"a\":62,\"b\":38},{\"tag\":\"incompatible\",\"a\":62,\"b\":40},{\"tag\":\"incompatible\",\"a\":62,\"b\":43},{\"tag\":\"incompatible\",\"a\":62,\"b\":60},{\"tag\":\"incompatible\",\"a\":66,\"b\":36},{\"tag\":\"incompatible\",\"a\":66,\"b\":45},{\"tag\":\"incompatible\",\"a\":67,\"b\":39},{\"tag\":\"incompatible\",\"a\":67,\"b\":47},{\"tag\":\"incompatible\",\"a\":68,\"b\":36},{\"tag\":\"incompatible\",\"a\":68,\"b\":39},{\"tag\":\"incompatible\",\"a\":69,\"b\":61},{\"tag\":\"incompatible\",\"a\":69,\"b\":62},{\"tag\":\"mate\",\"ridge\":69,\"a\":57,\"owners\":[3,20,39,42,63]},{\"tag\":\"mate\",\"ridge\":69,\"a\":58,\"owners\":[3,20,36,42,63]},{\"tag\":\"three\",\"ridge\":133,\"vertices\":[20,37,62]},{\"tag\":\"three\",\"ridge\":133,\"vertices\":[20,40,61]},{\"tag\":\"three\",\"ridge\":133,\"vertices\":[37,59,62]},{\"tag\":\"three\",\"ridge\":133,\"vertices\":[37,62,63]},{\"tag\":\"three\",\"ridge\":133,\"vertices\":[40,59,61]},{\"tag\":\"three\",\"ridge\":133,\"vertices\":[40,61,63]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[38,41,43,60,69],\"full_literals\":[-30,6,9,11,22,29]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[35,57,58,59],\"full_literals\":[-31,3,19,20,21]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[66,67,68],\"full_literals\":[-32,26,27,28]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[45,47,50],\"full_literals\":[-33,12,13,14]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[51,52,53,54],\"full_literals\":[-34,15,16,17,18]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[36,37,39,40],\"full_literals\":[-35,4,5,7,8]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-36,30,31],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-37,30,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-38,false,36],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-39,false,37],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-40,32,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-41,34,35],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-42,false,35],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-44,33,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-43,false,41],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-44,false,42],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-46,40,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-45,false,43],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-46,false,44],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-47,38,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-47,39,46],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-47,false,45],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[61,62],\"full_literals\":[-48,23,24]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-49,48,false],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true}]}"
  "79 38 0 75 72 0\n80 45 0 75 74 0\n81 36 0 79 61 0\n82 43 0 80 70 0\n83 41 0 82 67 0\n84 48 0 78 77 0\n85 -22 0 84 32 36 76 0\n86 -11 -35 0 17 18 19 20 58 0\n87 -4 29 -30 11 0 85 3 11 53 0\n88 -5 29 -30 11 0 85 4 12 53 0\n89 -7 29 -30 11 0 85 5 13 53 0\n90 29 -30 -35 0 85 86 87 88 89 58 9 14 53 0\n91 -29 0 84 43 44 76 0\n92 -8 -31 0 84 6 7 8 10 16 34 76 52 48 51 46 45 54 0\n93 4 7 -35 0 91 81 84 90 59 92 58 1 2 15 29 76 50 47 49 46 45 54 0\n94 -4 -46 0 71 66 69 63 21 23 37 41 56 55 40 0\n95 -46 0 69 71 63 66 68 65 94 93 22 24 39 42 56 55 38 0\n96 39 0 95 75 73 0\n97 37 0 96 62 0\n98 30 0 97 60 0\n99 -35 0 98 91 90 0\n100 34 0 99 83 64 0\n101 -24 9 0 85 91 98 33 35 53 0\n102 9 0 84 85 91 98 101 76 30 31 53 0\n103 -15 0 102 25 0\n104 -16 0 102 26 0\n105 -17 0 102 27 0\n106 -18 0 102 28 0\n107 0 106 104 100 103 105 57 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record018.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record018.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record018.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record018.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record018 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record018.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record018.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record018.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record018.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record018 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record018_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record018_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record018_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record018_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record018_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record018_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record018_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record018 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record018_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record018_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record018_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00002.record018
