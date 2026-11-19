module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00026Data
public import GraphInputsRow24Part00026Frames
public import GraphInputsRow24Part00026Leaves
public import GraphInputsRow24Part00026Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00026.record015
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record015
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 9259436020393312256, (certNat% 3), (certNat% 4), (certNat% 5), (certNat% 6)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), 11263397114937344, 13835110831840296960, 109493776677863424, (certNat% 8)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), 109493776677863424, (certNat% 10), (certNat% 11), (certNat% 12), 11529259026533580800, (certNat% 13)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record015_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record015_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record015_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record015_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record015_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record015_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record015_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record015_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record015_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00026.record015

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00026.record044
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record044
def vertexColumn : Fields := ⟨10, (certNat% 14)⟩
def kindColumn : Fields := ⟨3, (certNat% 15)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), (certNat% 17), (certNat% 18), 4591560557592576, (certNat% 19), 72057594037927936]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), (certNat% 21), (certNat% 22), (certNat% 23), 13835233977142607872]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), (certNat% 21), 13331578486784, (certNat% 25), (certNat% 26)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), (certNat% 28), 108086391056891904, (certNat% 29)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 30), 4535485464576, 1224979098644774912, (certNat% 23)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 21), (certNat% 23), (certNat% 29), 74344578223702016]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 32), (certNat% 33), 13245679140864, 4855443348258816, (certNat% 28)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), (certNat% 35), 576473946442956800, (certNat% 22), (certNat% 36)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), (certNat% 38), 4432406249472, 4503599627370496]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 39), (certNat% 40), (certNat% 41), 576473946442956800, 1157425104234217472]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), (certNat% 33), (certNat% 41), 576473946442956800, 1369094286720630784, 6931321301499904]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c18 c9
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c19 c8
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c20 c7
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c21 c2
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c22 c1
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 43), (certNat% 21), (certNat% 44), (certNat% 45), (certNat% 46)]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 47), (certNat% 21), 13331578486784, (certNat% 48), (certNat% 49)]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 50), (certNat% 51), 108086391056891904, (certNat% 52)]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 53), 4535485464576, 1224979098644774912, (certNat% 45)]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 54), (certNat% 21), (certNat% 45), (certNat% 52), 74344578223702016]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c28 c27
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c29 c26
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 55), (certNat% 56), 13245679140864, 4855443348258816, (certNat% 51)]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 57), (certNat% 58), 576473946442956800, (certNat% 44), (certNat% 59)]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c11 c10
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 60), (certNat% 61), 4432406249472, 4503599627370496]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c34 c33
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 62), (certNat% 63), (certNat% 64), 576473946442956800, 1157425104234217472]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c36 c35
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 65), (certNat% 66), (certNat% 48), 576473946442956800, 1369094286720630784, 6931321301499904]
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c38 c37
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c39 c32
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c40 c31
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c41 c30
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c42 c25
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c43 c24
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 67), (certNat% 68), (certNat% 69), 576475063134453760, (certNat% 70), 15569119009046528, 1675341260405080064]
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c45 c44
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c46 c23
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c47 c0
  c48
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record044_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record044_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record044_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record044_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record044_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record044_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record044_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record044_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record044_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00026.record044

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00026.record001
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3c8ea6693a2ea66c58d61db0e3386e4789e3c4e9665392e665c54d51d70d3346d4749dd0ec398ce3c4d9334d332cc73c2d8b32d2b2ac6bc1cc789e1745c9715e0f43c8f13c3c4689a0ea46198360b81e464990e645194350b41dc0e4330c6344c930cd0b22c2b06e0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6d249b4da49b4926d3692492492492492492492491249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record001 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record001 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record001.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record001.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record001.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 64), (facetIndex 67)]))
 (.branch 2
 (.leaf ([(facetIndex 78), (facetIndex 81)]))
 (.leaf ([(facetIndex 63), (facetIndex 66)]))))
 (.branch 4
 (.leaf ([(facetIndex 72), (facetIndex 73)]))
 (.branch 5
 (.leaf ([(facetIndex 77), (facetIndex 80)]))
 (.leaf ([(facetIndex 86), (facetIndex 87)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "b4000c06001b0000804z2f;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0003 : List Nat := [1]
def grouped3_0004 : List Nat := [1, 2]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [3]
def grouped3_0007 : List Nat := [3, 4, 5]
def grouped3_0008 : List Nat := [4]
def grouped3_0009 : List Nat := [4, 5]
def grouped3_0010 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record001 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record001_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00026.record001" "{\"atoms\":[{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00026.record001" 35

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00026.record001" "{\"ridges\":[[13,193],[15,769],[15,770],[42,193],[43,769],[47,193],[49,769],[49,770],[53,193],[55,769],[55,770],[56,193],[58,193],[59,769],[59,770],[64,780],[67,788],[77,204],[78,780],[80,212],[81,788]],\"owners\":[[13,193,[63,66,72,73],[42,47,53,56,58]],[42,193,[72,73],[13,47,53,56,58,63,66]],[47,193,[66,73],[13,42,53,56,58,63,72]],[53,193,[63,72],[13,42,47,56,58,66,73]],[56,193,[63,66],[13,42,47,53,58,72,73]],[58,193,[63,66,72,73],[13,42,47,53,56]],[15,769,[64,67],[43,49,55,59]],[43,769,[],[15,49,55,59,64,67]],[49,769,[67],[15,43,55,59,64]],[55,769,[64],[15,43,49,59,67]],[59,769,[64,67],[15,43,49,55]],[15,770,[78,81],[43,49,55,59]],[49,770,[81],[15,43,55,59,78]],[55,770,[78],[15,43,49,59,81]],[59,770,[78,81],[15,43,49,55]],[77,204,[63],[]],[64,780,[78],[]],[78,780,[64],[]],[80,212,[66],[]],[67,788,[81],[]],[81,788,[67],[]]],\"edges\":[[39,[13,42,47,53,56,58,63,66,72,73,77,80,86,87]],[44,[15,43,49,55,59,64,67,78,81]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00026.record001" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00026.record001\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,12,14,16,17],[-3,16,17],[-5,14,17],[-7,12,16],[-9,12,14],[-10,12,14,16,17],[-2,13,15],[-4],[-6,15],[-8,13],[-11,13,15],[-2,19,21],[-6,21],[-8,19],[-11,19,21],[-18,12],[-13,19],[-19,13],[-20,14],[-15,21],[-21,15],[-13,24],[-15,24],[-19,25],[-21,25],[-12,26],[-14,26],[-16,27],[-17,27],[-22,28],[-23,28],[-25,29],[-25,-26,30],[-24,-29,31],[-24,-30,32],[-28,33],[-33,34],[-27,34],[-31,-34,35],[-32,35],[-35],[1,3,5,7,9,10,12,14,16,17,18,20,22,23],[2,4,6,8,11,13,15,19,21]],\"atoms\":[{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":193,\"a\":13,\"owners\":[63,66,72,73]},{\"tag\":\"mate\",\"ridge\":193,\"a\":42,\"owners\":[72,73]},{\"tag\":\"mate\",\"ridge\":193,\"a\":47,\"owners\":[66,73]},{\"tag\":\"mate\",\"ridge\":193,\"a\":53,\"owners\":[63,72]},{\"tag\":\"mate\",\"ridge\":193,\"a\":56,\"owners\":[63,66]},{\"tag\":\"mate\",\"ridge\":193,\"a\":58,\"owners\":[63,66,72,73]},{\"tag\":\"mate\",\"ridge\":769,\"a\":15,\"owners\":[64,67]},{\"tag\":\"mate\",\"ridge\":769,\"a\":43,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":769,\"a\":49,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":769,\"a\":55,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":769,\"a\":59,\"owners\":[64,67]},{\"tag\":\"mate\",\"ridge\":770,\"a\":15,\"owners\":[78,81]},{\"tag\":\"mate\",\"ridge\":770,\"a\":49,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":770,\"a\":55,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":770,\"a\":59,\"owners\":[78,81]},{\"tag\":\"mate\",\"ridge\":204,\"a\":77,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":780,\"a\":64,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":780,\"a\":78,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":212,\"a\":80,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":788,\"a\":67,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":788,\"a\":81,\"owners\":[67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":64,\"full_literals\":[-13,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":67,\"full_literals\":[-15,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":78,\"full_literals\":[-19,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":81,\"full_literals\":[-21,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":63,\"full_literals\":[-12,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":66,\"full_literals\":[-14,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":72,\"full_literals\":[-16,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":73,\"full_literals\":[-17,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":86,\"full_literals\":[-22,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":87,\"full_literals\":[-23,28]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-25,false,29],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-25,-26,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-24,-29,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-24,-30,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-28,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-33,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-27,false,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-31,-34,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-32,false,35],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":39,\"owners\":[13,42,47,53,56,58,63,66,72,73,77,80,86,87]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[15,43,49,55,59,64,67,78,81]}]}"
  "44 -32 0 41 40 0\n45 2 6 8 11 13 15 19 21 0 8 43 0\n46 13 15 0 7 10 11 18 9 21 45 0\n47 24 0 22 23 46 0\n48 19 21 0 12 14 15 17 13 20 45 0\n49 25 0 24 25 48 0\n50 -30 0 47 44 35 0\n51 29 0 49 32 0\n52 -26 0 49 50 33 0\n53 31 0 51 47 34 0\n54 -12 0 52 26 0\n55 -14 0 52 27 0\n56 -34 0 53 41 39 0\n57 -18 0 54 16 0\n58 -20 0 55 19 0\n59 -9 0 55 54 5 0\n60 -33 0 56 37 0\n61 -27 0 56 38 0\n62 -28 0 60 36 0\n63 -16 0 61 28 0\n64 -17 0 61 29 0\n65 -22 0 62 30 0\n66 -23 0 62 31 0\n67 -3 0 63 64 2 0\n68 -1 0 63 55 54 64 1 0\n69 -7 0 63 54 4 0\n70 -10 0 63 55 54 64 6 0\n71 -5 0 64 55 3 0\n72 0 68 71 67 69 59 70 55 54 63 64 57 58 65 66 42 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record001.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record001.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record001.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record001.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record001 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record001.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record001.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record001.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record001.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record001 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record001_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record001 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record001_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record001_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00026.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00026.record002
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ea3687ab1a6639a5635876c398e4b8ae4789e3a4d91e6c5994e5954d51d70d6352d2b51d27743b0e6338e5334f0b62ccb4acab1ad1b26c5ba1d8791cc789d2729c6785d1725c5783c3c1c83ac18364388e0b81e1c439c14354348d0b41dc0e4330c6314c3342c8b0ac1b81d0721c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "da6db6924926d36db492492492492492492492492491249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record002 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record002 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record002.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 46), (facetIndex 49), (facetIndex 52), (facetIndex 73), (facetIndex 88)]))
 (.branch 2
 (.leaf ([(facetIndex 34), (facetIndex 38), (facetIndex 42), (facetIndex 43), (facetIndex 67), (facetIndex 82)]))
 (.leaf ([(facetIndex 33), (facetIndex 61), (facetIndex 62), (facetIndex 63), (facetIndex 64), (facetIndex 65), (facetIndex 66)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 76), (facetIndex 77), (facetIndex 78), (facetIndex 79), (facetIndex 80), (facetIndex 81)]))
 (.leaf ([(facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 58), (facetIndex 59), (facetIndex 60)])))
 (.branch 6
 (.leaf ([(facetIndex 47), (facetIndex 48), (facetIndex 50), (facetIndex 51), (facetIndex 53), (facetIndex 54)]))
 (.leaf ([(facetIndex 35), (facetIndex 36), (facetIndex 37), (facetIndex 39), (facetIndex 40), (facetIndex 41), (facetIndex 44), (facetIndex 45)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "5b6db000000292494924968b45a36276c76c5z19;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record002 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record002_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00026.record002" "{\"atoms\":[]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00026.record002" 0

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00026.record002" "{\"ridges\":[],\"owners\":[],\"edges\":[],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00026.record002" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00026.record002\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[]],\"atoms\":[],\"rules\":[{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true}]}"
  "2 0 1 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record002.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record002.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record002.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record002.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record002 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record002.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record002.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record002.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record002.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record002 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record002_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record002 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record002_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record002_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00026.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00026.record028
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "7cca87ad1b26998d61d98e4b8ae1b91e1783eca479d1725994d51d58d4b4ad1b51d1743dd0f2394cd31cf0b62e2b4acab1ad1b16c3bc1d8791d4731e2749ca745c3713c9c9889a198961590e2382e07a6126465254554348d0b41dc0e4388c6324c5342c8b0ac1b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db49249249b6d2492492492492492492492492449249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record028 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record028 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record028.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record028.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record028.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 40), (facetIndex 43), (facetIndex 45), (facetIndex 69), (facetIndex 83)]))
 (.leaf ([(facetIndex 57), (facetIndex 58), (facetIndex 59)])))
 (.branch 3
 (.leaf ([(facetIndex 36), (facetIndex 37), (facetIndex 41), (facetIndex 56), (facetIndex 68), (facetIndex 82)]))
 (.leaf ([(facetIndex 35), (facetIndex 60), (facetIndex 61), (facetIndex 62), (facetIndex 63), (facetIndex 64), (facetIndex 65), (facetIndex 66)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 74), (facetIndex 75), (facetIndex 76), (facetIndex 77), (facetIndex 78), (facetIndex 79), (facetIndex 80)]))
 (.leaf ([(facetIndex 46), (facetIndex 47), (facetIndex 48), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 53)])))
 (.branch 7
 (.leaf ([(facetIndex 42), (facetIndex 55), (facetIndex 67), (facetIndex 81)]))
 (.branch 8
 (.leaf ([(facetIndex 39), (facetIndex 44), (facetIndex 54)]))
 (.leaf ([(facetIndex 38), (facetIndex 52)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "264444444000002633333331112675855555507062078223z23;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 72)]))
 (.branch 2
 (.leaf ([(facetIndex 86)]))
 (.leaf ([(facetIndex 88)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 70), (facetIndex 71)]))
 (.leaf ([(facetIndex 73), (facetIndex 84)])))
 (.branch 6
 (.leaf ([(facetIndex 85)]))
 (.leaf ([(facetIndex 87)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "2c6c0000000206cz34;"⟩
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
def grouped2_0008 : List Nat := [4]
def grouped2_0009 : List Nat := [4, 5]
def grouped2_0010 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7, 8]
def grouped2_0014 : List Nat := [7]
def grouped2_0015 : List Nat := [7, 8]
def grouped2_0016 : List Nat := [8]
def grouped3_0017 : List Nat := [0]
def grouped3_0018 : List Nat := [0, 1, 2]
def grouped3_0020 : List Nat := [1]
def grouped3_0021 : List Nat := [1, 2]
def grouped3_0022 : List Nat := [2]
def grouped3_0023 : List Nat := [3]
def grouped3_0024 : List Nat := [3, 4]
def grouped3_0025 : List Nat := [3, 4, 5, 6]
def grouped3_0026 : List Nat := [4]
def grouped3_0027 : List Nat := [5]
def grouped3_0028 : List Nat := [5, 6]
def grouped3_0029 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record028 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record028_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00026.record028" "{\"atoms\":[{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00026.record028" 83

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00026.record028" "{\"ridges\":[[15,769],[17,37],[19,261],[26,38],[28,262],[38,35],[38,37],[38,38],[44,261],[44,262],[45,770],[52,41],[52,42],[54,769],[55,35],[58,35],[58,770],[59,769],[62,261],[64,37],[66,261],[67,37],[70,37],[70,804],[71,836],[73,808],[76,262],[78,38],[80,262],[81,38],[84,38],[84,804],[85,836],[87,808]],\"owners\":[[67,37,[2,17,38,39,40,64,65,70],[22,36,60,69]],[81,38,[2,26,38,39,40,78,79,84],[31,36,74,83]],[19,261,[5,37,39,42,44,45,70,71],[62,65,66]],[44,261,[19,62,65,70,71],[5,37,39,42,45,66]],[62,261,[5,39,42,44,45,70,71],[19,37,65,66]],[66,261,[5,37,39,42,45,70,71],[19,44,62,65]],[28,262,[5,37,39,42,44,45,84,85],[76,79,80]],[44,262,[28,76,79,84,85],[5,37,39,42,45,80]],[76,262,[5,39,42,44,45,84,85],[28,37,79,80]],[80,262,[5,37,39,42,45,84,85],[28,44,76,79]],[52,41,[17,60,63,64,65,72],[7,46,49,50,51,73]],[52,42,[26,74,77,78,79,86],[7,46,49,50,51,87]],[15,769,[70,71,73],[45,54,58,59]],[54,769,[70,71],[15,45,58,59,73]],[59,769,[70,73],[15,45,54,58,71]],[45,770,[87],[15,54,58,59,84,85]],[58,770,[85],[15,45,54,59,84,87]],[70,804,[84],[]],[84,804,[70],[]],[71,836,[85],[]],[85,836,[71],[]],[73,808,[87],[]],[87,808,[73],[]]],\"edges\":[[22,[5,19,28,37,39,42,44,45,62,65,66,70,71,76,79,80,84,85]],[44,[15,45,54,58,59,70,71,73,84,85,87]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00026.record028" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00026.record028\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-10,-2],[-10,-9],[-13,-10],[-15,-1],[-15,-8],[-15,-10],[-15,-12],[-15,-13],[-16,-10],[-18,-13],[-19,-17],[-20,-19],[-22,-19],[-23,-5],[-25,-4],[-27,-5],[-27,-25],[-29,-15],[-30,-23],[-30,-24],[-30,-26],[-32,-11],[-32,-12],[-32,-14],[-32,-26],[-32,-28],[-32,-31],[-33,-30],[-36,-7],[-38,-6],[-40,-7],[-40,-38],[-41,-32],[-42,-15],[-43,-36],[-43,-37],[-43,-39],[-44,-32],[-45,-39],[-46,-12],[-46,-13],[-46,-14],[-46,-22],[-46,-31],[-46,-43],[-46,-44],[-48,-11],[-48,-17],[-48,-18],[-48,-21],[-48,-28],[-48,-32],[-48,-41],[-48,-45],[-10,-19,-21],[-30,1,4,10,11,12,27,28,32],[-4,-30,-32],[-10,-30,-32],[-27,-30,-32],[-43,1,6,10,11,12,40,41,45],[-6,-43,-45],[-10,-43,-45],[-40,-43,-45],[-5,2,9,11,13,15,16,32,33],[-15,5,25,28,32,33],[-25,2,11,13,15,16,32,33],[-29,2,9,11,13,16,32,33],[-7,2,9,11,13,15,16,45,46],[-15,7,38,41,45,46],[-38,2,11,13,15,16,45,46],[-42,2,9,11,13,16,45,46],[-17,4,23,26,27,28,34],[-17,6,36,39,40,41,47],[-3,32,33,35],[-18,32,33],[-22,32,35],[-16,48],[-21,46],[-32,45],[-45,32],[-33,46],[-46,33],[-35,48],[-48,35],[-49,12,14,16,31,44],[-50,20,21,22],[-51,8,23,24,25,26,27,28,29],[-52,36,37,38,39,40,41,42],[-53,13,19,30,43],[-54,11,15,18],[-55,10,17],[-56,49,50],[-57,49],[-57,50],[-58,51],[-59,56],[-60,57],[-60,58],[-61,52],[-62,54,55],[-63,54],[-63,55],[-64,53,63],[-65,53],[-64,62],[-65,63],[-66,61,65],[-66,64],[-67,65],[-68,59],[-68,60,67],[-68,66],[68],[-34,69],[-47,70],[-71,32,33],[-32,71],[-72,35,45],[-35,72],[-45,72],[-73,46],[-46,73],[-74,48],[-48,74],[-70,75],[-75,76],[-69,76],[-72,77],[-78,71],[-78,72],[-71,-72,78],[-79,73,74],[-80,74],[-73,-74,80],[-81,78,79],[-77,-80,82],[-78,81],[-82,83],[-76,-81,83],[-83],[2,5,7,9,11,13,15,16,25,28,29,32,33,38,41,42,45,46],[3,16,18,21,22,32,33,35,45,46,48]],\"atoms\":[{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":38,\"b\":5},{\"tag\":\"incompatible\",\"a\":38,\"b\":37},{\"tag\":\"incompatible\",\"a\":42,\"b\":38},{\"tag\":\"incompatible\",\"a\":44,\"b\":2},{\"tag\":\"incompatible\",\"a\":44,\"b\":35},{\"tag\":\"incompatible\",\"a\":44,\"b\":38},{\"tag\":\"incompatible\",\"a\":44,\"b\":40},{\"tag\":\"incompatible\",\"a\":44,\"b\":42},{\"tag\":\"incompatible\",\"a\":45,\"b\":38},{\"tag\":\"incompatible\",\"a\":54,\"b\":42},{\"tag\":\"incompatible\",\"a\":55,\"b\":52},{\"tag\":\"incompatible\",\"a\":57,\"b\":55},{\"tag\":\"incompatible\",\"a\":59,\"b\":55},{\"tag\":\"incompatible\",\"a\":60,\"b\":19},{\"tag\":\"incompatible\",\"a\":62,\"b\":17},{\"tag\":\"incompatible\",\"a\":64,\"b\":19},{\"tag\":\"incompatible\",\"a\":64,\"b\":62},{\"tag\":\"incompatible\",\"a\":66,\"b\":44},{\"tag\":\"incompatible\",\"a\":67,\"b\":60},{\"tag\":\"incompatible\",\"a\":67,\"b\":61},{\"tag\":\"incompatible\",\"a\":67,\"b\":63},{\"tag\":\"incompatible\",\"a\":70,\"b\":39},{\"tag\":\"incompatible\",\"a\":70,\"b\":40},{\"tag\":\"incompatible\",\"a\":70,\"b\":43},{\"tag\":\"incompatible\",\"a\":70,\"b\":63},{\"tag\":\"incompatible\",\"a\":70,\"b\":65},{\"tag\":\"incompatible\",\"a\":70,\"b\":69},{\"tag\":\"incompatible\",\"a\":71,\"b\":67},{\"tag\":\"incompatible\",\"a\":74,\"b\":28},{\"tag\":\"incompatible\",\"a\":76,\"b\":26},{\"tag\":\"incompatible\",\"a\":78,\"b\":28},{\"tag\":\"incompatible\",\"a\":78,\"b\":76},{\"tag\":\"incompatible\",\"a\":79,\"b\":70},{\"tag\":\"incompatible\",\"a\":80,\"b\":44},{\"tag\":\"incompatible\",\"a\":81,\"b\":74},{\"tag\":\"incompatible\",\"a\":81,\"b\":75},{\"tag\":\"incompatible\",\"a\":81,\"b\":77},{\"tag\":\"incompatible\",\"a\":83,\"b\":70},{\"tag\":\"incompatible\",\"a\":84,\"b\":77},{\"tag\":\"incompatible\",\"a\":85,\"b\":40},{\"tag\":\"incompatible\",\"a\":85,\"b\":42},{\"tag\":\"incompatible\",\"a\":85,\"b\":43},{\"tag\":\"incompatible\",\"a\":85,\"b\":59},{\"tag\":\"incompatible\",\"a\":85,\"b\":69},{\"tag\":\"incompatible\",\"a\":85,\"b\":81},{\"tag\":\"incompatible\",\"a\":85,\"b\":83},{\"tag\":\"incompatible\",\"a\":87,\"b\":39},{\"tag\":\"incompatible\",\"a\":87,\"b\":52},{\"tag\":\"incompatible\",\"a\":87,\"b\":54},{\"tag\":\"incompatible\",\"a\":87,\"b\":58},{\"tag\":\"incompatible\",\"a\":87,\"b\":65},{\"tag\":\"incompatible\",\"a\":87,\"b\":70},{\"tag\":\"incompatible\",\"a\":87,\"b\":79},{\"tag\":\"incompatible\",\"a\":87,\"b\":84},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[38,55,58]},{\"tag\":\"mate\",\"ridge\":37,\"a\":67,\"owners\":[2,17,38,39,40,64,65,70]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[17,67,70]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[38,67,70]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[64,67,70]},{\"tag\":\"mate\",\"ridge\":38,\"a\":81,\"owners\":[2,26,38,39,40,78,79,84]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[26,81,84]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[38,81,84]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[78,81,84]},{\"tag\":\"mate\",\"ridge\":261,\"a\":19,\"owners\":[5,37,39,42,44,45,70,71]},{\"tag\":\"mate\",\"ridge\":261,\"a\":44,\"owners\":[19,62,65,70,71]},{\"tag\":\"mate\",\"ridge\":261,\"a\":62,\"owners\":[5,39,42,44,45,70,71]},{\"tag\":\"mate\",\"ridge\":261,\"a\":66,\"owners\":[5,37,39,42,45,70,71]},{\"tag\":\"mate\",\"ridge\":262,\"a\":28,\"owners\":[5,37,39,42,44,45,84,85]},{\"tag\":\"mate\",\"ridge\":262,\"a\":44,\"owners\":[28,76,79,84,85]},{\"tag\":\"mate\",\"ridge\":262,\"a\":76,\"owners\":[5,39,42,44,45,84,85]},{\"tag\":\"mate\",\"ridge\":262,\"a\":80,\"owners\":[5,37,39,42,45,84,85]},{\"tag\":\"mate\",\"ridge\":41,\"a\":52,\"owners\":[17,60,63,64,65,72]},{\"tag\":\"mate\",\"ridge\":42,\"a\":52,\"owners\":[26,74,77,78,79,86]},{\"tag\":\"mate\",\"ridge\":769,\"a\":15,\"owners\":[70,71,73]},{\"tag\":\"mate\",\"ridge\":769,\"a\":54,\"owners\":[70,71]},{\"tag\":\"mate\",\"ridge\":769,\"a\":59,\"owners\":[70,73]},{\"tag\":\"mate\",\"ridge\":770,\"a\":45,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":770,\"a\":58,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":804,\"a\":70,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":804,\"a\":84,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":836,\"a\":71,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":836,\"a\":85,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":808,\"a\":73,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":808,\"a\":87,\"owners\":[73]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[40,43,45,69,83],\"full_literals\":[-49,12,14,16,31,44]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[57,58,59],\"full_literals\":[-50,20,21,22]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[35,60,61,62,63,64,65,66],\"full_literals\":[-51,8,23,24,25,26,27,28,29]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[74,75,76,77,78,79,80],\"full_literals\":[-52,36,37,38,39,40,41,42]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[42,55,67,81],\"full_literals\":[-53,13,19,30,43]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[39,44,54],\"full_literals\":[-54,11,15,18]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[38,52],\"full_literals\":[-55,10,17]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-56,49,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-57,49,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-57,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-58,false,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-59,56,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-60,57,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-60,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-61,52,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-62,54,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-63,54,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-63,false,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-64,53,63],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-65,53,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-64,false,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-65,false,63],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-66,61,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-66,false,64],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-67,false,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-68,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-68,60,67],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-68,false,66],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":72,\"full_literals\":[-34,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":86,\"full_literals\":[-47,70]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[70,71],\"full_literals\":[-71,32,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":70,\"full_literals\":[-32,71]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[73,84],\"full_literals\":[-72,35,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":73,\"full_literals\":[-35,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":84,\"full_literals\":[-45,72]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[85],\"full_literals\":[-73,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":85,\"full_literals\":[-46,73]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[87],\"full_literals\":[-74,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":87,\"full_literals\":[-48,74]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-70,false,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-75,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-69,false,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-72,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-78,71,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-78,false,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-71,-72,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-79,73,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-80,false,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-73,-74,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-81,78,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-77,-80,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-78,false,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-82,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-76,-81,83],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":22,\"owners\":[5,19,28,37,39,42,44,45,62,65,66,70,71,76,79,80,84,85]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[15,45,54,58,59,70,71,73,84,85,87]}]}"
  "143 59 0 113 110 0\n144 66 0 113 112 0\n145 56 0 143 96 0\n146 64 0 144 108 0\n147 62 0 146 105 0\n148 -82 0 140 138 0\n149 -80 0 148 133 136 123 128 84 119 0\n150 -63 -48 0 49 48 47 101 102 90 91 6 0\n151 -10 -74 0 149 134 122 81 123 54 53 52 51 47 1 2 3 6 9 64 66 68 70 67 71 141 0\n152 -30 25 -74 0 113 147 149 134 122 81 123 52 51 47 49 48 151 91 100 90 65 16 14 18 5 150 106 109 111 98 95 20 21 87 0\n153 -43 38 -74 0 144 147 149 134 122 123 54 53 47 49 48 151 91 100 90 69 31 29 34 150 106 107 99 36 37 88 0\n154 -19 -48 0 113 150 106 109 111 97 94 50 12 13 86 0\n155 -30 -74 0 147 123 47 49 48 151 91 100 90 7 4 52 51 152 15 17 56 0\n156 -74 0 146 147 123 47 48 49 53 54 150 103 151 91 100 90 4 7 8 154 155 89 153 30 32 60 0\n157 -48 0 156 124 0\n158 -16 0 157 77 0\n159 -35 0 157 83 0\n160 -46 0 158 145 113 40 41 42 43 44 45 46 82 85 28 92 93 97 111 109 104 106 89 102 11 12 91 86 55 0\n161 -21 0 160 78 0\n162 -33 0 160 81 0\n163 -73 0 160 121 0\n164 -79 0 163 156 132 0\n165 -19 -50 0 161 12 13 86 0\n166 -13 -32 0 158 113 27 23 24 38 85 93 97 111 109 106 101 22 8 10 90 0\n167 -30 -81 0 140 158 164 162 113 135 129 116 27 23 24 38 85 93 97 111 109 106 102 26 25 139 127 114 19 57 58 59 91 72 0\n168 -81 0 140 164 162 159 158 145 113 139 126 125 115 135 129 130 116 118 23 24 27 33 38 39 85 92 93 97 111 109 104 106 102 165 166 167 89 35 61 62 63 73 91 0\n169 -78 0 168 137 0\n170 32 0 157 160 159 162 161 158 80 75 76 74 142 0\n171 45 0 170 79 0\n172 71 0 170 117 0\n173 72 0 171 120 0\n174 0 172 173 169 131 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record028.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record028.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record028.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record028.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record028 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record028.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record028.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record028.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record028.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record028 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record028_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record028_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record028_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record028_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record028_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record028_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record028_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record028 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record028_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record028_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record028_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00026.record028
