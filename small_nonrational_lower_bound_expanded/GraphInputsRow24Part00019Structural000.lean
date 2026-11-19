module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00019Data
public import GraphInputsRow24Part00019Frames
public import GraphInputsRow24Part00019Leaves
public import GraphInputsRow24Part00019Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00019.record031
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record031
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨48, by decide⟩, ⟨51, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨63, by decide⟩, ⟨68, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 1152930300699869184, 792633534417207296, (certNat% 3), (certNat% 4)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), 755914244096, (certNat% 6), 9370020499721027584, (certNat% 7), (certNat% 8)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), 9345848836096, (certNat% 10), 2017612633061982208, 9223372311732682752, 144115188075855872]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), (certNat% 12), 9223653786717782016, (certNat% 13), 35433480192, 8796093022208]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 15), (certNat% 16), (certNat% 17), 8796093022208, 9223372311732682752]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [10952764169450946560, (certNat% 18), 146648463403122688, 360287972337123328, (certNat% 16), (certNat% 19)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), 9223372311732682752, (certNat% 12), 216172782650654720, 1441151882906042368, (certNat% 4)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), 17798344474624, 9511602413006487552, (certNat% 22)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), 1441151887201009664, 9223372311732682752, (certNat% 24), 144115189686468608, 72057594037927936]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), 39728447488, 9223372311732682752, (certNat% 27), 1152930300699869184]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), 1152930339354574848, (certNat% 27), 9655717601082343424, (certNat% 29), 3758096384, 2533549676691456]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c13 c10
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c14 c7
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c15 c6
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c16 c5
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c17 c4
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c18 c3
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c19 c2
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record031_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record031_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record031_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record031_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record031_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record031_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record031_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record031_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record031_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00019.record031

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00019.record046
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record046
def vertexColumn : Fields := ⟨10, (certNat% 30)⟩
def kindColumn : Fields := ⟨3, (certNat% 31)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 32), (certNat% 33), (certNat% 34), 28621662060544, (certNat% 35), 35184372088832]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 36), (certNat% 37), (certNat% 38), 126382264543084544, (certNat% 39), 144115188075855872]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), 11579231830016, (certNat% 37), (certNat% 41), 10376293541461622784, 2305843009213693952]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), (certNat% 33), 56576470318841856, (certNat% 43), (certNat% 44), 1152921504606846976]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 45), 19791746170880, (certNat% 46), 90071992547409920, (certNat% 47), 30366760960]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), 30870077440, 28587302322176, 18014398509481984, 13836184504944820224, (certNat% 49)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 50), 30870077440, 18016597532737536, 108086391056891904, (certNat% 51), (certNat% 52)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 53), 30333206528, (certNat% 37), (certNat% 47), 2783138807808, 9223372036854775808]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 54), 30903631872, (certNat% 55), (certNat% 56), 56576470318841856, 11579231830016, 17592186044416]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c12 c3
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c13 c2
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c14 c1
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record046_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record046_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record046_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record046_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record046_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record046_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record046_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record046_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record046_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00019.record046

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00019.record001
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "791ccc738a728ba718e61db0e6394e338ae8783e78789727192e5c569565397151d70d6354d334ad8751d0f783d0dc38ccb31cf0ba2d8b52ccb2ac9b0ef0761d4731ca785c5783d0f23c4f0bce2868660d81e704e1c258986545194354341d30ca318e130ce0b22c1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6da4db6d249269a4d249b4936924926924da492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record001 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record001 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record001.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record001.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record001.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 38), (facetIndex 62)]))
 (.leaf ([(facetIndex 56), (facetIndex 67)])))
 (.branch 3
 (.leaf ([(facetIndex 74), (facetIndex 82)]))
 (.leaf ([(facetIndex 78), (facetIndex 85)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 37), (facetIndex 57), (facetIndex 65)]))
 (.leaf ([(facetIndex 75), (facetIndex 77), (facetIndex 87)])))
 (.branch 7
 (.leaf ([(facetIndex 43), (facetIndex 51), (facetIndex 52), (facetIndex 81)]))
 (.branch 8
 (.leaf ([(facetIndex 76), (facetIndex 84)]))
 (.leaf ([(facetIndex 83), (facetIndex 86)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "583782600357520000001040000000410006600000006000004z25;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record001 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record001_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00019.record001" "{\"atoms\":[{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00019.record001" 57

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00019.record001" "{\"ridges\":[[16,321],[16,324],[18,392],[19,769],[19,776],[21,448],[36,324],[44,138],[44,392],[46,776],[50,448],[51,834],[52,898],[58,268],[58,324],[59,392],[60,769],[60,776],[64,321],[64,324],[65,420],[66,448],[68,769],[68,776],[69,392],[69,448],[70,392],[70,776],[71,448],[81,390],[83,330],[84,898],[86,204],[87,420]],\"owners\":[[44,138,[74,75,82],[5,29,40,41,42,45,77,83,84]],[58,268,[77,78,85],[13,30,54,59,60,76,86]],[16,321,[21,43,50,51,69,71],[36,58,64]],[64,321,[21,43,50,51,69],[16,36,58,71]],[16,324,[76,81,86,87],[36,58,64,66]],[36,324,[86,87],[16,58,64,66,76,81]],[58,324,[81,87],[16,36,64,66,76,86]],[64,324,[76,81,86],[16,36,58,66,87]],[18,392,[77,83,84,86],[44,59,69,70]],[44,392,[86],[18,59,69,70,77,83,84]],[59,392,[83,84],[18,44,69,70,77,86]],[69,392,[77,84],[18,44,59,70,83,86]],[70,392,[77,83,86],[18,44,59,69,84]],[19,769,[38,51,52,62],[46,60,68,70]],[60,769,[51,52],[19,38,46,62,68,70]],[68,769,[38,51,52],[19,46,60,62,70]],[19,776,[78,84,85],[46,60,68,70]],[46,776,[85],[19,60,68,70,78,84]],[60,776,[84],[19,46,68,70,78,85]],[68,776,[78,84],[19,46,60,70,85]],[70,776,[78,85],[19,46,60,68,84]],[21,448,[81,83,86,87],[50,66,69,71]],[50,448,[86,87],[21,66,69,71,81,83]],[66,448,[83],[21,50,69,71,81,86,87]],[69,448,[81,87],[21,50,66,71,83,86]],[71,448,[81,83,86],[21,50,66,69,87]],[81,390,[37,77],[]],[83,330,[43,76],[]],[51,834,[],[]],[52,898,[84],[]],[84,898,[52],[]],[86,204,[57,75],[]],[65,420,[87],[]],[87,420,[65],[]]],\"edges\":[[40,[16,21,36,43,50,51,58,64,66,69,71,76,81,83,86,87]],[42,[18,21,37,44,50,52,59,65,66,69,70,71,77,81,83,84,86,87]],[44,[19,38,46,51,52,60,62,68,70,78,84,85]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00019.record001" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00019.record001\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-33,-13],[-34,-8],[-34,-28],[-34,-33],[-9,26,27,32],[-15,29,30,35],[-1,4,8,11,12,23,25],[-19,4,8,11,12,23],[-1,28,31,36,37],[-5,36,37],[-15,31,37],[-19,28,31,36],[-2,29,33,34,36],[-9,36],[-16,33,34],[-23,29,34],[-24,29,33,36],[-3,7,12,13,18],[-17,12,13],[-22,7,12,13],[-3,30,34,35],[-10,35],[-17,34],[-22,30,34],[-24,30,35],[-4,31,33,36,37],[-11,36,37],[-21,33],[-23,31,37],[-25,31,33,36],[-31,6,29],[-33,8,28],[-12],[-13,34],[-34,13],[-36,14,27],[-20,37],[-37,20],[-7,38],[-18,38],[-26,39],[-32,39],[-30,40],[-35,40],[-6,41],[-14,41],[-20,41],[-27,42],[-29,42],[-37,42],[-8,43],[-13,43],[-31,43],[-28,44],[-34,44],[-33,45],[-36,45],[-38,46],[-40,47],[-39,47],[-47,48],[-46,48],[-42,49],[-41,49],[-41,-42,50],[-45,51],[-44,51],[-44,-45,52],[-51,53],[-52,54],[-43,53],[-43,-51,54],[-54,55],[-49,-53,55],[-49,-54,56],[-50,55],[-56,57],[-48,-55,57],[-57],[1,4,5,8,11,12,15,19,21,23,25,28,31,33,36,37],[2,4,6,9,11,13,16,20,21,23,24,25,29,31,33,34,36,37],[3,7,10,12,13,17,18,22,24,30,34,35]],\"atoms\":[{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":83,\"b\":52},{\"tag\":\"incompatible\",\"a\":84,\"b\":43},{\"tag\":\"incompatible\",\"a\":84,\"b\":76},{\"tag\":\"incompatible\",\"a\":84,\"b\":83},{\"tag\":\"mate\",\"ridge\":138,\"a\":44,\"owners\":[74,75,82]},{\"tag\":\"mate\",\"ridge\":268,\"a\":58,\"owners\":[77,78,85]},{\"tag\":\"mate\",\"ridge\":321,\"a\":16,\"owners\":[21,43,50,51,69,71]},{\"tag\":\"mate\",\"ridge\":321,\"a\":64,\"owners\":[21,43,50,51,69]},{\"tag\":\"mate\",\"ridge\":324,\"a\":16,\"owners\":[76,81,86,87]},{\"tag\":\"mate\",\"ridge\":324,\"a\":36,\"owners\":[86,87]},{\"tag\":\"mate\",\"ridge\":324,\"a\":58,\"owners\":[81,87]},{\"tag\":\"mate\",\"ridge\":324,\"a\":64,\"owners\":[76,81,86]},{\"tag\":\"mate\",\"ridge\":392,\"a\":18,\"owners\":[77,83,84,86]},{\"tag\":\"mate\",\"ridge\":392,\"a\":44,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":392,\"a\":59,\"owners\":[83,84]},{\"tag\":\"mate\",\"ridge\":392,\"a\":69,\"owners\":[77,84]},{\"tag\":\"mate\",\"ridge\":392,\"a\":70,\"owners\":[77,83,86]},{\"tag\":\"mate\",\"ridge\":769,\"a\":19,\"owners\":[38,51,52,62]},{\"tag\":\"mate\",\"ridge\":769,\"a\":60,\"owners\":[51,52]},{\"tag\":\"mate\",\"ridge\":769,\"a\":68,\"owners\":[38,51,52]},{\"tag\":\"mate\",\"ridge\":776,\"a\":19,\"owners\":[78,84,85]},{\"tag\":\"mate\",\"ridge\":776,\"a\":46,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":776,\"a\":60,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":776,\"a\":68,\"owners\":[78,84]},{\"tag\":\"mate\",\"ridge\":776,\"a\":70,\"owners\":[78,85]},{\"tag\":\"mate\",\"ridge\":448,\"a\":21,\"owners\":[81,83,86,87]},{\"tag\":\"mate\",\"ridge\":448,\"a\":50,\"owners\":[86,87]},{\"tag\":\"mate\",\"ridge\":448,\"a\":66,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":448,\"a\":69,\"owners\":[81,87]},{\"tag\":\"mate\",\"ridge\":448,\"a\":71,\"owners\":[81,83,86]},{\"tag\":\"mate\",\"ridge\":390,\"a\":81,\"owners\":[37,77]},{\"tag\":\"mate\",\"ridge\":330,\"a\":83,\"owners\":[43,76]},{\"tag\":\"mate\",\"ridge\":834,\"a\":51,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":898,\"a\":52,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":898,\"a\":84,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":204,\"a\":86,\"owners\":[57,75]},{\"tag\":\"mate\",\"ridge\":420,\"a\":65,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":420,\"a\":87,\"owners\":[65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":38,\"full_literals\":[-7,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":62,\"full_literals\":[-18,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":74,\"full_literals\":[-26,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":82,\"full_literals\":[-32,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":78,\"full_literals\":[-30,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":85,\"full_literals\":[-35,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":37,\"full_literals\":[-6,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":57,\"full_literals\":[-14,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":65,\"full_literals\":[-20,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":75,\"full_literals\":[-27,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":77,\"full_literals\":[-29,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":87,\"full_literals\":[-37,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":43,\"full_literals\":[-8,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":52,\"full_literals\":[-13,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":81,\"full_literals\":[-31,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":76,\"full_literals\":[-28,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":84,\"full_literals\":[-34,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":83,\"full_literals\":[-33,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":86,\"full_literals\":[-36,45]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-40,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-39,false,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-47,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-42,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-41,false,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-41,-42,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-45,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-44,-45,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-51,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-52,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-43,false,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-43,-51,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-54,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-49,-53,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-49,-54,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-50,false,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-56,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-48,-55,57],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":40,\"owners\":[16,21,36,43,50,51,58,64,66,69,71,76,81,83,86,87]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[18,21,37,44,50,52,59,65,66,69,70,71,77,81,83,84,86,87]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[19,38,46,51,52,60,62,68,70,78,84,85]}]}"
  "83 -56 0 79 77 0\n84 1 4 5 8 11 15 19 21 23 25 28 31 33 36 37 0 33 80 0\n85 3 7 10 13 17 18 22 24 30 34 35 0 33 82 0\n86 -33 48 0 33 61 59 43 44 25 22 62 58 40 39 1 4 19 20 18 85 0\n87 34 49 48 0 64 46 63 48 36 45 49 31 86 30 50 26 29 27 61 60 42 41 5 47 28 59 43 44 25 34 15 13 81 0\n88 49 48 0 33 86 28 61 59 44 43 63 64 48 49 50 45 46 36 31 6 10 27 29 26 30 87 2 3 7 8 84 0\n89 -34 54 0 35 55 52 67 72 0\n90 48 0 83 61 62 59 58 43 44 39 40 22 25 88 75 89 23 34 24 21 85 0\n91 -55 0 90 79 78 0\n92 -54 0 91 73 0\n93 -50 0 91 76 0\n94 -52 0 92 70 0\n95 -34 0 92 89 0\n96 -13 0 95 34 0\n97 37 53 0 69 66 57 71 53 67 54 12 56 28 30 51 11 10 27 9 29 26 84 0\n98 -37 0 93 38 50 47 65 0\n99 -20 0 98 37 0\n100 53 0 98 97 0\n101 -49 0 100 91 74 0\n102 -42 0 101 63 0\n103 -41 0 101 64 0\n104 -27 0 102 48 0\n105 -29 0 102 49 0\n106 -6 0 103 45 0\n107 -14 0 103 46 0\n108 -36 0 104 107 36 0\n109 -31 0 105 106 31 0\n110 -23 0 105 95 16 0\n111 -9 0 108 14 0\n112 -11 0 108 98 27 0\n113 33 0 108 95 109 105 99 110 112 96 111 106 98 28 15 13 17 30 26 81 0\n114 45 0 113 56 0\n115 51 0 114 66 0\n116 -44 0 114 94 68 0\n117 -43 0 115 92 72 0\n118 -28 0 116 54 0\n119 -8 0 117 51 0\n120 0 118 119 113 32 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record001.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record001.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record001.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record001.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record001 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record001.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record001.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record001.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record001.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record001 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record001_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record001 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record001_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record001_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00019.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00019.record033
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "f2e29aa2eb4639876c3a2e2ba1e0f8f1e25c96a559364b9d14e51d70d534cd8b4ad8745de0f4368ce354cd32cc73c2e8b62e2b4acab86d1b26c3bc1e4751cc789ca719e1783d0f23c2f07c3c708560d9c1c25892a439154358342d0770360d4330ca314c3381c4709c17"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db69b6d349369b49b4924924924d369b692492493691249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record033 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record033 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record033.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record033.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record033.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 25), (facetIndex 56), (facetIndex 57), (facetIndex 59)]))
 (.leaf ([(facetIndex 45), (facetIndex 69), (facetIndex 70), (facetIndex 71)])))
 (.branch 3
 (.leaf ([(facetIndex 63), (facetIndex 73), (facetIndex 78)]))
 (.leaf ([(facetIndex 26), (facetIndex 38), (facetIndex 42), (facetIndex 58), (facetIndex 66)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 35), (facetIndex 51), (facetIndex 54), (facetIndex 55)]))
 (.leaf ([(facetIndex 29), (facetIndex 37), (facetIndex 47), (facetIndex 62)])))
 (.branch 7
 (.leaf ([(facetIndex 49), (facetIndex 50), (facetIndex 52), (facetIndex 53)]))
 (.branch 8
 (.leaf ([(facetIndex 30), (facetIndex 31), (facetIndex 32), (facetIndex 33), (facetIndex 34), (facetIndex 36)]))
 (.leaf ([(facetIndex 48)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "20000201110030025000300446646685010030003574777775003z1a;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 28), (facetIndex 61), (facetIndex 65)]))
 (.branch 2
 (.leaf ([(facetIndex 77), (facetIndex 80)]))
 (.leaf ([(facetIndex 60), (facetIndex 67), (facetIndex 68)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 64), (facetIndex 72)]))
 (.leaf ([(facetIndex 79), (facetIndex 84)])))
 (.branch 6
 (.leaf ([(facetIndex 27), (facetIndex 39), (facetIndex 40), (facetIndex 41), (facetIndex 43), (facetIndex 44), (facetIndex 46)]))
 (.leaf ([(facetIndex 74), (facetIndex 75), (facetIndex 76), (facetIndex 81), (facetIndex 82), (facetIndex 83)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "4db180ed83002403002000000000145a2da00000000az14;"⟩
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

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record033 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record033_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00019.record033" "{\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":4}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00019.record033" 71

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00019.record033" "{\"ridges\":[[1,37],[13,524],[14,21],[15,21],[19,776],[29,524],[32,37],[33,37],[42,168],[45,392],[47,776],[53,162],[57,21],[57,524],[59,524],[62,524],[69,392],[71,776],[75,142],[76,554],[77,270],[78,38],[78,84],[81,154],[83,650]],\"owners\":[[1,37,[12,14,58,59,63,64],[31,32,33]],[32,37,[12,14,59,63],[1,31,33,58,64]],[33,37,[12,14,58,63,64],[1,31,32,59]],[78,38,[1,26,32,33,75,76],[21,31,73,79]],[53,162,[75,79,81,84],[6,32,42,49,52,82]],[13,524,[74,76,77],[29,57,59,62]],[29,524,[],[13,57,59,62,74,76,77]],[57,524,[76,77],[13,29,59,62,74]],[59,524,[74,77],[13,29,57,62,76]],[62,524,[74,76],[13,29,57,59,77]],[78,84,[15,56],[22,63]],[42,168,[],[17,58,66,69,75,81,82]],[45,392,[],[18,69,70,71,82,83]],[69,392,[83],[18,45,70,71,82]],[19,776,[77,83],[47,62,71]],[47,776,[],[19,62,71,77,83]],[71,776,[77],[19,47,62,83]],[75,142,[27],[]],[77,270,[28],[]],[81,154,[39],[]],[76,554,[44],[]],[83,650,[46],[]]],\"edges\":[[29,[13,19,29,41,44,46,47,57,59,62,71,74,76,77,83]]],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00019.record033" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00019.record033\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-20,-15],[-24,-14],[-24,-17],[-25,-24],[-26,-24],[-27,-24],[-28,-24],[-30,-29],[-33,-2],[-33,-8],[-33,-9],[-34,-33],[-35,-10],[-35,-34],[-36,-33],[-37,-7],[-37,-8],[-37,-16],[-37,-24],[-37,-32],[-37,-33],[-39,-35],[-40,-22],[-41,-31],[-41,-32],[-42,-10],[-43,-18],[-43,-20],[-43,-22],[-44,-43],[-45,-43],[-46,-43],[-47,-43],[-48,-7],[-48,-24],[-48,-38],[-48,-44],[-49,-37],[-49,-48],[-51,-43],[-52,-37],[-52,-48],[-4,-5,-33],[-1,2,4,34,35,37,38],[-12,2,4,35,37],[-13,2,4,34,37,38],[-48,1,8,12,13,45,46],[-29,45,49,50,52],[-3,44,46,47],[-11],[-33,46,47],[-35,44,47],[-36,44,46],[-48,5,32],[-19],[-21],[-40,51],[-6,47,51],[-23],[-42,47],[-45,9],[-47,10],[-50,17],[-46,20],[-51,22],[-53,7,32,33,35],[-54,21,40,41,42],[-55,37,43,48],[-56,8,16,19,34,39],[-57,14,27,30,31],[-58,11,15,23,36],[-59,25,26,28,29],[-60,24],[-61,53],[-61,54],[-62,55],[-62,56],[-63,61,62],[-64,61],[-64,62],[-65,57],[-65,58],[-66,60],[-67,59],[-67,66],[-68,65,67],[-69,65],[-69,67],[-70,63],[-70,64,69],[-70,68],[70],[-71,49,52],[-49,71],[-52,71],[3,6,11,18,20,22,23,33,35,36,42,44,46,47,51]],\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":44,\"b\":37},{\"tag\":\"incompatible\",\"a\":48,\"b\":35},{\"tag\":\"incompatible\",\"a\":48,\"b\":39},{\"tag\":\"incompatible\",\"a\":49,\"b\":48},{\"tag\":\"incompatible\",\"a\":50,\"b\":48},{\"tag\":\"incompatible\",\"a\":51,\"b\":48},{\"tag\":\"incompatible\",\"a\":52,\"b\":48},{\"tag\":\"incompatible\",\"a\":54,\"b\":53},{\"tag\":\"incompatible\",\"a\":57,\"b\":12},{\"tag\":\"incompatible\",\"a\":57,\"b\":26},{\"tag\":\"incompatible\",\"a\":57,\"b\":27},{\"tag\":\"incompatible\",\"a\":58,\"b\":57},{\"tag\":\"incompatible\",\"a\":59,\"b\":28},{\"tag\":\"incompatible\",\"a\":59,\"b\":58},{\"tag\":\"incompatible\",\"a\":62,\"b\":57},{\"tag\":\"incompatible\",\"a\":63,\"b\":25},{\"tag\":\"incompatible\",\"a\":63,\"b\":26},{\"tag\":\"incompatible\",\"a\":63,\"b\":38},{\"tag\":\"incompatible\",\"a\":63,\"b\":48},{\"tag\":\"incompatible\",\"a\":63,\"b\":56},{\"tag\":\"incompatible\",\"a\":63,\"b\":57},{\"tag\":\"incompatible\",\"a\":66,\"b\":59},{\"tag\":\"incompatible\",\"a\":69,\"b\":46},{\"tag\":\"incompatible\",\"a\":70,\"b\":55},{\"tag\":\"incompatible\",\"a\":70,\"b\":56},{\"tag\":\"incompatible\",\"a\":71,\"b\":28},{\"tag\":\"incompatible\",\"a\":73,\"b\":41},{\"tag\":\"incompatible\",\"a\":73,\"b\":44},{\"tag\":\"incompatible\",\"a\":73,\"b\":46},{\"tag\":\"incompatible\",\"a\":74,\"b\":73},{\"tag\":\"incompatible\",\"a\":75,\"b\":73},{\"tag\":\"incompatible\",\"a\":76,\"b\":73},{\"tag\":\"incompatible\",\"a\":77,\"b\":73},{\"tag\":\"incompatible\",\"a\":78,\"b\":25},{\"tag\":\"incompatible\",\"a\":78,\"b\":48},{\"tag\":\"incompatible\",\"a\":78,\"b\":64},{\"tag\":\"incompatible\",\"a\":78,\"b\":74},{\"tag\":\"incompatible\",\"a\":79,\"b\":63},{\"tag\":\"incompatible\",\"a\":79,\"b\":78},{\"tag\":\"incompatible\",\"a\":83,\"b\":73},{\"tag\":\"incompatible\",\"a\":84,\"b\":63},{\"tag\":\"incompatible\",\"a\":84,\"b\":78},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[14,15,57]},{\"tag\":\"mate\",\"ridge\":37,\"a\":1,\"owners\":[12,14,58,59,63,64]},{\"tag\":\"mate\",\"ridge\":37,\"a\":32,\"owners\":[12,14,59,63]},{\"tag\":\"mate\",\"ridge\":37,\"a\":33,\"owners\":[12,14,58,63,64]},{\"tag\":\"mate\",\"ridge\":38,\"a\":78,\"owners\":[1,26,32,33,75,76]},{\"tag\":\"mate\",\"ridge\":162,\"a\":53,\"owners\":[75,79,81,84]},{\"tag\":\"mate\",\"ridge\":524,\"a\":13,\"owners\":[74,76,77]},{\"tag\":\"mate\",\"ridge\":524,\"a\":29,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":524,\"a\":57,\"owners\":[76,77]},{\"tag\":\"mate\",\"ridge\":524,\"a\":59,\"owners\":[74,77]},{\"tag\":\"mate\",\"ridge\":524,\"a\":62,\"owners\":[74,76]},{\"tag\":\"mate\",\"ridge\":84,\"a\":78,\"owners\":[15,56]},{\"tag\":\"mate\",\"ridge\":168,\"a\":42,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":392,\"a\":45,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":392,\"a\":69,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":776,\"a\":19,\"owners\":[77,83]},{\"tag\":\"mate\",\"ridge\":776,\"a\":47,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":776,\"a\":71,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":142,\"a\":75,\"owners\":[27]},{\"tag\":\"mate\",\"ridge\":270,\"a\":77,\"owners\":[28]},{\"tag\":\"mate\",\"ridge\":154,\"a\":81,\"owners\":[39]},{\"tag\":\"mate\",\"ridge\":554,\"a\":76,\"owners\":[44]},{\"tag\":\"mate\",\"ridge\":650,\"a\":83,\"owners\":[46]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[25,56,57,59],\"full_literals\":[-53,7,32,33,35]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[45,69,70,71],\"full_literals\":[-54,21,40,41,42]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[63,73,78],\"full_literals\":[-55,37,43,48]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[26,38,42,58,66],\"full_literals\":[-56,8,16,19,34,39]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[35,51,54,55],\"full_literals\":[-57,14,27,30,31]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[29,37,47,62],\"full_literals\":[-58,11,15,23,36]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[49,50,52,53],\"full_literals\":[-59,25,26,28,29]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[48],\"full_literals\":[-60,24]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-61,53,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-61,false,54],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-62,55,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-62,false,56],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-63,61,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-64,61,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-64,false,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-65,57,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-65,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-66,false,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-67,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-67,false,66],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-68,65,67],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-69,65,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-69,false,67],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-70,63,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-70,64,69],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-70,false,68],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[79,84],\"full_literals\":[-71,49,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":79,\"full_literals\":[-49,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":84,\"full_literals\":[-52,71]},{\"tag\":\"edge\",\"edge\":29,\"owners\":[13,19,29,41,44,46,47,57,59,62,71,74,76,77,83]}]}"
  "97 -54 40 41 42 0 56 67 0\n98 -56 8 16 34 39 0 55 69 0\n99 -58 15 36 0 50 59 71 0\n100 63 0 92 89 0\n101 68 0 92 91 0\n102 3 6 18 20 22 33 35 36 42 44 46 47 51 0 50 59 96 0\n103 -69 31 0 87 88 81 84 85 83 73 2 4 5 6 7 72 70 8 0\n104 -67 71 -55 0 95 94 84 85 83 73 3 4 5 7 19 35 63 72 68 48 31 0\n105 -37 -64 0 80 77 79 74 16 17 18 20 21 66 14 22 98 0\n106 -40 0 23 57 65 0\n107 -43 0 27 28 29 30 32 33 40 52 51 53 49 60 58 102 0\n108 -37 -55 0 92 38 41 105 93 90 104 88 0\n109 -42 0 26 60 62 0\n110 35 -55 0 101 109 106 92 107 108 68 42 39 93 104 88 90 79 75 97 25 54 74 86 82 36 34 66 9 10 11 12 15 43 44 45 61 46 99 47 1 64 0\n111 37 -55 0 107 68 37 110 13 52 62 0\n112 -55 0 108 111 0\n113 -62 0 112 76 0\n114 -64 0 113 80 0\n115 61 0 113 100 78 0\n116 69 0 114 92 90 0\n117 54 0 115 75 0\n118 31 0 116 103 0\n119 41 0 117 106 109 97 0\n120 0 119 118 24 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record033.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record033.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record033.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record033.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record033 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record033.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record033.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record033.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record033.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record033 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record033_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record033_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record033_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record033_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record033_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record033_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record033_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record033 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record033_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record033_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record033_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00019.record033
