module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00010Data
public import GraphInputsRow24Part00010Frames
public import GraphInputsRow24Part00010Leaves
public import GraphInputsRow24Part00010Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00010.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record008
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨66, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 3458764513820540928, (certNat% 3), 622904123460681728, (certNat% 4)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), (certNat% 6), 61572651155456, 85568392920039424, (certNat% 7), 562949953421312]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1152921504539738112, (certNat% 8), (certNat% 9), 3458764513820540928, (certNat% 3)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 11), 162349488910893056, 325684140240273408, 3458764513820540928, (certNat% 3)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), 5764609722057490432, (certNat% 13), 338086631401586688, 164601288724578304, 72057594037927936]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1152921504539738112, (certNat% 8), (certNat% 14), (certNat% 9), (certNat% 15)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), (certNat% 17), 20486100648722432, 3458764513820540928, (certNat% 3), 41957363715932160]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), 603623087556001792, 63771808628736, (certNat% 14), (certNat% 19)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), 593736278999040, 792844640649740288, 3458764513820540928, (certNat% 3)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), (certNat% 22), 593736278999040, 3458764513887649792, (certNat% 3), 268435456]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), (certNat% 24), 63771808628736, (certNat% 19), 34628173824, (certNat% 14)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), (certNat% 27), (certNat% 28), 330187739867643904, 594476284684271616, 146516521470918656]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c14 c11
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c15 c10
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c16 c9
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c17 c8
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c18 c5
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c19 c4
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c20 c1
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c21 c0
  c22
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record008_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00010.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00010.record016
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record016
def vertexColumn : Fields := ⟨10, (certNat% 29)⟩
def kindColumn : Fields := ⟨3, (certNat% 30)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨87, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 3), 18004670676992, (certNat% 32), (certNat% 33), 216172782113783808]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), 2322718313676800, (certNat% 35), (certNat% 36), (certNat% 37)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), (certNat% 32), (certNat% 39), (certNat% 40), 144115188075855872]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 41), (certNat% 42), (certNat% 43), 48722260000768, 9992372947517440, 17729624997888]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 44), (certNat% 45), (certNat% 46), 144115188075855872]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 47), (certNat% 46), (certNat% 48), (certNat% 49), (certNat% 50), 8796244017152]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 51), (certNat% 52), (certNat% 53), 9869364547289088, (certNat% 54), 70370631614464, 9723956953088]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record016_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record016_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record016_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record016_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record016_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record016_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record016_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record016_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record016_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00010.record016

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00010.record003
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "dcf0ab236b8671b26a98d62d94e3386e2785ef06b13678571725a94d52d54d3346d2745de0f43b0dc3c8ea3a4cd38ccb352ccb8ac6b26c5bc1e8761e2749ca719d1715d0f23c3c0e946318960d84e0b81e0e545314950d44d0b41dc0e8350cc388c930cc4b0ac1b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db4da49249b6d3692492492492492492492492491249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record003 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record003 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record003.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record003.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record003.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 71)]))
 (.leaf ([(facetIndex 85)])))
 (.branch 3
 (.leaf ([(facetIndex 88)]))
 (.leaf ([(facetIndex 67), (facetIndex 72)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 70), (facetIndex 73)]))
 (.leaf ([(facetIndex 81), (facetIndex 86)])))
 (.branch 7
 (.leaf ([(facetIndex 84), (facetIndex 87)]))
 (.branch 8
 (.leaf ([(facetIndex 68)]))
 (.leaf ([(facetIndex 82)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "2651608500000004304073z43;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record003 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record003_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00010.record003" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00010.record003" 40

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00010.record003" "{\"ridges\":[[11,545],[11,546],[14,641],[15,770],[40,545],[42,641],[43,769],[47,545],[47,546],[51,545],[51,546],[53,641],[54,545],[54,546],[54,641],[55,545],[55,769],[57,641],[58,770],[59,641],[59,770],[67,676],[72,688],[73,960],[81,676],[84,900],[86,688],[87,960]],\"owners\":[[11,545,[67,68,72],[40,47,51,54,55]],[40,545,[72],[11,47,51,54,55,67,68]],[47,545,[67,68,72],[11,40,51,54,55]],[51,545,[67,68],[11,40,47,54,55,72]],[54,545,[68],[11,40,47,51,55,67,72]],[55,545,[67,72],[11,40,47,51,54,68]],[11,546,[81,82,86],[40,47,51,54,55]],[47,546,[81,82,86],[11,40,51,54,55]],[51,546,[81,82],[11,40,47,54,55,86]],[54,546,[82],[11,40,47,51,55,81,86]],[14,641,[67,70,72,73],[42,53,54,57,59]],[42,641,[72,73],[14,53,54,57,59,67,70]],[53,641,[67,70,73],[14,42,54,57,59,72]],[54,641,[70,73],[14,42,53,57,59,67,72]],[57,641,[67,70,72],[14,42,53,54,59,73]],[59,641,[67,72],[14,42,53,54,57,70,73]],[43,769,[73],[15,55,58,59,68,70]],[55,769,[70,73],[15,43,58,59,68]],[15,770,[82,84,87],[43,55,58,59]],[58,770,[82,84],[15,43,55,59,87]],[59,770,[82],[15,43,55,58,84,87]],[67,676,[81],[]],[81,676,[67],[]],[84,900,[70],[]],[72,688,[86],[]],[86,688,[72],[]],[73,960,[87],[]],[87,960,[73],[]]],\"edges\":[[38,[11,40,47,51,54,55,67,68,72,81,82,86]],[43,[14,42,53,54,57,59,67,70,72,73,81,84,86,87]],[44,[15,43,55,58,59,68,70,73,82,84,87]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00010.record003" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00010.record003\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-17,-16],[-21,-17],[-1,15,16,18],[-4,18],[-7,15,16,18],[-8,15,16],[-10,16],[-11,15,18],[-1,20,21,23],[-7,20,21,23],[-8,20,21],[-10,21],[-2,15,17,18,19],[-5,18,19],[-9,15,17,19],[-10,17,19],[-12,15,17,18],[-14,15,18],[-6,19],[-11,17,19],[-3,21,22,24],[-13,21,22],[-14,21],[-15,20],[-20,15],[-22,17],[-18,23],[-23,18],[-19,24],[-24,19],[-25,15,18],[-15,25],[-18,25],[-26,17,19],[-17,26],[-19,26],[-20,27],[-23,27],[-24,28],[-16,29],[-21,30],[-25,31],[-31,32],[-27,33],[-26,33],[-26,-27,34],[-30,35],[-29,35],[-35,36],[-28,-35,37],[-33,-36,38],[-33,-37,39],[-34,38],[-39,40],[-32,-38,40],[-40],[1,4,7,8,10,11,15,16,18,20,21,23],[2,5,9,10,12,14,15,17,18,19,20,22,23,24],[3,6,11,13,14,16,17,19,21,22,24]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":70,\"b\":68},{\"tag\":\"incompatible\",\"a\":82,\"b\":70},{\"tag\":\"mate\",\"ridge\":545,\"a\":11,\"owners\":[67,68,72]},{\"tag\":\"mate\",\"ridge\":545,\"a\":40,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":545,\"a\":47,\"owners\":[67,68,72]},{\"tag\":\"mate\",\"ridge\":545,\"a\":51,\"owners\":[67,68]},{\"tag\":\"mate\",\"ridge\":545,\"a\":54,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":545,\"a\":55,\"owners\":[67,72]},{\"tag\":\"mate\",\"ridge\":546,\"a\":11,\"owners\":[81,82,86]},{\"tag\":\"mate\",\"ridge\":546,\"a\":47,\"owners\":[81,82,86]},{\"tag\":\"mate\",\"ridge\":546,\"a\":51,\"owners\":[81,82]},{\"tag\":\"mate\",\"ridge\":546,\"a\":54,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":641,\"a\":14,\"owners\":[67,70,72,73]},{\"tag\":\"mate\",\"ridge\":641,\"a\":42,\"owners\":[72,73]},{\"tag\":\"mate\",\"ridge\":641,\"a\":53,\"owners\":[67,70,73]},{\"tag\":\"mate\",\"ridge\":641,\"a\":54,\"owners\":[70,73]},{\"tag\":\"mate\",\"ridge\":641,\"a\":57,\"owners\":[67,70,72]},{\"tag\":\"mate\",\"ridge\":641,\"a\":59,\"owners\":[67,72]},{\"tag\":\"mate\",\"ridge\":769,\"a\":43,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":769,\"a\":55,\"owners\":[70,73]},{\"tag\":\"mate\",\"ridge\":770,\"a\":15,\"owners\":[82,84,87]},{\"tag\":\"mate\",\"ridge\":770,\"a\":58,\"owners\":[82,84]},{\"tag\":\"mate\",\"ridge\":770,\"a\":59,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":676,\"a\":67,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":676,\"a\":81,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":900,\"a\":84,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":688,\"a\":72,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":688,\"a\":86,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":960,\"a\":73,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":960,\"a\":87,\"owners\":[73]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[67,72],\"full_literals\":[-25,15,18]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":67,\"full_literals\":[-15,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":72,\"full_literals\":[-18,25]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[70,73],\"full_literals\":[-26,17,19]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":70,\"full_literals\":[-17,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":73,\"full_literals\":[-19,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":81,\"full_literals\":[-20,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":86,\"full_literals\":[-23,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":87,\"full_literals\":[-24,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":68,\"full_literals\":[-16,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":82,\"full_literals\":[-21,30]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-25,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-31,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-27,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-26,false,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-26,-27,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-30,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-29,false,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-35,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-28,-35,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-33,-36,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-33,-37,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-34,false,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-39,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-32,-38,40],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":38,\"owners\":[11,40,47,51,54,55,67,68,72,81,82,86]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[14,42,53,54,57,59,67,70,72,73,81,84,86,87]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[15,43,55,58,59,68,70,73,82,84,87]}]}"
  "60 -39 0 56 54 0\n61 26 25 0 33 28 32 25 18 35 36 16 26 13 17 30 14 15 58 0\n62 -17 25 0 33 28 4 32 25 8 1 2 7 5 3 6 57 0\n63 25 0 60 32 33 8 25 4 28 61 45 52 62 34 29 39 50 47 48 41 40 12 10 9 11 57 0\n64 31 0 63 42 0\n65 32 0 64 43 0\n66 -38 0 65 56 55 0\n67 -34 0 66 53 0\n68 27 0 63 37 38 24 27 31 0\n69 33 0 68 44 0\n70 -26 0 68 67 46 0\n71 -36 0 69 66 51 0\n72 -17 0 70 35 0\n73 -19 0 70 36 0\n74 -35 0 71 49 0\n75 -11 0 72 73 20 0\n76 -22 0 72 26 0\n77 -6 0 73 19 0\n78 -24 0 73 30 0\n79 -30 0 74 47 0\n80 -29 0 74 48 0\n81 -21 0 79 41 0\n82 -16 0 80 40 0\n83 -3 0 81 76 78 21 0\n84 -13 0 81 76 22 0\n85 -14 0 81 23 0\n86 0 82 81 77 75 85 84 83 72 73 76 78 59 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record003.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record003.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record003.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record003.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record003 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record003.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record003.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record003.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record003.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record003 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record003_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record003 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record003_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record003_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00010.record003
