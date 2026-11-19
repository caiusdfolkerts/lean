module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow23Part00030Data
public import GraphInputsRow23Part00030Frames
public import GraphInputsRow23Part00030Leaves
public import GraphInputsRow23Part00030Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00030.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record008
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), 985162418487296, (certNat% 5), (certNat% 6), 4449556431842050048, (certNat% 7)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), (certNat% 9), (certNat% 10), 1055531162664960, (certNat% 11), 4557642822898941952, (certNat% 12), (certNat% 13)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 15), (certNat% 16), (certNat% 17), (certNat% 18), (certNat% 19), 809240558043136, (certNat% 20)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), (certNat% 22), (certNat% 23), (certNat% 24), (certNat% 25), 738871813865472, 4449556431842050048, (certNat% 26)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), (certNat% 28), (certNat% 29), (certNat% 30), (certNat% 31), 4431542033332568064, (certNat% 32)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), (certNat% 34), (certNat% 35), (certNat% 36), (certNat% 37), (certNat% 38), 4449556431842050048, (certNat% 39)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), (certNat% 41), 985162418487296, (certNat% 42), (certNat% 43), (certNat% 44), 4575657221408423936, (certNat% 45)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), (certNat% 47), 4608309418218487808, (certNat% 48), (certNat% 49), (certNat% 50), 703687441776640, (certNat% 39), (certNat% 51)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨97, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨93, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record008_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00030.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00030.record002
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "a6a5a59a5635876638ae1ba1e4785e0fa9996565954d51d58d2b46d8751d1743d98d63a4cd31cf0ba2d8b92e2b2ac6b46c5b0ed8791d4731ca785d170de0f13d2c272524aa1a26926198961590e2382e07a514a61926525194951550d2342d0764348c6384c9314e0b42c8b0ac1b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "12492492492492492492492492492492492492449249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record002 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record002 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record002.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record002.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record002.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 45), (facetIndex 48), (facetIndex 50), (facetIndex 66), (facetIndex 78), (facetIndex 91)]))
 (.branch 2
 (.leaf ([(facetIndex 43), (facetIndex 44), (facetIndex 53), (facetIndex 54), (facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 58), (facetIndex 59), (facetIndex 60), (facetIndex 61), (facetIndex 62)]))
 (.leaf ([(facetIndex 49), (facetIndex 51), (facetIndex 63), (facetIndex 64), (facetIndex 67)]))))
 (.branch 4
 (.leaf ([(facetIndex 52), (facetIndex 74), (facetIndex 87)]))
 (.branch 5
 (.leaf ([(facetIndex 65), (facetIndex 80), (facetIndex 93)]))
 (.leaf ([(facetIndex 46), (facetIndex 69), (facetIndex 70), (facetIndex 76)])))))
 (.branch 9
 (.branch 7
 (.leaf ([(facetIndex 81), (facetIndex 82), (facetIndex 83), (facetIndex 84), (facetIndex 86)]))
 (.branch 8
 (.leaf ([(facetIndex 88), (facetIndex 89), (facetIndex 90)]))
 (.leaf ([(facetIndex 47), (facetIndex 71), (facetIndex 77), (facetIndex 79)]))))
 (.branch 10
 (.leaf ([(facetIndex 72), (facetIndex 85), (facetIndex 92)]))
 (.branch 11
 (.leaf ([(facetIndex 68), (facetIndex 73)]))
 (.leaf ([(facetIndex 75)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "490777369666648085b3a9855a2042211111111113202085011z2b;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 12
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0, 1, 2]
def grouped2_0001 : List Nat := [0, 1, 2, 3, 4, 5]
def grouped2_0003 : List Nat := [3]
def grouped2_0004 : List Nat := [3, 4, 5]
def grouped2_0005 : List Nat := [4]
def grouped2_0006 : List Nat := [4, 5]
def grouped2_0007 : List Nat := [5]
def grouped2_0008 : List Nat := [6]
def grouped2_0009 : List Nat := [6, 7, 8]
def grouped2_0010 : List Nat := [6, 7, 8, 9, 10, 11]
def grouped2_0011 : List Nat := [7]
def grouped2_0012 : List Nat := [7, 8]
def grouped2_0013 : List Nat := [8]
def grouped2_0014 : List Nat := [9]
def grouped2_0015 : List Nat := [9, 10, 11]
def grouped2_0016 : List Nat := [10]
def grouped2_0017 : List Nat := [10, 11]
def grouped2_0018 : List Nat := [11]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record002 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record002_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00030.record002" "{\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group\",\"kind\":2,\"index\":10},{\"tag\":\"group\",\"kind\":2,\"index\":11},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":6,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0017\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0017\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":6,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":10,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00030.record002" 97

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00030.record002" "{\"ridges\":[[1,22],[4,134],[5,262],[6,26],[8,138],[11,82],[12,19],[14,98],[21,84],[22,21],[23,37],[23,100],[24,37],[24,261],[32,14],[33,22],[34,22],[35,38],[36,38],[37,26],[42,44],[46,21],[46,22],[46,261],[46,262],[47,21],[47,22],[48,134],[50,262],[52,134],[52,261],[52,262],[53,26],[56,98],[57,138],[60,138],[61,138],[63,98],[64,82],[66,98],[67,98],[68,21],[68,44],[70,21],[71,21],[72,100],[73,37],[73,133],[75,21],[75,37],[75,84],[75,100],[77,21],[77,84],[78,100],[81,22],[83,22],[83,26],[84,14],[84,22],[85,14],[86,38],[86,44],[86,134],[88,22],[88,38],[88,82],[88,100],[90,22],[92,26],[92,82]],\"owners\":[[12,19,[1,6,11,13,45,46,53,55,63],[]],[73,133,[4,22,49,52,76],[19,48,74]],[4,134,[31,34,86,87,89],[48,49,52]],[48,134,[31,34,87,89],[4,49,52,86]],[52,134,[31,34,86,89],[4,48,49,87]],[86,134,[4,34,49,52,89],[31,48,87]],[24,261,[5,20,46,50,52,70,74],[78]],[46,261,[20,24,74,78],[5,50,52,70]],[52,261,[20,24,70,78],[5,46,50,74]],[5,262,[32,36,83,87,91],[46,50,52]],[46,262,[32,36,87,91],[5,50,52,83]],[50,262,[32,36,83,87],[5,46,52,91]],[52,262,[32,36,83,91],[5,46,50,87]],[8,138,[31,37,86,87,93],[57,60,61]],[57,138,[31,37,87,93],[8,60,61,86]],[60,138,[31,37,86,93],[8,57,61,87]],[61,138,[31,37,86,87],[8,57,60,93]],[14,98,[35,85,88,91],[56,63,66,67]],[56,98,[35,88,91],[14,63,66,67,85]],[63,98,[35,85,91],[14,56,66,67,88]],[66,98,[35,85,88],[14,56,63,67,91]],[67,98,[35,85,88,91],[14,56,63,66]],[21,84,[33,82,88,89,90],[69,75,76,77]],[75,84,[33,82,89,90],[21,69,76,77,88]],[77,84,[33,82,88,89],[21,69,75,76,90]],[23,100,[35,85,88,91],[72,75,78]],[72,100,[35,88,91],[23,75,78,85]],[75,100,[35,85,91],[23,72,78,88]],[78,100,[35,85,88],[23,72,75,91]],[88,100,[23,72,78],[35,75,85,91]]],\"edges\":[[14,[4,8,12,31,34,37,48,49,52,57,60,61,64,65,86,87,89,93]],[20,[3,21,23,33,35,43,49,50,51,69,72,75,76,77,78,82,85,88,89,90,91]],[22,[5,20,24,32,36,42,46,50,52,70,74,78,83,87,91]],[35,[14,23,35,56,63,66,67,72,75,78,85,88,91]]],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00030.record002" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00030.record002\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-26,-2],[-26,-3],[-27,-26],[-29,-26],[-30,-26],[-31,-26],[-32,-26],[-32,-27],[-44,-11],[-45,-26],[-45,-27],[-45,-44],[-46,-44],[-47,-44],[-47,-46],[-48,-44],[-48,-45],[-49,-11],[-49,-46],[-49,-47],[-49,-48],[-50,-44],[-50,-45],[-50,-46],[-50,-47],[-50,-48],[-50,-49],[-51,-44],[-51,-45],[-51,-48],[-52,-26],[-52,-27],[-52,-44],[-52,-47],[-52,-51],[-53,-45],[-53,-51],[-53,-52],[-54,-44],[-54,-49],[-54,-51],[-55,-41],[-55,-48],[-56,-44],[-56,-47],[-56,-55],[-57,-16],[-57,-44],[-57,-51],[-58,-27],[-58,-48],[-58,-55],[-59,-16],[-59,-26],[-59,-34],[-59,-46],[-60,-27],[-60,-47],[-60,-53],[-60,-58],[-60,-59],[-61,-21],[-61,-55],[-61,-57],[-61,-58],[-61,-59],[-62,-17],[-62,-24],[-62,-49],[-62,-58],[-62,-59],[-62,-61],[-63,-57],[-63,-58],[-63,-59],[-63,-60],[-63,-61],[-63,-62],[-64,-25],[-64,-29],[-64,-39],[-64,-44],[-64,-51],[-64,-57],[-64,-58],[-64,-61],[-65,-26],[-65,-57],[-65,-58],[-65,-59],[-65,-60],[-66,-27],[-66,-47],[-66,-53],[-66,-58],[-66,-60],[-67,-61],[-67,-62],[-68,-9],[-68,-27],[-68,-41],[-68,-45],[-68,-55],[-68,-58],[-68,-60],[-68,-66],[-69,-57],[-69,-59],[-69,-60],[-69,-68],[-17,-60,-61],[-8,1,5,7,9,25,26,33,34,39],[-13,-26,-53],[-26,-44,-53],[-26,-47,-51],[-27,-46,-51],[-1,-59,-64],[-18,-19,-26],[-18,-19,-57],[-18,-26,-60],[-19,-26,-66],[-19,-59,-64],[-27,-59,-64],[-14,-15,-49],[-15,-49,-51],[-20,-21,-62],[-21,-62,-64],[-49,3,13,29,32,52],[-3,16,19,62,63,65],[-28,16,19,63,65],[-32,16,19,62,65],[-62,3,19,29,32,65],[-15,4,11,26,30,32,46,50],[-26,11,15,50,54],[-32,11,15,46,54],[-4,17,21,59,63,67],[-26,17,21,63,67],[-30,17,21,59,63],[-32,17,21,59,67],[-5,-59,-68],[-22,-59,-68],[-33,-59,-68],[-6,16,22,62,63,69],[-36,16,22,63,69],[-37,16,22,62,69],[-38,16,22,62,63],[-7,-64,-68],[-40,-64,-68],[-10,20,61,64,67],[-35,20,64,67],[-39,20,61,67],[-42,20,61,64],[-43,20,61,64,67],[-23,-44,-62],[-12,18,58,64,65,66],[-51,18,58,65,66],[-53,18,58,64,65],[-14,20,61,64,67],[-48,20,64,67],[-51,20,61,67],[-54,20,61,64],[-64,14,48,54],[-70,32,50,63],[-71,41,56,69],[-72,26,45,46,52],[-73,57,58,59,60,62],[-74,64,65,66],[-75,27,47,53,55],[-76,48,61,68],[-48,76],[-77,44,49],[-78,51],[-51,78],[-79,71,72],[-80,71],[-80,72],[-81,70,80],[-82,70],[-81,79],[-82,80],[-83,81],[-84,82],[-85,74,75],[-86,74],[-86,75],[-87,73,86],[-88,73],[-87,85],[-88,86],[-89,77,78],[-90,77],[-90,78],[-91,76,89],[-92,76,90],[-93,76],[-92,89],[-93,90],[-94,87,93],[-95,87],[-94,88,92],[-95,88,93],[-96,88],[-94,91],[-95,92],[-96,93],[-97,83,96],[-97,84,95],[-97,94],[97],[3,6,8,16,19,22,28,29,32,36,37,38,40,41,62,63,65,69],[2,12,14,18,20,24,29,30,31,45,48,51,52,53,54,58,61,64,65,66,67],[4,11,15,17,21,23,26,30,32,46,50,54,59,63,67],[10,14,20,35,39,42,43,48,51,54,61,64,67]],\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group\",\"index\":10,\"kind\":2},{\"tag\":\"group\",\"index\":11,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":46,\"b\":3},{\"tag\":\"incompatible\",\"a\":46,\"b\":4},{\"tag\":\"incompatible\",\"a\":47,\"b\":46},{\"tag\":\"incompatible\",\"a\":49,\"b\":46},{\"tag\":\"incompatible\",\"a\":50,\"b\":46},{\"tag\":\"incompatible\",\"a\":51,\"b\":46},{\"tag\":\"incompatible\",\"a\":52,\"b\":46},{\"tag\":\"incompatible\",\"a\":52,\"b\":47},{\"tag\":\"incompatible\",\"a\":68,\"b\":20},{\"tag\":\"incompatible\",\"a\":69,\"b\":46},{\"tag\":\"incompatible\",\"a\":69,\"b\":47},{\"tag\":\"incompatible\",\"a\":69,\"b\":68},{\"tag\":\"incompatible\",\"a\":70,\"b\":68},{\"tag\":\"incompatible\",\"a\":71,\"b\":68},{\"tag\":\"incompatible\",\"a\":71,\"b\":70},{\"tag\":\"incompatible\",\"a\":72,\"b\":68},{\"tag\":\"incompatible\",\"a\":72,\"b\":69},{\"tag\":\"incompatible\",\"a\":73,\"b\":20},{\"tag\":\"incompatible\",\"a\":73,\"b\":70},{\"tag\":\"incompatible\",\"a\":73,\"b\":71},{\"tag\":\"incompatible\",\"a\":73,\"b\":72},{\"tag\":\"incompatible\",\"a\":74,\"b\":68},{\"tag\":\"incompatible\",\"a\":74,\"b\":69},{\"tag\":\"incompatible\",\"a\":74,\"b\":70},{\"tag\":\"incompatible\",\"a\":74,\"b\":71},{\"tag\":\"incompatible\",\"a\":74,\"b\":72},{\"tag\":\"incompatible\",\"a\":74,\"b\":73},{\"tag\":\"incompatible\",\"a\":75,\"b\":68},{\"tag\":\"incompatible\",\"a\":75,\"b\":69},{\"tag\":\"incompatible\",\"a\":75,\"b\":72},{\"tag\":\"incompatible\",\"a\":76,\"b\":46},{\"tag\":\"incompatible\",\"a\":76,\"b\":47},{\"tag\":\"incompatible\",\"a\":76,\"b\":68},{\"tag\":\"incompatible\",\"a\":76,\"b\":71},{\"tag\":\"incompatible\",\"a\":76,\"b\":75},{\"tag\":\"incompatible\",\"a\":77,\"b\":69},{\"tag\":\"incompatible\",\"a\":77,\"b\":75},{\"tag\":\"incompatible\",\"a\":77,\"b\":76},{\"tag\":\"incompatible\",\"a\":78,\"b\":68},{\"tag\":\"incompatible\",\"a\":78,\"b\":73},{\"tag\":\"incompatible\",\"a\":78,\"b\":75},{\"tag\":\"incompatible\",\"a\":79,\"b\":65},{\"tag\":\"incompatible\",\"a\":79,\"b\":72},{\"tag\":\"incompatible\",\"a\":80,\"b\":68},{\"tag\":\"incompatible\",\"a\":80,\"b\":71},{\"tag\":\"incompatible\",\"a\":80,\"b\":79},{\"tag\":\"incompatible\",\"a\":81,\"b\":31},{\"tag\":\"incompatible\",\"a\":81,\"b\":68},{\"tag\":\"incompatible\",\"a\":81,\"b\":75},{\"tag\":\"incompatible\",\"a\":82,\"b\":47},{\"tag\":\"incompatible\",\"a\":82,\"b\":72},{\"tag\":\"incompatible\",\"a\":82,\"b\":79},{\"tag\":\"incompatible\",\"a\":83,\"b\":31},{\"tag\":\"incompatible\",\"a\":83,\"b\":46},{\"tag\":\"incompatible\",\"a\":83,\"b\":55},{\"tag\":\"incompatible\",\"a\":83,\"b\":70},{\"tag\":\"incompatible\",\"a\":84,\"b\":47},{\"tag\":\"incompatible\",\"a\":84,\"b\":71},{\"tag\":\"incompatible\",\"a\":84,\"b\":77},{\"tag\":\"incompatible\",\"a\":84,\"b\":82},{\"tag\":\"incompatible\",\"a\":84,\"b\":83},{\"tag\":\"incompatible\",\"a\":85,\"b\":36},{\"tag\":\"incompatible\",\"a\":85,\"b\":79},{\"tag\":\"incompatible\",\"a\":85,\"b\":81},{\"tag\":\"incompatible\",\"a\":85,\"b\":82},{\"tag\":\"incompatible\",\"a\":85,\"b\":83},{\"tag\":\"incompatible\",\"a\":86,\"b\":32},{\"tag\":\"incompatible\",\"a\":86,\"b\":43},{\"tag\":\"incompatible\",\"a\":86,\"b\":73},{\"tag\":\"incompatible\",\"a\":86,\"b\":82},{\"tag\":\"incompatible\",\"a\":86,\"b\":83},{\"tag\":\"incompatible\",\"a\":86,\"b\":85},{\"tag\":\"incompatible\",\"a\":87,\"b\":81},{\"tag\":\"incompatible\",\"a\":87,\"b\":82},{\"tag\":\"incompatible\",\"a\":87,\"b\":83},{\"tag\":\"incompatible\",\"a\":87,\"b\":84},{\"tag\":\"incompatible\",\"a\":87,\"b\":85},{\"tag\":\"incompatible\",\"a\":87,\"b\":86},{\"tag\":\"incompatible\",\"a\":88,\"b\":45},{\"tag\":\"incompatible\",\"a\":88,\"b\":49},{\"tag\":\"incompatible\",\"a\":88,\"b\":63},{\"tag\":\"incompatible\",\"a\":88,\"b\":68},{\"tag\":\"incompatible\",\"a\":88,\"b\":75},{\"tag\":\"incompatible\",\"a\":88,\"b\":81},{\"tag\":\"incompatible\",\"a\":88,\"b\":82},{\"tag\":\"incompatible\",\"a\":88,\"b\":85},{\"tag\":\"incompatible\",\"a\":89,\"b\":46},{\"tag\":\"incompatible\",\"a\":89,\"b\":81},{\"tag\":\"incompatible\",\"a\":89,\"b\":82},{\"tag\":\"incompatible\",\"a\":89,\"b\":83},{\"tag\":\"incompatible\",\"a\":89,\"b\":84},{\"tag\":\"incompatible\",\"a\":90,\"b\":47},{\"tag\":\"incompatible\",\"a\":90,\"b\":71},{\"tag\":\"incompatible\",\"a\":90,\"b\":77},{\"tag\":\"incompatible\",\"a\":90,\"b\":82},{\"tag\":\"incompatible\",\"a\":90,\"b\":84},{\"tag\":\"incompatible\",\"a\":91,\"b\":85},{\"tag\":\"incompatible\",\"a\":91,\"b\":86},{\"tag\":\"incompatible\",\"a\":92,\"b\":13},{\"tag\":\"incompatible\",\"a\":92,\"b\":47},{\"tag\":\"incompatible\",\"a\":92,\"b\":65},{\"tag\":\"incompatible\",\"a\":92,\"b\":69},{\"tag\":\"incompatible\",\"a\":92,\"b\":79},{\"tag\":\"incompatible\",\"a\":92,\"b\":82},{\"tag\":\"incompatible\",\"a\":92,\"b\":84},{\"tag\":\"incompatible\",\"a\":92,\"b\":90},{\"tag\":\"incompatible\",\"a\":93,\"b\":81},{\"tag\":\"incompatible\",\"a\":93,\"b\":83},{\"tag\":\"incompatible\",\"a\":93,\"b\":84},{\"tag\":\"incompatible\",\"a\":93,\"b\":92},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[32,84,85]},{\"tag\":\"mate\",\"ridge\":19,\"a\":12,\"owners\":[1,6,11,13,45,46,53,55,63]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[22,46,77]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[46,68,77]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[46,71,75]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[47,70,75]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[1,83,88]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[33,34,46]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[33,34,81]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[33,46,84]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[34,46,90]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[34,83,88]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[47,83,88]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[23,24,73]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[24,73,75]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[35,36,86]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[36,86,88]},{\"tag\":\"mate\",\"ridge\":133,\"a\":73,\"owners\":[4,22,49,52,76]},{\"tag\":\"mate\",\"ridge\":134,\"a\":4,\"owners\":[31,34,86,87,89]},{\"tag\":\"mate\",\"ridge\":134,\"a\":48,\"owners\":[31,34,87,89]},{\"tag\":\"mate\",\"ridge\":134,\"a\":52,\"owners\":[31,34,86,89]},{\"tag\":\"mate\",\"ridge\":134,\"a\":86,\"owners\":[4,34,49,52,89]},{\"tag\":\"mate\",\"ridge\":261,\"a\":24,\"owners\":[5,20,46,50,52,70,74]},{\"tag\":\"mate\",\"ridge\":261,\"a\":46,\"owners\":[20,24,74,78]},{\"tag\":\"mate\",\"ridge\":261,\"a\":52,\"owners\":[20,24,70,78]},{\"tag\":\"mate\",\"ridge\":262,\"a\":5,\"owners\":[32,36,83,87,91]},{\"tag\":\"mate\",\"ridge\":262,\"a\":46,\"owners\":[32,36,87,91]},{\"tag\":\"mate\",\"ridge\":262,\"a\":50,\"owners\":[32,36,83,87]},{\"tag\":\"mate\",\"ridge\":262,\"a\":52,\"owners\":[32,36,83,91]},{\"tag\":\"three\",\"ridge\":26,\"vertices\":[6,83,92]},{\"tag\":\"three\",\"ridge\":26,\"vertices\":[37,83,92]},{\"tag\":\"three\",\"ridge\":26,\"vertices\":[53,83,92]},{\"tag\":\"mate\",\"ridge\":138,\"a\":8,\"owners\":[31,37,86,87,93]},{\"tag\":\"mate\",\"ridge\":138,\"a\":57,\"owners\":[31,37,87,93]},{\"tag\":\"mate\",\"ridge\":138,\"a\":60,\"owners\":[31,37,86,93]},{\"tag\":\"mate\",\"ridge\":138,\"a\":61,\"owners\":[31,37,86,87]},{\"tag\":\"three\",\"ridge\":82,\"vertices\":[11,88,92]},{\"tag\":\"three\",\"ridge\":82,\"vertices\":[64,88,92]},{\"tag\":\"mate\",\"ridge\":98,\"a\":14,\"owners\":[35,85,88,91]},{\"tag\":\"mate\",\"ridge\":98,\"a\":56,\"owners\":[35,88,91]},{\"tag\":\"mate\",\"ridge\":98,\"a\":63,\"owners\":[35,85,91]},{\"tag\":\"mate\",\"ridge\":98,\"a\":66,\"owners\":[35,85,88]},{\"tag\":\"mate\",\"ridge\":98,\"a\":67,\"owners\":[35,85,88,91]},{\"tag\":\"three\",\"ridge\":44,\"vertices\":[42,68,86]},{\"tag\":\"mate\",\"ridge\":84,\"a\":21,\"owners\":[33,82,88,89,90]},{\"tag\":\"mate\",\"ridge\":84,\"a\":75,\"owners\":[33,82,89,90]},{\"tag\":\"mate\",\"ridge\":84,\"a\":77,\"owners\":[33,82,88,89]},{\"tag\":\"mate\",\"ridge\":100,\"a\":23,\"owners\":[35,85,88,91]},{\"tag\":\"mate\",\"ridge\":100,\"a\":72,\"owners\":[35,88,91]},{\"tag\":\"mate\",\"ridge\":100,\"a\":75,\"owners\":[35,85,91]},{\"tag\":\"mate\",\"ridge\":100,\"a\":78,\"owners\":[35,85,88]},{\"tag\":\"mate\",\"ridge\":100,\"a\":88,\"owners\":[23,72,78]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[52,74,87],\"full_literals\":[-70,32,50,63]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[65,80,93],\"full_literals\":[-71,41,56,69]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[46,69,70,76],\"full_literals\":[-72,26,45,46,52]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[81,82,83,84,86],\"full_literals\":[-73,57,58,59,60,62]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[88,89,90],\"full_literals\":[-74,64,65,66]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[47,71,77,79],\"full_literals\":[-75,27,47,53,55]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[72,85,92],\"full_literals\":[-76,48,61,68]},{\"tag\":\"group_take\",\"kind\":2,\"index\":9,\"member\":72,\"full_literals\":[-48,76]},{\"tag\":\"group_or\",\"kind\":2,\"index\":10,\"members\":[68,73],\"full_literals\":[-77,44,49]},{\"tag\":\"group_or\",\"kind\":2,\"index\":11,\"members\":[75],\"full_literals\":[-78,51]},{\"tag\":\"group_take\",\"kind\":2,\"index\":11,\"member\":75,\"full_literals\":[-51,78]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-79,71,72],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-80,71,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-80,false,72],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-81,70,80],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-82,70,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-81,false,79],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-82,false,80],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":3,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-83,false,81],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":3,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-84,false,82],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0012\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-85,74,75],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0012\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-86,74,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0012\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-86,false,75],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-87,73,86],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-88,73,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-87,false,85],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-88,false,86],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0018\",\"joined_name\":\"grouped2_0017\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-89,77,78],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0018\",\"joined_name\":\"grouped2_0017\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-90,77,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0018\",\"joined_name\":\"grouped2_0017\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-90,false,78],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-91,76,89],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-92,76,90],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-93,76,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-92,false,89],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-93,false,90],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-94,87,93],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-95,87,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-94,88,92],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-95,88,93],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-96,88,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0010\",\"a\":3,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-94,false,91],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0010\",\"a\":3,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-95,false,92],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0010\",\"a\":3,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-96,false,93],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-97,83,96],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-97,84,95],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":6,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-97,false,94],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":10,\"grouped\":true},{\"tag\":\"edge\",\"edge\":14,\"owners\":[4,8,12,31,34,37,48,49,52,57,60,61,64,65,86,87,89,93]},{\"tag\":\"edge\",\"edge\":20,\"owners\":[3,21,23,33,35,43,49,50,51,69,72,75,76,77,78,82,85,88,89,90,91]},{\"tag\":\"edge\",\"edge\":22,\"owners\":[5,20,24,32,36,42,46,50,52,70,74,78,83,87,91]},{\"tag\":\"edge\",\"edge\":35,\"owners\":[14,23,35,56,63,66,67,72,75,78,85,88,91]}]}"
  "214 94 0 209 208 0\n215 91 0 214 203 0\n216 -58 -96 0 205 197 191 192 172 28 171 20 37 202 189 185 50 52 168 0\n217 -59 -96 0 205 197 192 172 83 30 202 189 184 195 66 90 169 167 106 0\n218 -96 0 202 205 187 189 197 184 191 192 172 28 49 83 171 69 216 217 166 91 96 167 0\n219 83 0 218 209 206 0\n220 81 0 219 181 0\n221 79 0 220 179 0\n222 -64 -76 -60 0 214 105 59 58 57 82 83 86 172 169 21 43 171 168 190 185 196 189 200 0\n223 -48 -89 0 16 21 30 171 172 190 0\n224 -76 -60 0 214 209 105 96 91 76 61 59 58 57 222 167 184 189 200 196 223 169 62 63 97 111 168 139 183 188 198 199 197 207 191 192 182 172 178 28 163 171 27 0\n225 -90 -60 0 220 96 91 76 60 191 192 172 28 29 35 41 156 171 120 18 19 27 125 135 165 163 176 177 0\n226 -60 0 214 209 57 58 59 109 224 225 194 204 200 207 189 182 185 180 168 175 42 46 164 0\n227 -65 57 62 -73 0 226 89 90 166 0\n228 -51 92 62 -73 0 214 209 226 204 207 182 180 175 200 189 185 184 37 49 83 227 167 92 93 95 168 166 42 46 108 164 0\n229 -66 92 62 -73 0 214 209 226 204 207 182 180 175 200 189 185 92 93 94 95 168 42 46 164 107 108 166 0\n230 -57 66 -74 0 84 88 167 0\n231 92 76 62 -73 0 215 214 209 226 193 170 204 200 207 189 182 184 178 228 172 190 229 230 227 167 82 171 18 40 27 85 19 162 166 124 75 135 163 0\n232 -90 62 -73 0 220 226 191 192 172 28 29 35 41 49 171 18 19 27 125 135 134 165 176 177 163 74 75 166 0\n233 -92 -57 58 90 62 0 214 209 49 172 88 84 73 64 48 47 197 198 188 196 194 223 190 169 171 100 103 106 20 27 230 184 183 189 168 201 157 207 119 182 131 178 163 0\n234 -57 58 62 -73 0 214 232 233 200 229 189 230 184 0\n235 92 58 62 -73 0 226 214 209 234 166 75 66 56 54 53 227 204 200 229 231 207 189 182 184 185 178 180 167 176 122 123 131 163 23 25 26 165 169 38 103 168 0\n236 -64 -68 -59 65 62 0 108 53 75 141 144 145 146 143 142 140 101 99 55 54 79 80 81 117 122 147 148 112 130 131 129 210 0\n237 58 62 -73 0 214 226 209 232 197 198 188 234 227 166 54 56 66 108 235 196 194 223 169 100 101 102 103 106 236 167 184 183 189 201 207 182 180 175 176 164 165 45 38 168 0\n238 62 -73 0 232 237 51 65 104 169 231 194 0\n239 -90 49 0 191 192 171 172 28 0\n240 -51 -82 -62 0 180 176 178 98 78 72 71 67 29 35 160 126 137 139 165 163 24 0\n241 76 -62 0 215 209 69 239 78 193 194 204 207 182 178 180 176 240 172 190 171 12 13 22 33 165 163 7 0\n242 -26 51 -62 0 98 78 72 70 68 67 1 2 4 5 6 7 10 31 87 137 132 126 127 118 121 158 161 159 155 157 211 0\n243 -21 51 -62 0 98 72 126 127 149 150 152 158 161 159 153 151 213 0\n244 -82 32 45 52 26 63 0 178 180 163 176 24 165 0\n245 32 45 52 78 -62 0 209 98 78 71 67 173 243 136 138 242 69 244 182 207 204 196 190 171 9 13 22 39 154 133 212 0\n246 -45 -62 0 241 72 17 102 169 0\n247 -55 -62 0 241 72 43 103 169 0\n248 -47 -68 -62 0 221 110 101 246 15 34 45 164 174 165 115 242 0\n249 88 -68 -62 0 214 209 110 101 69 239 197 200 201 196 207 182 180 240 175 172 164 190 44 171 0\n250 -53 -62 0 246 98 71 67 37 38 172 243 245 139 0\n251 51 -62 0 214 250 247 246 98 71 69 67 172 243 139 245 32 33 34 171 168 190 185 196 189 200 0\n252 -62 0 72 241 247 250 251 30 169 100 248 249 168 189 185 0\n253 -73 0 252 238 0\n254 -88 0 253 187 0\n255 92 0 254 214 200 0\n256 89 0 255 196 0\n257 -48 0 256 223 0\n258 87 -51 0 214 209 41 35 29 198 199 197 207 239 182 18 19 27 125 180 134 176 165 0\n259 -49 -51 0 253 220 209 254 257 258 186 185 41 37 35 29 18 19 20 27 125 135 134 165 176 180 177 182 163 207 77 201 195 169 100 103 168 0\n260 -55 -76 0 257 63 103 169 0\n261 -27 -51 0 254 209 259 239 197 201 207 182 180 176 35 29 3 116 165 0\n262 -51 0 253 255 254 209 29 35 37 258 186 185 259 239 197 194 201 207 182 180 176 260 261 168 15 115 165 0\n263 -78 0 262 172 0\n264 -90 0 263 192 0\n265 77 0 263 256 190 0\n266 -93 0 264 197 0\n267 76 0 264 255 194 0\n268 87 0 266 214 198 0\n269 -95 0 266 254 201 0\n270 -55 0 267 260 0\n271 86 0 268 253 186 0\n272 84 0 269 209 207 0\n273 75 0 271 185 0\n274 82 0 272 182 0\n275 80 0 274 180 0\n276 72 0 275 176 0\n277 -47 0 265 14 20 171 0\n278 -27 0 274 257 267 3 8 11 32 100 244 169 77 0\n279 53 0 278 273 270 277 168 0\n280 -45 0 279 36 0\n281 -52 0 279 38 0\n282 -46 0 265 13 19 171 0\n283 26 0 282 281 276 280 165 0\n284 -3 0 283 2 0\n285 -29 0 283 4 0\n286 -32 0 283 7 0\n287 -44 0 283 279 114 0\n288 -13 0 283 279 113 0\n289 49 0 287 265 171 0\n290 0 288 289 284 286 285 281 128 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record002.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record002.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record002.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record002.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record002 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record002.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record002.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record002.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record002.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record002 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record002_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record002 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record002_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record002_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00030.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00030.record003
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "26659a9635876638ae1ba1e4785e0fa655969535475634ad1b61d4745d0f66358e9334c7362cab1ae1b46c5b0ef07a1d8751cc789ca745c3783c4f9512c272524a89a9192619a16258564388e0b81e945292664549465854951550d2342d0764348c6384c9314d0b22c2b06e0741c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "2492492492492492492492492492492492489249249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record003 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record003 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record003.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 46), (facetIndex 47), (facetIndex 48), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 52), (facetIndex 53), (facetIndex 54), (facetIndex 55), (facetIndex 56)]))
 (.leaf ([(facetIndex 57), (facetIndex 58), (facetIndex 59), (facetIndex 60), (facetIndex 62), (facetIndex 63)])))
 (.branch 3
 (.leaf ([(facetIndex 66), (facetIndex 78), (facetIndex 90)]))
 (.leaf ([(facetIndex 61), (facetIndex 64), (facetIndex 67), (facetIndex 68)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 73), (facetIndex 76), (facetIndex 79), (facetIndex 80)]))
 (.leaf ([(facetIndex 69), (facetIndex 70), (facetIndex 71), (facetIndex 72), (facetIndex 74), (facetIndex 75)])))
 (.branch 7
 (.leaf ([(facetIndex 65), (facetIndex 77), (facetIndex 89)]))
 (.branch 8
 (.leaf ([(facetIndex 85), (facetIndex 88), (facetIndex 91), (facetIndex 92)]))
 (.leaf ([(facetIndex 81), (facetIndex 82), (facetIndex 83), (facetIndex 84), (facetIndex 86), (facetIndex 87)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "772678878888442645545555332631131111z39;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record003 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record003_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00030.record003" "{\"atoms\":[]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00030.record003" 0

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00030.record003" "{\"ridges\":[],\"owners\":[],\"edges\":[],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00030.record003" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00030.record003\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[]],\"atoms\":[],\"rules\":[{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":10,\"grouped\":true}]}"
  "2 0 1 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record003.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record003.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record003.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record003.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record003 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record003.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record003.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record003.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record003.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record003 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record003_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record003 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record003_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record003_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00030.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00030.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "968da1e9362d876c3a8e63a4e4ba1e4785e0fa59364794d4b51d70da358d9352d8751d1743d98d6394cd34ccb3c2e8b62d4b32d2b1ae1b46c3bc1e8761e4789ca719e1745c5713c2f270729289a16926258368390e2381e1c64926459494950d60d4348d0764348c6324c530ce0b42c8b12c1b81d0721c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "12492492492492492492492492492492492492492492249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record005.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record005.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record005.data.quota

def groupMembers1 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 20
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 0)]))
 (.leaf ([(facetIndex 1)])))
 (.branch 3
 (.leaf ([(facetIndex 2)]))
 (.branch 4
 (.leaf ([(facetIndex 3)]))
 (.leaf ([(facetIndex 4)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 5)]))
 (.leaf ([(facetIndex 6)])))
 (.branch 8
 (.leaf ([(facetIndex 7)]))
 (.branch 9
 (.leaf ([(facetIndex 8)]))
 (.leaf ([(facetIndex 9)]))))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ([(facetIndex 10)]))
 (.leaf ([(facetIndex 11)])))
 (.branch 13
 (.leaf ([(facetIndex 12)]))
 (.branch 14
 (.leaf ([(facetIndex 13)]))
 (.leaf ([(facetIndex 14)])))))
 (.branch 17
 (.branch 16
 (.leaf ([(facetIndex 15)]))
 (.leaf ([(facetIndex 16)])))
 (.branch 18
 (.leaf ([(facetIndex 17)]))
 (.branch 19
 (.leaf ([(facetIndex 18)]))
 (.leaf ([(facetIndex 19)])))))))
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf ([(facetIndex 20)]))
 (.leaf ([(facetIndex 21)])))
 (.branch 23
 (.leaf ([(facetIndex 22)]))
 (.branch 24
 (.leaf ([(facetIndex 23)]))
 (.leaf ([(facetIndex 24)])))))
 (.branch 27
 (.branch 26
 (.leaf ([(facetIndex 25)]))
 (.leaf ([(facetIndex 26)])))
 (.branch 28
 (.leaf ([(facetIndex 27)]))
 (.branch 29
 (.leaf ([(facetIndex 28)]))
 (.leaf ([(facetIndex 29)]))))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf ([(facetIndex 30)]))
 (.leaf ([(facetIndex 31)])))
 (.branch 33
 (.leaf ([(facetIndex 32)]))
 (.branch 34
 (.leaf ([(facetIndex 33)]))
 (.leaf ([(facetIndex 34)])))))
 (.branch 37
 (.branch 36
 (.leaf ([(facetIndex 35)]))
 (.leaf ([(facetIndex 36)])))
 (.branch 38
 (.leaf ([(facetIndex 37)]))
 (.branch 39
 (.leaf ([(facetIndex 38)]))
 (.leaf ([(facetIndex 39)]))))))))
def groupColors1 : PackedGraphCertificate.Fields :=
  ⟨6, sparse_nat% "9e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040"⟩
def grouping1 : FacetSat.Grouping data.count where
  count := 40
  members := fun g => groupMembers1.get g
  color := fun c => groupColors1.get c.val
def groupKind1 : List Nat := List.range grouping1.count

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 45), (facetIndex 47), (facetIndex 63), (facetIndex 66), (facetIndex 67)]))
 (.leaf ([(facetIndex 42), (facetIndex 43), (facetIndex 44), (facetIndex 46), (facetIndex 62), (facetIndex 78), (facetIndex 93)])))
 (.branch 3
 (.leaf ([(facetIndex 52), (facetIndex 53), (facetIndex 54), (facetIndex 57), (facetIndex 64), (facetIndex 81), (facetIndex 96)]))
 (.branch 4
 (.leaf ([(facetIndex 40), (facetIndex 41), (facetIndex 49), (facetIndex 59), (facetIndex 74), (facetIndex 89)]))
 (.leaf ([(facetIndex 50), (facetIndex 60), (facetIndex 75), (facetIndex 90)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 70), (facetIndex 79), (facetIndex 85), (facetIndex 94)]))
 (.branch 7
 (.leaf ([(facetIndex 55), (facetIndex 58), (facetIndex 65), (facetIndex 82), (facetIndex 97)]))
 (.leaf ([(facetIndex 51), (facetIndex 61), (facetIndex 76), (facetIndex 91)]))))
 (.branch 9
 (.leaf ([(facetIndex 48), (facetIndex 69), (facetIndex 73), (facetIndex 77), (facetIndex 84), (facetIndex 88), (facetIndex 92)]))
 (.branch 10
 (.leaf ([(facetIndex 56), (facetIndex 68), (facetIndex 72), (facetIndex 80), (facetIndex 83), (facetIndex 87), (facetIndex 95)]))
 (.leaf ([(facetIndex 71), (facetIndex 86)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "62951874389a58962951874389a5890062017436296222743801011133z28;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 11
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped1_0000 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
def grouped1_0001 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
def grouped1_0003 : List Nat := [10, 11, 12, 13, 14]
def grouped1_0004 : List Nat := [10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
def grouped1_0005 : List Nat := [15]
def grouped1_0006 : List Nat := [15, 16]
def grouped1_0007 : List Nat := [15, 16, 17, 18, 19]
def grouped1_0008 : List Nat := [16]
def grouped1_0009 : List Nat := [17, 18, 19]
def grouped1_0010 : List Nat := [20, 21]
def grouped1_0011 : List Nat := [20, 21, 22, 23, 24]
def grouped1_0012 : List Nat := [20, 21, 22, 23, 24, 25, 26, 27, 28, 29]
def grouped1_0013 : List Nat := [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39]
def grouped1_0014 : List Nat := [22]
def grouped1_0015 : List Nat := [22, 23, 24]
def grouped1_0016 : List Nat := [23, 24]
def grouped1_0017 : List Nat := [25]
def grouped1_0018 : List Nat := [25, 26]
def grouped1_0019 : List Nat := [25, 26, 27, 28, 29]
def grouped1_0020 : List Nat := [26]
def grouped1_0021 : List Nat := [27]
def grouped1_0022 : List Nat := [27, 28, 29]
def grouped1_0023 : List Nat := [28, 29]
def grouped1_0024 : List Nat := [30, 31]
def grouped1_0025 : List Nat := [30, 31, 32, 33, 34]
def grouped1_0026 : List Nat := [30, 31, 32, 33, 34, 35, 36, 37, 38, 39]
def grouped1_0027 : List Nat := [32]
def grouped1_0028 : List Nat := [32, 33, 34]
def grouped1_0029 : List Nat := [33]
def grouped1_0030 : List Nat := [33, 34]
def grouped1_0031 : List Nat := [34]
def grouped1_0032 : List Nat := [35]
def grouped1_0033 : List Nat := [35, 36]
def grouped1_0034 : List Nat := [35, 36, 37, 38, 39]
def grouped1_0035 : List Nat := [36]
def grouped1_0036 : List Nat := [37]
def grouped1_0037 : List Nat := [37, 38, 39]
def grouped1_0038 : List Nat := [38]
def grouped1_0039 : List Nat := [38, 39]
def grouped1_0040 : List Nat := [39]
def grouped2_0041 : List Nat := [0]
def grouped2_0042 : List Nat := [0, 1]
def grouped2_0043 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0045 : List Nat := [1]
def grouped2_0046 : List Nat := [2]
def grouped2_0047 : List Nat := [2, 3, 4]
def grouped2_0048 : List Nat := [3]
def grouped2_0049 : List Nat := [3, 4]
def grouped2_0050 : List Nat := [4]
def grouped2_0051 : List Nat := [5]
def grouped2_0052 : List Nat := [5, 6, 7]
def grouped2_0053 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped2_0054 : List Nat := [6]
def grouped2_0055 : List Nat := [6, 7]
def grouped2_0056 : List Nat := [7]
def grouped2_0057 : List Nat := [8]
def grouped2_0058 : List Nat := [8, 9, 10]
def grouped2_0059 : List Nat := [9]
def grouped2_0060 : List Nat := [9, 10]
def grouped2_0061 : List Nat := [10]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record005_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00030.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"group\",\"kind\":1,\"index\":15},{\"tag\":\"group\",\"kind\":1,\"index\":16},{\"tag\":\"group\",\"kind\":1,\"index\":22},{\"tag\":\"group\",\"kind\":1,\"index\":25},{\"tag\":\"group\",\"kind\":1,\"index\":27},{\"tag\":\"group\",\"kind\":1,\"index\":33},{\"tag\":\"group\",\"kind\":1,\"index\":36},{\"tag\":\"group\",\"kind\":1,\"index\":38},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0006\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0007\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0004\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0015\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0011\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0018\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0022\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0019\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0019\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0012\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0012\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0030\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0028\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0025\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0033\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0039\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0037\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0034\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0034\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0026\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0026\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":4,\"list_name\":\"grouped1_0013\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":5,\"list_name\":\"groupKind1\"},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group\",\"kind\":2,\"index\":10},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0042\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0049\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0047\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0043\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0055\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0052\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0060\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0060\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0058\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0058\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0053\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":6,\"list_name\":\"grouped2_0053\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":10,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00030.record005" 136

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00030.record005" "{\"ridges\":[[5,517],[5,518],[9,265],[9,266],[17,13],[18,13],[18,140],[19,13],[19,265],[19,268],[20,13],[20,524],[29,14],[29,134],[30,14],[30,268],[31,524],[39,28],[39,140],[44,517],[44,518],[47,517],[47,518],[48,517],[48,518],[49,259],[50,131],[50,133],[50,134],[50,517],[50,518],[51,517],[51,518],[53,266],[56,265],[56,266],[58,259],[58,265],[58,266],[59,131],[59,259],[59,265],[59,266],[61,265],[61,266],[62,131],[63,259],[64,131],[66,97],[66,98],[67,97],[67,98],[68,13],[68,28],[69,13],[69,28],[70,28],[70,268],[72,13],[72,268],[72,289],[73,524],[74,140],[74,268],[75,140],[75,524],[76,265],[76,268],[76,524],[82,25],[82,577],[83,14],[84,28],[85,268],[87,268],[88,524],[89,268],[90,524],[91,266],[91,268],[91,524],[93,134],[94,22],[97,26],[97,578]],\"owners\":[[94,22,[1,28,33,42,44,84,86],[32,43,85,92]],[50,133,[18,22,74,78],[3,46,49,75]],[50,134,[29,33,89,93],[3,46,49,90]],[59,259,[4,15,43,51,63,66],[9,49,53,58,61]],[5,517,[20,71,73,75,76],[44,47,48,50,51]],[44,517,[20,73,75,76],[5,47,48,50,51,71]],[47,517,[20,71,73,75,76],[5,44,48,50,51]],[48,517,[20,71,75,76],[5,44,47,50,51,73]],[50,517,[20,71,73,76],[5,44,47,48,51,75]],[51,517,[20,71,73,75],[5,44,47,48,50,76]],[5,518,[31,86,88,90,91],[44,47,48,50,51]],[44,518,[31,88,90,91],[5,47,48,50,51,86]],[47,518,[31,86,88,90,91],[5,44,48,50,51]],[48,518,[31,86,90,91],[5,44,47,50,51,88]],[50,518,[31,86,88,91],[5,44,47,48,51,90]],[51,518,[31,86,88,90],[5,44,47,48,50,91]],[82,25,[6,17,25,52,53,68,70],[24,54,71,80]],[97,26,[6,28,36,52,53,83,85],[35,54,86,95]],[9,265,[19,70,72,74,76],[53,56,58,59,61]],[19,265,[9,53,56,58,59,61],[70,72,74,76]],[56,265,[19,70,74,76],[9,53,58,59,61,72]],[58,265,[19,70,72,74,76],[9,53,56,59,61]],[59,265,[19,70,72,76],[9,53,56,58,61,74]],[61,265,[19,70,72,74],[9,53,56,58,59,76]],[76,265,[9,53,56,58,59],[19,61,70,72,74]],[9,266,[30,85,87,89,91],[53,56,58,59,61]],[53,266,[30,87,89,91],[9,56,58,59,61,85]],[56,266,[30,85,89,91],[9,53,58,59,61,87]],[58,266,[30,85,87,89,91],[9,53,56,59,61]],[59,266,[30,85,87,91],[9,53,56,58,61,89]],[61,266,[30,85,87,89],[9,53,56,58,59,91]],[91,266,[9,53,56,58,59],[30,61,85,87,89]],[66,97,[27,77,80],[14,45,55,67]],[67,97,[27,77,80],[14,45,55,66]],[66,98,[38,92,95],[14,45,55,67]],[67,98,[38,92,95],[14,45,55,66]],[72,289,[15,63,66],[23,56,79]],[82,577,[16,48,67],[26,65,73]],[97,578,[16,48,67],[37,65,88]],[39,28,[17,28,68,69,70,71,83,84,85,86],[]],[68,28,[28,39,84,85,86],[17,69,70,71,83]],[69,28,[28,39,83,85,86],[17,68,70,71,84]],[70,28,[28,39,83,84,86],[17,68,69,71,85]],[84,28,[17,39,68,70,71],[28,69,83,85,86]],[18,140,[29,39,89,90],[74,75]],[39,140,[18,29,74,75,89,90],[]],[74,140,[29,39,90],[18,75,89]],[75,140,[29,39,89],[18,74,90]],[19,268,[30,85,87,89,91],[70,72,74,76]],[30,268,[19,70,72,74,76],[85,87,89,91]],[70,268,[30,87,89,91],[19,72,74,76,85]],[72,268,[30,85,89,91],[19,70,74,76,87]],[74,268,[30,85,87,91],[19,70,72,76,89]],[76,268,[30,85,87,89],[19,70,72,74,91]],[85,268,[19,72,74,76],[30,70,87,89,91]],[87,268,[19,70,74,76],[30,72,85,89,91]],[89,268,[19,70,72,76],[30,74,85,87,91]],[91,268,[19,70,72,74],[30,76,85,87,89]],[20,524,[31,86,88,90,91],[71,73,75,76]],[31,524,[20,71,73,75,76],[86,88,90,91]],[73,524,[31,86,90,91],[20,71,75,76,88]],[75,524,[31,86,88,91],[20,71,73,76,90]],[76,524,[31,86,88,90],[20,71,73,75,91]],[88,524,[20,71,75,76],[31,73,86,90,91]],[90,524,[20,71,73,76],[31,75,86,88,91]],[91,524,[20,71,73,75],[31,76,86,88,90]]],\"edges\":[[23,[5,20,31,44,47,48,50,51,71,73,75,76,86,88,90,91]],[28,[9,19,30,53,56,58,59,61,70,72,74,76,85,87,89,91]]],\"groupings\":[1,2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00030.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00030.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-32,-28],[-32,-30],[-33,-1],[-33,-23],[-33,-24],[-33,-25],[-33,-26],[-33,-27],[-33,-28],[-33,-29],[-33,-30],[-33,-31],[-33,-32],[-34,-33],[-41,-23],[-41,-24],[-42,-4],[-42,-35],[-42,-36],[-42,-37],[-42,-38],[-42,-39],[-42,-40],[-42,-41],[-43,-5],[-43,-36],[-43,-39],[-43,-41],[-43,-42],[-44,-42],[-44,-43],[-49,-41],[-49,-48],[-50,-41],[-50,-48],[-50,-49],[-53,-9],[-53,-11],[-54,-10],[-54,-53],[-55,-34],[-55,-51],[-55,-54],[-56,-52],[-56,-53],[-57,-8],[-57,-10],[-57,-11],[-57,-51],[-57,-52],[-57,-53],[-57,-54],[-57,-55],[-57,-56],[-58,-8],[-58,-10],[-58,-51],[-58,-52],[-58,-53],[-58,-55],[-58,-57],[-59,-8],[-59,-9],[-59,-23],[-59,-24],[-59,-51],[-59,-52],[-59,-53],[-59,-54],[-59,-55],[-59,-56],[-59,-57],[-59,-58],[-61,-60],[-62,-28],[-62,-29],[-62,-30],[-62,-46],[-62,-55],[-62,-60],[-62,-61],[-63,-48],[-63,-55],[-64,-63],[-65,-56],[-65,-63],[-65,-64],[-66,-19],[-68,-18],[-69,-17],[-69,-68],[-70,-2],[-70,-23],[-70,-26],[-70,-32],[-70,-34],[-70,-35],[-70,-38],[-70,-51],[-70,-63],[-70,-68],[-70,-69],[-71,-68],[-72,-18],[-72,-69],[-72,-70],[-72,-71],[-73,-17],[-73,-68],[-73,-70],[-73,-72],[-74,-15],[-74,-16],[-74,-23],[-74,-24],[-74,-59],[-74,-66],[-74,-67],[-74,-68],[-74,-69],[-74,-70],[-74,-71],[-74,-72],[-74,-73],[-76,-66],[-76,-75],[-77,-46],[-77,-70],[-77,-75],[-77,-76],[-78,-48],[-78,-55],[-78,-70],[-79,-78],[-80,-71],[-80,-78],[-80,-79],[-8,-9,-10],[-8,-9,-55],[-9,-10,-51],[-9,-11,-52],[-16,-17,-66],[-77,1,15,19,25,27,67,69],[-33,-42,-45],[-33,-42,-47],[-33,9,12,57,61],[-33,16,19,72,76],[-16,-33,-76],[-42,2,6,26,34,46,49],[-32,-41,-46],[-3,11,54,56,58,59],[-27,11,56,58,59],[-30,11,54,56,58,59],[-31,11,54,58,59],[-33,11,54,56,59],[-34,11,54,56,58],[-3,18,69,71,73,74],[-27,18,71,73,74],[-30,18,69,71,73,74],[-31,18,69,73,74],[-33,18,69,71,74],[-34,18,69,71,73],[-65,4,8,13,35,36,51,53],[-80,4,15,20,35,36,66,68],[-5,10,53,55,57,59],[-10,5,36,39,41,42,44],[-39,10,53,57,59],[-41,10,53,55,57,59],[-42,10,53,55,59],[-44,10,53,55,57],[-59,5,36,39,41,42],[-5,17,68,70,72,74],[-36,17,70,72,74],[-39,17,68,72,74],[-41,17,68,70,72,74],[-42,17,68,70,74],[-44,17,68,70,72],[-74,5,36,39,41,42],[-49,14,60,63],[-50,14,60,63],[-49,21,75,78],[-50,21,75,78],[-55,6,46,49],[-65,7,31,50],[-80,7,31,50],[-22,8,15,51,52,53,54,66,67,68,69],[-51,15,22,67,68,69],[-52,15,22,66,68,69],[-53,15,22,66,67,69],[-67,8,22,51,53,54],[-9,16,22,72,73],[-22,9,16,57,58,72,73],[-57,16,22,73],[-58,16,22,72],[-10,17,68,70,72,74],[-17,10,53,55,57,59],[-53,17,70,72,74],[-55,17,68,72,74],[-57,17,68,70,74],[-59,17,68,70,72],[-68,10,55,57,59],[-70,10,53,57,59],[-72,10,53,55,59],[-74,10,53,55,57],[-11,18,69,71,73,74],[-18,11,54,56,58,59],[-56,18,69,73,74],[-58,18,69,71,74],[-59,18,69,71,73],[-71,11,54,58,59],[-73,11,54,56,59],[-74,11,54,56,58],[-6,81],[-7,82],[-12,83],[-13,84],[-14,85],[-19,86],[-20,87],[-21,88],[-82,89],[-81,89],[-89,90],[-90,91],[-91,92],[-83,93],[-93,94],[-84,95],[-85,96],[-96,97],[-95,-96,98],[-97,99],[-94,-98,100],[-86,101],[-101,102],[-102,103],[-87,104],[-88,105],[-105,106],[-106,107],[-104,-106,108],[-107,109],[-103,-108,110],[-99,-110,111],[-100,-109,111],[-92,-111,112],[-112],[-113,28,30,46,49,50],[-114,25,26,27,29,45,61,76],[-115,35,36,37,40,47,64,79],[-116,23,24,32,42,57,72],[-117,33,43,58,73],[-118,53,62,68,77],[-119,38,41,48,65,80],[-120,34,44,59,74],[-121,31,52,56,60,67,71,75],[-122,39,51,55,63,66,70,78],[-123,54,69],[-54,123],[-69,123],[-124,113],[-124,114],[-125,116],[-125,117],[-126,115],[-126,125],[-127,124],[-127,126],[-128,119],[-128,120],[-129,118],[-129,128],[-130,122,123],[-131,123],[-132,121,131],[-132,130],[-133,131],[-134,129,133],[-134,132],[-135,133],[-136,127,135],[-136,134],[136],[3,11,18,27,30,31,33,34,54,56,58,59,69,71,73,74],[5,10,17,36,39,41,42,44,53,55,57,59,68,70,72,74]],\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"group\",\"index\":15,\"kind\":1},{\"tag\":\"group\",\"index\":16,\"kind\":1},{\"tag\":\"group\",\"index\":22,\"kind\":1},{\"tag\":\"group\",\"index\":25,\"kind\":1},{\"tag\":\"group\",\"index\":27,\"kind\":1},{\"tag\":\"group\",\"index\":33,\"kind\":1},{\"tag\":\"group\",\"index\":36,\"kind\":1},{\"tag\":\"group\",\"index\":38,\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group\",\"index\":10,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":49,\"b\":45},{\"tag\":\"incompatible\",\"a\":49,\"b\":47},{\"tag\":\"incompatible\",\"a\":50,\"b\":1},{\"tag\":\"incompatible\",\"a\":50,\"b\":40},{\"tag\":\"incompatible\",\"a\":50,\"b\":41},{\"tag\":\"incompatible\",\"a\":50,\"b\":42},{\"tag\":\"incompatible\",\"a\":50,\"b\":43},{\"tag\":\"incompatible\",\"a\":50,\"b\":44},{\"tag\":\"incompatible\",\"a\":50,\"b\":45},{\"tag\":\"incompatible\",\"a\":50,\"b\":46},{\"tag\":\"incompatible\",\"a\":50,\"b\":47},{\"tag\":\"incompatible\",\"a\":50,\"b\":48},{\"tag\":\"incompatible\",\"a\":50,\"b\":49},{\"tag\":\"incompatible\",\"a\":51,\"b\":50},{\"tag\":\"incompatible\",\"a\":58,\"b\":40},{\"tag\":\"incompatible\",\"a\":58,\"b\":41},{\"tag\":\"incompatible\",\"a\":59,\"b\":6},{\"tag\":\"incompatible\",\"a\":59,\"b\":52},{\"tag\":\"incompatible\",\"a\":59,\"b\":53},{\"tag\":\"incompatible\",\"a\":59,\"b\":54},{\"tag\":\"incompatible\",\"a\":59,\"b\":55},{\"tag\":\"incompatible\",\"a\":59,\"b\":56},{\"tag\":\"incompatible\",\"a\":59,\"b\":57},{\"tag\":\"incompatible\",\"a\":59,\"b\":58},{\"tag\":\"incompatible\",\"a\":60,\"b\":9},{\"tag\":\"incompatible\",\"a\":60,\"b\":53},{\"tag\":\"incompatible\",\"a\":60,\"b\":56},{\"tag\":\"incompatible\",\"a\":60,\"b\":58},{\"tag\":\"incompatible\",\"a\":60,\"b\":59},{\"tag\":\"incompatible\",\"a\":61,\"b\":59},{\"tag\":\"incompatible\",\"a\":61,\"b\":60},{\"tag\":\"incompatible\",\"a\":66,\"b\":58},{\"tag\":\"incompatible\",\"a\":66,\"b\":65},{\"tag\":\"incompatible\",\"a\":67,\"b\":58},{\"tag\":\"incompatible\",\"a\":67,\"b\":65},{\"tag\":\"incompatible\",\"a\":67,\"b\":66},{\"tag\":\"incompatible\",\"a\":70,\"b\":18},{\"tag\":\"incompatible\",\"a\":70,\"b\":20},{\"tag\":\"incompatible\",\"a\":71,\"b\":19},{\"tag\":\"incompatible\",\"a\":71,\"b\":70},{\"tag\":\"incompatible\",\"a\":72,\"b\":51},{\"tag\":\"incompatible\",\"a\":72,\"b\":68},{\"tag\":\"incompatible\",\"a\":72,\"b\":71},{\"tag\":\"incompatible\",\"a\":73,\"b\":69},{\"tag\":\"incompatible\",\"a\":73,\"b\":70},{\"tag\":\"incompatible\",\"a\":74,\"b\":17},{\"tag\":\"incompatible\",\"a\":74,\"b\":19},{\"tag\":\"incompatible\",\"a\":74,\"b\":20},{\"tag\":\"incompatible\",\"a\":74,\"b\":68},{\"tag\":\"incompatible\",\"a\":74,\"b\":69},{\"tag\":\"incompatible\",\"a\":74,\"b\":70},{\"tag\":\"incompatible\",\"a\":74,\"b\":71},{\"tag\":\"incompatible\",\"a\":74,\"b\":72},{\"tag\":\"incompatible\",\"a\":74,\"b\":73},{\"tag\":\"incompatible\",\"a\":75,\"b\":17},{\"tag\":\"incompatible\",\"a\":75,\"b\":19},{\"tag\":\"incompatible\",\"a\":75,\"b\":68},{\"tag\":\"incompatible\",\"a\":75,\"b\":69},{\"tag\":\"incompatible\",\"a\":75,\"b\":70},{\"tag\":\"incompatible\",\"a\":75,\"b\":72},{\"tag\":\"incompatible\",\"a\":75,\"b\":74},{\"tag\":\"incompatible\",\"a\":76,\"b\":17},{\"tag\":\"incompatible\",\"a\":76,\"b\":18},{\"tag\":\"incompatible\",\"a\":76,\"b\":40},{\"tag\":\"incompatible\",\"a\":76,\"b\":41},{\"tag\":\"incompatible\",\"a\":76,\"b\":68},{\"tag\":\"incompatible\",\"a\":76,\"b\":69},{\"tag\":\"incompatible\",\"a\":76,\"b\":70},{\"tag\":\"incompatible\",\"a\":76,\"b\":71},{\"tag\":\"incompatible\",\"a\":76,\"b\":72},{\"tag\":\"incompatible\",\"a\":76,\"b\":73},{\"tag\":\"incompatible\",\"a\":76,\"b\":74},{\"tag\":\"incompatible\",\"a\":76,\"b\":75},{\"tag\":\"incompatible\",\"a\":78,\"b\":77},{\"tag\":\"incompatible\",\"a\":79,\"b\":45},{\"tag\":\"incompatible\",\"a\":79,\"b\":46},{\"tag\":\"incompatible\",\"a\":79,\"b\":47},{\"tag\":\"incompatible\",\"a\":79,\"b\":63},{\"tag\":\"incompatible\",\"a\":79,\"b\":72},{\"tag\":\"incompatible\",\"a\":79,\"b\":77},{\"tag\":\"incompatible\",\"a\":79,\"b\":78},{\"tag\":\"incompatible\",\"a\":80,\"b\":65},{\"tag\":\"incompatible\",\"a\":80,\"b\":72},{\"tag\":\"incompatible\",\"a\":81,\"b\":80},{\"tag\":\"incompatible\",\"a\":82,\"b\":73},{\"tag\":\"incompatible\",\"a\":82,\"b\":80},{\"tag\":\"incompatible\",\"a\":82,\"b\":81},{\"tag\":\"incompatible\",\"a\":83,\"b\":33},{\"tag\":\"incompatible\",\"a\":85,\"b\":31},{\"tag\":\"incompatible\",\"a\":86,\"b\":30},{\"tag\":\"incompatible\",\"a\":86,\"b\":85},{\"tag\":\"incompatible\",\"a\":87,\"b\":4},{\"tag\":\"incompatible\",\"a\":87,\"b\":40},{\"tag\":\"incompatible\",\"a\":87,\"b\":43},{\"tag\":\"incompatible\",\"a\":87,\"b\":49},{\"tag\":\"incompatible\",\"a\":87,\"b\":51},{\"tag\":\"incompatible\",\"a\":87,\"b\":52},{\"tag\":\"incompatible\",\"a\":87,\"b\":55},{\"tag\":\"incompatible\",\"a\":87,\"b\":68},{\"tag\":\"incompatible\",\"a\":87,\"b\":80},{\"tag\":\"incompatible\",\"a\":87,\"b\":85},{\"tag\":\"incompatible\",\"a\":87,\"b\":86},{\"tag\":\"incompatible\",\"a\":88,\"b\":85},{\"tag\":\"incompatible\",\"a\":89,\"b\":31},{\"tag\":\"incompatible\",\"a\":89,\"b\":86},{\"tag\":\"incompatible\",\"a\":89,\"b\":87},{\"tag\":\"incompatible\",\"a\":89,\"b\":88},{\"tag\":\"incompatible\",\"a\":90,\"b\":30},{\"tag\":\"incompatible\",\"a\":90,\"b\":85},{\"tag\":\"incompatible\",\"a\":90,\"b\":87},{\"tag\":\"incompatible\",\"a\":90,\"b\":89},{\"tag\":\"incompatible\",\"a\":91,\"b\":28},{\"tag\":\"incompatible\",\"a\":91,\"b\":29},{\"tag\":\"incompatible\",\"a\":91,\"b\":40},{\"tag\":\"incompatible\",\"a\":91,\"b\":41},{\"tag\":\"incompatible\",\"a\":91,\"b\":76},{\"tag\":\"incompatible\",\"a\":91,\"b\":83},{\"tag\":\"incompatible\",\"a\":91,\"b\":84},{\"tag\":\"incompatible\",\"a\":91,\"b\":85},{\"tag\":\"incompatible\",\"a\":91,\"b\":86},{\"tag\":\"incompatible\",\"a\":91,\"b\":87},{\"tag\":\"incompatible\",\"a\":91,\"b\":88},{\"tag\":\"incompatible\",\"a\":91,\"b\":89},{\"tag\":\"incompatible\",\"a\":91,\"b\":90},{\"tag\":\"incompatible\",\"a\":93,\"b\":83},{\"tag\":\"incompatible\",\"a\":93,\"b\":92},{\"tag\":\"incompatible\",\"a\":94,\"b\":63},{\"tag\":\"incompatible\",\"a\":94,\"b\":87},{\"tag\":\"incompatible\",\"a\":94,\"b\":92},{\"tag\":\"incompatible\",\"a\":94,\"b\":93},{\"tag\":\"incompatible\",\"a\":95,\"b\":65},{\"tag\":\"incompatible\",\"a\":95,\"b\":72},{\"tag\":\"incompatible\",\"a\":95,\"b\":87},{\"tag\":\"incompatible\",\"a\":96,\"b\":95},{\"tag\":\"incompatible\",\"a\":97,\"b\":88},{\"tag\":\"incompatible\",\"a\":97,\"b\":95},{\"tag\":\"incompatible\",\"a\":97,\"b\":96},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[17,18,19]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[17,18,72]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[18,19,68]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[18,20,69]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[29,30,83]},{\"tag\":\"mate\",\"ridge\":22,\"a\":94,\"owners\":[1,28,33,42,44,84,86]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[50,59,62]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[50,59,64]},{\"tag\":\"mate\",\"ridge\":133,\"a\":50,\"owners\":[18,22,74,78]},{\"tag\":\"mate\",\"ridge\":134,\"a\":50,\"owners\":[29,33,89,93]},{\"tag\":\"three\",\"ridge\":134,\"vertices\":[29,50,93]},{\"tag\":\"mate\",\"ridge\":259,\"a\":59,\"owners\":[4,15,43,51,63,66]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[49,58,63]},{\"tag\":\"mate\",\"ridge\":517,\"a\":5,\"owners\":[20,71,73,75,76]},{\"tag\":\"mate\",\"ridge\":517,\"a\":44,\"owners\":[20,73,75,76]},{\"tag\":\"mate\",\"ridge\":517,\"a\":47,\"owners\":[20,71,73,75,76]},{\"tag\":\"mate\",\"ridge\":517,\"a\":48,\"owners\":[20,71,75,76]},{\"tag\":\"mate\",\"ridge\":517,\"a\":50,\"owners\":[20,71,73,76]},{\"tag\":\"mate\",\"ridge\":517,\"a\":51,\"owners\":[20,71,73,75]},{\"tag\":\"mate\",\"ridge\":518,\"a\":5,\"owners\":[31,86,88,90,91]},{\"tag\":\"mate\",\"ridge\":518,\"a\":44,\"owners\":[31,88,90,91]},{\"tag\":\"mate\",\"ridge\":518,\"a\":47,\"owners\":[31,86,88,90,91]},{\"tag\":\"mate\",\"ridge\":518,\"a\":48,\"owners\":[31,86,90,91]},{\"tag\":\"mate\",\"ridge\":518,\"a\":50,\"owners\":[31,86,88,91]},{\"tag\":\"mate\",\"ridge\":518,\"a\":51,\"owners\":[31,86,88,90]},{\"tag\":\"mate\",\"ridge\":25,\"a\":82,\"owners\":[6,17,25,52,53,68,70]},{\"tag\":\"mate\",\"ridge\":26,\"a\":97,\"owners\":[6,28,36,52,53,83,85]},{\"tag\":\"mate\",\"ridge\":265,\"a\":9,\"owners\":[19,70,72,74,76]},{\"tag\":\"mate\",\"ridge\":265,\"a\":19,\"owners\":[9,53,56,58,59,61]},{\"tag\":\"mate\",\"ridge\":265,\"a\":56,\"owners\":[19,70,74,76]},{\"tag\":\"mate\",\"ridge\":265,\"a\":58,\"owners\":[19,70,72,74,76]},{\"tag\":\"mate\",\"ridge\":265,\"a\":59,\"owners\":[19,70,72,76]},{\"tag\":\"mate\",\"ridge\":265,\"a\":61,\"owners\":[19,70,72,74]},{\"tag\":\"mate\",\"ridge\":265,\"a\":76,\"owners\":[9,53,56,58,59]},{\"tag\":\"mate\",\"ridge\":266,\"a\":9,\"owners\":[30,85,87,89,91]},{\"tag\":\"mate\",\"ridge\":266,\"a\":53,\"owners\":[30,87,89,91]},{\"tag\":\"mate\",\"ridge\":266,\"a\":56,\"owners\":[30,85,89,91]},{\"tag\":\"mate\",\"ridge\":266,\"a\":58,\"owners\":[30,85,87,89,91]},{\"tag\":\"mate\",\"ridge\":266,\"a\":59,\"owners\":[30,85,87,91]},{\"tag\":\"mate\",\"ridge\":266,\"a\":61,\"owners\":[30,85,87,89]},{\"tag\":\"mate\",\"ridge\":266,\"a\":91,\"owners\":[9,53,56,58,59]},{\"tag\":\"mate\",\"ridge\":97,\"a\":66,\"owners\":[27,77,80]},{\"tag\":\"mate\",\"ridge\":97,\"a\":67,\"owners\":[27,77,80]},{\"tag\":\"mate\",\"ridge\":98,\"a\":66,\"owners\":[38,92,95]},{\"tag\":\"mate\",\"ridge\":98,\"a\":67,\"owners\":[38,92,95]},{\"tag\":\"mate\",\"ridge\":289,\"a\":72,\"owners\":[15,63,66]},{\"tag\":\"mate\",\"ridge\":577,\"a\":82,\"owners\":[16,48,67]},{\"tag\":\"mate\",\"ridge\":578,\"a\":97,\"owners\":[16,48,67]},{\"tag\":\"mate\",\"ridge\":28,\"a\":39,\"owners\":[17,28,68,69,70,71,83,84,85,86]},{\"tag\":\"mate\",\"ridge\":28,\"a\":68,\"owners\":[28,39,84,85,86]},{\"tag\":\"mate\",\"ridge\":28,\"a\":69,\"owners\":[28,39,83,85,86]},{\"tag\":\"mate\",\"ridge\":28,\"a\":70,\"owners\":[28,39,83,84,86]},{\"tag\":\"mate\",\"ridge\":28,\"a\":84,\"owners\":[17,39,68,70,71]},{\"tag\":\"mate\",\"ridge\":140,\"a\":18,\"owners\":[29,39,89,90]},{\"tag\":\"mate\",\"ridge\":140,\"a\":39,\"owners\":[18,29,74,75,89,90]},{\"tag\":\"mate\",\"ridge\":140,\"a\":74,\"owners\":[29,39,90]},{\"tag\":\"mate\",\"ridge\":140,\"a\":75,\"owners\":[29,39,89]},{\"tag\":\"mate\",\"ridge\":268,\"a\":19,\"owners\":[30,85,87,89,91]},{\"tag\":\"mate\",\"ridge\":268,\"a\":30,\"owners\":[19,70,72,74,76]},{\"tag\":\"mate\",\"ridge\":268,\"a\":70,\"owners\":[30,87,89,91]},{\"tag\":\"mate\",\"ridge\":268,\"a\":72,\"owners\":[30,85,89,91]},{\"tag\":\"mate\",\"ridge\":268,\"a\":74,\"owners\":[30,85,87,91]},{\"tag\":\"mate\",\"ridge\":268,\"a\":76,\"owners\":[30,85,87,89]},{\"tag\":\"mate\",\"ridge\":268,\"a\":85,\"owners\":[19,72,74,76]},{\"tag\":\"mate\",\"ridge\":268,\"a\":87,\"owners\":[19,70,74,76]},{\"tag\":\"mate\",\"ridge\":268,\"a\":89,\"owners\":[19,70,72,76]},{\"tag\":\"mate\",\"ridge\":268,\"a\":91,\"owners\":[19,70,72,74]},{\"tag\":\"mate\",\"ridge\":524,\"a\":20,\"owners\":[31,86,88,90,91]},{\"tag\":\"mate\",\"ridge\":524,\"a\":31,\"owners\":[20,71,73,75,76]},{\"tag\":\"mate\",\"ridge\":524,\"a\":73,\"owners\":[31,86,90,91]},{\"tag\":\"mate\",\"ridge\":524,\"a\":75,\"owners\":[31,86,88,91]},{\"tag\":\"mate\",\"ridge\":524,\"a\":76,\"owners\":[31,86,88,90]},{\"tag\":\"mate\",\"ridge\":524,\"a\":88,\"owners\":[20,71,75,76]},{\"tag\":\"mate\",\"ridge\":524,\"a\":90,\"owners\":[20,71,73,76]},{\"tag\":\"mate\",\"ridge\":524,\"a\":91,\"owners\":[20,71,73,75]},{\"tag\":\"group_take\",\"kind\":1,\"index\":15,\"member\":15,\"full_literals\":[-6,81]},{\"tag\":\"group_take\",\"kind\":1,\"index\":16,\"member\":16,\"full_literals\":[-7,82]},{\"tag\":\"group_take\",\"kind\":1,\"index\":22,\"member\":22,\"full_literals\":[-12,83]},{\"tag\":\"group_take\",\"kind\":1,\"index\":25,\"member\":25,\"full_literals\":[-13,84]},{\"tag\":\"group_take\",\"kind\":1,\"index\":27,\"member\":27,\"full_literals\":[-14,85]},{\"tag\":\"group_take\",\"kind\":1,\"index\":33,\"member\":33,\"full_literals\":[-19,86]},{\"tag\":\"group_take\",\"kind\":1,\"index\":36,\"member\":36,\"full_literals\":[-20,87]},{\"tag\":\"group_take\",\"kind\":1,\"index\":38,\"member\":38,\"full_literals\":[-21,88]},{\"tag\":\"merge\",\"left\":[15],\"right\":[16],\"left_name\":\"grouped1_0005\",\"right_name\":\"grouped1_0008\",\"joined_name\":\"grouped1_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-82,89],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15],\"right\":[16],\"left_name\":\"grouped1_0005\",\"right_name\":\"grouped1_0008\",\"joined_name\":\"grouped1_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-81,false,89],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16],\"right\":[17,18,19],\"left_name\":\"grouped1_0006\",\"right_name\":\"grouped1_0009\",\"joined_name\":\"grouped1_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-89,false,90],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-90,91],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9],\"right\":[10,11,12,13,14,15,16,17,18,19],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0004\",\"joined_name\":\"grouped1_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-91,92],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[22],\"right\":[23,24],\"left_name\":\"grouped1_0014\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-83,false,93],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20,21],\"right\":[22,23,24],\"left_name\":\"grouped1_0010\",\"right_name\":\"grouped1_0015\",\"joined_name\":\"grouped1_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-93,94],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[25],\"right\":[26],\"left_name\":\"grouped1_0017\",\"right_name\":\"grouped1_0020\",\"joined_name\":\"grouped1_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-84,false,95],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[27],\"right\":[28,29],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"grouped1_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-85,false,96],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[25,26],\"right\":[27,28,29],\"left_name\":\"grouped1_0018\",\"right_name\":\"grouped1_0022\",\"joined_name\":\"grouped1_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-96,97],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[25,26],\"right\":[27,28,29],\"left_name\":\"grouped1_0018\",\"right_name\":\"grouped1_0022\",\"joined_name\":\"grouped1_0019\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-95,-96,98],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20,21,22,23,24],\"right\":[25,26,27,28,29],\"left_name\":\"grouped1_0011\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-97,99],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20,21,22,23,24],\"right\":[25,26,27,28,29],\"left_name\":\"grouped1_0011\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0012\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-94,-98,100],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[33],\"right\":[34],\"left_name\":\"grouped1_0029\",\"right_name\":\"grouped1_0031\",\"joined_name\":\"grouped1_0030\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-86,false,101],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[32],\"right\":[33,34],\"left_name\":\"grouped1_0027\",\"right_name\":\"grouped1_0030\",\"joined_name\":\"grouped1_0028\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-101,102],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[30,31],\"right\":[32,33,34],\"left_name\":\"grouped1_0024\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0025\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-102,103],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[35],\"right\":[36],\"left_name\":\"grouped1_0032\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0033\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-87,104],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[38],\"right\":[39],\"left_name\":\"grouped1_0038\",\"right_name\":\"grouped1_0040\",\"joined_name\":\"grouped1_0039\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-88,false,105],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[37],\"right\":[38,39],\"left_name\":\"grouped1_0036\",\"right_name\":\"grouped1_0039\",\"joined_name\":\"grouped1_0037\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-105,106],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[35,36],\"right\":[37,38,39],\"left_name\":\"grouped1_0033\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0034\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-106,107],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[35,36],\"right\":[37,38,39],\"left_name\":\"grouped1_0033\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0034\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-104,-106,108],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[30,31,32,33,34],\"right\":[35,36,37,38,39],\"left_name\":\"grouped1_0025\",\"right_name\":\"grouped1_0034\",\"joined_name\":\"grouped1_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-107,109],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[30,31,32,33,34],\"right\":[35,36,37,38,39],\"left_name\":\"grouped1_0025\",\"right_name\":\"grouped1_0034\",\"joined_name\":\"grouped1_0026\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-103,-108,110],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20,21,22,23,24,25,26,27,28,29],\"right\":[30,31,32,33,34,35,36,37,38,39],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0013\",\"a\":1,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-99,-110,111],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20,21,22,23,24,25,26,27,28,29],\"right\":[30,31,32,33,34,35,36,37,38,39],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0013\",\"a\":3,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-100,-109,111],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19],\"right\":[20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"groupKind1\",\"a\":1,\"b\":4,\"direction\":\"forward\",\"full_literals\":[-92,-111,112],\"grouped\":true,\"kind\":1},{\"tag\":\"quota_upper\",\"kind\":1,\"quota\":4,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[45,47,63,66,67],\"full_literals\":[-113,28,30,46,49,50]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[42,43,44,46,62,78,93],\"full_literals\":[-114,25,26,27,29,45,61,76]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[52,53,54,57,64,81,96],\"full_literals\":[-115,35,36,37,40,47,64,79]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[40,41,49,59,74,89],\"full_literals\":[-116,23,24,32,42,57,72]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[50,60,75,90],\"full_literals\":[-117,33,43,58,73]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[70,79,85,94],\"full_literals\":[-118,53,62,68,77]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[55,58,65,82,97],\"full_literals\":[-119,38,41,48,65,80]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[51,61,76,91],\"full_literals\":[-120,34,44,59,74]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[48,69,73,77,84,88,92],\"full_literals\":[-121,31,52,56,60,67,71,75]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[56,68,72,80,83,87,95],\"full_literals\":[-122,39,51,55,63,66,70,78]},{\"tag\":\"group_or\",\"kind\":2,\"index\":10,\"members\":[71,86],\"full_literals\":[-123,54,69]},{\"tag\":\"group_take\",\"kind\":2,\"index\":10,\"member\":71,\"full_literals\":[-54,123]},{\"tag\":\"group_take\",\"kind\":2,\"index\":10,\"member\":86,\"full_literals\":[-69,123]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0042\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-124,113,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0042\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-124,false,114],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0048\",\"right_name\":\"grouped2_0050\",\"joined_name\":\"grouped2_0049\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-125,116,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0048\",\"right_name\":\"grouped2_0050\",\"joined_name\":\"grouped2_0049\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-125,false,117],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0047\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-126,115,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0047\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-126,false,125],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0042\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0043\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-127,124,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0042\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0043\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-127,false,126],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0054\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0055\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-128,119,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0054\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0055\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-128,false,120],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0055\",\"joined_name\":\"grouped2_0052\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-129,118,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0055\",\"joined_name\":\"grouped2_0052\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-129,false,128],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped2_0059\",\"right_name\":\"grouped2_0061\",\"joined_name\":\"grouped2_0060\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-130,122,123],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped2_0059\",\"right_name\":\"grouped2_0061\",\"joined_name\":\"grouped2_0060\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-131,false,123],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0060\",\"joined_name\":\"grouped2_0058\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-132,121,131],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0060\",\"joined_name\":\"grouped2_0058\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-132,false,130],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0060\",\"joined_name\":\"grouped2_0058\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-133,false,131],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0053\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-134,129,133],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0053\",\"a\":3,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-134,false,132],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0053\",\"a\":3,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-135,false,133],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped2_0043\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-136,127,135],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped2_0043\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-136,false,134],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":10,\"grouped\":true},{\"tag\":\"edge\",\"edge\":23,\"owners\":[5,20,31,44,47,48,50,51,71,73,75,76,86,88,90,91]},{\"tag\":\"edge\",\"edge\":28,\"owners\":[9,19,30,53,56,58,59,61,70,72,74,76,85,87,89,91]}]}"
  "286 134 0 283 282 0\n287 132 0 286 279 0\n288 130 0 287 276 0\n289 31 7 41 48 38 50 -119 0 184 185 254 0\n290 68 74 5 10 39 17 41 42 44 53 55 59 57 70 72 0 285 173 0\n291 -55 -123 0 43 258 90 91 105 120 198 0\n292 -69 55 0 90 91 102 105 120 172 195 175 176 177 199 200 197 174 290 0\n293 -123 0 291 292 258 39 40 52 69 202 168 169 170 196 203 204 165 201 167 290 0\n294 -54 0 293 259 0\n295 -69 0 293 260 0\n296 -131 0 293 274 0\n297 122 0 293 288 273 0\n298 -133 0 296 277 0\n299 121 0 296 287 275 0\n300 -135 0 298 280 0\n301 129 0 298 286 278 0\n302 127 0 300 283 281 0\n303 118 0 301 271 0\n304 128 0 301 272 0\n305 124 0 302 267 0\n306 126 0 302 268 0\n307 119 0 304 269 0\n308 120 0 304 270 0\n309 113 0 305 261 0\n310 114 0 305 262 0\n311 115 0 306 265 0\n312 125 0 306 266 0\n313 116 0 312 263 0\n314 117 0 312 264 0\n315 17 68 72 74 70 41 0 172 195 198 176 177 199 200 197 174 290 0\n316 -53 59 73 74 0 295 294 38 45 59 151 153 155 156 210 152 154 206 284 0\n317 59 10 55 -17 74 0 295 294 108 316 196 48 54 61 151 153 155 156 210 152 154 206 284 0\n318 -43 -59 41 0 25 26 27 29 171 0\n319 -65 66 47 40 39 37 36 35 51 55 70 0 297 311 86 87 257 250 134 0\n320 -80 66 47 40 39 37 36 35 51 55 70 0 297 311 136 137 257 250 84 0\n321 66 47 40 39 38 37 36 35 51 55 70 41 0 307 297 319 320 254 82 131 257 0\n322 -59 55 -17 72 70 41 0 314 313 108 64 65 66 72 73 318 252 13 251 18 19 20 21 22 23 145 321 88 125 142 147 0\n323 -33 57 59 72 74 0 313 308 4 5 13 14 251 255 30 0\n324 55 -17 72 74 70 41 0 314 108 322 317 47 56 323 252 25 26 27 29 31 166 0\n325 -17 72 74 70 41 0 308 314 108 324 41 53 60 70 255 323 31 252 0\n326 18 71 74 73 0 294 295 157 160 205 159 162 207 208 158 209 161 284 0\n327 -68 74 0 89 103 109 326 0\n328 72 74 70 41 0 327 325 315 0\n329 74 70 41 0 328 104 107 326 111 0\n330 -43 -74 41 0 25 26 27 29 178 0\n331 -58 -74 0 295 294 123 119 118 117 113 112 55 57 58 59 194 186 0\n332 -22 52 53 51 32 58 73 72 68 67 66 59 24 23 16 15 0 295 294 313 186 46 192 251 138 139 169 0\n333 -48 46 -33 0 309 11 9 33 35 248 0\n334 50 -104 -103 60 75 46 78 63 38 -33 41 0 309 307 247 333 12 11 9 248 289 179 181 214 217 220 221 229 238 223 230 239 224 232 241 225 243 246 244 0\n335 52 53 51 70 41 0 314 313 303 295 310 299 307 247 329 330 124 331 252 13 12 10 8 7 6 3 123 122 119 118 117 116 115 114 113 112 332 193 251 17 18 19 20 21 22 23 144 145 321 79 83 132 253 127 129 130 143 249 218 74 234 256 235 85 236 333 254 164 219 237 334 36 180 182 183 217 220 213 229 238 222 230 239 223 232 241 224 243 225 244 246 0\n336 -52 -74 0 295 294 331 124 123 119 117 113 112 44 50 188 212 192 141 0\n337 -53 -74 0 295 331 124 123 118 117 113 112 37 51 189 192 0\n338 70 41 0 295 329 112 113 118 119 123 124 331 336 337 335 42 49 187 204 192 140 0\n339 57 -22 16 58 -70 0 308 314 121 110 106 96 192 63 255 323 31 252 0\n340 -57 58 -70 0 294 121 110 48 54 72 210 206 326 0\n341 59 58 -70 0 308 314 340 121 110 106 96 255 323 31 252 0\n342 -50 -95 -94 75 60 46 -42 -70 0 247 133 100 96 94 92 36 180 182 149 217 220 213 229 238 222 231 239 223 233 240 224 242 225 245 246 0\n343 16 58 41 0 313 310 314 303 294 299 309 307 247 338 101 128 341 68 253 81 76 110 318 252 8 94 6 106 95 93 340 65 251 144 249 126 78 333 12 80 77 75 19 17 71 67 62 133 100 99 98 97 339 191 190 146 215 226 256 227 135 254 163 216 228 342 248 289 179 181 214 217 220 221 229 238 223 231 239 224 233 240 225 242 246 245 0\n344 58 41 0 313 303 314 310 338 128 110 106 101 95 94 93 340 341 65 68 318 251 253 252 144 76 81 6 8 249 343 148 0\n345 41 0 338 344 56 59 61 73 202 0\n346 -23 0 345 15 0\n347 -24 0 345 16 0\n348 -42 0 345 24 0\n349 -43 0 345 28 0\n350 -49 0 345 32 0\n351 -50 0 345 34 0\n352 -32 0 345 309 350 351 1 2 150 248 0\n353 -72 0 104 107 111 123 326 0\n354 57 0 353 347 313 346 348 352 251 0\n355 -11 0 354 48 0\n356 -56 0 354 54 0\n357 -58 0 354 61 0\n358 -59 0 354 72 0\n359 -73 0 355 294 356 358 211 0\n360 -33 0 356 294 355 358 155 0\n361 0 360 357 359 349 314 252 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record005.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record005.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00030.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00030.record006
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "99966958d61db0ea398e93a2e2b86e8791e1783e99565954d51d70da358d9362d2b46d8751d1743d98d6394cd31cf0ba2d8b92e2b2ac6b86d1b16c3bc1e8761d4731e2729e1745c3713d2c2712a26a4649866258568390e2382e079292664549465254558350d2342d0764348c6324c5382d0b22c2b06e0741c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "12492492492492492492492492492492492492492492449249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record006 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record006 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record006.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 43), (facetIndex 44), (facetIndex 45), (facetIndex 46), (facetIndex 47), (facetIndex 48), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 52), (facetIndex 53)]))
 (.leaf ([(facetIndex 66), (facetIndex 82), (facetIndex 98)])))
 (.branch 3
 (.leaf ([(facetIndex 58), (facetIndex 65), (facetIndex 67), (facetIndex 68), (facetIndex 69)]))
 (.leaf ([(facetIndex 54), (facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 59), (facetIndex 60), (facetIndex 61), (facetIndex 62), (facetIndex 63), (facetIndex 64)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 70), (facetIndex 71), (facetIndex 72), (facetIndex 73), (facetIndex 74), (facetIndex 75), (facetIndex 76), (facetIndex 77), (facetIndex 78), (facetIndex 79), (facetIndex 80)]))
 (.leaf ([(facetIndex 86), (facetIndex 87), (facetIndex 88), (facetIndex 89), (facetIndex 90), (facetIndex 91), (facetIndex 92), (facetIndex 93), (facetIndex 94), (facetIndex 95), (facetIndex 96)])))
 (.branch 7
 (.leaf ([(facetIndex 81), (facetIndex 83), (facetIndex 84), (facetIndex 85)]))
 (.leaf ([(facetIndex 97), (facetIndex 99), (facetIndex 100), (facetIndex 101)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "3fe7db6db6db76c749249249124536db69b6cz28;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record006 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record006_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00030.record006" "{\"atoms\":[]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00030.record006" 0

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00030.record006" "{\"ridges\":[],\"owners\":[],\"edges\":[],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00030.record006" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00030.record006\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[]],\"atoms\":[],\"rules\":[{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":10,\"grouped\":true}]}"
  "2 0 1 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record006.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record006.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record006.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record006.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record006 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record006.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record006.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record006.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record006.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record006 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record006_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record006 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record006_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record006_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00030.record006
