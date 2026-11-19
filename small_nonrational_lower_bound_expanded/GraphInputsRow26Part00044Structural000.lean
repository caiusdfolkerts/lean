module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow26Part00044Data
public import GraphInputsRow26Part00044Frames
public import GraphInputsRow26Part00044Leaves
public import GraphInputsRow26Part00044Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00044.record057
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record057
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 11529215595824283648, (certNat% 3), (certNat% 4), 1237084798976]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), 704374636544, (certNat% 6), (certNat% 7)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 8), (certNat% 9), (certNat% 10)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), (certNat% 12), 569083166720, (certNat% 13)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), 706522120192, (certNat% 3), (certNat% 15), (certNat% 16)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), (certNat% 18), 403701760, 2308094809027379200, (certNat% 19)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), (certNat% 21), (certNat% 22), 108086391073669120, 140737488355328]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), (certNat% 24), 704374636544, (certNat% 15), 9223372105574252544]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), 108086391073669120, (certNat% 27), 140737488355328]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), 154618822656, (certNat% 19), (certNat% 29)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 30), (certNat% 31), (certNat% 32)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c3 c15
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c3 c16
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), 2251799813685248, (certNat% 34), 154618822656]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 35), (certNat% 36), 9223372603790458880, (certNat% 13), 137438953472]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c21 c14
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), 108086391056891904, (certNat% 38), (certNat% 39), (certNat% 40)]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 41), 137573171200, 2251799814733824, 108086391107223552, (certNat% 42)]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 43), 2308094809028427776, 108086391107223552, (certNat% 44)]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 45), (certNat% 13), (certNat% 46), 687194767360]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 47), (certNat% 44), (certNat% 46), (certNat% 13), 108086391107223552, 687194767360]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨20, by decide⟩ c27 c26
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c28 c25
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c29 c24
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c30 c23
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c31 c22
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c32 c13
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c33 c12
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c34 c11
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c35 c10
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c36 c9
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨17, by decide⟩ c37 c0
  c38
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record057_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record057_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record057_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record057_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record057_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record057_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record057_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record057_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record057_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00044.record057

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00044.record001
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1ac5aaa699a96958b61da8e9392e2b86e4789e17ae1b44f1b25a95a4e9366a569665a56552d475a358d9352d2b46d4745da8e6358e9394cb31ce8b92d4b4acab1ad1b26f07a1e4789ca719e1745c9715c3783c8f13c2f2705a4990e0789916685494a52550d2341d90d2318c5342c4b06e0741c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db6da6d24db6db4934d349a4d26934d3493492492492492489249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record001 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record001 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record001.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record001.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record001.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 41), (facetIndex 42), (facetIndex 56), (facetIndex 57), (facetIndex 71)]))
 (.branch 2
 (.leaf ([(facetIndex 26), (facetIndex 43), (facetIndex 45), (facetIndex 59), (facetIndex 60), (facetIndex 84)]))
 (.leaf ([(facetIndex 79), (facetIndex 80), (facetIndex 81)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 46), (facetIndex 47), (facetIndex 49), (facetIndex 51), (facetIndex 53), (facetIndex 54)]))
 (.leaf ([(facetIndex 62), (facetIndex 63), (facetIndex 65), (facetIndex 67), (facetIndex 69), (facetIndex 70)])))
 (.branch 6
 (.leaf ([(facetIndex 27), (facetIndex 29), (facetIndex 30), (facetIndex 31), (facetIndex 33), (facetIndex 34), (facetIndex 35), (facetIndex 37), (facetIndex 38), (facetIndex 40)]))
 (.leaf ([(facetIndex 28), (facetIndex 32), (facetIndex 36), (facetIndex 39)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "10124000001208209012000d86186c8205d6eb6eb6ea4z13;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1, 2]
def grouped2_0003 : List Nat := [1]
def grouped2_0004 : List Nat := [1, 2]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [3, 4]
def grouped2_0007 : List Nat := [3, 4, 5, 6]
def grouped2_0008 : List Nat := [5]
def grouped2_0009 : List Nat := [5, 6]
def grouped2_0010 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record001 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record001_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00044.record001" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00044.record001" 38

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00044.record001" "{\"ridges\":[[11,577],[18,641],[38,578],[39,644],[47,577],[48,650],[51,577],[54,577],[75,712],[77,720],[78,736]],\"owners\":[[11,577,[61,66,68,75,77,78],[38,47,51,54]],[47,577,[66,68,77,78],[11,38,51,54,61,75]],[51,577,[61,68,75,78],[11,38,47,54,66,77]],[54,577,[61,66,75,77],[11,38,47,51,68,78]],[38,578,[],[11,47,51,54,85,89,91]],[18,641,[48,52,55,75,77,78],[39,63,67,70]],[39,644,[],[18,63,67,70,86,90,92]],[48,650,[86],[]],[75,712,[],[]],[77,720,[],[]],[78,736,[],[]]],\"edges\":[[41,[11,38,47,51,54,61,66,68,75,77,78,85,89,91]],[43,[18,39,48,52,55,63,67,70,75,77,78,86,90,92]]],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00044.record001" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00044.record001\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-9,-5],[-11,-4],[-11,-5],[-13,-4],[-13,-5],[-15,-4],[-15,-5],[-17,-4],[-17,-5],[-19,-4],[-19,-5],[-23,-14],[-23,-16],[-23,-18],[-24,-3],[-24,-4],[-25,-3],[-26,-23],[-27,-5],[-27,-25],[-28,-23],[-29,-4],[-29,-5],[-30,-23],[-31,-4],[-31,-5],[-1,14,16,18,20,21,22],[-8,16,18,21,22],[-10,14,18,20,22],[-12,14,16,20,21],[-6],[-2,9,11,13,20,21,22],[-7],[-9,27],[-20],[-21],[-22],[-32,23,24,25],[-33,3,4,5,7],[-34,32],[-35,34],[-36,33],[-37,36],[-38,35],[-38,37],[38],[1,6,8,10,12,14,16,18,20,21,22,26,28,30],[2,7,9,11,13,15,17,19,20,21,22,27,29,31]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":48,\"b\":36},{\"tag\":\"incompatible\",\"a\":52,\"b\":32},{\"tag\":\"incompatible\",\"a\":52,\"b\":36},{\"tag\":\"incompatible\",\"a\":55,\"b\":32},{\"tag\":\"incompatible\",\"a\":55,\"b\":36},{\"tag\":\"incompatible\",\"a\":63,\"b\":32},{\"tag\":\"incompatible\",\"a\":63,\"b\":36},{\"tag\":\"incompatible\",\"a\":67,\"b\":32},{\"tag\":\"incompatible\",\"a\":67,\"b\":36},{\"tag\":\"incompatible\",\"a\":70,\"b\":32},{\"tag\":\"incompatible\",\"a\":70,\"b\":36},{\"tag\":\"incompatible\",\"a\":79,\"b\":61},{\"tag\":\"incompatible\",\"a\":79,\"b\":66},{\"tag\":\"incompatible\",\"a\":79,\"b\":68},{\"tag\":\"incompatible\",\"a\":80,\"b\":28},{\"tag\":\"incompatible\",\"a\":80,\"b\":32},{\"tag\":\"incompatible\",\"a\":81,\"b\":28},{\"tag\":\"incompatible\",\"a\":85,\"b\":79},{\"tag\":\"incompatible\",\"a\":86,\"b\":36},{\"tag\":\"incompatible\",\"a\":86,\"b\":81},{\"tag\":\"incompatible\",\"a\":89,\"b\":79},{\"tag\":\"incompatible\",\"a\":90,\"b\":32},{\"tag\":\"incompatible\",\"a\":90,\"b\":36},{\"tag\":\"incompatible\",\"a\":91,\"b\":79},{\"tag\":\"incompatible\",\"a\":92,\"b\":32},{\"tag\":\"incompatible\",\"a\":92,\"b\":36},{\"tag\":\"mate\",\"ridge\":577,\"a\":11,\"owners\":[61,66,68,75,77,78]},{\"tag\":\"mate\",\"ridge\":577,\"a\":47,\"owners\":[66,68,77,78]},{\"tag\":\"mate\",\"ridge\":577,\"a\":51,\"owners\":[61,68,75,78]},{\"tag\":\"mate\",\"ridge\":577,\"a\":54,\"owners\":[61,66,75,77]},{\"tag\":\"mate\",\"ridge\":578,\"a\":38,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":641,\"a\":18,\"owners\":[48,52,55,75,77,78]},{\"tag\":\"mate\",\"ridge\":644,\"a\":39,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":650,\"a\":48,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":712,\"a\":75,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":720,\"a\":77,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":736,\"a\":78,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[79,80,81],\"full_literals\":[-32,23,24,25]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[28,32,36,39],\"full_literals\":[-33,3,4,5,7]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-34,false,32],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-35,false,34],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-36,false,33],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-37,false,36],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-38,35,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-38,false,37],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"edge\",\"edge\":41,\"owners\":[11,38,47,51,54,61,66,68,75,77,78,85,89,91]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[18,39,48,52,55,63,67,70,75,77,78,86,90,92]}]}"
  "49 -33 3 4 5 0 33 39 0\n50 35 0 46 44 0\n51 37 0 46 45 0\n52 34 0 50 41 0\n53 36 0 51 43 0\n54 32 0 52 40 0\n55 33 0 53 42 0\n56 1 8 10 12 14 16 18 26 28 30 0 31 35 36 37 47 0\n57 2 9 11 13 15 17 19 27 29 31 0 33 35 36 37 48 0\n58 -24 5 0 55 15 16 49 0\n59 -4 27 0 37 36 35 34 2 4 6 8 10 22 25 32 57 0\n60 -25 0 55 37 36 35 17 20 34 59 49 3 5 7 9 11 23 26 32 57 0\n61 -5 0 37 36 35 1 3 5 7 9 11 19 23 26 32 57 0\n62 -24 0 61 58 0\n63 23 0 62 54 60 38 0\n64 -14 0 63 12 0\n65 -16 0 63 13 0\n66 -18 0 63 14 0\n67 -26 0 63 18 0\n68 -28 0 63 21 0\n69 -30 0 63 24 0\n70 -8 0 65 66 36 37 28 0\n71 -12 0 65 64 35 36 30 0\n72 -10 0 66 64 35 37 29 0\n73 -1 0 66 65 64 35 36 37 27 0\n74 0 70 72 73 71 64 65 66 67 68 69 56 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record001.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record001.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record001.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record001.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record001 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record001.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record001.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record001.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record001.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record001 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record001_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record001 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record001_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record001_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00044.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00044.record039
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "15c4f07caa95a4e8ba1eac665956359362d8765392e1b91e1783eb46a9a6659565392e479b1595554d54d4755352d1b51d1743db0ea364d5334d332cc73c2e8b52e2b4acab1ad1b26c5b0ee8761e4751cc749c6745c9715c3743c4f0bc1f2d24a298b1925191643929515254550d68390ca382d0b12c2b41c8711c27"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db6db6d36db6db69249a4926da4926db4d249249a492492492493249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record039 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record039 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record039.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record039.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record039.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 40), (facetIndex 59), (facetIndex 70), (facetIndex 72), (facetIndex 73), (facetIndex 74)]))
 (.branch 2
 (.leaf ([(facetIndex 28), (facetIndex 29), (facetIndex 30), (facetIndex 31), (facetIndex 39), (facetIndex 42), (facetIndex 51), (facetIndex 85)]))
 (.leaf ([(facetIndex 38), (facetIndex 48), (facetIndex 56), (facetIndex 57)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 44), (facetIndex 71)]))
 (.leaf ([(facetIndex 58), (facetIndex 60), (facetIndex 64), (facetIndex 65), (facetIndex 66), (facetIndex 67), (facetIndex 68)])))
 (.branch 6
 (.leaf ([(facetIndex 25), (facetIndex 26), (facetIndex 27), (facetIndex 43), (facetIndex 45), (facetIndex 46), (facetIndex 47), (facetIndex 49)]))
 (.leaf ([(facetIndex 32), (facetIndex 33), (facetIndex 34), (facetIndex 35), (facetIndex 36), (facetIndex 37)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "800000000060492400411200022ab6ba402b6db6249b68z12;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1, 2]
def grouped2_0003 : List Nat := [1]
def grouped2_0004 : List Nat := [1, 2]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [3]
def grouped2_0007 : List Nat := [3, 4]
def grouped2_0008 : List Nat := [3, 4, 5, 6]
def grouped2_0009 : List Nat := [4]
def grouped2_0010 : List Nat := [5, 6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record039 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record039_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00044.record039" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00044.record039" 48

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00044.record039" "{\"ridges\":[[10,642],[18,25],[31,273],[38,642],[42,25],[48,642],[56,642],[57,642],[60,25],[67,273],[68,273],[69,708],[71,25],[74,25],[75,664],[76,680],[77,720],[90,708]],\"owners\":[[10,642,[90,95],[38,48,56,57]],[38,642,[95],[10,48,56,57,90]],[48,642,[90],[10,38,56,57,95]],[56,642,[90],[10,38,48,57,95]],[57,642,[95],[10,38,48,56,90]],[31,273,[18,72,73],[14,42,52,54,55,65,67,68]],[67,273,[18,42,52,55,72],[14,31,54,65,68,73]],[68,273,[18,42,52,54,72,73],[14,31,55,65,67]],[69,708,[90],[]],[90,708,[69],[]],[75,664,[],[]],[76,680,[95],[]],[77,720,[],[]]],\"edges\":[[43,[10,38,48,56,57,69,75,76,77,90,95]]],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00044.record039" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00044.record039\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-9,-6],[-10,-9],[-12,-11],[-17,-11],[-17,-13],[-17,-16],[-21,-20],[-25,-20],[-26,-20],[-27,-4],[-27,-5],[-29,-3],[-29,-8],[-29,-12],[-29,-14],[-29,-19],[-29,-22],[-29,-23],[-29,-28],[-30,-29],[-31,-29],[-36,-9],[-36,-15],[-37,-24],[-38,-11],[-38,-29],[-1,37,38],[-7,38],[-12,37],[-17,37],[-18,38],[-6,2,30,31],[-25,2,10,14,16,30],[-26,2,10,14,15,30,31],[-2,-29,-32],[-10,-29,-32],[-21,-29,-32],[-27,37],[-37,27],[-33],[-34,38],[-35],[-39,9,20,28,30,31,32],[-40,3,4,5,6,8,10,13,36],[-41,7,12,17,18],[-42,11,29],[-43,19,21,22,23,24,25,26],[-44,40],[-44,41],[-45,39],[-45,44],[-46,42],[-46,43],[-47,46],[-48,45],[-48,47],[48],[1,7,12,17,18,27,33,34,35,37,38]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":40,\"b\":31},{\"tag\":\"incompatible\",\"a\":42,\"b\":40},{\"tag\":\"incompatible\",\"a\":48,\"b\":44},{\"tag\":\"incompatible\",\"a\":56,\"b\":44},{\"tag\":\"incompatible\",\"a\":56,\"b\":51},{\"tag\":\"incompatible\",\"a\":56,\"b\":55},{\"tag\":\"incompatible\",\"a\":60,\"b\":59},{\"tag\":\"incompatible\",\"a\":67,\"b\":59},{\"tag\":\"incompatible\",\"a\":68,\"b\":59},{\"tag\":\"incompatible\",\"a\":69,\"b\":29},{\"tag\":\"incompatible\",\"a\":69,\"b\":30},{\"tag\":\"incompatible\",\"a\":71,\"b\":28},{\"tag\":\"incompatible\",\"a\":71,\"b\":39},{\"tag\":\"incompatible\",\"a\":71,\"b\":48},{\"tag\":\"incompatible\",\"a\":71,\"b\":52},{\"tag\":\"incompatible\",\"a\":71,\"b\":58},{\"tag\":\"incompatible\",\"a\":71,\"b\":64},{\"tag\":\"incompatible\",\"a\":71,\"b\":65},{\"tag\":\"incompatible\",\"a\":71,\"b\":70},{\"tag\":\"incompatible\",\"a\":72,\"b\":71},{\"tag\":\"incompatible\",\"a\":73,\"b\":71},{\"tag\":\"incompatible\",\"a\":85,\"b\":40},{\"tag\":\"incompatible\",\"a\":85,\"b\":54},{\"tag\":\"incompatible\",\"a\":90,\"b\":66},{\"tag\":\"incompatible\",\"a\":95,\"b\":44},{\"tag\":\"incompatible\",\"a\":95,\"b\":71},{\"tag\":\"mate\",\"ridge\":642,\"a\":10,\"owners\":[90,95]},{\"tag\":\"mate\",\"ridge\":642,\"a\":38,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":642,\"a\":48,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":642,\"a\":56,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":642,\"a\":57,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":273,\"a\":31,\"owners\":[18,72,73]},{\"tag\":\"mate\",\"ridge\":273,\"a\":67,\"owners\":[18,42,52,55,72]},{\"tag\":\"mate\",\"ridge\":273,\"a\":68,\"owners\":[18,42,52,54,72,73]},{\"tag\":\"three\",\"ridge\":25,\"vertices\":[18,71,74]},{\"tag\":\"three\",\"ridge\":25,\"vertices\":[42,71,74]},{\"tag\":\"three\",\"ridge\":25,\"vertices\":[60,71,74]},{\"tag\":\"mate\",\"ridge\":708,\"a\":69,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":708,\"a\":90,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":664,\"a\":75,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":680,\"a\":76,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":720,\"a\":77,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[40,59,70,72,73,74],\"full_literals\":[-39,9,20,28,30,31,32]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[28,29,30,31,39,42,51,85],\"full_literals\":[-40,3,4,5,6,8,10,13,36]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[38,48,56,57],\"full_literals\":[-41,7,12,17,18]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[44,71],\"full_literals\":[-42,11,29]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[58,60,64,65,66,67,68],\"full_literals\":[-43,19,21,22,23,24,25,26]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-44,40,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-44,false,41],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-45,39,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-45,false,44],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-46,42,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-46,false,43],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-47,46,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-48,45,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-48,false,47],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"edge\",\"edge\":43,\"owners\":[10,38,48,56,57,69,75,76,77,90,95]}]}"
  "59 45 0 57 55 0\n60 47 0 57 56 0\n61 39 0 59 50 0\n62 44 0 59 51 0\n63 46 0 60 54 0\n64 40 0 62 48 0\n65 41 0 62 49 0\n66 42 0 63 52 0\n67 43 0 63 53 0\n68 1 7 12 17 18 27 34 37 38 0 40 42 58 0\n69 37 38 0 27 29 30 38 28 31 41 68 0\n70 -12 0 66 3 14 46 0\n71 -9 38 0 70 65 66 64 31 28 45 4 46 13 12 5 69 39 11 10 1 2 22 44 0\n72 -20 38 0 70 65 66 67 31 28 45 4 46 18 17 16 69 24 7 8 9 47 0\n73 38 0 65 70 66 61 64 67 28 31 69 24 39 10 11 45 4 5 6 46 12 13 15 16 17 18 19 20 21 71 72 43 35 36 37 33 32 44 47 23 34 0\n74 -11 0 73 25 0\n75 -29 0 73 26 0\n76 0 74 75 66 46 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record039.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record039.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record039.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record039.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record039 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record039.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record039.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record039.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record039.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record039 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record039_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record039_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record039_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record039_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record039_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record039_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record039_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record039 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record039_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record039_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record039_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00044.record039
