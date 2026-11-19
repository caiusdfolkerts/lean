module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow16Part00030Data
public import GraphInputsRow16Part00030Frames
public import GraphInputsRow16Part00030Leaves
public import GraphInputsRow16Part00030Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00030.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record006
def vertexColumn : Fields := ⟨10, hexnat% "9b19c4f26a668ba999969598e93a2e1b91e2783e665392e665656558d5356354d4b46d4749d0f66364e538ccb362ccb2ac6b46c9b0ed8791e2719e1745c9715d0f23c1f8d23291a26858361382e64589454354344d0b4930cc8b12c2b11c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db4d34936936d34924934d349249a4d2492492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [6918285327207497728, 16888498602639360, 54043196602187776, 144115188075855872, hexnat% "8e0000000000000000", hexnat% "200000000208000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ae6226a25bff000000", 1649267441664, 6755399441055744, 13194139533312, 54043195528445952]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ae6004804bff000000", 36037593111986176, 3917010173952, 16325548649218048, 39582418599936, 162129586585337856]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ae6082881bc9000000", 4123269267456, 39583223906304, 16888498602639360, 162129586585337856]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ae42ce804bff000000", 13194139533312, 13510798882111488, 3917010173952, 2305878193585782784]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8e42c6ae4bff000000", hexnat% "200000000000000000", 1717986918400, 15762598695796736, 2305843009213693952]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8e627e03dbb7000000", 39582418599936, 36169534507319296, hexnat% "200000000048000000", 8796093022208]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ae4064004bef000000", 3917010173952, 7459086882832384, 36037593111986176, 2449993381661638656, 4398314946560]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ae4000000880000000", 36037607070629888, 4191921635328, 2449993381661638656, 17451448623169536, 4399002812416, 18155135997837312]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c13 c4
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c14 c3
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00030.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00030.record018
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record018
def vertexColumn : Fields := ⟨10, hexnat% "9e25c1f2726aa6a96a3a1e99695876a3a4e1ba1e1783e5c5a996479656551d64d3346d8745d0f5a364e531cd8b92d2b2ac6b86c5b0ed8791c6785d1725c570de0f13c2f07e549313285a0e239311c4691548d1358348d130cc8b0ac8705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "69b6db6d349a6d369a49269a4d26926d26d2492491249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨74, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [164383585422278656, 14987979559905787904, 27492085661696, 2040693589540864, hexnat% "4020010000000000000", 489630466048, 1042284544]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record018_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record018_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record018_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record018_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record018_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record018_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record018_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record018_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record018_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00030.record018

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00030.record045
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "23c66a3a55a368b8ae8785e0faa966639955558d4ad1743d70da364e3362e2b86d1b26c5b0ed4789ca719e1745c3783c8f13e2c871522a8560b81e546292a619896151560d0b41d60d4328d1314c8b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "26d349249a4924924d2492492492491249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record045 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record045 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record045.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record045.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record045.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 39), (facetIndex 44), (facetIndex 50), (facetIndex 52), (facetIndex 56), (facetIndex 58)]))
 (.leaf ([(facetIndex 33), (facetIndex 40), (facetIndex 60), (facetIndex 65)])))
 (.branch 3
 (.leaf ([(facetIndex 45), (facetIndex 47), (facetIndex 48), (facetIndex 49)]))
 (.leaf ([(facetIndex 34), (facetIndex 51), (facetIndex 54), (facetIndex 55)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 30), (facetIndex 36), (facetIndex 62)]))
 (.leaf ([(facetIndex 29), (facetIndex 32), (facetIndex 35), (facetIndex 38)])))
 (.branch 7
 (.leaf ([(facetIndex 31), (facetIndex 53), (facetIndex 59), (facetIndex 68)]))
 (.branch 8
 (.leaf ([(facetIndex 41), (facetIndex 42), (facetIndex 43)]))
 (.leaf ([(facetIndex 37), (facetIndex 61), (facetIndex 63)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "6001084816000336030222020777105845315645z1d;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
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
def grouped2_0010 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7, 8]
def grouped2_0014 : List Nat := [7]
def grouped2_0015 : List Nat := [7, 8]
def grouped2_0016 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record045 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record045_matrix_checked

def leafCount : Nat := 1
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaf0000 : List (Fin data.count) := [(facetIndex 18), (facetIndex 21), (facetIndex 26), (facetIndex 37), (facetIndex 38), (facetIndex 48), (facetIndex 55), (facetIndex 57), (facetIndex 58), (facetIndex 60), (facetIndex 62), (facetIndex 67), (facetIndex 68)]
theorem leaf0000_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0000 = true := by
  decide +kernel
theorem leaf0000_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0000 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0000_counts_checked
def leavesTable : ConcreteGrowth.Table (List (Fin data.count)) :=
(.leaf (leaf0000))
def leaves (j : Fin leafCount) : List (Fin data.count) := leavesTable.get j.val

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00030.record045" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00030.record045" 64

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00030.record045" "{\"ridges\":[[11,385],[12,25],[18,25],[30,13],[38,321],[38,322],[40,25],[45,385],[47,385],[48,385],[49,385],[51,25],[53,529],[57,25],[57,408],[67,408],[68,536]],\"owners\":[[30,13,[12,13,14,51],[0,29,52]],[38,321,[21],[10,49,54]],[38,322,[26],[10,49,65]],[11,385,[57],[45,47,48,49]],[45,385,[],[11,47,48,49,57]],[47,385,[],[11,45,48,49,57]],[48,385,[57],[11,45,47,49]],[49,385,[57],[11,45,47,48]],[53,529,[18,43],[16,34,46,55,56]],[68,536,[18,43],[27,56,61,66]],[57,408,[67],[]],[67,408,[57],[]]],\"edges\":[[42,[11,45,47,48,49,57,67]]],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00030.record045" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00030.record045\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-14,-9],[-15,-14],[-16,-3],[-16,-8],[-16,-10],[-16,-13],[-16,-14],[-16,-15],[-17,-12],[-23,-16],[-27,-17],[-30,-16],[-31,-11],[-31,-13],[-31,-16],[-31,-29],[-32,-12],[-32,-17],[-33,-31],[-35,-20],[-35,-21],[-35,-22],[-37,-9],[-38,-8],[-39,-10],[-39,-37],[-39,-38],[-40,-37],[-41,-10],[-41,-37],[-41,-40],[-42,-17],[-42,-32],[-44,-4],[-44,-11],[-44,-18],[-44,-28],[-44,-34],[-44,-39],[-44,-41],[-9,2,3,4,29],[-2,-5,-35],[-5,-19,-35],[-5,-29,-35],[-17,6],[-17,7],[-1,35],[-24],[-25],[-26,35],[-27,35],[-31,5,22],[-44,5,22],[-35,43],[-43,35],[-45,18,23,28,30,34,36],[-46,12,19,38,42],[-47,24,25,26,27],[-48,13,29,32,33],[-49,9,15,40],[-50,8,11,14,17],[-51,10,31,37,44],[-52,20,21,22],[-53,16,39,41],[-54,45],[-54,46],[-55,47],[-55,48],[-56,54],[-56,55],[-57,49],[-57,50],[-58,52,53],[-59,52],[-60,51,59],[-60,58],[-61,59],[-62,57,61],[-62,60],[-63,61],[-64,56,63],[-64,62],[64],[-5,-6,-7,-16,-17,-26,-33,-35,-36,-38,-40,-43,-44],[1,24,25,26,27,35,43]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":35,\"b\":30},{\"tag\":\"incompatible\",\"a\":36,\"b\":35},{\"tag\":\"incompatible\",\"a\":37,\"b\":13},{\"tag\":\"incompatible\",\"a\":37,\"b\":29},{\"tag\":\"incompatible\",\"a\":37,\"b\":31},{\"tag\":\"incompatible\",\"a\":37,\"b\":34},{\"tag\":\"incompatible\",\"a\":37,\"b\":35},{\"tag\":\"incompatible\",\"a\":37,\"b\":36},{\"tag\":\"incompatible\",\"a\":38,\"b\":33},{\"tag\":\"incompatible\",\"a\":44,\"b\":37},{\"tag\":\"incompatible\",\"a\":49,\"b\":38},{\"tag\":\"incompatible\",\"a\":52,\"b\":37},{\"tag\":\"incompatible\",\"a\":53,\"b\":32},{\"tag\":\"incompatible\",\"a\":53,\"b\":34},{\"tag\":\"incompatible\",\"a\":53,\"b\":37},{\"tag\":\"incompatible\",\"a\":53,\"b\":51},{\"tag\":\"incompatible\",\"a\":54,\"b\":33},{\"tag\":\"incompatible\",\"a\":54,\"b\":38},{\"tag\":\"incompatible\",\"a\":55,\"b\":53},{\"tag\":\"incompatible\",\"a\":57,\"b\":41},{\"tag\":\"incompatible\",\"a\":57,\"b\":42},{\"tag\":\"incompatible\",\"a\":57,\"b\":43},{\"tag\":\"incompatible\",\"a\":59,\"b\":30},{\"tag\":\"incompatible\",\"a\":60,\"b\":29},{\"tag\":\"incompatible\",\"a\":61,\"b\":31},{\"tag\":\"incompatible\",\"a\":61,\"b\":59},{\"tag\":\"incompatible\",\"a\":61,\"b\":60},{\"tag\":\"incompatible\",\"a\":62,\"b\":59},{\"tag\":\"incompatible\",\"a\":63,\"b\":31},{\"tag\":\"incompatible\",\"a\":63,\"b\":59},{\"tag\":\"incompatible\",\"a\":63,\"b\":62},{\"tag\":\"incompatible\",\"a\":65,\"b\":38},{\"tag\":\"incompatible\",\"a\":65,\"b\":54},{\"tag\":\"incompatible\",\"a\":68,\"b\":14},{\"tag\":\"incompatible\",\"a\":68,\"b\":32},{\"tag\":\"incompatible\",\"a\":68,\"b\":39},{\"tag\":\"incompatible\",\"a\":68,\"b\":50},{\"tag\":\"incompatible\",\"a\":68,\"b\":56},{\"tag\":\"incompatible\",\"a\":68,\"b\":61},{\"tag\":\"incompatible\",\"a\":68,\"b\":63},{\"tag\":\"mate\",\"ridge\":13,\"a\":30,\"owners\":[12,13,14,51]},{\"tag\":\"three\",\"ridge\":25,\"vertices\":[12,18,57]},{\"tag\":\"three\",\"ridge\":25,\"vertices\":[18,40,57]},{\"tag\":\"three\",\"ridge\":25,\"vertices\":[18,51,57]},{\"tag\":\"mate\",\"ridge\":321,\"a\":38,\"owners\":[21]},{\"tag\":\"mate\",\"ridge\":322,\"a\":38,\"owners\":[26]},{\"tag\":\"mate\",\"ridge\":385,\"a\":11,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":385,\"a\":45,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":385,\"a\":47,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":385,\"a\":48,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":385,\"a\":49,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":529,\"a\":53,\"owners\":[18,43]},{\"tag\":\"mate\",\"ridge\":536,\"a\":68,\"owners\":[18,43]},{\"tag\":\"mate\",\"ridge\":408,\"a\":57,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":408,\"a\":67,\"owners\":[57]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[39,44,50,52,56,58],\"full_literals\":[-45,18,23,28,30,34,36]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[33,40,60,65],\"full_literals\":[-46,12,19,38,42]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[45,47,48,49],\"full_literals\":[-47,24,25,26,27]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[34,51,54,55],\"full_literals\":[-48,13,29,32,33]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[30,36,62],\"full_literals\":[-49,9,15,40]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[29,32,35,38],\"full_literals\":[-50,8,11,14,17]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[31,53,59,68],\"full_literals\":[-51,10,31,37,44]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[41,42,43],\"full_literals\":[-52,20,21,22]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[37,61,63],\"full_literals\":[-53,16,39,41]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-54,45,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-54,false,46],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-55,47,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-55,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-56,54,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-56,false,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-57,49,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-57,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-58,52,53],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-59,52,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-60,51,59],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-60,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-61,false,59],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-62,57,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-62,false,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-63,false,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-64,56,63],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-64,false,62],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"block\",\"leaf\":0,\"vertices\":[18,21,26,37,38,48,55,57,58,60,62,67,68]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[11,45,47,48,49,57,67]}]}"
  "p cnf 64 85\n-14 -9 0\n-15 -14 0\n-16 -3 0\n-16 -8 0\n-16 -10 0\n-16 -13 0\n-16 -14 0\n-16 -15 0\n-17 -12 0\n-23 -16 0\n-27 -17 0\n-30 -16 0\n-31 -11 0\n-31 -13 0\n-31 -16 0\n-31 -29 0\n-32 -12 0\n-32 -17 0\n-33 -31 0\n-35 -20 0\n-35 -21 0\n-35 -22 0\n-37 -9 0\n-38 -8 0\n-39 -10 0\n-39 -37 0\n-39 -38 0\n-40 -37 0\n-41 -10 0\n-41 -37 0\n-41 -40 0\n-42 -17 0\n-42 -32 0\n-44 -4 0\n-44 -11 0\n-44 -18 0\n-44 -28 0\n-44 -34 0\n-44 -39 0\n-44 -41 0\n-9 2 3 4 29 0\n-2 -5 -35 0\n-5 -19 -35 0\n-5 -29 -35 0\n-17 6 0\n-17 7 0\n-1 35 0\n-24 0\n-25 0\n-26 35 0\n-27 35 0\n-31 5 22 0\n-44 5 22 0\n-35 43 0\n-43 35 0\n-45 18 23 28 30 34 36 0\n-46 12 19 38 42 0\n-47 24 25 26 27 0\n-48 13 29 32 33 0\n-49 9 15 40 0\n-50 8 11 14 17 0\n-51 10 31 37 44 0\n-52 20 21 22 0\n-53 16 39 41 0\n-54 45 0\n-54 46 0\n-55 47 0\n-55 48 0\n-56 54 0\n-56 55 0\n-57 49 0\n-57 50 0\n-58 52 53 0\n-59 52 0\n-60 51 59 0\n-60 58 0\n-61 59 0\n-62 57 61 0\n-62 60 0\n-63 61 0\n-64 56 63 0\n-64 62 0\n64 0\n-5 -6 -7 -16 -17 -26 -33 -35 -36 -38 -40 -43 -44 0\n1 24 25 26 27 35 43 0\n"
  "86 -47 26 27 0 48 49 58 0\n87 62 0 83 82 0\n88 60 0 87 79 0\n89 58 0 88 76 0\n90 1 26 27 35 43 0 48 49 85 0\n91 35 0 47 50 51 55 90 0\n92 -20 0 91 20 0\n93 -21 0 91 21 0\n94 -22 0 91 22 0\n95 43 0 91 54 0\n96 -52 0 93 94 92 63 0\n97 53 0 96 89 73 0\n98 -59 0 96 74 0\n99 -61 0 98 77 0\n100 51 0 98 88 75 0\n101 -63 0 99 80 0\n102 57 0 99 87 78 0\n103 56 0 101 83 81 0\n104 49 0 102 71 0\n105 50 0 102 72 0\n106 54 0 103 69 0\n107 55 0 103 70 0\n108 45 0 106 65 0\n109 46 0 106 66 0\n110 47 0 107 67 0\n111 48 0 107 68 0\n112 -37 0 104 97 23 26 28 30 60 64 8 0\n113 -44 0 94 97 105 104 108 110 111 109 95 91 34 35 36 37 38 39 40 53 64 42 44 43 3 4 6 7 8 10 12 41 61 60 56 9 11 18 32 45 46 86 59 57 84 0\n114 -10 0 97 5 25 29 64 0\n115 31 0 114 113 112 100 62 0\n116 -11 0 115 13 0\n117 -13 0 115 14 0\n118 -16 0 115 15 0\n119 -29 0 115 16 0\n120 -33 0 115 19 0\n121 5 0 115 94 52 0\n122 32 0 120 119 117 111 59 0\n123 -19 0 121 91 43 0\n124 -12 0 122 17 0\n125 -17 0 122 18 0\n126 -42 0 122 33 0\n127 38 0 126 109 124 123 57 0\n128 -8 0 127 24 0\n129 -39 0 127 27 0\n130 14 0 128 116 125 105 61 0\n131 41 0 129 97 118 64 0\n132 -9 0 130 1 0\n133 -15 0 130 2 0\n134 -40 0 131 31 0\n135 0 134 133 132 104 60 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record045.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record045.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record045.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record045.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record045 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeafTable : ConcreteGrowth.Table (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record045.l) :=
(.leaf (⟨0, by decide⟩))
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record045.l := originalLeafTable.get j.val
def orbitWordTable : ConcreteGrowth.Table (List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record045.g)) :=
(.leaf ([]))
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record045.g) := orbitWordTable.get j.val
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record045.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record045.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record045 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record045_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record045_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record045_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record045_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record045_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record045_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record045_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record045 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record045_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record045_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record045_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00030.record045
