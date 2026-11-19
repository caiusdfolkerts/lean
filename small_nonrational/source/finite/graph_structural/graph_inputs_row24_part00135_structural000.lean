module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00135Data
public import GraphInputsRow24Part00135Frames
public import GraphInputsRow24Part00135Leaves
public import GraphInputsRow24Part00135Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00135.record013
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record013
def vertexColumn : Fields := ⟨10, hexnat% "d326c8f0bc9a8ba998b663a4e538ce8b92e2b86e4789e1783ed26698e4b9d16658d4b5c368d6364d534cd8b52d2b46d8751d2745d0f6632cd8b92ccb8ad2b2ac6b46c5b61e4731e2749ca719d1715e0f43c8f13c2f07d4a2683a518960da49526292643991545894950d54324c3342c8b12c2b06d0721c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6da69b4db6da69249249b6934db6d34d24924924924924d2491249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨80, by decide⟩, ⟨87, by decide⟩, ⟨90, by decide⟩, ⟨92, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10003c00803ff00be0000000", hexnat% "40000400000005000000000", hexnat% "2000000062000000000", 10445360463872, hexnat% "8140060280000000000000", hexnat% "1800000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40001c080203ffbe0000000", hexnat% "22060000000000000000", hexnat% "100004000000800000000000", 8796093022208000, hexnat% "8140000280000000000000", hexnat% "18000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1d80809ff53040000000", hexnat% "22060000000080000000", hexnat% "140000400020004020000000", 11592116731904, hexnat% "8140000200000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40003c080221ffbe0000000", hexnat% "100004000000a00000000000", 8233143068786688, hexnat% "30040000000000000000", hexnat% "8140020280000000000000", hexnat% "8000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "22060002101880000000", hexnat% "11000000402000000000", hexnat% "8808080000040000000", hexnat% "140004400020804020000000", 17042430230528, 8197958696697856, hexnat% "8140000200000300000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record013_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record013_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00135.record013

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00135.record007
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "bc2ea6665956359362d87693a2e2b91e2785e0fa71966392e74599595554d54d4b51d68d934ad4749d1743d98d9334d332cc7392e2b2ad1b16d8791cc789d2729c6745c9715c3783d0f13c1f8b1522683a5188e0b9518a4990e645516258348d0b54344c9314c3322c2b06d0721c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "d369b6da4d34da4934db69269a69249a492492492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record007 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record007 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record007.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record007.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record007.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 47), (facetIndex 48), (facetIndex 56), (facetIndex 60), (facetIndex 71), (facetIndex 72)]))
 (.leaf ([(facetIndex 43), (facetIndex 61), (facetIndex 69), (facetIndex 70)])))
 (.branch 3
 (.leaf ([(facetIndex 75), (facetIndex 79), (facetIndex 80)]))
 (.leaf ([(facetIndex 30), (facetIndex 34), (facetIndex 35), (facetIndex 36), (facetIndex 37), (facetIndex 58), (facetIndex 67), (facetIndex 77), (facetIndex 86)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 45), (facetIndex 46), (facetIndex 51), (facetIndex 89)]))
 (.leaf ([(facetIndex 50), (facetIndex 52), (facetIndex 53), (facetIndex 54)])))
 (.branch 7
 (.leaf ([(facetIndex 31), (facetIndex 32), (facetIndex 33), (facetIndex 38), (facetIndex 39), (facetIndex 40), (facetIndex 41), (facetIndex 42), (facetIndex 44)]))
 (.leaf ([(facetIndex 62)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "200c00024184000486001c80c016d9401263b6d9b6f6ccz16;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 49), (facetIndex 55)]))
 (.branch 2
 (.leaf ([(facetIndex 73), (facetIndex 74)]))
 (.leaf ([(facetIndex 81), (facetIndex 88)]))))
 (.branch 4
 (.leaf ([(facetIndex 57), (facetIndex 59), (facetIndex 63), (facetIndex 64), (facetIndex 65), (facetIndex 66), (facetIndex 68)]))
 (.branch 5
 (.leaf ([(facetIndex 76), (facetIndex 78), (facetIndex 82), (facetIndex 83), (facetIndex 84), (facetIndex 85), (facetIndex 87)]))
 (.leaf ([(facetIndex 90)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1428249101040480030db600618z2a;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2, 3]
def grouped2_0006 : List Nat := [4]
def grouped2_0007 : List Nat := [4, 5]
def grouped2_0008 : List Nat := [4, 5, 6, 7]
def grouped2_0009 : List Nat := [5]
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7]
def grouped2_0012 : List Nat := [7]
def grouped3_0013 : List Nat := [0]
def grouped3_0014 : List Nat := [0, 1, 2]
def grouped3_0016 : List Nat := [1]
def grouped3_0017 : List Nat := [1, 2]
def grouped3_0018 : List Nat := [2]
def grouped3_0019 : List Nat := [3]
def grouped3_0020 : List Nat := [3, 4, 5]
def grouped3_0021 : List Nat := [4]
def grouped3_0022 : List Nat := [4, 5]
def grouped3_0023 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record007 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record007_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00135.record007" "{\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00135.record007" 80

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00135.record007" "{\"ridges\":[[1,37],[10,145],[12,259],[16,517],[20,25],[20,137],[27,152],[34,37],[39,37],[40,37],[41,517],[43,580],[44,259],[45,25],[47,137],[48,545],[50,35],[51,145],[52,259],[53,145],[55,67],[62,137],[62,517],[70,517],[70,577],[70,580],[72,25],[72,49],[72,545],[73,600],[74,624],[77,152],[85,212],[89,152]],\"owners\":[[50,35,[1,6,39,40,41,47,48],[8,38,51,52,55]],[1,37,[13,16,56,60,63,64,65,69],[34,38,39,40]],[34,37,[13,16,60,69],[1,38,39,40,56,63,64,65]],[39,37,[13,16,56,63,65,69],[1,34,38,40,60,64]],[40,37,[13,16,56,60,63,64,69],[1,34,38,39,65]],[55,67,[2,9,12,31,42,45,53],[38,43,49,50]],[72,49,[8,34,50,51,52,63,64,65],[19,56,71,74]],[10,145,[20,58,64,66,68,71],[36,51,53,54]],[51,145,[20,58,66,68],[10,36,53,54,64,71]],[53,145,[20,58,64,68,71],[10,36,51,54,66]],[48,545,[16,69,74],[21,41,55,72]],[72,545,[16,41,55,69],[21,48,74]],[70,577,[49,55,73,74],[18,43,61,69]],[43,580,[],[18,61,69,70,81,88]],[70,580,[81,88],[18,43,61,69]],[27,152,[20,58,71,90],[77,89]],[77,152,[20,71],[27,58,89,90]],[89,152,[20,58],[27,71,77,90]],[85,212,[66],[]],[73,600,[],[]],[74,624,[],[]]],\"edges\":[[32,[10,20,27,36,51,53,54,58,64,66,68,71,77,83,85,87,89,90]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00135.record007" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00135.record007\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-23,-16],[-31,-5],[-32,-4],[-32,-30],[-32,-31],[-33,-23],[-39,-8],[-39,-12],[-39,-13],[-39,-14],[-39,-35],[-39,-36],[-39,-37],[-39,-38],[-45,-39],[-46,-2],[-46,-17],[-46,-21],[-46,-40],[-46,-43],[-47,-10],[-47,-24],[-47,-25],[-48,-3],[-29,1,3,18,19,20,26,27],[-1,8,9,35,37,40,41,42,45],[-15,8,9,37,45],[-18,8,9,35,40,42,45],[-19,8,9,35,37,40,41,45],[-34,2,5,7,12,21,24,32],[-7,-23,-31],[-10,-24,-48],[-10,-26,-39],[-48,4,15,29,30,31,40,41,42],[-6,10,36,41,43,44,47],[-30,10,36,43,44],[-32,10,36,41,44,47],[-9,-39,-46],[-20,-39,-46],[-27,9,45,50],[-48,9,20,34,45],[-46,28,34,49,50],[-22],[-46,52,56],[-11,10,36,47,58],[-51,10,47],[-57,10,36],[-54,43],[-49],[-50],[-59,26,27,35,37,47,48],[-60,22,38,45,46],[-61,24,25,30,57],[-62,29,31,32,33],[-63,12,13,14,17,18,19,20,21,23],[-64,39],[-65,59],[-65,60],[-66,65],[-67,61],[-67,62],[-68,63],[-68,64],[-69,67],[-69,68],[-70,66],[-70,69],[70],[-28,71],[-34,71],[-52,72],[-56,72],[-41,73],[-42,73],[-44,73],[-53,74],[-55,74],[-58,75],[-72,76],[-71,-76,77],[-75,78],[-74,78],[-78,79],[-73,79],[-77,-79,80],[-80],[6,10,11,16,30,32,33,36,41,43,44,47,51,53,54,55,57,58]],\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":44,\"b\":36},{\"tag\":\"incompatible\",\"a\":52,\"b\":9},{\"tag\":\"incompatible\",\"a\":53,\"b\":8},{\"tag\":\"incompatible\",\"a\":53,\"b\":51},{\"tag\":\"incompatible\",\"a\":53,\"b\":52},{\"tag\":\"incompatible\",\"a\":54,\"b\":44},{\"tag\":\"incompatible\",\"a\":62,\"b\":13},{\"tag\":\"incompatible\",\"a\":62,\"b\":31},{\"tag\":\"incompatible\",\"a\":62,\"b\":32},{\"tag\":\"incompatible\",\"a\":62,\"b\":33},{\"tag\":\"incompatible\",\"a\":62,\"b\":56},{\"tag\":\"incompatible\",\"a\":62,\"b\":58},{\"tag\":\"incompatible\",\"a\":62,\"b\":60},{\"tag\":\"incompatible\",\"a\":62,\"b\":61},{\"tag\":\"incompatible\",\"a\":69,\"b\":62},{\"tag\":\"incompatible\",\"a\":70,\"b\":2},{\"tag\":\"incompatible\",\"a\":70,\"b\":38},{\"tag\":\"incompatible\",\"a\":70,\"b\":42},{\"tag\":\"incompatible\",\"a\":70,\"b\":63},{\"tag\":\"incompatible\",\"a\":70,\"b\":66},{\"tag\":\"incompatible\",\"a\":71,\"b\":20},{\"tag\":\"incompatible\",\"a\":71,\"b\":45},{\"tag\":\"incompatible\",\"a\":71,\"b\":46},{\"tag\":\"incompatible\",\"a\":72,\"b\":6},{\"tag\":\"mate\",\"ridge\":35,\"a\":50,\"owners\":[1,6,39,40,41,47,48]},{\"tag\":\"mate\",\"ridge\":37,\"a\":1,\"owners\":[13,16,56,60,63,64,65,69]},{\"tag\":\"mate\",\"ridge\":37,\"a\":34,\"owners\":[13,16,60,69]},{\"tag\":\"mate\",\"ridge\":37,\"a\":39,\"owners\":[13,16,56,63,65,69]},{\"tag\":\"mate\",\"ridge\":37,\"a\":40,\"owners\":[13,16,56,60,63,64,69]},{\"tag\":\"mate\",\"ridge\":67,\"a\":55,\"owners\":[2,9,12,31,42,45,53]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[12,44,52]},{\"tag\":\"three\",\"ridge\":25,\"vertices\":[20,45,72]},{\"tag\":\"three\",\"ridge\":137,\"vertices\":[20,47,62]},{\"tag\":\"mate\",\"ridge\":49,\"a\":72,\"owners\":[8,34,50,51,52,63,64,65]},{\"tag\":\"mate\",\"ridge\":145,\"a\":10,\"owners\":[20,58,64,66,68,71]},{\"tag\":\"mate\",\"ridge\":145,\"a\":51,\"owners\":[20,58,66,68]},{\"tag\":\"mate\",\"ridge\":145,\"a\":53,\"owners\":[20,58,64,68,71]},{\"tag\":\"three\",\"ridge\":517,\"vertices\":[16,62,70]},{\"tag\":\"three\",\"ridge\":517,\"vertices\":[41,62,70]},{\"tag\":\"mate\",\"ridge\":545,\"a\":48,\"owners\":[16,69,74]},{\"tag\":\"mate\",\"ridge\":545,\"a\":72,\"owners\":[16,41,55,69]},{\"tag\":\"mate\",\"ridge\":577,\"a\":70,\"owners\":[49,55,73,74]},{\"tag\":\"mate\",\"ridge\":580,\"a\":43,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":580,\"a\":70,\"owners\":[81,88]},{\"tag\":\"mate\",\"ridge\":152,\"a\":27,\"owners\":[20,58,71,90]},{\"tag\":\"mate\",\"ridge\":152,\"a\":77,\"owners\":[20,71]},{\"tag\":\"mate\",\"ridge\":152,\"a\":89,\"owners\":[20,58]},{\"tag\":\"mate\",\"ridge\":212,\"a\":85,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":600,\"a\":73,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":624,\"a\":74,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[47,48,56,60,71,72],\"full_literals\":[-59,26,27,35,37,47,48]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[43,61,69,70],\"full_literals\":[-60,22,38,45,46]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[45,46,51,89],\"full_literals\":[-61,24,25,30,57]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[50,52,53,54],\"full_literals\":[-62,29,31,32,33]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[31,32,33,38,39,40,41,42,44],\"full_literals\":[-63,12,13,14,17,18,19,20,21,23]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[62],\"full_literals\":[-64,39]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-65,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-65,false,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-66,65,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-67,61,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-67,false,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-68,63,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-68,false,64],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-69,67,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-69,false,68],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-70,66,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-70,false,69],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":49,\"full_literals\":[-28,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":55,\"full_literals\":[-34,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":81,\"full_literals\":[-52,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":88,\"full_literals\":[-56,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":64,\"full_literals\":[-41,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":65,\"full_literals\":[-42,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":68,\"full_literals\":[-44,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":83,\"full_literals\":[-53,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":87,\"full_literals\":[-55,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":90,\"full_literals\":[-58,75]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-72,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-71,-76,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-75,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-74,false,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-78,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-73,false,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-77,-79,80],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":32,\"owners\":[10,20,27,36,51,53,54,58,64,66,68,71,77,83,85,87,89,90]}]}"
  "p cnf 80 87\n-23 -16 0\n-31 -5 0\n-32 -4 0\n-32 -30 0\n-32 -31 0\n-33 -23 0\n-39 -8 0\n-39 -12 0\n-39 -13 0\n-39 -14 0\n-39 -35 0\n-39 -36 0\n-39 -37 0\n-39 -38 0\n-45 -39 0\n-46 -2 0\n-46 -17 0\n-46 -21 0\n-46 -40 0\n-46 -43 0\n-47 -10 0\n-47 -24 0\n-47 -25 0\n-48 -3 0\n-29 1 3 18 19 20 26 27 0\n-1 8 9 35 37 40 41 42 45 0\n-15 8 9 37 45 0\n-18 8 9 35 40 42 45 0\n-19 8 9 35 37 40 41 45 0\n-34 2 5 7 12 21 24 32 0\n-7 -23 -31 0\n-10 -24 -48 0\n-10 -26 -39 0\n-48 4 15 29 30 31 40 41 42 0\n-6 10 36 41 43 44 47 0\n-30 10 36 43 44 0\n-32 10 36 41 44 47 0\n-9 -39 -46 0\n-20 -39 -46 0\n-27 9 45 50 0\n-48 9 20 34 45 0\n-46 28 34 49 50 0\n-22 0\n-46 52 56 0\n-11 10 36 47 58 0\n-51 10 47 0\n-57 10 36 0\n-54 43 0\n-49 0\n-50 0\n-59 26 27 35 37 47 48 0\n-60 22 38 45 46 0\n-61 24 25 30 57 0\n-62 29 31 32 33 0\n-63 12 13 14 17 18 19 20 21 23 0\n-64 39 0\n-65 59 0\n-65 60 0\n-66 65 0\n-67 61 0\n-67 62 0\n-68 63 0\n-68 64 0\n-69 67 0\n-69 68 0\n-70 66 0\n-70 69 0\n70 0\n-28 71 0\n-34 71 0\n-52 72 0\n-56 72 0\n-41 73 0\n-42 73 0\n-44 73 0\n-53 74 0\n-55 74 0\n-58 75 0\n-72 76 0\n-71 -76 77 0\n-75 78 0\n-74 78 0\n-78 79 0\n-73 79 0\n-77 -79 80 0\n-80 0\n6 10 11 16 30 32 33 36 41 43 44 47 51 53 54 55 57 58 0\n"
  "88 -60 38 45 46 0 43 52 0\n89 66 0 68 66 0\n90 69 0 68 67 0\n91 65 0 89 59 0\n92 67 0 90 64 0\n93 68 0 90 65 0\n94 59 0 91 57 0\n95 60 0 91 58 0\n96 61 0 92 60 0\n97 62 0 92 61 0\n98 63 0 93 62 0\n99 64 0 93 63 0\n100 39 0 99 56 0\n101 -8 0 100 7 0\n102 -12 0 100 8 0\n103 -13 0 100 9 0\n104 -14 0 100 10 0\n105 -35 0 100 11 0\n106 -36 0 100 12 0\n107 -37 0 100 13 0\n108 -38 0 100 14 0\n109 -45 0 100 15 0\n110 46 0 109 95 108 88 0\n111 -2 0 110 16 0\n112 -17 0 110 17 0\n113 -21 0 110 18 0\n114 -40 0 110 19 0\n115 -43 0 110 20 0\n116 -9 0 110 100 38 0\n117 -20 0 110 100 39 0\n118 -54 0 115 48 0\n119 -27 0 116 109 50 40 0\n120 -15 0 116 101 107 109 27 0\n121 6 10 11 16 30 32 33 41 44 47 51 53 55 57 58 0 106 115 118 87 0\n122 71 0 50 49 110 69 70 42 0\n123 72 0 110 71 72 44 0\n124 76 0 123 79 0\n125 77 0 124 122 80 0\n126 -79 0 125 86 85 0\n127 -78 0 126 83 0\n128 -73 0 126 84 0\n129 -75 0 127 81 0\n130 -74 0 127 82 0\n131 -41 0 128 73 0\n132 -42 0 128 74 0\n133 -44 0 128 75 0\n134 -58 0 129 78 0\n135 -53 0 130 76 0\n136 -55 0 130 77 0\n137 -19 0 131 101 105 107 114 116 109 29 0\n138 -18 0 132 101 105 114 116 109 28 0\n139 -1 0 132 101 105 107 114 116 131 109 26 0\n140 23 0 137 98 104 102 103 112 117 113 138 55 0\n141 -16 0 140 1 0\n142 -33 0 140 6 0\n143 -10 48 0 100 119 107 105 94 21 33 51 0\n144 47 10 0 115 106 134 136 135 133 131 142 141 36 47 46 45 35 37 121 0\n145 10 0 133 115 106 96 47 36 144 22 23 53 0\n146 -26 0 145 100 33 0\n147 48 0 145 143 0\n148 -3 0 147 24 0\n149 34 0 147 117 116 109 41 0\n150 -24 0 147 145 32 0\n151 -29 0 148 139 138 137 117 146 119 25 0\n152 32 0 142 151 97 140 149 150 113 102 111 54 2 31 30 0\n153 -4 0 152 3 0\n154 -30 0 152 4 0\n155 -31 0 152 5 0\n156 0 154 155 120 153 151 147 114 131 132 34 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record007.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record007.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record007.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record007.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record007 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record007.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record007.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record007.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record007.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record007 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record007_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record007 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record007_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record007_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00135.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00135.record008
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "bc9ca6a6695a3693a2e87a95a362da4e8b8ae4789e1783e9c66966559365392e479956352d64d8b4ad4749d1743dd0e6364e5334e334ccb31cd8b92ccb8ad2b2ac6b46c9b16c3ba1e4729e1745c5783d0f13c1f5494a898960d88e0b95152625254352342d90d4388d1324c530cd0b22c4b0ae0721c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36da6db69349a69b69b6da4d269a492492492492492492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record008 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record008 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record008.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 37), (facetIndex 60), (facetIndex 64), (facetIndex 65), (facetIndex 67), (facetIndex 68)]))
 (.branch 2
 (.leaf ([(facetIndex 78), (facetIndex 82), (facetIndex 83), (facetIndex 85), (facetIndex 86)]))
 (.leaf ([(facetIndex 41), (facetIndex 43), (facetIndex 59), (facetIndex 74), (facetIndex 92)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 33), (facetIndex 36), (facetIndex 38), (facetIndex 39), (facetIndex 58)]))
 (.leaf ([(facetIndex 31), (facetIndex 32), (facetIndex 44), (facetIndex 45), (facetIndex 46), (facetIndex 47), (facetIndex 48), (facetIndex 49), (facetIndex 50)])))
 (.branch 6
 (.leaf ([(facetIndex 34), (facetIndex 35), (facetIndex 51), (facetIndex 52), (facetIndex 53), (facetIndex 54), (facetIndex 55), (facetIndex 56), (facetIndex 57)]))
 (.leaf ([(facetIndex 30), (facetIndex 40), (facetIndex 42), (facetIndex 62), (facetIndex 80)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "20000482460400800000001804edb6db249245966c3b5c98z16;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record008 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record008_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00135.record008" "{\"atoms\":[]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00135.record008" 0

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00135.record008" "{\"ridges\":[],\"owners\":[],\"edges\":[],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00135.record008" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00135.record008\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[]],\"atoms\":[],\"rules\":[{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true}]}"
  "p cnf 0 1\n 0\n"
  "2 0 1 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record008.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record008.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record008.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record008.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record008 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record008.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record008.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record008.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record008.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record008 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record008_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record008 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record008_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record008_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00135.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00135.record009
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "26c570dc2f07c568bad1996559362da4e53a2e2b91e2785e0fa719a559364b91e74599595554d54d4b51d64d534cd8b4ad1b51d2745d0f74364e5354e334ccb392d4b8acab46c5bc1e8761e4751d2729d1725c570de0f43c4f07c9a0ea262382e5449916439915458948d1342d88d1324c3322c2b06e0741c8709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6da6db6da4d34da4924d36da4924d24d34926d2492492493492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record009 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record009 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record009.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record009.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record009.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 31), (facetIndex 43), (facetIndex 48), (facetIndex 49), (facetIndex 50), (facetIndex 53)]))
 (.leaf ([(facetIndex 30), (facetIndex 45), (facetIndex 61), (facetIndex 64), (facetIndex 84)])))
 (.branch 3
 (.leaf ([(facetIndex 38), (facetIndex 63), (facetIndex 71), (facetIndex 72)]))
 (.leaf ([(facetIndex 42), (facetIndex 56), (facetIndex 73), (facetIndex 74), (facetIndex 75), (facetIndex 76)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 34), (facetIndex 37), (facetIndex 51), (facetIndex 69)]))
 (.leaf ([(facetIndex 27), (facetIndex 44), (facetIndex 79), (facetIndex 81), (facetIndex 83), (facetIndex 92)])))
 (.branch 7
 (.leaf ([(facetIndex 29), (facetIndex 33), (facetIndex 35), (facetIndex 36), (facetIndex 39), (facetIndex 40), (facetIndex 41)]))
 (.leaf ([(facetIndex 28), (facetIndex 55), (facetIndex 57), (facetIndex 59), (facetIndex 60), (facetIndex 62)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "5000001a28a036da4200015cfe3be0080000d0f6ca6d30077az14;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 65), (facetIndex 77), (facetIndex 78)]))
 (.leaf ([(facetIndex 47), (facetIndex 98)])))
 (.branch 3
 (.leaf ([(facetIndex 32), (facetIndex 46), (facetIndex 52), (facetIndex 54), (facetIndex 86)]))
 (.leaf ([(facetIndex 80), (facetIndex 85), (facetIndex 91)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 58), (facetIndex 66), (facetIndex 67), (facetIndex 68), (facetIndex 70), (facetIndex 89), (facetIndex 94)]))
 (.leaf ([(facetIndex 82), (facetIndex 87), (facetIndex 88), (facetIndex 90), (facetIndex 96)])))
 (.branch 7
 (.leaf ([(facetIndex 95), (facetIndex 97)]))
 (.leaf ([(facetIndex 93)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "75d38765a98143000000104900000100082000280000000002z18;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
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
def grouped2_0012 : List Nat := [6, 7]
def grouped3_0013 : List Nat := [0]
def grouped3_0014 : List Nat := [0, 1]
def grouped3_0015 : List Nat := [0, 1, 2, 3]
def grouped3_0017 : List Nat := [1]
def grouped3_0018 : List Nat := [2]
def grouped3_0019 : List Nat := [2, 3]
def grouped3_0020 : List Nat := [3]
def grouped3_0021 : List Nat := [4]
def grouped3_0022 : List Nat := [4, 5]
def grouped3_0023 : List Nat := [4, 5, 6, 7]
def grouped3_0024 : List Nat := [5]
def grouped3_0025 : List Nat := [6]
def grouped3_0026 : List Nat := [6, 7]
def grouped3_0027 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record009 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record009_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00135.record009" "{\"atoms\":[{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00135.record009" 54

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00135.record009" "{\"ridges\":[[17,580],[34,274],[37,262],[38,580],[51,274],[52,594],[64,577],[64,580],[69,336],[71,577],[71,580],[72,577],[72,580],[78,624],[82,284],[88,308],[90,404]],\"owners\":[[37,262,[82,88,90],[3,29,34,36,39,41,85,89,91]],[34,274,[93],[10,43,49,51,53,82,88,89,90]],[51,274,[82,88,90],[10,34,43,49,53,89,93]],[64,577,[52,54,78],[17,38,47,71,72,77]],[71,577,[47,52,54],[17,38,64,72,77,78]],[72,577,[47,52,77,78],[17,38,54,64,71]],[17,580,[86,91,98],[38,64,71,72]],[38,580,[98],[17,64,71,72,86,91]],[64,580,[91],[17,38,71,72,86,98]],[71,580,[86,91],[17,38,64,72,98]],[72,580,[86,98],[17,38,64,71,91]],[69,336,[93],[21,51,76,89,97]],[52,594,[],[]],[82,284,[58,97],[]],[88,308,[67],[]],[90,404,[70],[]],[78,624,[],[]]],\"edges\":[[41,[17,38,47,52,54,64,71,72,77,78,86,91,98]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00135.record009" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00135.record009\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-20,-2],[-20,-6],[-20,-12],[-23,-20],[-28,-5],[-28,-7],[-28,-10],[-28,-13],[-4,22,25,26],[-3,28],[-8,22,25,26],[-14,9,10,21],[-18,7,9,10],[-19,7,9,20,21],[-1,24,27,30],[-5,30],[-14,27],[-18,24,27],[-19,24,30],[-16,28],[-9],[-22,11,29],[-25,15],[-26,17],[-21],[-31,2,6,12,14,23],[-32,5,13,18,19],[-33,3,4,8,16],[-34,31],[-35,32],[-36,34],[-36,35],[-37,33],[-38,37],[-39,36],[-39,38],[39],[-20,40],[-7,41],[-30,41],[-10,42],[-24,42],[-27,43],[-11,44],[-15,44],[-17,44],[-22,45],[-25,45],[-26,45],[-29,46],[-41,47],[-40,47],[-43,48],[-42,48],[-48,49],[-47,49],[-45,50],[-44,-45,51],[-46,52],[-50,-52,53],[-51,53],[-49,-53,54],[-54],[1,5,7,9,10,14,18,19,20,21,24,27,30]],\"atoms\":[{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":77,\"b\":30},{\"tag\":\"incompatible\",\"a\":77,\"b\":45},{\"tag\":\"incompatible\",\"a\":77,\"b\":61},{\"tag\":\"incompatible\",\"a\":84,\"b\":77},{\"tag\":\"incompatible\",\"a\":93,\"b\":38},{\"tag\":\"incompatible\",\"a\":93,\"b\":47},{\"tag\":\"incompatible\",\"a\":93,\"b\":54},{\"tag\":\"incompatible\",\"a\":93,\"b\":63},{\"tag\":\"mate\",\"ridge\":262,\"a\":37,\"owners\":[82,88,90]},{\"tag\":\"mate\",\"ridge\":274,\"a\":34,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":274,\"a\":51,\"owners\":[82,88,90]},{\"tag\":\"mate\",\"ridge\":577,\"a\":64,\"owners\":[52,54,78]},{\"tag\":\"mate\",\"ridge\":577,\"a\":71,\"owners\":[47,52,54]},{\"tag\":\"mate\",\"ridge\":577,\"a\":72,\"owners\":[47,52,77,78]},{\"tag\":\"mate\",\"ridge\":580,\"a\":17,\"owners\":[86,91,98]},{\"tag\":\"mate\",\"ridge\":580,\"a\":38,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":580,\"a\":64,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":580,\"a\":71,\"owners\":[86,91]},{\"tag\":\"mate\",\"ridge\":580,\"a\":72,\"owners\":[86,98]},{\"tag\":\"mate\",\"ridge\":336,\"a\":69,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":594,\"a\":52,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":284,\"a\":82,\"owners\":[58,97]},{\"tag\":\"mate\",\"ridge\":308,\"a\":88,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":404,\"a\":90,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":624,\"a\":78,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[30,45,61,64,84],\"full_literals\":[-31,2,6,12,14,23]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[38,63,71,72],\"full_literals\":[-32,5,13,18,19]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[34,37,51,69],\"full_literals\":[-33,3,4,8,16]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-34,false,31],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-35,32,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-36,34,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-36,false,35],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-37,33,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-38,37,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-39,36,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-39,false,38],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":77,\"full_literals\":[-20,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":47,\"full_literals\":[-7,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":98,\"full_literals\":[-30,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":54,\"full_literals\":[-10,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":86,\"full_literals\":[-24,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":91,\"full_literals\":[-27,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":58,\"full_literals\":[-11,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":67,\"full_literals\":[-15,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":70,\"full_literals\":[-17,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":82,\"full_literals\":[-22,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":88,\"full_literals\":[-25,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":90,\"full_literals\":[-26,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":97,\"full_literals\":[-29,46]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-48,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-47,false,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-45,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-44,-45,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-50,-52,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-51,false,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-49,-53,54],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":41,\"owners\":[17,38,47,52,54,64,71,72,77,78,86,91,98]}]}"
  "p cnf 54 64\n-20 -2 0\n-20 -6 0\n-20 -12 0\n-23 -20 0\n-28 -5 0\n-28 -7 0\n-28 -10 0\n-28 -13 0\n-4 22 25 26 0\n-3 28 0\n-8 22 25 26 0\n-14 9 10 21 0\n-18 7 9 10 0\n-19 7 9 20 21 0\n-1 24 27 30 0\n-5 30 0\n-14 27 0\n-18 24 27 0\n-19 24 30 0\n-16 28 0\n-9 0\n-22 11 29 0\n-25 15 0\n-26 17 0\n-21 0\n-31 2 6 12 14 23 0\n-32 5 13 18 19 0\n-33 3 4 8 16 0\n-34 31 0\n-35 32 0\n-36 34 0\n-36 35 0\n-37 33 0\n-38 37 0\n-39 36 0\n-39 38 0\n39 0\n-20 40 0\n-7 41 0\n-30 41 0\n-10 42 0\n-24 42 0\n-27 43 0\n-11 44 0\n-15 44 0\n-17 44 0\n-22 45 0\n-25 45 0\n-26 45 0\n-29 46 0\n-41 47 0\n-40 47 0\n-43 48 0\n-42 48 0\n-48 49 0\n-47 49 0\n-45 50 0\n-44 -45 51 0\n-46 52 0\n-50 -52 53 0\n-51 53 0\n-49 -53 54 0\n-54 0\n1 5 7 9 10 14 18 19 20 21 24 27 30 0\n"
  "65 36 0 37 35 0\n66 38 0 37 36 0\n67 34 0 65 31 0\n68 35 0 65 32 0\n69 37 0 66 34 0\n70 31 0 67 29 0\n71 32 0 68 30 0\n72 33 0 69 33 0\n73 1 5 7 10 14 18 19 20 24 27 30 0 21 25 64 0\n74 49 0 55 56 53 54 51 52 43 41 42 39 40 38 17 15 18 19 16 73 0\n75 -53 0 74 63 62 0\n76 -51 0 75 61 0\n77 -28 0 71 25 21 70 5 6 7 8 13 12 27 14 1 2 3 4 26 0\n78 -3 0 77 10 0\n79 -16 0 77 20 0\n80 22 26 25 0 72 78 79 9 11 28 0\n81 45 0 47 48 49 80 0\n82 50 0 81 57 0\n83 -44 0 81 76 58 0\n84 -52 0 82 75 60 0\n85 -11 0 83 44 0\n86 -15 0 83 45 0\n87 -17 0 83 46 0\n88 -46 0 84 59 0\n89 -25 0 86 23 0\n90 -26 0 87 24 0\n91 -29 0 88 50 0\n92 22 0 90 89 80 0\n93 0 92 91 85 22 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record009.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record009.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record009.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record009.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record009 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record009.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record009.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record009.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record009.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record009 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record009_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record009 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record009_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record009_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00135.record009

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00135.record011
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "26c570bc9a95a2eb469999655a364d8b69394e33a2e2b86e4789e1783e9a5592e74599595556354d4b59354d3362d2b46d4745dd0e6364d538cd332ce4b52ccb8acab1ad1b16f07a1d8791d4731e2749ca719e1745c9715c3783d0f23c4f0bc1f2703c2683a264399154589515254352344d0b41d90d4388d1324c3322c4b0ac1b"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "da6d36db6db6db69a6d24924924924924924924924db49a6db49a6d2489249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record011 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record011 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record011.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record011.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record011.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 49), (facetIndex 51), (facetIndex 57), (facetIndex 60)]))
 (.leaf ([(facetIndex 47), (facetIndex 48), (facetIndex 55), (facetIndex 56), (facetIndex 58), (facetIndex 59)])))
 (.branch 3
 (.leaf ([(facetIndex 64), (facetIndex 68), (facetIndex 69), (facetIndex 75), (facetIndex 76)]))
 (.leaf ([(facetIndex 26), (facetIndex 50), (facetIndex 65), (facetIndex 70), (facetIndex 77), (facetIndex 97), (facetIndex 100)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 62), (facetIndex 63), (facetIndex 71), (facetIndex 73), (facetIndex 74)]))
 (.leaf ([(facetIndex 28), (facetIndex 52), (facetIndex 53), (facetIndex 54), (facetIndex 61)])))
 (.branch 7
 (.leaf ([(facetIndex 27), (facetIndex 32), (facetIndex 40), (facetIndex 66), (facetIndex 72)]))
 (.branch 8
 (.leaf ([(facetIndex 29), (facetIndex 67)]))
 (.leaf ([(facetIndex 34), (facetIndex 35), (facetIndex 42), (facetIndex 43), (facetIndex 80), (facetIndex 82)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "300300000000000000808003224464322763244501101155503011000880600008806007563z1a;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 30), (facetIndex 33), (facetIndex 78)]))
 (.leaf ([(facetIndex 31), (facetIndex 37), (facetIndex 79)])))
 (.branch 3
 (.leaf ([(facetIndex 81), (facetIndex 83), (facetIndex 98)]))
 (.leaf ([(facetIndex 84), (facetIndex 86), (facetIndex 99)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 88), (facetIndex 93), (facetIndex 101)]))
 (.leaf ([(facetIndex 89), (facetIndex 95), (facetIndex 102)])))
 (.branch 7
 (.leaf ([(facetIndex 36), (facetIndex 38), (facetIndex 39), (facetIndex 41), (facetIndex 44), (facetIndex 45), (facetIndex 46)]))
 (.branch 8
 (.leaf ([(facetIndex 85), (facetIndex 87), (facetIndex 91), (facetIndex 92), (facetIndex 94), (facetIndex 96)]))
 (.leaf ([(facetIndex 90)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "540320757477854737320201z20;6660060661600001z1f;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
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
def grouped2_0008 : List Nat := [4, 5]
def grouped2_0009 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7, 8]
def grouped2_0012 : List Nat := [7]
def grouped2_0013 : List Nat := [7, 8]
def grouped2_0014 : List Nat := [8]
def grouped3_0015 : List Nat := [0]
def grouped3_0016 : List Nat := [0, 1]
def grouped3_0017 : List Nat := [0, 1, 2, 3]
def grouped3_0019 : List Nat := [1]
def grouped3_0020 : List Nat := [2]
def grouped3_0021 : List Nat := [2, 3]
def grouped3_0022 : List Nat := [3]
def grouped3_0023 : List Nat := [4]
def grouped3_0024 : List Nat := [4, 5]
def grouped3_0025 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0026 : List Nat := [5]
def grouped3_0027 : List Nat := [6]
def grouped3_0028 : List Nat := [6, 7, 8]
def grouped3_0029 : List Nat := [7]
def grouped3_0030 : List Nat := [7, 8]
def grouped3_0031 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record011 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record011_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00135.record011" "{\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0030\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00135.record011" 88

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00135.record011" "{\"ridges\":[[8,322],[9,578],[16,276],[18,324],[19,580],[35,274],[42,322],[42,324],[43,578],[43,580],[45,646],[46,774],[53,322],[54,578],[57,515],[58,322],[60,578],[61,322],[61,578],[63,276],[67,76],[68,324],[69,580],[71,276],[73,324],[74,276],[75,580],[76,324],[76,580],[79,616],[88,270],[89,526],[93,86],[95,102],[96,774],[99,578],[99,616],[101,344],[102,616]],\"owners\":[[35,274,[98],[6,48,56,58,59,83,91,93,94]],[57,515,[9,31,43,45,46,54,61],[7,36,40,51]],[8,322,[88,93,96,98],[42,53,58,61]],[42,322,[98],[8,53,58,61,88,93,96]],[53,322,[93,96],[8,42,58,61,88,98]],[58,322,[88,96],[8,42,53,61,93,98]],[61,322,[88,93,98],[8,42,53,58,96]],[9,578,[89,95,96,99],[43,54,60,61]],[43,578,[99],[9,54,60,61,89,95,96]],[54,578,[95,96],[9,43,60,61,89,99]],[60,578,[89,96],[9,43,54,61,95,99]],[61,578,[89,95,99],[9,43,54,60,96]],[99,578,[9,43,61,96],[54,60,89,95]],[67,76,[81,84,88,89,101,102],[12,28,62,64,68,69,87]],[16,276,[83,91,93,94,101],[35,63,71,73,74]],[63,276,[91,93,94],[16,35,71,73,74,83,101]],[71,276,[83,93,94,101],[16,35,63,73,74,91]],[74,276,[83,91,93,101],[16,35,63,71,73,94]],[18,324,[88,93,96,101],[42,68,73,76]],[42,324,[101],[18,68,73,76,88,93,96]],[68,324,[93,96],[18,42,73,76,88,101]],[73,324,[88,96],[18,42,68,76,93,101]],[76,324,[88,93,101],[18,42,68,73,96]],[19,580,[89,95,96,102],[43,69,75,76]],[43,580,[102],[19,69,75,76,89,95,96]],[69,580,[95,96],[19,43,75,76,89,102]],[75,580,[89,96],[19,43,69,76,95,102]],[76,580,[89,95,102],[19,43,69,75,96]],[88,270,[30,83],[]],[89,526,[31,86],[]],[93,86,[33,81],[]],[95,102,[37,84],[]],[45,646,[],[]],[46,774,[96],[]],[96,774,[46],[]],[101,344,[78,98],[]],[79,616,[99,102],[]],[99,616,[79,102],[]],[102,616,[79,99],[]]],\"edges\":[[22,[16,18,30,35,39,42,44,46,63,68,71,73,74,76,83,88,91,93,94,96,101]],[40,[8,18,42,53,58,61,68,73,76,78,88,93,96,98,101]],[41,[9,19,43,54,60,61,69,75,76,79,89,95,96,99,102]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00135.record011" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00135.record011\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-21,-2],[-26,-9],[-46,-7],[-46,-11],[-46,-13],[-46,-14],[-46,-16],[-46,-42],[-46,-45],[-47,-46],[-48,-46],[-49,-46],[-50,-7],[-50,-11],[-50,-13],[-50,-14],[-50,-16],[-50,-42],[-50,-45],[-50,-47],[-50,-48],[-50,-49],[-51,-6],[-51,-10],[-51,-39],[-51,-41],[-55,-8],[-55,-19],[-55,-20],[-55,-28],[-11,52],[-23,2,8,15,17,18,22,26],[-1,45,48,51,52],[-14,52],[-21,48,51],[-24,45,51],[-26,45,48,52],[-2,46,50,51,53],[-15,53],[-22,50,51],[-25,46,51],[-26,46,50,53],[-53,2,15,26,51],[-29,40,43,45,46,54,55],[-3,42,47,48,49,54],[-27,47,48,49],[-32,42,48,49,54],[-34,42,47,48,54],[-4,45,48,51,54],[-14,54],[-30,48,51],[-33,45,51],[-36,45,48,54],[-5,46,50,51,55],[-15,55],[-31,50,51],[-35,46,51],[-36,46,50,55],[-45,7,42],[-46,8,44],[-48,9,40],[-50,12,43],[-17],[-18,51],[-51,18],[-54,37,52],[-38,53,55],[-53,38,55],[-55,38,53],[-56,19,20,23,25],[-57,28,30,31,35,36],[-58,6,29],[-59,10,11,14,15,39,41],[-60,56],[-61,57],[-62,60,61],[-63,58,59],[-64,63],[-65,64],[-66,62],[-66,65],[66],[-7,67],[-9,67],[-37,67],[-8,68],[-12,68],[-38,68],[-40,69],[-42,69],[-52,69],[-43,70],[-44,70],[-53,70],[-45,71],[-48,71],[-54,71],[-46,72],[-50,72],[-55,72],[-18,73],[-51,74],[-68,75],[-67,75],[-67,-68,76],[-70,77],[-69,77],[-69,-70,78],[-77,79],[-78,80],[-75,79],[-75,-77,80],[-75,-78,81],[-76,-77,81],[-72,82],[-71,-72,83],[-74,84],[-73,-84,85],[-85,87],[-82,86],[-83,87],[-79,-87,88],[-80,-86,88],[-81,88],[-88],[3,4,7,11,13,14,16,18,27,30,32,33,34,36,42,45,47,48,49,51,54],[1,4,14,21,24,26,30,33,36,37,45,48,51,52,54],[2,5,15,22,25,26,31,35,36,38,46,50,51,53,55]],\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":53,\"b\":9},{\"tag\":\"incompatible\",\"a\":61,\"b\":33},{\"tag\":\"incompatible\",\"a\":89,\"b\":30},{\"tag\":\"incompatible\",\"a\":89,\"b\":35},{\"tag\":\"incompatible\",\"a\":89,\"b\":39},{\"tag\":\"incompatible\",\"a\":89,\"b\":42},{\"tag\":\"incompatible\",\"a\":89,\"b\":44},{\"tag\":\"incompatible\",\"a\":89,\"b\":83},{\"tag\":\"incompatible\",\"a\":89,\"b\":88},{\"tag\":\"incompatible\",\"a\":91,\"b\":89},{\"tag\":\"incompatible\",\"a\":93,\"b\":89},{\"tag\":\"incompatible\",\"a\":94,\"b\":89},{\"tag\":\"incompatible\",\"a\":95,\"b\":30},{\"tag\":\"incompatible\",\"a\":95,\"b\":35},{\"tag\":\"incompatible\",\"a\":95,\"b\":39},{\"tag\":\"incompatible\",\"a\":95,\"b\":42},{\"tag\":\"incompatible\",\"a\":95,\"b\":44},{\"tag\":\"incompatible\",\"a\":95,\"b\":83},{\"tag\":\"incompatible\",\"a\":95,\"b\":88},{\"tag\":\"incompatible\",\"a\":95,\"b\":91},{\"tag\":\"incompatible\",\"a\":95,\"b\":93},{\"tag\":\"incompatible\",\"a\":95,\"b\":94},{\"tag\":\"incompatible\",\"a\":96,\"b\":29},{\"tag\":\"incompatible\",\"a\":96,\"b\":34},{\"tag\":\"incompatible\",\"a\":96,\"b\":80},{\"tag\":\"incompatible\",\"a\":96,\"b\":82},{\"tag\":\"incompatible\",\"a\":102,\"b\":31},{\"tag\":\"incompatible\",\"a\":102,\"b\":49},{\"tag\":\"incompatible\",\"a\":102,\"b\":51},{\"tag\":\"incompatible\",\"a\":102,\"b\":64},{\"tag\":\"mate\",\"ridge\":274,\"a\":35,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":515,\"a\":57,\"owners\":[9,31,43,45,46,54,61]},{\"tag\":\"mate\",\"ridge\":322,\"a\":8,\"owners\":[88,93,96,98]},{\"tag\":\"mate\",\"ridge\":322,\"a\":42,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":322,\"a\":53,\"owners\":[93,96]},{\"tag\":\"mate\",\"ridge\":322,\"a\":58,\"owners\":[88,96]},{\"tag\":\"mate\",\"ridge\":322,\"a\":61,\"owners\":[88,93,98]},{\"tag\":\"mate\",\"ridge\":578,\"a\":9,\"owners\":[89,95,96,99]},{\"tag\":\"mate\",\"ridge\":578,\"a\":43,\"owners\":[99]},{\"tag\":\"mate\",\"ridge\":578,\"a\":54,\"owners\":[95,96]},{\"tag\":\"mate\",\"ridge\":578,\"a\":60,\"owners\":[89,96]},{\"tag\":\"mate\",\"ridge\":578,\"a\":61,\"owners\":[89,95,99]},{\"tag\":\"mate\",\"ridge\":578,\"a\":99,\"owners\":[9,43,61,96]},{\"tag\":\"mate\",\"ridge\":76,\"a\":67,\"owners\":[81,84,88,89,101,102]},{\"tag\":\"mate\",\"ridge\":276,\"a\":16,\"owners\":[83,91,93,94,101]},{\"tag\":\"mate\",\"ridge\":276,\"a\":63,\"owners\":[91,93,94]},{\"tag\":\"mate\",\"ridge\":276,\"a\":71,\"owners\":[83,93,94,101]},{\"tag\":\"mate\",\"ridge\":276,\"a\":74,\"owners\":[83,91,93,101]},{\"tag\":\"mate\",\"ridge\":324,\"a\":18,\"owners\":[88,93,96,101]},{\"tag\":\"mate\",\"ridge\":324,\"a\":42,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":324,\"a\":68,\"owners\":[93,96]},{\"tag\":\"mate\",\"ridge\":324,\"a\":73,\"owners\":[88,96]},{\"tag\":\"mate\",\"ridge\":324,\"a\":76,\"owners\":[88,93,101]},{\"tag\":\"mate\",\"ridge\":580,\"a\":19,\"owners\":[89,95,96,102]},{\"tag\":\"mate\",\"ridge\":580,\"a\":43,\"owners\":[102]},{\"tag\":\"mate\",\"ridge\":580,\"a\":69,\"owners\":[95,96]},{\"tag\":\"mate\",\"ridge\":580,\"a\":75,\"owners\":[89,96]},{\"tag\":\"mate\",\"ridge\":580,\"a\":76,\"owners\":[89,95,102]},{\"tag\":\"mate\",\"ridge\":270,\"a\":88,\"owners\":[30,83]},{\"tag\":\"mate\",\"ridge\":526,\"a\":89,\"owners\":[31,86]},{\"tag\":\"mate\",\"ridge\":86,\"a\":93,\"owners\":[33,81]},{\"tag\":\"mate\",\"ridge\":102,\"a\":95,\"owners\":[37,84]},{\"tag\":\"mate\",\"ridge\":646,\"a\":45,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":774,\"a\":46,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":774,\"a\":96,\"owners\":[46]},{\"tag\":\"mate\",\"ridge\":344,\"a\":101,\"owners\":[78,98]},{\"tag\":\"mate\",\"ridge\":616,\"a\":79,\"owners\":[99,102]},{\"tag\":\"mate\",\"ridge\":616,\"a\":99,\"owners\":[79,102]},{\"tag\":\"mate\",\"ridge\":616,\"a\":102,\"owners\":[79,99]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[49,51,57,60],\"full_literals\":[-56,19,20,23,25]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[64,68,69,75,76],\"full_literals\":[-57,28,30,31,35,36]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[29,67],\"full_literals\":[-58,6,29]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[34,35,42,43,80,82],\"full_literals\":[-59,10,11,14,15,39,41]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-60,56,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-61,57,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-62,60,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-63,58,59],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-64,false,63],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-65,false,64],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-66,62,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-66,false,65],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":30,\"full_literals\":[-7,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":33,\"full_literals\":[-9,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":78,\"full_literals\":[-37,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":31,\"full_literals\":[-8,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":37,\"full_literals\":[-12,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":79,\"full_literals\":[-38,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":81,\"full_literals\":[-40,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":83,\"full_literals\":[-42,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":98,\"full_literals\":[-52,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":84,\"full_literals\":[-43,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":86,\"full_literals\":[-44,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":99,\"full_literals\":[-53,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":88,\"full_literals\":[-45,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":93,\"full_literals\":[-48,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":101,\"full_literals\":[-54,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":89,\"full_literals\":[-46,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":95,\"full_literals\":[-50,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":102,\"full_literals\":[-55,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":46,\"full_literals\":[-18,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":96,\"full_literals\":[-51,74]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-68,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-67,false,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-67,-68,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-70,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-69,false,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-69,-70,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-77,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-78,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-75,false,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-75,-77,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-75,-78,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-76,-77,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-72,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-71,-72,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0030\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-74,false,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-73,-84,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-85,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-82,false,86],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-83,false,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-79,-87,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-80,-86,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-81,false,88],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":22,\"owners\":[16,18,30,35,39,42,44,46,63,68,71,73,74,76,83,88,91,93,94,96,101]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[8,18,42,53,58,61,68,73,76,78,88,93,96,98,101]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[9,19,43,54,60,61,69,75,76,79,89,95,96,99,102]}]}"
  "p cnf 88 128\n-21 -2 0\n-26 -9 0\n-46 -7 0\n-46 -11 0\n-46 -13 0\n-46 -14 0\n-46 -16 0\n-46 -42 0\n-46 -45 0\n-47 -46 0\n-48 -46 0\n-49 -46 0\n-50 -7 0\n-50 -11 0\n-50 -13 0\n-50 -14 0\n-50 -16 0\n-50 -42 0\n-50 -45 0\n-50 -47 0\n-50 -48 0\n-50 -49 0\n-51 -6 0\n-51 -10 0\n-51 -39 0\n-51 -41 0\n-55 -8 0\n-55 -19 0\n-55 -20 0\n-55 -28 0\n-11 52 0\n-23 2 8 15 17 18 22 26 0\n-1 45 48 51 52 0\n-14 52 0\n-21 48 51 0\n-24 45 51 0\n-26 45 48 52 0\n-2 46 50 51 53 0\n-15 53 0\n-22 50 51 0\n-25 46 51 0\n-26 46 50 53 0\n-53 2 15 26 51 0\n-29 40 43 45 46 54 55 0\n-3 42 47 48 49 54 0\n-27 47 48 49 0\n-32 42 48 49 54 0\n-34 42 47 48 54 0\n-4 45 48 51 54 0\n-14 54 0\n-30 48 51 0\n-33 45 51 0\n-36 45 48 54 0\n-5 46 50 51 55 0\n-15 55 0\n-31 50 51 0\n-35 46 51 0\n-36 46 50 55 0\n-45 7 42 0\n-46 8 44 0\n-48 9 40 0\n-50 12 43 0\n-17 0\n-18 51 0\n-51 18 0\n-54 37 52 0\n-38 53 55 0\n-53 38 55 0\n-55 38 53 0\n-56 19 20 23 25 0\n-57 28 30 31 35 36 0\n-58 6 29 0\n-59 10 11 14 15 39 41 0\n-60 56 0\n-61 57 0\n-62 60 61 0\n-63 58 59 0\n-64 63 0\n-65 64 0\n-66 62 0\n-66 65 0\n66 0\n-7 67 0\n-9 67 0\n-37 67 0\n-8 68 0\n-12 68 0\n-38 68 0\n-40 69 0\n-42 69 0\n-52 69 0\n-43 70 0\n-44 70 0\n-53 70 0\n-45 71 0\n-48 71 0\n-54 71 0\n-46 72 0\n-50 72 0\n-55 72 0\n-18 73 0\n-51 74 0\n-68 75 0\n-67 75 0\n-67 -68 76 0\n-70 77 0\n-69 77 0\n-69 -70 78 0\n-77 79 0\n-78 80 0\n-75 79 0\n-75 -77 80 0\n-75 -78 81 0\n-76 -77 81 0\n-72 82 0\n-71 -72 83 0\n-74 84 0\n-73 -84 85 0\n-85 87 0\n-82 86 0\n-83 87 0\n-79 -87 88 0\n-80 -86 88 0\n-81 88 0\n-88 0\n3 4 7 11 13 14 16 18 27 30 32 33 34 36 42 45 47 48 49 51 54 0\n1 4 14 21 24 26 30 33 36 37 45 48 51 52 54 0\n2 5 15 22 25 26 31 35 36 38 46 50 51 53 55 0\n"
  "129 62 0 82 80 0\n130 65 0 82 81 0\n131 64 0 130 79 0\n132 63 0 131 78 0\n133 -81 0 125 124 0\n134 51 79 0 111 103 88 109 106 94 69 87 92 62 86 93 60 58 42 39 40 56 38 41 54 57 128 0\n135 79 0 132 109 111 106 107 103 104 92 93 94 89 90 91 86 88 83 85 60 39 69 59 31 34 66 44 134 23 24 25 26 72 73 77 0\n136 -87 0 135 125 122 0\n137 -85 0 136 119 0\n138 -83 0 136 121 0\n139 -51 0 137 65 102 101 117 118 0\n140 -18 0 139 64 0\n141 55 50 26 46 53 0 139 38 56 40 57 41 39 67 54 58 128 0\n142 50 26 46 53 0 140 63 138 129 139 57 41 39 40 56 38 141 27 28 29 30 100 32 70 116 74 95 96 97 76 53 51 75 71 0\n143 -50 0 138 139 140 13 14 15 16 17 18 19 20 21 22 99 52 46 51 116 97 49 48 45 53 47 126 0\n144 46 53 0 143 42 142 0\n145 -46 0 138 139 140 3 4 5 6 7 8 9 10 11 12 98 52 46 51 116 97 49 48 45 53 47 126 0\n146 53 0 145 144 0\n147 70 0 146 94 0\n148 77 0 147 106 0\n149 -76 0 148 133 114 0\n150 55 26 0 143 145 146 149 133 147 139 55 68 58 43 88 1 103 105 113 83 84 85 108 89 90 91 61 59 34 66 33 51 36 52 49 127 0\n151 26 0 138 125 148 147 139 150 100 115 116 120 95 96 97 123 36 52 51 35 50 49 53 110 112 108 104 91 85 33 127 0\n152 -9 0 151 2 0\n153 -72 0 138 125 151 147 115 116 120 95 96 123 37 110 91 108 0\n154 -55 0 153 100 0\n155 38 0 154 146 68 0\n156 68 0 155 88 0\n157 75 0 156 103 0\n158 -67 0 156 149 105 0\n159 -78 0 157 133 113 0\n160 -7 0 158 83 0\n161 -69 0 159 147 108 0\n162 -40 0 161 89 0\n163 -42 0 161 90 0\n164 -52 0 161 91 0\n165 -48 0 162 152 61 0\n166 -45 0 163 160 59 0\n167 0 164 165 166 151 37 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record011.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record011.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record011.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record011.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record011 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record011.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record011.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record011.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record011.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record011 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record011_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record011 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record011_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record011_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00135.record011
