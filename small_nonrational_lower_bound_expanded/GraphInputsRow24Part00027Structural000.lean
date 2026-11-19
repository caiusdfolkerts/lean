module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00027Frames
public import GraphInputsRow24Part00027Leaves
public import GraphInputsRow24Part00027Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00027.record000
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "7cd88da1eb2699a561da4e4b8ae1b85e0fb6136479c9665954759352d2b46d1743dd0f2398d6394cd31ce4b32d2b2ac3ba1d8791e2729c6785d1715c3783d0f13c9c1a89a16b06498962382e0786926459c15252548d0b41dc0e4348c6324c5322c4b0ac1b81d0721c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "da49b6d24934936da492492492492492492492449249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record000 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record000 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record000.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record000.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record000.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 48), (facetIndex 51), (facetIndex 54), (facetIndex 71), (facetIndex 84)]))
 (.leaf ([(facetIndex 36), (facetIndex 40), (facetIndex 44), (facetIndex 46), (facetIndex 58), (facetIndex 69), (facetIndex 82)])))
 (.branch 3
 (.leaf ([(facetIndex 35), (facetIndex 37), (facetIndex 43), (facetIndex 49), (facetIndex 63), (facetIndex 76)]))
 (.leaf ([(facetIndex 52), (facetIndex 53), (facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 59)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 38), (facetIndex 42), (facetIndex 50), (facetIndex 64), (facetIndex 77)]))
 (.leaf ([(facetIndex 39), (facetIndex 45), (facetIndex 61), (facetIndex 62), (facetIndex 74), (facetIndex 75)])))
 (.branch 7
 (.leaf ([(facetIndex 60), (facetIndex 70), (facetIndex 73), (facetIndex 83)]))
 (.leaf ([(facetIndex 41), (facetIndex 47)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "c40022b7018800456e65b61b110e69539b114z1a;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 68), (facetIndex 72)]))
 (.leaf ([(facetIndex 81), (facetIndex 85)])))
 (.branch 3
 (.leaf ([(facetIndex 65), (facetIndex 66), (facetIndex 67)]))
 (.branch 4
 (.leaf ([(facetIndex 78), (facetIndex 79), (facetIndex 80)]))
 (.leaf ([(facetIndex 86)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "10800b6c000000049z31;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 5
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
def grouped3_0015 : List Nat := [0]
def grouped3_0016 : List Nat := [0, 1]
def grouped3_0018 : List Nat := [1]
def grouped3_0019 : List Nat := [2]
def grouped3_0020 : List Nat := [2, 3, 4]
def grouped3_0021 : List Nat := [3]
def grouped3_0022 : List Nat := [3, 4]
def grouped3_0023 : List Nat := [4]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record000 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record000_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00027.record000" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00027.record000" 69

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00027.record000" "{\"ridges\":[[14,577],[15,515],[22,73],[22,81],[31,74],[31,82],[45,577],[45,578],[47,515],[52,73],[52,74],[53,98],[55,515],[57,577],[58,515],[59,577],[61,81],[62,73],[69,769],[71,73],[71,81],[74,82],[75,74],[75,98],[80,596],[82,770],[84,74],[84,82],[85,98]],\"owners\":[[22,81,[10,39,53,54,55,66,67],[61,70,71]],[61,81,[10,53,54,55],[22,39,66,67,70,71]],[71,81,[10,39,53,55,66,67],[22,54,61,70]],[31,82,[10,39,53,54,55,79,80],[74,83,84]],[74,82,[10,53,54,55],[31,39,79,80,83,84]],[84,82,[10,39,53,55,79,80],[31,54,74,83]],[14,577,[65,67,68,72],[45,52,55,57,59]],[45,577,[72],[14,52,55,57,59,65,67,68]],[57,577,[65,67],[14,45,52,55,59,68,72]],[59,577,[65,67,68],[14,45,52,55,57,72]],[45,578,[85],[14,52,55,57,59,78,80,81]],[69,769,[15,59],[21,58,72]],[82,770,[15,59],[30,58,85]],[80,596,[67],[]]],\"edges\":[[31,[10,22,31,39,53,54,55,61,66,67,70,71,74,79,80,83,84,86]],[41,[14,45,52,55,57,59,65,67,68,72,78,80,81,85]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00027.record000" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00027.record000\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-9,-7],[-13,-6],[-13,-7],[-13,-8],[-13,-10],[-13,-12],[-14,-1],[-14,-11],[-16,-14],[-17,-9],[-21,-9],[-21,-13],[-22,-15],[-25,-23],[-25,-24],[-26,-23],[-26,-24],[-27,-23],[-27,-24],[-28,-19],[-28,-23],[-28,-24],[-30,-14],[-30,-15],[-32,-10],[-32,-18],[-32,-19],[-32,-20],[-32,-29],[-33,-15],[-34,-25],[-34,-26],[-34,-27],[-34,-28],[-35,-23],[-35,-25],[-35,-26],[-35,-27],[-35,-28],[-35,-34],[-36,-23],[-36,-24],[-36,-34],[-36,-35],[-37,-24],[-37,-35],[-38,-24],[-38,-35],[-39,-19],[-39,-23],[-39,-24],[-39,-34],[-39,-35],[-40,-32],[-41,-14],[-41,-15],[-41,-35],[-43,-18],[-43,-19],[-44,-7],[-44,-23],[-44,-24],[-44,-34],[-44,-35],[-3,-13,-17],[-13,-17,-20],[-4,-14,-24],[-14,-24,-31],[-5,-14,-35],[-14,-35,-42],[-4,1,7,15,16,17,26,27],[-23,1,15,16,17],[-31,1,7,15,17,26,27],[-5,1,7,15,16,17,37,38],[-34,1,15,16,17],[-42,1,7,15,17,37,38],[-15,-35,-43],[-2,25,27,28,32],[-11,32],[-19,25,27],[-21,25,27,28],[-11,43],[-29,3,21],[-40,3,21],[-38,27],[-45,6,8,10,12,20,29,40],[-46,14,15,17,18,19,21],[-47,7,11,23,24,34,35],[-48,22,30,33,41],[-49,9,13],[-50,45],[-51,46],[-52,50],[-52,51],[-53,47],[-54,48],[-54,49],[-55,53],[-55,54],[-56,52],[-56,55],[56],[-57,28,32],[-58,39,43],[-43,58],[-59,25,26,27],[-60,36,37,38],[-61,44],[-62,57,58],[-58,62],[-63,57],[-63,58],[-64,60,61],[-65,61],[-66,59,64],[-67,59,65],[-68,62,67],[-68,63,66],[-62,-67,69],[68],[-69],[1,4,5,7,15,16,17,23,26,27,30,31,34,37,38,41,42,44],[2,11,14,17,19,21,25,27,28,32,36,38,39,43]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":41,\"b\":39},{\"tag\":\"incompatible\",\"a\":47,\"b\":36},{\"tag\":\"incompatible\",\"a\":47,\"b\":39},{\"tag\":\"incompatible\",\"a\":47,\"b\":40},{\"tag\":\"incompatible\",\"a\":47,\"b\":44},{\"tag\":\"incompatible\",\"a\":47,\"b\":46},{\"tag\":\"incompatible\",\"a\":52,\"b\":10},{\"tag\":\"incompatible\",\"a\":52,\"b\":45},{\"tag\":\"incompatible\",\"a\":54,\"b\":52},{\"tag\":\"incompatible\",\"a\":55,\"b\":41},{\"tag\":\"incompatible\",\"a\":59,\"b\":41},{\"tag\":\"incompatible\",\"a\":59,\"b\":47},{\"tag\":\"incompatible\",\"a\":60,\"b\":53},{\"tag\":\"incompatible\",\"a\":65,\"b\":61},{\"tag\":\"incompatible\",\"a\":65,\"b\":62},{\"tag\":\"incompatible\",\"a\":66,\"b\":61},{\"tag\":\"incompatible\",\"a\":66,\"b\":62},{\"tag\":\"incompatible\",\"a\":67,\"b\":61},{\"tag\":\"incompatible\",\"a\":67,\"b\":62},{\"tag\":\"incompatible\",\"a\":68,\"b\":57},{\"tag\":\"incompatible\",\"a\":68,\"b\":61},{\"tag\":\"incompatible\",\"a\":68,\"b\":62},{\"tag\":\"incompatible\",\"a\":70,\"b\":52},{\"tag\":\"incompatible\",\"a\":70,\"b\":53},{\"tag\":\"incompatible\",\"a\":72,\"b\":44},{\"tag\":\"incompatible\",\"a\":72,\"b\":56},{\"tag\":\"incompatible\",\"a\":72,\"b\":57},{\"tag\":\"incompatible\",\"a\":72,\"b\":58},{\"tag\":\"incompatible\",\"a\":72,\"b\":69},{\"tag\":\"incompatible\",\"a\":73,\"b\":53},{\"tag\":\"incompatible\",\"a\":74,\"b\":65},{\"tag\":\"incompatible\",\"a\":74,\"b\":66},{\"tag\":\"incompatible\",\"a\":74,\"b\":67},{\"tag\":\"incompatible\",\"a\":74,\"b\":68},{\"tag\":\"incompatible\",\"a\":75,\"b\":61},{\"tag\":\"incompatible\",\"a\":75,\"b\":65},{\"tag\":\"incompatible\",\"a\":75,\"b\":66},{\"tag\":\"incompatible\",\"a\":75,\"b\":67},{\"tag\":\"incompatible\",\"a\":75,\"b\":68},{\"tag\":\"incompatible\",\"a\":75,\"b\":74},{\"tag\":\"incompatible\",\"a\":78,\"b\":61},{\"tag\":\"incompatible\",\"a\":78,\"b\":62},{\"tag\":\"incompatible\",\"a\":78,\"b\":74},{\"tag\":\"incompatible\",\"a\":78,\"b\":75},{\"tag\":\"incompatible\",\"a\":79,\"b\":62},{\"tag\":\"incompatible\",\"a\":79,\"b\":75},{\"tag\":\"incompatible\",\"a\":80,\"b\":62},{\"tag\":\"incompatible\",\"a\":80,\"b\":75},{\"tag\":\"incompatible\",\"a\":81,\"b\":57},{\"tag\":\"incompatible\",\"a\":81,\"b\":61},{\"tag\":\"incompatible\",\"a\":81,\"b\":62},{\"tag\":\"incompatible\",\"a\":81,\"b\":74},{\"tag\":\"incompatible\",\"a\":81,\"b\":75},{\"tag\":\"incompatible\",\"a\":82,\"b\":72},{\"tag\":\"incompatible\",\"a\":83,\"b\":52},{\"tag\":\"incompatible\",\"a\":83,\"b\":53},{\"tag\":\"incompatible\",\"a\":83,\"b\":75},{\"tag\":\"incompatible\",\"a\":85,\"b\":56},{\"tag\":\"incompatible\",\"a\":85,\"b\":57},{\"tag\":\"incompatible\",\"a\":86,\"b\":39},{\"tag\":\"incompatible\",\"a\":86,\"b\":61},{\"tag\":\"incompatible\",\"a\":86,\"b\":62},{\"tag\":\"incompatible\",\"a\":86,\"b\":74},{\"tag\":\"incompatible\",\"a\":86,\"b\":75},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[15,47,55]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[47,55,58]},{\"tag\":\"three\",\"ridge\":73,\"vertices\":[22,52,62]},{\"tag\":\"three\",\"ridge\":73,\"vertices\":[52,62,71]},{\"tag\":\"three\",\"ridge\":74,\"vertices\":[31,52,75]},{\"tag\":\"three\",\"ridge\":74,\"vertices\":[52,75,84]},{\"tag\":\"mate\",\"ridge\":81,\"a\":22,\"owners\":[10,39,53,54,55,66,67]},{\"tag\":\"mate\",\"ridge\":81,\"a\":61,\"owners\":[10,53,54,55]},{\"tag\":\"mate\",\"ridge\":81,\"a\":71,\"owners\":[10,39,53,55,66,67]},{\"tag\":\"mate\",\"ridge\":82,\"a\":31,\"owners\":[10,39,53,54,55,79,80]},{\"tag\":\"mate\",\"ridge\":82,\"a\":74,\"owners\":[10,53,54,55]},{\"tag\":\"mate\",\"ridge\":82,\"a\":84,\"owners\":[10,39,53,55,79,80]},{\"tag\":\"three\",\"ridge\":98,\"vertices\":[53,75,85]},{\"tag\":\"mate\",\"ridge\":577,\"a\":14,\"owners\":[65,67,68,72]},{\"tag\":\"mate\",\"ridge\":577,\"a\":45,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":577,\"a\":57,\"owners\":[65,67]},{\"tag\":\"mate\",\"ridge\":577,\"a\":59,\"owners\":[65,67,68]},{\"tag\":\"mate\",\"ridge\":578,\"a\":45,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":769,\"a\":69,\"owners\":[15,59]},{\"tag\":\"mate\",\"ridge\":770,\"a\":82,\"owners\":[15,59]},{\"tag\":\"mate\",\"ridge\":596,\"a\":80,\"owners\":[67]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[36,40,44,46,58,69,82],\"full_literals\":[-45,6,8,10,12,20,29,40]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[52,53,55,56,57,59],\"full_literals\":[-46,14,15,17,18,19,21]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[39,45,61,62,74,75],\"full_literals\":[-47,7,11,23,24,34,35]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[60,70,73,83],\"full_literals\":[-48,22,30,33,41]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[41,47],\"full_literals\":[-49,9,13]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-50,false,45],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-51,false,46],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-52,50,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-52,false,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-53,false,47],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-54,48,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-54,false,49],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-55,53,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-55,false,54],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-56,52,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-56,false,55],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[68,72],\"full_literals\":[-57,28,32]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[81,85],\"full_literals\":[-58,39,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":85,\"full_literals\":[-43,58]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[65,66,67],\"full_literals\":[-59,25,26,27]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[78,79,80],\"full_literals\":[-60,36,37,38]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[86],\"full_literals\":[-61,44]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-62,57,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-58,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-63,57,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-63,false,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-64,60,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-65,false,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-66,59,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-67,59,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-68,62,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-68,63,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-62,-67,69],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":31,\"owners\":[10,22,31,39,53,54,55,61,66,67,70,71,74,79,80,83,84,86]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[14,45,52,55,57,59,65,67,68,72,78,80,81,85]}]}"
  "124 52 0 102 100 0\n125 55 0 102 101 0\n126 50 0 124 93 0\n127 51 0 124 94 0\n128 53 0 125 98 0\n129 54 0 125 99 0\n130 45 0 126 91 0\n131 46 0 127 92 0\n132 47 0 128 95 0\n133 48 0 129 96 0\n134 49 0 129 97 0\n135 -44 11 0 132 60 61 62 63 64 88 0\n136 -7 0 134 1 3 90 0\n137 -23 -59 0 14 16 18 106 0\n138 -24 -59 0 15 17 19 106 0\n139 -34 -59 0 31 32 33 106 0\n140 -67 0 121 136 132 119 110 105 82 135 108 114 116 137 138 139 88 36 37 38 106 0\n141 62 0 140 120 117 0\n142 17 -35 0 120 131 136 53 38 36 37 106 48 44 46 107 64 108 113 115 118 112 104 77 39 111 103 26 81 80 57 40 35 87 7 9 23 69 70 71 73 122 0\n143 -35 0 120 134 130 36 37 38 39 44 46 48 64 106 107 108 113 115 118 111 103 25 28 29 54 142 10 90 2 4 6 86 0\n144 -17 21 0 134 130 10 90 2 4 5 6 65 66 83 84 86 0\n145 -14 15 17 0 143 132 136 7 8 9 23 55 72 75 135 88 17 19 45 47 67 68 74 76 122 0\n146 -19 0 141 20 27 49 59 103 104 109 0\n147 15 18 21 0 146 131 144 145 87 0\n148 -15 0 133 13 24 30 56 89 0\n149 -24 27 21 0 148 146 85 147 26 79 58 144 145 15 22 42 51 78 123 0\n150 -23 27 21 0 148 146 85 147 26 79 58 144 145 14 21 41 50 78 123 0\n151 27 21 0 148 143 136 132 146 147 26 79 58 144 145 85 149 150 88 31 34 43 52 78 123 0\n152 21 0 148 143 136 132 147 26 79 151 18 19 33 88 0\n153 -9 0 152 11 0\n154 -13 0 152 12 0\n155 0 153 154 134 90 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record000.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record000.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record000.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record000.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record000 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record000.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record000.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record000.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record000.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record000 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record000_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record000 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record000_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record000_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00027.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00027.record013
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "31c1f3521e8e6c5a561d86e4789e1783ed47191e665397151d70d1b61d4749d1743dd0ce3c4e5354c7362d2b1ac9b16c3bc1e4731e1745c970dd0f13e542b0aa468a6198562382e07b11944a94664529465854552342d074a318d1314d0b22c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db69a4924926924d2492692492492692492449249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record013 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record013 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record013.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record013.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record013.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 35), (facetIndex 36), (facetIndex 44), (facetIndex 45), (facetIndex 46), (facetIndex 47), (facetIndex 48), (facetIndex 49)]))
 (.leaf ([(facetIndex 42), (facetIndex 61), (facetIndex 63), (facetIndex 65), (facetIndex 66)])))
 (.branch 3
 (.leaf ([(facetIndex 51), (facetIndex 53), (facetIndex 68), (facetIndex 69)]))
 (.branch 4
 (.leaf ([(facetIndex 37), (facetIndex 70), (facetIndex 74), (facetIndex 75), (facetIndex 78)]))
 (.leaf ([(facetIndex 40), (facetIndex 52), (facetIndex 57), (facetIndex 76)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 38), (facetIndex 58), (facetIndex 72)]))
 (.leaf ([(facetIndex 41), (facetIndex 50), (facetIndex 54)])))
 (.branch 8
 (.leaf ([(facetIndex 39), (facetIndex 59), (facetIndex 64), (facetIndex 73)]))
 (.branch 9
 (.leaf ([(facetIndex 56), (facetIndex 60)]))
 (.leaf ([(facetIndex 71)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "304337593220117101875480624260000000164753z25;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 67)]))
 (.branch 2
 (.leaf ([(facetIndex 79)]))
 (.leaf ([(facetIndex 81)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 43), (facetIndex 55)]))
 (.leaf ([(facetIndex 62), (facetIndex 77)])))
 (.branch 6
 (.leaf ([(facetIndex 80)]))
 (.leaf ([(facetIndex 82)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1952200000000001000006000000006z20;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3, 4]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [3, 4]
def grouped2_0007 : List Nat := [4]
def grouped2_0008 : List Nat := [5]
def grouped2_0009 : List Nat := [5, 6]
def grouped2_0010 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0011 : List Nat := [6]
def grouped2_0012 : List Nat := [7]
def grouped2_0013 : List Nat := [7, 8, 9]
def grouped2_0014 : List Nat := [8]
def grouped2_0015 : List Nat := [8, 9]
def grouped2_0016 : List Nat := [9]
def grouped3_0017 : List Nat := [3]
def grouped3_0018 : List Nat := [3, 4]
def grouped3_0019 : List Nat := [3, 4, 5, 6]
def grouped3_0020 : List Nat := [4]
def grouped3_0021 : List Nat := [5]
def grouped3_0022 : List Nat := [5, 6]
def grouped3_0023 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record013 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record013_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00027.record013" "{\"atoms\":[{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0019\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00027.record013" 59

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00027.record013" "{\"ridges\":[[17,21],[20,517],[24,769],[34,532],[38,21],[43,774],[53,784],[55,834],[56,21],[62,780],[64,769],[66,517],[68,769],[69,769],[76,592],[77,774],[80,834],[82,780]],\"owners\":[[20,517,[17,40,43,60,62,64],[42,66]],[66,517,[17,40,43,60,62,64],[20,42]],[34,532,[17,40,60,64,77,82],[76]],[76,592,[23,69],[34,52,80]],[24,769,[43,55,62],[53,64,68,69]],[64,769,[55],[24,43,53,62,68,69]],[68,769,[43,55],[24,53,62,64,69]],[69,769,[43,62],[24,53,55,64,68]],[53,784,[82],[24,64,68,69,77,80]],[43,774,[77],[]],[77,774,[43],[]],[55,834,[80],[]],[80,834,[55],[]],[62,780,[82],[]],[82,780,[62],[]]],\"edges\":[[23,[17,20,34,40,42,43,60,62,64,66,76,77,82]],[44,[24,43,53,55,62,64,68,69,77,80,82]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00027.record013" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00027.record013\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-10,-7],[-10,-8],[-12,-10],[-14,-8],[-14,-11],[-14,-12],[-16,-1],[-16,-15],[-17,-15],[-18,-10],[-19,-16],[-19,-17],[-20,-15],[-20,-17],[-21,-3],[-21,-8],[-21,-12],[-21,-16],[-22,-16],[-23,-7],[-23,-18],[-23,-19],[-23,-21],[-24,-21],[-25,-6],[-26,-25],[-27,-10],[-27,-25],[-27,-26],[-28,-10],[-28,-14],[-29,-25],[-30,-8],[-30,-9],[-30,-10],[-30,-11],[-30,-12],[-30,-24],[-30,-28],[-30,-29],[-31,-7],[-31,-18],[-31,-19],[-31,-21],[-31,-27],[-1,-6,-15],[-2,1,8,10,19,20,21],[-22,1,8,10,19,20,21],[-5,1,8,19,21,29,31],[-28,3,24],[-4,10,14,20],[-21,14],[-23,10,14],[-24,10,20],[-13,31],[-10,29],[-29,10],[-14,30],[-30,14],[-20,31],[-31,20],[-32,11,13,23,24],[-33,8,12,16,28],[-34,6,17,26],[-35,7,18,21,27],[-36,15,19],[-37,25],[-38,33],[-39,32,38],[-40,32],[-40,38],[-41,39],[-42,40],[-43,34],[-44,36,37],[-45,36],[-45,37],[-46,35,44],[-47,35,45],[-48,35],[-47,44],[-48,45],[-49,43,47],[-50,43,48],[-51,43],[-49,46],[-50,47],[-51,48],[-52,41,51],[-52,42,50],[-52,49],[52],[-53,10,14],[-10,53],[-54,20,29],[-29,54],[-55,30],[-56,31],[-57,53],[-57,54],[-53,-54,57],[-58,55,56],[-59,57,58],[-57,59],[1,2,5,8,9,10,19,20,21,22,28,29,31],[4,10,13,14,20,21,23,24,29,30,31]],\"atoms\":[{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":43,\"b\":39},{\"tag\":\"incompatible\",\"a\":43,\"b\":40},{\"tag\":\"incompatible\",\"a\":52,\"b\":43},{\"tag\":\"incompatible\",\"a\":55,\"b\":40},{\"tag\":\"incompatible\",\"a\":55,\"b\":51},{\"tag\":\"incompatible\",\"a\":55,\"b\":52},{\"tag\":\"incompatible\",\"a\":57,\"b\":17},{\"tag\":\"incompatible\",\"a\":57,\"b\":56},{\"tag\":\"incompatible\",\"a\":58,\"b\":56},{\"tag\":\"incompatible\",\"a\":59,\"b\":43},{\"tag\":\"incompatible\",\"a\":60,\"b\":57},{\"tag\":\"incompatible\",\"a\":60,\"b\":58},{\"tag\":\"incompatible\",\"a\":62,\"b\":56},{\"tag\":\"incompatible\",\"a\":62,\"b\":58},{\"tag\":\"incompatible\",\"a\":64,\"b\":23},{\"tag\":\"incompatible\",\"a\":64,\"b\":40},{\"tag\":\"incompatible\",\"a\":64,\"b\":52},{\"tag\":\"incompatible\",\"a\":64,\"b\":57},{\"tag\":\"incompatible\",\"a\":66,\"b\":57},{\"tag\":\"incompatible\",\"a\":68,\"b\":39},{\"tag\":\"incompatible\",\"a\":68,\"b\":59},{\"tag\":\"incompatible\",\"a\":68,\"b\":60},{\"tag\":\"incompatible\",\"a\":68,\"b\":64},{\"tag\":\"incompatible\",\"a\":69,\"b\":64},{\"tag\":\"incompatible\",\"a\":71,\"b\":38},{\"tag\":\"incompatible\",\"a\":72,\"b\":71},{\"tag\":\"incompatible\",\"a\":73,\"b\":43},{\"tag\":\"incompatible\",\"a\":73,\"b\":71},{\"tag\":\"incompatible\",\"a\":73,\"b\":72},{\"tag\":\"incompatible\",\"a\":76,\"b\":43},{\"tag\":\"incompatible\",\"a\":76,\"b\":55},{\"tag\":\"incompatible\",\"a\":77,\"b\":71},{\"tag\":\"incompatible\",\"a\":80,\"b\":40},{\"tag\":\"incompatible\",\"a\":80,\"b\":42},{\"tag\":\"incompatible\",\"a\":80,\"b\":43},{\"tag\":\"incompatible\",\"a\":80,\"b\":51},{\"tag\":\"incompatible\",\"a\":80,\"b\":52},{\"tag\":\"incompatible\",\"a\":80,\"b\":69},{\"tag\":\"incompatible\",\"a\":80,\"b\":76},{\"tag\":\"incompatible\",\"a\":80,\"b\":77},{\"tag\":\"incompatible\",\"a\":82,\"b\":39},{\"tag\":\"incompatible\",\"a\":82,\"b\":59},{\"tag\":\"incompatible\",\"a\":82,\"b\":60},{\"tag\":\"incompatible\",\"a\":82,\"b\":64},{\"tag\":\"incompatible\",\"a\":82,\"b\":73},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[17,38,56]},{\"tag\":\"mate\",\"ridge\":517,\"a\":20,\"owners\":[17,40,43,60,62,64]},{\"tag\":\"mate\",\"ridge\":517,\"a\":66,\"owners\":[17,40,43,60,62,64]},{\"tag\":\"mate\",\"ridge\":532,\"a\":34,\"owners\":[17,40,60,64,77,82]},{\"tag\":\"mate\",\"ridge\":592,\"a\":76,\"owners\":[23,69]},{\"tag\":\"mate\",\"ridge\":769,\"a\":24,\"owners\":[43,55,62]},{\"tag\":\"mate\",\"ridge\":769,\"a\":64,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":769,\"a\":68,\"owners\":[43,55]},{\"tag\":\"mate\",\"ridge\":769,\"a\":69,\"owners\":[43,62]},{\"tag\":\"mate\",\"ridge\":784,\"a\":53,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":774,\"a\":43,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":774,\"a\":77,\"owners\":[43]},{\"tag\":\"mate\",\"ridge\":834,\"a\":55,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":834,\"a\":80,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":780,\"a\":62,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":780,\"a\":82,\"owners\":[62]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[51,53,68,69],\"full_literals\":[-32,11,13,23,24]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[40,52,57,76],\"full_literals\":[-33,8,12,16,28]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[38,58,72],\"full_literals\":[-34,6,17,26]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[39,59,64,73],\"full_literals\":[-35,7,18,21,27]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[56,60],\"full_literals\":[-36,15,19]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[71],\"full_literals\":[-37,25]},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-38,false,33],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-39,32,38],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-40,32,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-40,false,38],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-41,false,39],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-42,false,40],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-43,34,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-44,36,37],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-45,36,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-45,false,37],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-46,35,44],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-47,35,45],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-48,35,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-47,false,44],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-48,false,45],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-49,43,47],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-50,43,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-51,43,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-49,false,46],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-50,false,47],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-51,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-52,41,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-52,42,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-52,false,49],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[43,55],\"full_literals\":[-53,10,14]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":43,\"full_literals\":[-10,53]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[62,77],\"full_literals\":[-54,20,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":77,\"full_literals\":[-29,54]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[80],\"full_literals\":[-55,30]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[82],\"full_literals\":[-56,31]},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-57,53,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-57,false,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-53,-54,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-58,55,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-59,57,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0019\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-57,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"edge\",\"edge\":23,\"owners\":[17,20,34,40,42,43,60,62,64,66,76,77,82]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[24,43,53,55,62,64,68,69,77,80,82]}]}"
  "107 49 0 92 91 0\n108 46 0 107 86 0\n109 -31 0 108 107 41 42 43 44 45 61 65 13 14 78 66 75 76 67 79 25 26 83 64 74 0\n110 -13 0 109 55 0\n111 -20 0 109 60 0\n112 -56 0 109 98 0\n113 -40 -30 0 110 109 111 40 39 38 37 36 35 34 33 70 71 62 68 22 23 63 7 19 47 49 105 0\n114 -16 -30 0 109 111 40 39 35 34 33 7 11 18 19 47 49 105 0\n115 -27 -34 -1 19 -44 0 28 29 67 75 66 9 46 64 0\n116 -34 -1 -23 -47 0 23 22 21 20 81 115 65 79 76 77 66 67 9 46 26 64 0\n117 -48 -23 0 23 21 20 80 82 65 77 28 67 0\n118 -23 -30 0 92 109 111 113 73 90 87 40 39 35 34 33 22 23 117 84 74 116 47 48 49 105 0\n119 -51 0 85 88 74 82 76 77 67 25 26 64 9 12 66 0\n120 41 0 119 92 89 0\n121 39 0 120 72 0\n122 -14 -33 0 4 6 31 58 63 114 0\n123 32 21 -59 0 121 92 112 111 69 70 68 73 90 87 122 59 97 102 103 99 100 93 95 1 10 27 32 65 67 79 77 0\n124 30 21 -59 0 112 111 108 92 58 97 102 103 99 100 93 95 1 2 3 10 27 30 32 65 67 78 77 75 79 87 90 73 71 68 63 8 11 66 0\n125 21 -59 0 110 123 124 36 38 62 118 0\n126 -21 0 110 121 15 16 17 18 23 24 52 50 63 5 68 62 69 0\n127 -59 0 126 125 0\n128 -57 0 127 104 0\n129 -30 0 110 121 36 38 59 118 62 122 69 68 0\n130 -14 0 129 58 0\n131 -10 0 128 56 94 96 101 0\n132 -29 0 131 57 0\n133 -24 0 131 111 54 0\n134 -4 0 131 130 111 51 0\n135 -23 0 131 130 53 0\n136 0 134 132 131 110 111 126 135 133 130 129 109 106 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record013.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record013.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record013.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record013.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record013 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record013.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record013.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record013.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record013.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record013 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record013_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record013 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record013_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record013_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00027.record013

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00027.record014
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "7cd4b1a1e8e6958761b91e2785e0fb51c6479396551d46d4749d1743dd0e6338d531cf0b62d2b1ae1b26c5b0ee4731e1745c970dd0f13cacc4a522a91a298661588e0b81ec46512a519294651548d0b41dc0e4328c6384d1314d0b22c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "349a4924924d2492492492492492492491249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record014 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record014 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record014.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record014.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record014.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 39), (facetIndex 58), (facetIndex 62), (facetIndex 63), (facetIndex 65)]))
 (.leaf ([(facetIndex 41), (facetIndex 48), (facetIndex 52), (facetIndex 54), (facetIndex 67), (facetIndex 78)])))
 (.branch 3
 (.leaf ([(facetIndex 42), (facetIndex 57), (facetIndex 68), (facetIndex 79)]))
 (.branch 4
 (.leaf ([(facetIndex 37), (facetIndex 38), (facetIndex 45), (facetIndex 46), (facetIndex 47), (facetIndex 49), (facetIndex 50), (facetIndex 51)]))
 (.leaf ([(facetIndex 43), (facetIndex 44), (facetIndex 53), (facetIndex 55), (facetIndex 56)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 40), (facetIndex 59), (facetIndex 60)]))
 (.leaf ([(facetIndex 64), (facetIndex 75)])))
 (.branch 8
 (.leaf ([(facetIndex 69), (facetIndex 70), (facetIndex 71), (facetIndex 72)]))
 (.branch 9
 (.leaf ([(facetIndex 73), (facetIndex 74), (facetIndex 76)]))
 (.leaf ([(facetIndex 61)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "2108688777721006009550244141333133344215033z25;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 1
 (.leaf ([(facetIndex 66)]))
 (.branch 2
 (.leaf ([(facetIndex 77)]))
 (.leaf ([(facetIndex 80)]))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨2, sparse_nat% "204z26;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 3
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3, 4]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [3, 4]
def grouped2_0009 : List Nat := [4]
def grouped2_0010 : List Nat := [5]
def grouped2_0011 : List Nat := [5, 6]
def grouped2_0012 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0013 : List Nat := [6]
def grouped2_0014 : List Nat := [7]
def grouped2_0015 : List Nat := [7, 8, 9]
def grouped2_0016 : List Nat := [8]
def grouped2_0017 : List Nat := [8, 9]
def grouped2_0018 : List Nat := [9]
def grouped3_0019 : List Nat := [0]
def grouped3_0021 : List Nat := [1]
def grouped3_0022 : List Nat := [1, 2]
def grouped3_0023 : List Nat := [2]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record014 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record014_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00027.record014" "{\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0017\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0017\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00027.record014" 69

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00027.record014" "{\"ridges\":[[5,26],[8,266],[16,28],[22,25],[32,26],[40,21],[40,22],[48,26],[50,266],[51,266],[52,266],[56,98],[60,28],[61,21],[61,28],[64,21],[66,120],[67,25],[71,26],[71,28],[72,22],[72,28],[75,22],[76,98],[77,26],[77,98],[78,26],[80,28]],\"owners\":[[22,25,[5,16,45,46,47,48,58,59,60,66],[67]],[67,25,[5,16,45,46,47,58,59,60,66],[22,48]],[8,266,[32,72,78],[38,50,51,52]],[50,266,[32,72,78],[8,38,51,52]],[51,266,[32,72,78],[8,38,50,52]],[52,266,[32,72],[8,38,50,51,78]],[66,120,[77,80],[]]],\"edges\":[[28,[8,22,32,38,50,51,52,61,67,72,78]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00027.record014" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00027.record014\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-10,-8],[-24,-23],[-29,-7],[-29,-21],[-29,-22],[-29,-24],[-29,-25],[-29,-26],[-29,-27],[-31,-29],[-32,-29],[-33,-6],[-33,-8],[-33,-13],[-33,-23],[-35,-29],[-36,-29],[-38,-9],[-38,-19],[-38,-28],[-39,-7],[-39,-11],[-39,-12],[-39,-18],[-39,-21],[-39,-22],[-39,-25],[-39,-26],[-39,-31],[-39,-32],[-39,-34],[-39,-35],[-39,-36],[-39,-37],[-8,-24,-27],[-8,-34,-37],[-4,1,3,11,12,13,14,21,22,23,29],[-30,1,3,11,12,13,21,22,23,29],[-1,-33,-39],[-5,-33,-39],[-14,-33,-39],[-33,-39,-40],[-2,5,34,40],[-15,5,34,40],[-16,5,34,40],[-17,5,34],[-20,-38,-39],[-3,-33,-41],[-23,-34,-41],[-24,-33,-41],[-29,39,41],[-42,7,21,25,26,28],[-43,9,10,18,19,20],[-44,8,22,23],[-45,27,37],[-46,31,32,33,34],[-47,35,36,38],[-48,24],[-49,42],[-50,43],[-51,50],[-52,49,51],[-53,49],[-54,44],[-54,45],[-55,47,48],[-56,47],[-56,48],[-57,46,55],[-58,46,56],[-59,46],[-58,55],[-59,56],[-60,54,58],[-61,54,59],[-60,57],[-61,58],[-62,59],[-63,52,62],[-63,53,61],[-63,60],[63],[-64,29],[-29,64],[-65,39],[-66,41],[-67,65],[-67,66],[-68,64,67],[-64,-67,69],[68],[-69],[2,4,5,6,15,16,17,24,30,34,40]],\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":44,\"b\":40},{\"tag\":\"incompatible\",\"a\":61,\"b\":60},{\"tag\":\"incompatible\",\"a\":66,\"b\":39},{\"tag\":\"incompatible\",\"a\":66,\"b\":58},{\"tag\":\"incompatible\",\"a\":66,\"b\":59},{\"tag\":\"incompatible\",\"a\":66,\"b\":61},{\"tag\":\"incompatible\",\"a\":66,\"b\":62},{\"tag\":\"incompatible\",\"a\":66,\"b\":63},{\"tag\":\"incompatible\",\"a\":66,\"b\":64},{\"tag\":\"incompatible\",\"a\":69,\"b\":66},{\"tag\":\"incompatible\",\"a\":70,\"b\":66},{\"tag\":\"incompatible\",\"a\":71,\"b\":38},{\"tag\":\"incompatible\",\"a\":71,\"b\":40},{\"tag\":\"incompatible\",\"a\":71,\"b\":47},{\"tag\":\"incompatible\",\"a\":71,\"b\":60},{\"tag\":\"incompatible\",\"a\":73,\"b\":66},{\"tag\":\"incompatible\",\"a\":74,\"b\":66},{\"tag\":\"incompatible\",\"a\":76,\"b\":43},{\"tag\":\"incompatible\",\"a\":76,\"b\":55},{\"tag\":\"incompatible\",\"a\":76,\"b\":65},{\"tag\":\"incompatible\",\"a\":77,\"b\":39},{\"tag\":\"incompatible\",\"a\":77,\"b\":45},{\"tag\":\"incompatible\",\"a\":77,\"b\":46},{\"tag\":\"incompatible\",\"a\":77,\"b\":53},{\"tag\":\"incompatible\",\"a\":77,\"b\":58},{\"tag\":\"incompatible\",\"a\":77,\"b\":59},{\"tag\":\"incompatible\",\"a\":77,\"b\":62},{\"tag\":\"incompatible\",\"a\":77,\"b\":63},{\"tag\":\"incompatible\",\"a\":77,\"b\":69},{\"tag\":\"incompatible\",\"a\":77,\"b\":70},{\"tag\":\"incompatible\",\"a\":77,\"b\":72},{\"tag\":\"incompatible\",\"a\":77,\"b\":73},{\"tag\":\"incompatible\",\"a\":77,\"b\":74},{\"tag\":\"incompatible\",\"a\":77,\"b\":75},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[40,61,64]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[40,72,75]},{\"tag\":\"mate\",\"ridge\":25,\"a\":22,\"owners\":[5,16,45,46,47,48,58,59,60,66]},{\"tag\":\"mate\",\"ridge\":25,\"a\":67,\"owners\":[5,16,45,46,47,58,59,60,66]},{\"tag\":\"three\",\"ridge\":26,\"vertices\":[5,71,77]},{\"tag\":\"three\",\"ridge\":26,\"vertices\":[32,71,77]},{\"tag\":\"three\",\"ridge\":26,\"vertices\":[48,71,77]},{\"tag\":\"three\",\"ridge\":26,\"vertices\":[71,77,78]},{\"tag\":\"mate\",\"ridge\":266,\"a\":8,\"owners\":[32,72,78]},{\"tag\":\"mate\",\"ridge\":266,\"a\":50,\"owners\":[32,72,78]},{\"tag\":\"mate\",\"ridge\":266,\"a\":51,\"owners\":[32,72,78]},{\"tag\":\"mate\",\"ridge\":266,\"a\":52,\"owners\":[32,72]},{\"tag\":\"three\",\"ridge\":98,\"vertices\":[56,76,77]},{\"tag\":\"three\",\"ridge\":28,\"vertices\":[16,71,80]},{\"tag\":\"three\",\"ridge\":28,\"vertices\":[60,72,80]},{\"tag\":\"three\",\"ridge\":28,\"vertices\":[61,71,80]},{\"tag\":\"mate\",\"ridge\":120,\"a\":66,\"owners\":[77,80]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[39,58,62,63,65],\"full_literals\":[-42,7,21,25,26,28]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[43,44,53,55,56],\"full_literals\":[-43,9,10,18,19,20]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[40,59,60],\"full_literals\":[-44,8,22,23]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[64,75],\"full_literals\":[-45,27,37]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[69,70,71,72],\"full_literals\":[-46,31,32,33,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[73,74,76],\"full_literals\":[-47,35,36,38]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[61],\"full_literals\":[-48,24]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-49,42,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-50,false,43],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-51,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-52,49,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-53,49,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-54,44,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-54,false,45],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0018\",\"joined_name\":\"grouped2_0017\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-55,47,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0018\",\"joined_name\":\"grouped2_0017\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-56,47,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0018\",\"joined_name\":\"grouped2_0017\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-56,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-57,46,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-58,46,56],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-59,46,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-58,false,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-59,false,56],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-60,54,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-61,54,59],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-60,false,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-61,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-62,false,59],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-63,52,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-63,53,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-63,false,60],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[66],\"full_literals\":[-64,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":66,\"full_literals\":[-29,64]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[77],\"full_literals\":[-65,39]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[80],\"full_literals\":[-66,41]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-67,65,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-67,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-68,64,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-64,-67,69],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":28,\"owners\":[8,22,32,38,50,51,52,61,67,72,78]}]}"
  "94 60 0 82 81 0\n95 57 0 94 76 0\n96 -59 -67 0 87 85 31 30 29 88 86 71 73 56 68 50 58 0\n97 -56 -67 0 82 96 78 79 87 85 33 32 28 27 26 25 24 21 67 68 57 58 18 19 20 47 2 52 59 62 63 61 80 60 75 53 64 1 54 0\n98 -24 -67 0 94 97 87 85 34 31 30 29 26 88 86 2 50 56 70 74 64 65 54 55 35 0\n99 46 -67 0 95 82 98 58 97 87 85 33 32 28 27 25 21 69 70 66 77 57 80 20 63 52 59 0\n100 -67 0 92 87 88 90 85 86 84 22 23 25 26 29 30 31 98 99 56 12 14 15 39 40 41 42 48 38 37 43 44 45 46 93 0\n101 64 0 100 91 89 0\n102 29 0 101 83 0\n103 -7 0 102 3 0\n104 -21 0 102 4 0\n105 -22 0 102 5 0\n106 -24 0 102 6 0\n107 -25 0 102 7 0\n108 -26 0 102 8 0\n109 -27 0 102 9 0\n110 -31 0 102 10 0\n111 -32 0 102 11 0\n112 -35 0 102 16 0\n113 -36 0 102 17 0\n114 -48 0 106 58 0\n115 -56 0 114 68 0\n116 -59 0 115 73 0\n117 54 0 94 116 82 114 113 112 107 108 103 104 74 75 72 80 66 63 57 59 20 52 0\n118 44 0 117 64 0\n119 45 0 117 65 0\n120 37 0 119 109 55 0\n121 -39 0 120 34 0\n122 41 0 121 102 51 0\n123 -33 0 118 105 13 15 54 0\n124 -34 0 120 122 118 105 36 49 54 0\n125 -46 0 124 110 123 111 56 0\n126 55 0 125 95 69 0\n127 -58 0 125 115 70 0\n128 47 0 126 114 66 0\n129 -61 0 127 77 0\n130 38 0 128 112 113 57 0\n131 53 0 129 82 80 0\n132 -28 0 130 20 0\n133 49 0 131 63 0\n134 -42 0 132 104 103 108 107 52 0\n135 0 133 134 59 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record014.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record014.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record014.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record014.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record014 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record014.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record014.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record014.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record014.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record014 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record014_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record014_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record014_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record014_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record014_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record014_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record014_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record014 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record014_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record014_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record014_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00027.record014
