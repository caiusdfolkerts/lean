module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow19Part00027Frames
public import GraphInputsRow19Part00027Leaves
public import GraphInputsRow19Part00027Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00027.record054
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2783d1ac670bc66a5a1e996958766391e2783e9c4f16a669a66598e4b91e5a539655354b51d58d4b4ad2743d94c73c2d8b92c6b86c9b16c3b61e4751c6785c9715c3743c8f0bc1f2e0b41d25286856624a9614a51964382d0b41c47"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "34da69b49b6db4db69a4da49a6d34934db4926d34db249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record054 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record054 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record054.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record054.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record054.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 19), (facetIndex 34), (facetIndex 35)]))
 (.leaf ([(facetIndex 31), (facetIndex 33), (facetIndex 37), (facetIndex 66)])))
 (.branch 3
 (.leaf ([(facetIndex 25), (facetIndex 27)]))
 (.leaf ([(facetIndex 40), (facetIndex 42), (facetIndex 48), (facetIndex 55)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 21), (facetIndex 62), (facetIndex 63)]))
 (.leaf ([(facetIndex 43), (facetIndex 44), (facetIndex 47), (facetIndex 71)])))
 (.branch 7
 (.leaf ([(facetIndex 50), (facetIndex 68)]))
 (.leaf ([(facetIndex 24), (facetIndex 26)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "a06040900000600183a05ac30080082005d702z10;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 29), (facetIndex 32), (facetIndex 54)]))
 (.leaf ([(facetIndex 18), (facetIndex 60), (facetIndex 64)])))
 (.branch 3
 (.leaf ([(facetIndex 59), (facetIndex 67), (facetIndex 69)]))
 (.leaf ([(facetIndex 49), (facetIndex 65), (facetIndex 72)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 16), (facetIndex 17), (facetIndex 41), (facetIndex 61)]))
 (.leaf ([(facetIndex 38), (facetIndex 58), (facetIndex 70)])))
 (.branch 7
 (.leaf ([(facetIndex 20), (facetIndex 22), (facetIndex 23), (facetIndex 39), (facetIndex 45), (facetIndex 51), (facetIndex 52), (facetIndex 53)]))
 (.branch 8
 (.leaf ([(facetIndex 28), (facetIndex 30), (facetIndex 46), (facetIndex 56), (facetIndex 57)]))
 (.leaf ([(facetIndex 36)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "305202031004125770066603007600040650800000707000066060144z10;"⟩
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
def grouped2_0008 : List Nat := [4]
def grouped2_0009 : List Nat := [4, 5]
def grouped2_0010 : List Nat := [4, 5, 6, 7]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7]
def grouped2_0014 : List Nat := [7]
def grouped3_0015 : List Nat := [0]
def grouped3_0016 : List Nat := [0, 1]
def grouped3_0017 : List Nat := [1]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record054 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record054_matrix_checked

def leafCount : Nat := 4
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaf0000 : List (Fin data.count) := [(facetIndex 7), (facetIndex 11), (facetIndex 25), (facetIndex 35), (facetIndex 37), (facetIndex 47), (facetIndex 54), (facetIndex 55), (facetIndex 62), (facetIndex 64), (facetIndex 67), (facetIndex 68), (facetIndex 72)]
theorem leaf0000_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0000 = true := by
  decide +kernel
theorem leaf0000_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0000 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0000_counts_checked
def leaf0001 : List (Fin data.count) := [(facetIndex 14), (facetIndex 15), (facetIndex 26), (facetIndex 27), (facetIndex 35), (facetIndex 47), (facetIndex 51), (facetIndex 55), (facetIndex 57), (facetIndex 60), (facetIndex 62), (facetIndex 66), (facetIndex 69)]
theorem leaf0001_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0001 = true := by
  decide +kernel
theorem leaf0001_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0001 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0001_counts_checked
def leaf0002 : List (Fin data.count) := [(facetIndex 1), (facetIndex 7), (facetIndex 26), (facetIndex 35), (facetIndex 47), (facetIndex 51), (facetIndex 55), (facetIndex 57), (facetIndex 62), (facetIndex 64), (facetIndex 66), (facetIndex 67), (facetIndex 68)]
theorem leaf0002_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0002 = true := by
  decide +kernel
theorem leaf0002_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0002 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0002_counts_checked
def leaf0003 : List (Fin data.count) := [(facetIndex 4), (facetIndex 7), (facetIndex 25), (facetIndex 35), (facetIndex 47), (facetIndex 51), (facetIndex 55), (facetIndex 57), (facetIndex 62), (facetIndex 64), (facetIndex 66), (facetIndex 67), (facetIndex 68)]
theorem leaf0003_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0003 = true := by
  decide +kernel
theorem leaf0003_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0003 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0003_counts_checked
def leavesTable : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf (leaf0000))
 (.leaf (leaf0001)))
 (.branch 3
 (.leaf (leaf0002))
 (.leaf (leaf0003))))
def leaves (j : Fin leafCount) : List (Fin data.count) := leavesTable.get j.val

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00027.record054" "{\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00027.record054" 71

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00027.record054" "{\"ridges\":[[1,262],[2,266],[19,262],[19,266],[25,262],[27,262],[33,521],[34,266],[35,266],[35,522],[37,577],[37,592],[42,392],[43,97],[47,133],[50,41],[51,561],[53,657],[55,168],[60,284],[62,52],[64,262],[64,402],[66,536],[66,578],[67,402]],\"owners\":[[1,262,[60,61,64],[19,25,27]],[19,262,[64],[1,25,27,60,61]],[25,262,[60,61,64],[1,19,27]],[27,262,[60],[1,19,25,61,64]],[64,262,[1,19,25],[27,60,61]],[2,266,[60,61,67],[19,34,35]],[19,266,[67],[2,34,35,60,61]],[34,266,[60],[2,19,35,61,67]],[35,266,[60,61,67],[2,19,34]],[33,521,[51,53],[3,31,35,52,54]],[35,522,[11,66],[3,33]],[37,577,[54],[4,26,33,46,52,57]],[66,578,[4,26],[12,33,63]],[43,97,[32,54],[5,24,36,47,49,56,57]],[47,133,[7,18,22,27,39,42],[6,40,44,45]],[50,41,[17,32,41,54],[8,28,38,40,49,51,55]],[55,168,[15,68],[8,40,70]],[42,392,[67],[9,34,55,61,69,70]],[66,536,[51,53],[11,31,52,72]],[37,592,[72],[12,46,52,57,63,66]],[62,52,[14,38,44,68],[13,20,43,58]],[51,561,[57],[]],[53,657,[],[]],[60,284,[69],[]],[64,402,[67],[]],[67,402,[64],[]]],\"edges\":[[15,[1,2,19,25,27,34,35,60,61,64,67]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00027.record054" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00027.record054\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-14,-11],[-14,-13],[-15,-14],[-21,-16],[-22,-9],[-22,-17],[-22,-18],[-22,-19],[-22,-20],[-23,-11],[-23,-15],[-29,-23],[-32,-16],[-32,-31],[-33,-18],[-33,-23],[-34,-11],[-34,-25],[-34,-30],[-34,-33],[-37,-33],[-39,-24],[-39,-26],[-40,-8],[-40,-16],[-40,-21],[-40,-27],[-40,-39],[-41,-13],[-42,-23],[-44,-19],[-44,-36],[-44,-42],[-45,-9],[-45,-12],[-45,-16],[-45,-21],[-46,-9],[-46,-10],[-46,-25],[-46,-26],[-46,-28],[-46,-30],[-46,-39],[-46,-40],[-48,-41],[-48,-46],[-1,39,40,43],[-10,43],[-14,39,40,43],[-16,39],[-43,1,10,14],[-2,39,40,45],[-10,45],[-21,39],[-22,39,40,45],[-20,34,35],[-22,5,44],[-23,36],[-44,3,15],[-29,19,36],[-31,4,9,12,16,25,28],[-33,8,19,27,36],[-37,7,46],[-28,45],[-44,34,35],[-23,49],[-41,6,24,30,46],[-34,38],[-35],[-39,47],[-43,45],[-45,43],[-50,10,21,22],[-51,18,20,23,44],[-52,14,16],[-53,26,28,32,37],[-54,11,41,42],[-55,29,30,31,48],[-56,33,46],[-57,13,15],[-15,57],[-58,50],[-58,51],[-59,52,53],[-60,52],[-60,53],[-61,58,60],[-62,58],[-61,59],[-62,60],[-63,54],[-63,55],[-64,56,57],[-65,56],[-65,57],[-66,63,65],[-67,63],[-66,64],[-67,65],[-68,61],[-68,62,67],[-68,66],[68],[-69,17,19,36],[-19,69],[-36,69],[-70,9,39,43],[-39,70],[-43,70],[-71,69,70],[-70,71],[-69,71],[-4,-5,-14,-22,-23,-31,-36,-37,-41,-43,-45,-46,-49],[-6,-7,-15,-16,-22,-31,-34,-37,-38,-39,-41,-44,-47],[-1,-4,-15,-22,-31,-34,-37,-38,-41,-43,-44,-45,-46],[-3,-4,-14,-22,-31,-34,-37,-38,-41,-43,-44,-45,-46],[1,2,10,14,16,21,22,39,40,43,45]],\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":25,\"b\":21},{\"tag\":\"incompatible\",\"a\":25,\"b\":24},{\"tag\":\"incompatible\",\"a\":26,\"b\":25},{\"tag\":\"incompatible\",\"a\":34,\"b\":27},{\"tag\":\"incompatible\",\"a\":35,\"b\":18},{\"tag\":\"incompatible\",\"a\":35,\"b\":29},{\"tag\":\"incompatible\",\"a\":35,\"b\":31},{\"tag\":\"incompatible\",\"a\":35,\"b\":32},{\"tag\":\"incompatible\",\"a\":35,\"b\":33},{\"tag\":\"incompatible\",\"a\":37,\"b\":21},{\"tag\":\"incompatible\",\"a\":37,\"b\":26},{\"tag\":\"incompatible\",\"a\":43,\"b\":37},{\"tag\":\"incompatible\",\"a\":48,\"b\":27},{\"tag\":\"incompatible\",\"a\":48,\"b\":47},{\"tag\":\"incompatible\",\"a\":50,\"b\":31},{\"tag\":\"incompatible\",\"a\":50,\"b\":37},{\"tag\":\"incompatible\",\"a\":51,\"b\":21},{\"tag\":\"incompatible\",\"a\":51,\"b\":39},{\"tag\":\"incompatible\",\"a\":51,\"b\":44},{\"tag\":\"incompatible\",\"a\":51,\"b\":50},{\"tag\":\"incompatible\",\"a\":55,\"b\":50},{\"tag\":\"incompatible\",\"a\":60,\"b\":38},{\"tag\":\"incompatible\",\"a\":60,\"b\":40},{\"tag\":\"incompatible\",\"a\":61,\"b\":17},{\"tag\":\"incompatible\",\"a\":61,\"b\":27},{\"tag\":\"incompatible\",\"a\":61,\"b\":34},{\"tag\":\"incompatible\",\"a\":61,\"b\":41},{\"tag\":\"incompatible\",\"a\":61,\"b\":60},{\"tag\":\"incompatible\",\"a\":62,\"b\":24},{\"tag\":\"incompatible\",\"a\":63,\"b\":37},{\"tag\":\"incompatible\",\"a\":66,\"b\":32},{\"tag\":\"incompatible\",\"a\":66,\"b\":54},{\"tag\":\"incompatible\",\"a\":66,\"b\":63},{\"tag\":\"incompatible\",\"a\":67,\"b\":18},{\"tag\":\"incompatible\",\"a\":67,\"b\":22},{\"tag\":\"incompatible\",\"a\":67,\"b\":27},{\"tag\":\"incompatible\",\"a\":67,\"b\":34},{\"tag\":\"incompatible\",\"a\":68,\"b\":18},{\"tag\":\"incompatible\",\"a\":68,\"b\":19},{\"tag\":\"incompatible\",\"a\":68,\"b\":39},{\"tag\":\"incompatible\",\"a\":68,\"b\":40},{\"tag\":\"incompatible\",\"a\":68,\"b\":42},{\"tag\":\"incompatible\",\"a\":68,\"b\":44},{\"tag\":\"incompatible\",\"a\":68,\"b\":60},{\"tag\":\"incompatible\",\"a\":68,\"b\":61},{\"tag\":\"incompatible\",\"a\":71,\"b\":62},{\"tag\":\"incompatible\",\"a\":71,\"b\":68},{\"tag\":\"mate\",\"ridge\":262,\"a\":1,\"owners\":[60,61,64]},{\"tag\":\"mate\",\"ridge\":262,\"a\":19,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":262,\"a\":25,\"owners\":[60,61,64]},{\"tag\":\"mate\",\"ridge\":262,\"a\":27,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":262,\"a\":64,\"owners\":[1,19,25]},{\"tag\":\"mate\",\"ridge\":266,\"a\":2,\"owners\":[60,61,67]},{\"tag\":\"mate\",\"ridge\":266,\"a\":19,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":266,\"a\":34,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":266,\"a\":35,\"owners\":[60,61,67]},{\"tag\":\"mate\",\"ridge\":521,\"a\":33,\"owners\":[51,53]},{\"tag\":\"mate\",\"ridge\":522,\"a\":35,\"owners\":[11,66]},{\"tag\":\"mate\",\"ridge\":577,\"a\":37,\"owners\":[54]},{\"tag\":\"mate\",\"ridge\":578,\"a\":66,\"owners\":[4,26]},{\"tag\":\"mate\",\"ridge\":97,\"a\":43,\"owners\":[32,54]},{\"tag\":\"mate\",\"ridge\":133,\"a\":47,\"owners\":[7,18,22,27,39,42]},{\"tag\":\"mate\",\"ridge\":41,\"a\":50,\"owners\":[17,32,41,54]},{\"tag\":\"mate\",\"ridge\":168,\"a\":55,\"owners\":[15,68]},{\"tag\":\"mate\",\"ridge\":392,\"a\":42,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":536,\"a\":66,\"owners\":[51,53]},{\"tag\":\"mate\",\"ridge\":592,\"a\":37,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":52,\"a\":62,\"owners\":[14,38,44,68]},{\"tag\":\"mate\",\"ridge\":561,\"a\":51,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":657,\"a\":53,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":284,\"a\":60,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":402,\"a\":64,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":402,\"a\":67,\"owners\":[64]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[19,34,35],\"full_literals\":[-50,10,21,22]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[31,33,37,66],\"full_literals\":[-51,18,20,23,44]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[25,27],\"full_literals\":[-52,14,16]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[40,42,48,55],\"full_literals\":[-53,26,28,32,37]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[21,62,63],\"full_literals\":[-54,11,41,42]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[43,44,47,71],\"full_literals\":[-55,29,30,31,48]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[50,68],\"full_literals\":[-56,33,46]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[24,26],\"full_literals\":[-57,13,15]},{\"tag\":\"group_take\",\"kind\":2,\"index\":7,\"member\":26,\"full_literals\":[-15,57]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-58,50,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-58,false,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-59,52,53],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-60,52,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-60,false,53],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-61,58,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-62,58,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-61,false,59],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-62,false,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-63,54,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-63,false,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-64,56,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-65,56,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-65,false,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-66,63,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-67,63,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-66,false,64],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-67,false,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-68,61,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-68,62,67],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-68,false,66],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[29,32,54],\"full_literals\":[-69,17,19,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":32,\"full_literals\":[-19,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":54,\"full_literals\":[-36,69]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[18,60,64],\"full_literals\":[-70,9,39,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":60,\"full_literals\":[-39,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":64,\"full_literals\":[-43,70]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-71,69,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-70,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-69,false,71],\"grouped\":true,\"kind\":3},{\"tag\":\"block\",\"leaf\":0,\"vertices\":[7,11,25,35,37,47,54,55,62,64,67,68,72]},{\"tag\":\"block\",\"leaf\":1,\"vertices\":[14,15,26,27,35,47,51,55,57,60,62,66,69]},{\"tag\":\"block\",\"leaf\":2,\"vertices\":[1,7,26,35,47,51,55,57,62,64,66,67,68]},{\"tag\":\"block\",\"leaf\":3,\"vertices\":[4,7,25,35,47,51,55,57,62,64,66,67,68]},{\"tag\":\"edge\",\"edge\":15,\"owners\":[1,2,19,25,27,34,35,60,61,64,67]}]}"
  "119 61 0 104 101 0\n120 66 0 104 103 0\n121 59 0 119 90 0\n122 64 0 120 99 0\n123 40 70 0 110 73 49 109 55 51 48 50 53 56 118 0\n124 71 0 122 104 112 113 109 106 107 51 123 24 27 45 63 80 94 95 100 102 91 86 76 2 3 81 0\n125 57 44 20 18 46 0 122 104 96 94 100 80 102 16 89 75 84 0\n126 -14 -57 0 2 3 81 0\n127 -22 -40 43 0 124 119 104 45 28 25 5 6 7 8 9 108 111 105 32 125 126 76 86 91 88 102 84 100 75 95 16 80 0\n128 -40 45 0 119 104 72 54 25 26 127 74 83 88 89 86 102 76 100 126 96 0\n129 46 57 0 122 70 94 80 15 20 57 66 125 0\n130 -46 45 0 128 123 72 38 44 108 0\n131 39 45 0 130 129 126 128 72 54 51 55 48 53 56 118 0\n132 60 46 0 119 104 70 91 88 102 84 100 95 80 15 16 20 57 66 75 0\n133 -23 45 0 120 130 65 132 87 131 23 129 126 86 76 13 77 21 80 95 97 92 10 11 30 81 78 29 0\n134 45 0 120 104 70 54 65 130 129 126 131 22 23 71 132 86 87 76 4 13 77 21 64 80 95 100 97 102 92 93 89 83 84 74 7 8 9 133 75 32 33 66 61 17 19 69 78 29 46 68 81 79 115 0\n135 -9 0 134 34 0\n136 -12 0 134 35 0\n137 -16 0 134 36 0\n138 -21 0 134 37 0\n139 43 0 134 73 0\n140 -57 -44 0 70 121 119 104 138 137 136 135 134 139 66 69 19 18 17 31 32 61 33 126 76 85 86 91 88 132 102 83 39 41 42 47 98 74 52 92 93 78 79 29 14 62 81 77 116 0\n141 -44 0 70 120 104 136 135 138 137 134 139 31 32 33 66 61 17 18 19 69 140 82 96 129 60 100 97 39 41 42 47 102 92 93 89 91 78 79 83 86 87 14 62 74 76 77 117 0\n142 57 0 120 104 138 141 137 136 135 134 139 96 129 100 97 39 40 41 42 43 47 102 92 93 89 91 83 84 86 87 74 76 7 9 58 1 75 12 30 59 67 79 78 14 62 77 114 0\n143 -14 0 142 126 0\n144 -52 0 143 137 76 0\n145 -60 0 144 86 0\n146 -62 0 145 91 0\n147 58 0 145 119 88 0\n148 46 0 145 132 0\n149 67 0 146 104 102 0\n150 50 0 147 83 0\n151 51 0 147 84 0\n152 -10 0 148 39 0\n153 63 0 149 98 0\n154 22 0 150 138 152 74 0\n155 54 0 153 92 0\n156 -18 0 154 7 0\n157 -20 0 154 9 0\n158 23 0 157 141 156 151 75 0\n159 -11 0 158 10 0\n160 -15 0 158 11 0\n161 -42 0 158 30 0\n162 13 0 160 142 81 0\n163 41 0 161 159 155 78 0\n164 0 163 162 29 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record054.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record054.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record054.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record054.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record054 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeafTable : ConcreteGrowth.Table (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record054.l) :=
(.branch 2
 (.branch 1
 (.leaf (⟨0, by decide⟩))
 (.leaf (⟨1, by decide⟩)))
 (.branch 3
 (.leaf (⟨2, by decide⟩))
 (.leaf (⟨3, by decide⟩))))
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record054.l := originalLeafTable.get j.val
def orbitWordTable : ConcreteGrowth.Table (List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record054.g)) :=
(.branch 2
 (.branch 1
 (.leaf ([]))
 (.leaf ([])))
 (.branch 3
 (.leaf ([]))
 (.leaf ([]))))
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record054.g) := orbitWordTable.get j.val
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record054.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record054.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record054 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record054_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record054_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record054_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record054_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record054_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record054_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record054_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record054 Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record054_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record054_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record054_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00027.record054
