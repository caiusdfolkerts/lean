module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow31Part00155Frames
public import GraphInputsRow31Part00155Leaves
public import GraphInputsRow31Part00155Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00155.record001
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "9d2cc970dc8f0bc5c9ca568da4e8ba999662d8769394e33a2e4b8ae17b619c571d26c97272996559366394e4b9b1665596558d4b51d68d9354d3352d2b61d175c398d6354d332cc7362e4b52ccb8acab46c5b91d4789d2729c6783d0f13cd48b09c0f0d24a89a0e8c6258560d88e0b81e346294a4990e64531625254550d60d2342d0754330d2324c530cd0b22c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6da49b6926d26d24936db69b49249a4924d2492692493492492492491249249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record001 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record001 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record001.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record001.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record001.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 67), (facetIndex 81), (facetIndex 94), (facetIndex 95), (facetIndex 96)]))
 (.leaf ([(facetIndex 106), (facetIndex 107), (facetIndex 113), (facetIndex 119)])))
 (.branch 3
 (.leaf ([(facetIndex 60), (facetIndex 74), (facetIndex 88), (facetIndex 89), (facetIndex 91), (facetIndex 92), (facetIndex 93)]))
 (.leaf ([(facetIndex 102), (facetIndex 103), (facetIndex 111), (facetIndex 112), (facetIndex 117), (facetIndex 118)]))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨2, sparse_nat% "7c07c050f0000a8a00000020000002z1e;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 4
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0003 : List Nat := [1]
def grouped3_0004 : List Nat := [2]
def grouped3_0005 : List Nat := [2, 3]
def grouped3_0006 : List Nat := [3]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record001 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record001_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00155.record001" "{\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"facet\",\"index\":117},{\"tag\":\"facet\",\"index\":118},{\"tag\":\"facet\",\"index\":119},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0005\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0005\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00155.record001" 43

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00155.record001" "{\"ridges\":[[14,321],[24,577],[24,580],[52,321],[53,577],[53,580],[59,321],[59,322],[65,321],[66,321],[68,321],[74,332],[75,577],[75,580],[80,577],[80,580],[81,356],[82,577],[83,577],[83,580],[88,344],[91,456],[93,840],[94,368],[96,864],[102,332],[106,356],[111,344],[112,456],[113,368]],\"owners\":[[14,321,[74,81,88,91,93,94,96],[52,59,65,66,68]],[52,321,[88,91,93,94,96],[14,59,65,66,68,74,81]],[59,321,[81,94,96],[14,52,65,66,68,74,88,91,93]],[65,321,[74,81,91,93,96],[14,52,59,66,68,88,94]],[66,321,[74,88,91,93],[14,52,59,65,68,81,94,96]],[68,321,[74,81,88,93,94,96],[14,52,59,65,66,91]],[59,322,[106,113],[14,52,65,66,68,102,111,112]],[24,577,[60,67,89,92,93,95,96],[53,75,80,82,83]],[53,577,[89,92,93,95,96],[24,60,67,75,80,82,83]],[75,577,[67,95,96],[24,53,60,80,82,83,89,92,93]],[80,577,[60,67,92,93,96],[24,53,75,82,83,89,95]],[82,577,[60,89,92,93],[24,53,67,75,80,83,95,96]],[83,577,[60,67,89,93,95,96],[24,53,75,80,82,92]],[24,580,[103,107,117,118,119],[53,75,80,82,83]],[53,580,[117,118,119],[24,75,80,82,83,103,107]],[75,580,[107,119],[24,53,80,82,83,103,117,118]],[80,580,[103,107,118],[24,53,75,82,83,117,119]],[83,580,[103,107,117,119],[24,53,75,80,82,118]],[74,332,[102],[]],[102,332,[74],[]],[81,356,[106],[]],[106,356,[81],[]],[88,344,[111],[]],[111,344,[88],[]],[91,456,[112],[]],[112,456,[91],[]],[93,840,[],[]],[94,368,[113],[]],[113,368,[94],[]],[96,864,[],[]]],\"edges\":[[40,[14,52,59,65,66,68,74,81,88,91,93,94,96,102,106,111,112,113]],[41,[24,53,60,67,75,80,82,83,89,92,93,95,96,103,107,117,118,119]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00155.record001" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00155.record001\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-11,-4],[-11,-6],[-13,-11],[-14,-4],[-14,-9],[-14,-13],[-15,-14],[-16,-11],[-16,-14],[-17,-6],[-18,-11],[-18,-17],[-19,-6],[-19,-18],[-20,-11],[-20,-17],[-20,-19],[-22,-9],[-22,-15],[-23,-14],[-23,-22],[-26,-11],[-26,-17],[-26,-19],[-28,-14],[-28,-22],[-32,-11],[-32,-17],[-32,-19],[-33,-11],[-33,-17],[-33,-19],[-34,-14],[-34,-22],[-1,11,14,17,19,21,22,24],[-3,17,19,21,22,24],[-5,14,22,24],[-7,11,14,19,21,24],[-8,11,17,19,21],[-10,11,14,17,21,22,24],[-5,27,31],[-2,6,9,18,20,21,23,24],[-4,18,20,21,23,24],[-12,9,23,24],[-13,6,9,20,21,24],[-15,6,18,20,21],[-16,6,9,18,21,23,24],[-2,26,28,32,33,34],[-4,32,33,34],[-12,28,34],[-13,26,28,33],[-16,26,28,32,34],[-11,25],[-25,11],[-14,27],[-27,14],[-17,29],[-29,17],[-19,30],[-30,19],[-21],[-22,31],[-31,22],[-24],[-9,35],[-14,35],[-22,35],[-23,35],[-27,36],[-28,36],[-31,36],[-34,36],[-6,37],[-11,37],[-17,37],[-18,37],[-19,37],[-20,37],[-25,38],[-26,38],[-29,38],[-30,38],[-32,38],[-33,38],[-36,39],[-35,39],[-35,-36,40],[-38,41],[-37,41],[-37,-38,42],[-39,-42,43],[-40,-41,43],[-43],[1,3,5,7,8,10,11,14,17,19,21,22,24,25,27,29,30,31],[2,4,6,9,12,13,15,16,18,20,21,23,24,26,28,32,33,34]],\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"facet\",\"index\":117},{\"tag\":\"facet\",\"index\":118},{\"tag\":\"facet\",\"index\":119},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":74,\"b\":53},{\"tag\":\"incompatible\",\"a\":74,\"b\":60},{\"tag\":\"incompatible\",\"a\":80,\"b\":74},{\"tag\":\"incompatible\",\"a\":81,\"b\":53},{\"tag\":\"incompatible\",\"a\":81,\"b\":67},{\"tag\":\"incompatible\",\"a\":81,\"b\":80},{\"tag\":\"incompatible\",\"a\":82,\"b\":81},{\"tag\":\"incompatible\",\"a\":83,\"b\":74},{\"tag\":\"incompatible\",\"a\":83,\"b\":81},{\"tag\":\"incompatible\",\"a\":88,\"b\":60},{\"tag\":\"incompatible\",\"a\":89,\"b\":74},{\"tag\":\"incompatible\",\"a\":89,\"b\":88},{\"tag\":\"incompatible\",\"a\":91,\"b\":60},{\"tag\":\"incompatible\",\"a\":91,\"b\":89},{\"tag\":\"incompatible\",\"a\":92,\"b\":74},{\"tag\":\"incompatible\",\"a\":92,\"b\":88},{\"tag\":\"incompatible\",\"a\":92,\"b\":91},{\"tag\":\"incompatible\",\"a\":94,\"b\":67},{\"tag\":\"incompatible\",\"a\":94,\"b\":82},{\"tag\":\"incompatible\",\"a\":95,\"b\":81},{\"tag\":\"incompatible\",\"a\":95,\"b\":94},{\"tag\":\"incompatible\",\"a\":103,\"b\":74},{\"tag\":\"incompatible\",\"a\":103,\"b\":88},{\"tag\":\"incompatible\",\"a\":103,\"b\":91},{\"tag\":\"incompatible\",\"a\":107,\"b\":81},{\"tag\":\"incompatible\",\"a\":107,\"b\":94},{\"tag\":\"incompatible\",\"a\":117,\"b\":74},{\"tag\":\"incompatible\",\"a\":117,\"b\":88},{\"tag\":\"incompatible\",\"a\":117,\"b\":91},{\"tag\":\"incompatible\",\"a\":118,\"b\":74},{\"tag\":\"incompatible\",\"a\":118,\"b\":88},{\"tag\":\"incompatible\",\"a\":118,\"b\":91},{\"tag\":\"incompatible\",\"a\":119,\"b\":81},{\"tag\":\"incompatible\",\"a\":119,\"b\":94},{\"tag\":\"mate\",\"ridge\":321,\"a\":14,\"owners\":[74,81,88,91,93,94,96]},{\"tag\":\"mate\",\"ridge\":321,\"a\":52,\"owners\":[88,91,93,94,96]},{\"tag\":\"mate\",\"ridge\":321,\"a\":59,\"owners\":[81,94,96]},{\"tag\":\"mate\",\"ridge\":321,\"a\":65,\"owners\":[74,81,91,93,96]},{\"tag\":\"mate\",\"ridge\":321,\"a\":66,\"owners\":[74,88,91,93]},{\"tag\":\"mate\",\"ridge\":321,\"a\":68,\"owners\":[74,81,88,93,94,96]},{\"tag\":\"mate\",\"ridge\":322,\"a\":59,\"owners\":[106,113]},{\"tag\":\"mate\",\"ridge\":577,\"a\":24,\"owners\":[60,67,89,92,93,95,96]},{\"tag\":\"mate\",\"ridge\":577,\"a\":53,\"owners\":[89,92,93,95,96]},{\"tag\":\"mate\",\"ridge\":577,\"a\":75,\"owners\":[67,95,96]},{\"tag\":\"mate\",\"ridge\":577,\"a\":80,\"owners\":[60,67,92,93,96]},{\"tag\":\"mate\",\"ridge\":577,\"a\":82,\"owners\":[60,89,92,93]},{\"tag\":\"mate\",\"ridge\":577,\"a\":83,\"owners\":[60,67,89,93,95,96]},{\"tag\":\"mate\",\"ridge\":580,\"a\":24,\"owners\":[103,107,117,118,119]},{\"tag\":\"mate\",\"ridge\":580,\"a\":53,\"owners\":[117,118,119]},{\"tag\":\"mate\",\"ridge\":580,\"a\":75,\"owners\":[107,119]},{\"tag\":\"mate\",\"ridge\":580,\"a\":80,\"owners\":[103,107,118]},{\"tag\":\"mate\",\"ridge\":580,\"a\":83,\"owners\":[103,107,117,119]},{\"tag\":\"mate\",\"ridge\":332,\"a\":74,\"owners\":[102]},{\"tag\":\"mate\",\"ridge\":332,\"a\":102,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":356,\"a\":81,\"owners\":[106]},{\"tag\":\"mate\",\"ridge\":356,\"a\":106,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":344,\"a\":88,\"owners\":[111]},{\"tag\":\"mate\",\"ridge\":344,\"a\":111,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":456,\"a\":91,\"owners\":[112]},{\"tag\":\"mate\",\"ridge\":456,\"a\":112,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":840,\"a\":93,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":368,\"a\":94,\"owners\":[113]},{\"tag\":\"mate\",\"ridge\":368,\"a\":113,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":864,\"a\":96,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":67,\"full_literals\":[-9,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":81,\"full_literals\":[-14,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":94,\"full_literals\":[-22,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":95,\"full_literals\":[-23,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":106,\"full_literals\":[-27,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":107,\"full_literals\":[-28,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":113,\"full_literals\":[-31,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":119,\"full_literals\":[-34,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":60,\"full_literals\":[-6,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":74,\"full_literals\":[-11,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":88,\"full_literals\":[-17,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":89,\"full_literals\":[-18,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":91,\"full_literals\":[-19,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":92,\"full_literals\":[-20,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":102,\"full_literals\":[-25,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":103,\"full_literals\":[-26,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":111,\"full_literals\":[-29,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":112,\"full_literals\":[-30,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":117,\"full_literals\":[-32,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":118,\"full_literals\":[-33,38]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0003\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-36,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0003\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-35,false,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0003\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-35,-36,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-38,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-37,false,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-37,-38,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-39,-42,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-40,-41,43],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":40,\"owners\":[14,52,59,65,66,68,74,81,88,91,93,94,96,102,106,111,112,113]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[24,53,60,67,75,80,82,83,89,92,93,95,96,103,107,117,118,119]}]}"
  "p cnf 43 95\n-11 -4 0\n-11 -6 0\n-13 -11 0\n-14 -4 0\n-14 -9 0\n-14 -13 0\n-15 -14 0\n-16 -11 0\n-16 -14 0\n-17 -6 0\n-18 -11 0\n-18 -17 0\n-19 -6 0\n-19 -18 0\n-20 -11 0\n-20 -17 0\n-20 -19 0\n-22 -9 0\n-22 -15 0\n-23 -14 0\n-23 -22 0\n-26 -11 0\n-26 -17 0\n-26 -19 0\n-28 -14 0\n-28 -22 0\n-32 -11 0\n-32 -17 0\n-32 -19 0\n-33 -11 0\n-33 -17 0\n-33 -19 0\n-34 -14 0\n-34 -22 0\n-1 11 14 17 19 21 22 24 0\n-3 17 19 21 22 24 0\n-5 14 22 24 0\n-7 11 14 19 21 24 0\n-8 11 17 19 21 0\n-10 11 14 17 21 22 24 0\n-5 27 31 0\n-2 6 9 18 20 21 23 24 0\n-4 18 20 21 23 24 0\n-12 9 23 24 0\n-13 6 9 20 21 24 0\n-15 6 18 20 21 0\n-16 6 9 18 21 23 24 0\n-2 26 28 32 33 34 0\n-4 32 33 34 0\n-12 28 34 0\n-13 26 28 33 0\n-16 26 28 32 34 0\n-11 25 0\n-25 11 0\n-14 27 0\n-27 14 0\n-17 29 0\n-29 17 0\n-19 30 0\n-30 19 0\n-21 0\n-22 31 0\n-31 22 0\n-24 0\n-9 35 0\n-14 35 0\n-22 35 0\n-23 35 0\n-27 36 0\n-28 36 0\n-31 36 0\n-34 36 0\n-6 37 0\n-11 37 0\n-17 37 0\n-18 37 0\n-19 37 0\n-20 37 0\n-25 38 0\n-26 38 0\n-29 38 0\n-30 38 0\n-32 38 0\n-33 38 0\n-36 39 0\n-35 39 0\n-35 -36 40 0\n-38 41 0\n-37 41 0\n-37 -38 42 0\n-39 -42 43 0\n-40 -41 43 0\n-43 0\n1 3 5 7 8 10 11 14 17 19 21 22 24 25 27 29 30 31 0\n2 4 6 9 12 13 15 16 18 20 21 23 24 26 28 32 33 34 0\n"
  "96 1 3 5 7 8 10 11 14 17 19 22 25 27 29 30 31 0 61 64 94 0\n97 2 4 6 9 12 13 15 16 18 20 23 26 28 32 33 34 0 61 64 95 0\n98 17 19 7 11 10 1 8 39 0 64 61 60 54 85 71 69 41 86 67 66 58 36 96 0\n99 19 17 1 11 39 0 64 61 86 67 66 40 38 39 98 0\n100 -19 39 0 64 61 85 70 72 50 86 68 65 13 14 17 24 29 32 47 46 43 42 45 97 0\n101 -17 39 0 64 61 85 70 72 50 86 68 65 10 12 16 23 28 31 47 46 43 42 45 97 0\n102 11 39 0 64 61 101 100 86 67 66 35 99 0\n103 39 0 64 61 85 86 70 72 65 68 50 102 1 2 3 8 11 15 22 27 30 46 42 97 0\n104 -42 0 103 93 91 0\n105 -11 0 104 53 74 79 90 0\n106 -25 0 105 54 0\n107 22 14 19 17 1 0 64 61 106 105 38 56 39 60 58 63 37 40 36 96 0\n108 33 34 4 6 20 13 9 12 15 18 23 26 28 32 16 0 97 48 0\n109 -22 0 64 93 18 19 21 26 34 62 67 44 71 87 92 88 89 80 83 84 73 76 78 52 49 51 108 0\n110 -14 0 64 93 4 5 6 7 9 20 25 33 55 66 44 69 87 92 88 89 80 83 84 73 76 78 108 0\n111 -19 0 104 59 77 82 90 0\n112 -17 0 104 57 75 81 90 0\n113 -1 0 112 110 105 111 61 109 64 35 0\n114 0 112 113 109 110 111 107 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record001.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record001.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record001.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record001.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record001 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record001.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record001.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record001.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record001.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record001 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record001_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record001 Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record001_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record001_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00155.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00155.record002
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "370bcd8a725ca6a5a8ba1eb46b19c6c9a56558d68d9362da4e538ce8b92e2b85ed86715c6695a4b91e745b15c5c9655554d58d5352d64d534cd8b52d2b45dd0ec370f2398d6394d538cd332cc7392d4b8ad2b2ac6bc1e8761e4751cc729e1745c5783d0f13cd82703c348ca2685a0ea26498960d88e0b81e344c9264590e625494950d48d0b41d90d4330e2348c9314c3322c4b0ac1b81d0721c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "126db6936d36924da4926db6936d36924da492492492492492492492492491249249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record002 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record002 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record002.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record002.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record002.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 58), (facetIndex 64), (facetIndex 70), (facetIndex 71), (facetIndex 93), (facetIndex 117)]))
 (.leaf ([(facetIndex 51), (facetIndex 77), (facetIndex 78), (facetIndex 79), (facetIndex 83), (facetIndex 84), (facetIndex 85), (facetIndex 89)])))
 (.branch 3
 (.leaf ([(facetIndex 101), (facetIndex 102), (facetIndex 103), (facetIndex 107), (facetIndex 108), (facetIndex 109), (facetIndex 113)]))
 (.leaf ([(facetIndex 94), (facetIndex 118), (facetIndex 124), (facetIndex 125)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 45), (facetIndex 46), (facetIndex 47), (facetIndex 48), (facetIndex 49), (facetIndex 50), (facetIndex 52), (facetIndex 53), (facetIndex 54), (facetIndex 55), (facetIndex 56), (facetIndex 57)]))
 (.leaf ([(facetIndex 76), (facetIndex 80), (facetIndex 86), (facetIndex 100), (facetIndex 104), (facetIndex 110)])))
 (.branch 7
 (.leaf ([(facetIndex 62), (facetIndex 63), (facetIndex 68), (facetIndex 69), (facetIndex 73), (facetIndex 74), (facetIndex 75)]))
 (.leaf ([(facetIndex 59), (facetIndex 60), (facetIndex 61), (facetIndex 65), (facetIndex 66), (facetIndex 67), (facetIndex 72)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b0000c00101524054950000c000814920524ddb7036ff8dbfe2492432492z22;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 95), (facetIndex 96), (facetIndex 97), (facetIndex 98), (facetIndex 99)]))
 (.leaf ([(facetIndex 119), (facetIndex 120), (facetIndex 121), (facetIndex 122), (facetIndex 123)])))
 (.branch 3
 (.leaf ([(facetIndex 81), (facetIndex 82), (facetIndex 87), (facetIndex 88), (facetIndex 90), (facetIndex 91), (facetIndex 92)]))
 (.leaf ([(facetIndex 105), (facetIndex 106), (facetIndex 111), (facetIndex 112), (facetIndex 114), (facetIndex 115), (facetIndex 116)]))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨2, sparse_nat% "5543f3c03c000002a28028z28;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 4
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
def grouped2_0010 : List Nat := [6, 7]
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1]
def grouped3_0014 : List Nat := [1]
def grouped3_0015 : List Nat := [2]
def grouped3_0016 : List Nat := [2, 3]
def grouped3_0017 : List Nat := [3]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record002 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record002_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00155.record002" "{\"atoms\":[{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"facet\",\"index\":116},{\"tag\":\"facet\",\"index\":117},{\"tag\":\"facet\",\"index\":120},{\"tag\":\"facet\",\"index\":122},{\"tag\":\"facet\",\"index\":123},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00155.record002" 52

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00155.record002" "{\"ridges\":[[17,577],[54,577],[54,578],[63,577],[69,577],[70,321],[71,577],[74,577],[75,577],[75,578],[81,332],[82,588],[87,340],[88,596],[90,452],[98,624],[106,588],[112,596],[115,708],[116,836],[120,616],[123,864]],\"owners\":[[70,321,[81,87,90,92],[16,53,62,68,73,75,95,97,99]],[17,577,[82,88,91,92,96,98,99],[54,63,69,71,74,75]],[54,577,[96,98,99],[17,63,69,71,74,75,82,88,91,92]],[63,577,[88,91,92,98,99],[17,54,69,71,74,75,82,96]],[69,577,[82,91,92,96,99],[17,54,63,71,74,75,88,98]],[71,577,[82,88,91,92],[17,54,63,69,74,75,96,98,99]],[74,577,[82,88,92,96,98,99],[17,54,63,69,71,75,91]],[75,577,[82,88,91,96,98],[17,54,63,69,71,74,92,99]],[54,578,[120,122,123],[17,63,69,71,74,75,106,112,115,116]],[75,578,[106,112,115,120,122],[17,54,63,69,71,74,116,123]],[81,332,[105],[]],[82,588,[106],[]],[106,588,[82],[]],[87,340,[111],[]],[88,596,[112],[]],[112,596,[88],[]],[90,452,[114],[]],[115,708,[91],[]],[116,836,[92],[]],[120,616,[96],[]],[98,624,[122],[]],[123,864,[99],[]]],\"edges\":[[41,[17,54,63,69,71,74,75,82,88,91,92,96,98,99,106,112,115,116,120,122,123]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00155.record002" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00155.record002\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-14,-11],[-14,-12],[-15,-13],[-15,-14],[-16,-15],[-17,-11],[-17,-12],[-17,-15],[-18,-15],[-19,-11],[-19,-12],[-19,-15],[-20,-11],[-20,-12],[-20,-15],[-22,-3],[-22,-5],[-22,-21],[-24,-3],[-24,-5],[-24,-21],[-25,-14],[-25,-17],[-25,-19],[-25,-20],[-26,-13],[-26,-14],[-26,-16],[-26,-17],[-26,-18],[-26,-19],[-26,-20],[-29,-13],[-29,-14],[-29,-16],[-29,-17],[-29,-18],[-29,-19],[-29,-20],[-35,-22],[-35,-24],[-37,-3],[-37,-5],[-37,-21],[-37,-35],[-7,13,16,18,20],[-1,14,17,19,20,22,23,24],[-2,22,23,24],[-4,17,19,20,23,24],[-6,14,19,20,22,24],[-8,14,17,19,20],[-9,14,17,20,22,23,24],[-10,14,17,19,22,23],[-2,36,37,38],[-10,28,31,33,36,37],[-13,27],[-14,28],[-28,14],[-16,30],[-17,31],[-31,17],[-18,32],[-33,19],[-34,20],[-36,22],[-23,37],[-38,24],[-39,3,5,7,8,21,35],[-40,11,12,15,25,26,29],[-41,39],[-42,41],[-43,40],[-44,43],[-45,42],[-45,44],[45],[-22,46],[-23,46],[-24,46],[-36,47],[-37,47],[-38,47],[-48,13,14,16,17,18,19,20],[-13,48],[-14,48],[-16,48],[-17,48],[-18,48],[-19,48],[-20,48],[-27,49],[-28,49],[-30,49],[-31,49],[-32,49],[-47,50],[-46,50],[-51,48],[-48,-49,51],[-50,-51,52],[-52],[1,2,4,6,8,9,10,14,17,19,20,22,23,24,28,31,33,34,36,37,38]],\"atoms\":[{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"facet\",\"index\":116},{\"tag\":\"facet\",\"index\":117},{\"tag\":\"facet\",\"index\":120},{\"tag\":\"facet\",\"index\":122},{\"tag\":\"facet\",\"index\":123},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":82,\"b\":76},{\"tag\":\"incompatible\",\"a\":82,\"b\":80},{\"tag\":\"incompatible\",\"a\":86,\"b\":81},{\"tag\":\"incompatible\",\"a\":86,\"b\":82},{\"tag\":\"incompatible\",\"a\":87,\"b\":86},{\"tag\":\"incompatible\",\"a\":88,\"b\":76},{\"tag\":\"incompatible\",\"a\":88,\"b\":80},{\"tag\":\"incompatible\",\"a\":88,\"b\":86},{\"tag\":\"incompatible\",\"a\":90,\"b\":86},{\"tag\":\"incompatible\",\"a\":91,\"b\":76},{\"tag\":\"incompatible\",\"a\":91,\"b\":80},{\"tag\":\"incompatible\",\"a\":91,\"b\":86},{\"tag\":\"incompatible\",\"a\":92,\"b\":76},{\"tag\":\"incompatible\",\"a\":92,\"b\":80},{\"tag\":\"incompatible\",\"a\":92,\"b\":86},{\"tag\":\"incompatible\",\"a\":96,\"b\":58},{\"tag\":\"incompatible\",\"a\":96,\"b\":64},{\"tag\":\"incompatible\",\"a\":96,\"b\":93},{\"tag\":\"incompatible\",\"a\":99,\"b\":58},{\"tag\":\"incompatible\",\"a\":99,\"b\":64},{\"tag\":\"incompatible\",\"a\":99,\"b\":93},{\"tag\":\"incompatible\",\"a\":100,\"b\":82},{\"tag\":\"incompatible\",\"a\":100,\"b\":88},{\"tag\":\"incompatible\",\"a\":100,\"b\":91},{\"tag\":\"incompatible\",\"a\":100,\"b\":92},{\"tag\":\"incompatible\",\"a\":104,\"b\":81},{\"tag\":\"incompatible\",\"a\":104,\"b\":82},{\"tag\":\"incompatible\",\"a\":104,\"b\":87},{\"tag\":\"incompatible\",\"a\":104,\"b\":88},{\"tag\":\"incompatible\",\"a\":104,\"b\":90},{\"tag\":\"incompatible\",\"a\":104,\"b\":91},{\"tag\":\"incompatible\",\"a\":104,\"b\":92},{\"tag\":\"incompatible\",\"a\":110,\"b\":81},{\"tag\":\"incompatible\",\"a\":110,\"b\":82},{\"tag\":\"incompatible\",\"a\":110,\"b\":87},{\"tag\":\"incompatible\",\"a\":110,\"b\":88},{\"tag\":\"incompatible\",\"a\":110,\"b\":90},{\"tag\":\"incompatible\",\"a\":110,\"b\":91},{\"tag\":\"incompatible\",\"a\":110,\"b\":92},{\"tag\":\"incompatible\",\"a\":117,\"b\":96},{\"tag\":\"incompatible\",\"a\":117,\"b\":99},{\"tag\":\"incompatible\",\"a\":122,\"b\":58},{\"tag\":\"incompatible\",\"a\":122,\"b\":64},{\"tag\":\"incompatible\",\"a\":122,\"b\":93},{\"tag\":\"incompatible\",\"a\":122,\"b\":117},{\"tag\":\"mate\",\"ridge\":321,\"a\":70,\"owners\":[81,87,90,92]},{\"tag\":\"mate\",\"ridge\":577,\"a\":17,\"owners\":[82,88,91,92,96,98,99]},{\"tag\":\"mate\",\"ridge\":577,\"a\":54,\"owners\":[96,98,99]},{\"tag\":\"mate\",\"ridge\":577,\"a\":63,\"owners\":[88,91,92,98,99]},{\"tag\":\"mate\",\"ridge\":577,\"a\":69,\"owners\":[82,91,92,96,99]},{\"tag\":\"mate\",\"ridge\":577,\"a\":71,\"owners\":[82,88,91,92]},{\"tag\":\"mate\",\"ridge\":577,\"a\":74,\"owners\":[82,88,92,96,98,99]},{\"tag\":\"mate\",\"ridge\":577,\"a\":75,\"owners\":[82,88,91,96,98]},{\"tag\":\"mate\",\"ridge\":578,\"a\":54,\"owners\":[120,122,123]},{\"tag\":\"mate\",\"ridge\":578,\"a\":75,\"owners\":[106,112,115,120,122]},{\"tag\":\"mate\",\"ridge\":332,\"a\":81,\"owners\":[105]},{\"tag\":\"mate\",\"ridge\":588,\"a\":82,\"owners\":[106]},{\"tag\":\"mate\",\"ridge\":588,\"a\":106,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":340,\"a\":87,\"owners\":[111]},{\"tag\":\"mate\",\"ridge\":596,\"a\":88,\"owners\":[112]},{\"tag\":\"mate\",\"ridge\":596,\"a\":112,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":452,\"a\":90,\"owners\":[114]},{\"tag\":\"mate\",\"ridge\":708,\"a\":115,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":836,\"a\":116,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":616,\"a\":120,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":624,\"a\":98,\"owners\":[122]},{\"tag\":\"mate\",\"ridge\":864,\"a\":123,\"owners\":[99]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[58,64,70,71,93,117],\"full_literals\":[-39,3,5,7,8,21,35]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[76,80,86,100,104,110],\"full_literals\":[-40,11,12,15,25,26,29]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-41,39,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-42,41,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-43,false,40],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-44,43,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-45,42,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-45,false,44],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":96,\"full_literals\":[-22,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":98,\"full_literals\":[-23,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":99,\"full_literals\":[-24,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":120,\"full_literals\":[-36,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":122,\"full_literals\":[-37,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":123,\"full_literals\":[-38,47]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[81,82,87,88,90,91,92],\"full_literals\":[-48,13,14,16,17,18,19,20]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":81,\"full_literals\":[-13,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":82,\"full_literals\":[-14,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":87,\"full_literals\":[-16,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":88,\"full_literals\":[-17,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":90,\"full_literals\":[-18,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":91,\"full_literals\":[-19,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":92,\"full_literals\":[-20,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":105,\"full_literals\":[-27,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":106,\"full_literals\":[-28,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":111,\"full_literals\":[-30,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":112,\"full_literals\":[-31,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":114,\"full_literals\":[-32,49]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-47,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-51,48,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-48,-49,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-50,-51,52],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":41,\"owners\":[17,54,63,69,71,74,75,82,88,91,92,96,98,99,106,112,115,116,120,122,123]}]}"
  "p cnf 52 102\n-14 -11 0\n-14 -12 0\n-15 -13 0\n-15 -14 0\n-16 -15 0\n-17 -11 0\n-17 -12 0\n-17 -15 0\n-18 -15 0\n-19 -11 0\n-19 -12 0\n-19 -15 0\n-20 -11 0\n-20 -12 0\n-20 -15 0\n-22 -3 0\n-22 -5 0\n-22 -21 0\n-24 -3 0\n-24 -5 0\n-24 -21 0\n-25 -14 0\n-25 -17 0\n-25 -19 0\n-25 -20 0\n-26 -13 0\n-26 -14 0\n-26 -16 0\n-26 -17 0\n-26 -18 0\n-26 -19 0\n-26 -20 0\n-29 -13 0\n-29 -14 0\n-29 -16 0\n-29 -17 0\n-29 -18 0\n-29 -19 0\n-29 -20 0\n-35 -22 0\n-35 -24 0\n-37 -3 0\n-37 -5 0\n-37 -21 0\n-37 -35 0\n-7 13 16 18 20 0\n-1 14 17 19 20 22 23 24 0\n-2 22 23 24 0\n-4 17 19 20 23 24 0\n-6 14 19 20 22 24 0\n-8 14 17 19 20 0\n-9 14 17 20 22 23 24 0\n-10 14 17 19 22 23 0\n-2 36 37 38 0\n-10 28 31 33 36 37 0\n-13 27 0\n-14 28 0\n-28 14 0\n-16 30 0\n-17 31 0\n-31 17 0\n-18 32 0\n-33 19 0\n-34 20 0\n-36 22 0\n-23 37 0\n-38 24 0\n-39 3 5 7 8 21 35 0\n-40 11 12 15 25 26 29 0\n-41 39 0\n-42 41 0\n-43 40 0\n-44 43 0\n-45 42 0\n-45 44 0\n45 0\n-22 46 0\n-23 46 0\n-24 46 0\n-36 47 0\n-37 47 0\n-38 47 0\n-48 13 14 16 17 18 19 20 0\n-13 48 0\n-14 48 0\n-16 48 0\n-17 48 0\n-18 48 0\n-19 48 0\n-20 48 0\n-27 49 0\n-28 49 0\n-30 49 0\n-31 49 0\n-32 49 0\n-47 50 0\n-46 50 0\n-51 48 0\n-48 -49 51 0\n-50 -51 52 0\n-52 0\n1 2 4 6 8 9 10 14 17 19 20 22 23 24 28 31 33 34 36 37 38 0\n"
  "103 42 0 76 74 0\n104 44 0 76 75 0\n105 41 0 103 71 0\n106 43 0 104 73 0\n107 39 0 105 70 0\n108 40 0 106 72 0\n109 -15 -48 0 3 4 5 8 9 12 15 83 0\n110 -17 25 26 29 15 0 108 6 7 69 0\n111 -26 19 18 -48 0 26 27 28 29 32 83 0\n112 -29 -48 0 33 34 35 36 37 38 39 83 0\n113 -14 26 -48 0 108 112 109 1 2 22 69 0\n114 -19 -48 0 108 112 109 10 11 24 31 69 0\n115 -20 -48 0 108 112 109 13 14 25 32 69 0\n116 17 14 -51 0 101 58 100 97 79 77 98 115 114 50 64 63 96 82 81 80 54 78 61 49 52 53 47 51 102 0\n117 26 -51 0 98 112 109 113 116 23 110 0\n118 -51 0 98 114 117 30 111 0\n119 -48 0 118 99 114 115 91 92 93 94 95 56 57 59 60 62 83 0\n120 -13 0 119 84 0\n121 -14 0 119 85 0\n122 -16 0 119 86 0\n123 -17 0 119 87 0\n124 -18 0 119 88 0\n125 -19 0 119 89 0\n126 -20 0 119 90 0\n127 -7 0 120 122 124 126 46 0\n128 -28 0 121 58 0\n129 -31 0 123 61 0\n130 -8 0 123 121 125 126 51 0\n131 -33 0 125 63 0\n132 -34 0 126 64 0\n133 37 1 4 22 24 9 2 0 132 131 125 126 123 121 129 128 130 50 65 67 66 55 102 0\n134 -37 0 127 130 107 42 43 44 45 68 0\n135 -23 0 134 66 0\n136 22 24 9 2 0 135 123 126 125 121 134 49 47 133 0\n137 -22 0 127 130 107 16 17 18 40 68 0\n138 -24 0 127 130 107 19 20 21 41 68 0\n139 -9 0 138 121 126 123 135 137 52 0\n140 -2 0 137 135 138 48 0\n141 0 138 139 137 140 136 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record002.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record002.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record002.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record002.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record002 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record002.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record002.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record002.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record002.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record002 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record002_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record002 Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record002_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record002_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00155.record002
