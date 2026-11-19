module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsSix0Part00030Frames
public import GraphInputsSix0Part00030Leaves
public import GraphInputsSix0Part00030Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00030.record057
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ada979da759763e87de9735ba6b99b63d5d56cf63ccee3afb0cb16c2f07c729aa5a8da2e87a8d8b61d8ae1b89e1783ee8791d45d1cc6b16c5c9ca5a9364b9d1725956352d70d5362d4b4ad2745d0f5c368cd38ccb362d4b32d2b2ac9b16c3b89ca785c970dc8f0bc1f6a2342c8aa158361382e62549854551349314c8b12c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "9249249249249236db69b4d249349b6db69a6db49b4db69b69a4934936d2492249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record057 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record057 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record057.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record057.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record057.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 32), (facetIndex 40), (facetIndex 77)]))
 (.leaf ([(facetIndex 45), (facetIndex 48), (facetIndex 53), (facetIndex 82)])))
 (.branch 3
 (.leaf ([(facetIndex 59), (facetIndex 62), (facetIndex 63), (facetIndex 64)]))
 (.branch 4
 (.leaf ([(facetIndex 55), (facetIndex 79)]))
 (.leaf ([(facetIndex 46), (facetIndex 52), (facetIndex 83)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 28), (facetIndex 43), (facetIndex 74), (facetIndex 76)]))
 (.branch 7
 (.leaf ([(facetIndex 41), (facetIndex 68), (facetIndex 80)]))
 (.leaf ([(facetIndex 26), (facetIndex 54), (facetIndex 81)]))))
 (.branch 9
 (.leaf ([(facetIndex 27), (facetIndex 39), (facetIndex 44), (facetIndex 57), (facetIndex 60), (facetIndex 61)]))
 (.branch 10
 (.leaf ([(facetIndex 37), (facetIndex 49), (facetIndex 65)]))
 (.leaf ([(facetIndex 84)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "a4176300505000006009222882080371400910418506080900000000587z1a;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 11
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def groupMembers4 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 1
 (.leaf ([(facetIndex 97), (facetIndex 98), (facetIndex 99), (facetIndex 100), (facetIndex 101), (facetIndex 102)]))
 (.branch 2
 (.leaf ([(facetIndex 86), (facetIndex 87), (facetIndex 88), (facetIndex 95), (facetIndex 103)]))
 (.leaf ([(facetIndex 85), (facetIndex 89), (facetIndex 90), (facetIndex 91), (facetIndex 92), (facetIndex 93), (facetIndex 94), (facetIndex 96)]))))
def groupColors4 : PackedGraphCertificate.Fields :=
  ⟨2, sparse_nat% "40026aa958z2a;"⟩
def grouping4 : FacetSat.Grouping data.count where
  count := 3
  members := fun g => groupMembers4.get g
  color := fun c => groupColors4.get c.val
def groupKind4 : List Nat := List.range grouping4.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [2, 3, 4]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [3, 4]
def grouped3_0009 : List Nat := [4]
def grouped3_0010 : List Nat := [5, 6, 7]
def grouped3_0011 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped3_0012 : List Nat := [8]
def grouped3_0013 : List Nat := [8, 9, 10]
def grouped3_0014 : List Nat := [9]
def grouped3_0015 : List Nat := [9, 10]
def grouped3_0016 : List Nat := [10]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record057 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record057_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3, 4]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00030.record057" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":10},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":4,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":5,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":5,\"list_name\":\"groupKind3\"},{\"tag\":\"group\",\"kind\":4,\"index\":2}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00030.record057" 63

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00030.record057" "{\"ridges\":[[10,265],[10,321],[10,328],[11,385],[11,392],[19,296],[19,392],[34,321],[40,385],[40,450],[47,265],[47,328],[48,780],[52,800],[53,836],[56,296],[57,553],[57,800],[58,321],[61,800],[62,464],[63,848],[64,385],[64,912],[65,673],[65,800],[77,354],[79,328],[79,392],[79,450],[82,356],[83,296],[83,780],[83,800],[84,416],[84,800],[84,912],[89,321],[92,385],[93,296],[94,416],[95,321],[96,328]],\"owners\":[[10,265,[11,32,35,45,48,56,57,91,92],[34,47,89,90]],[47,265,[11,32,35,56,57,92],[10,34,45,48,89,90,91]],[10,321,[40,53,62,63],[34,47,58,89,90,95,96]],[34,321,[53,62,63],[10,40,47,58,89,90,95,96]],[58,321,[53,63],[10,34,40,47,62,89,90,95,96]],[89,321,[53],[10,34,40,47,58,62,63,90,95,96]],[95,321,[63],[10,34,40,47,53,58,62,89,90,96]],[10,328,[77,79,82],[34,47,58,89,90,95,96]],[47,328,[77,79],[10,34,58,82,89,90,95,96]],[79,328,[10,47,82,90],[34,58,77,89,95,96]],[96,328,[],[10,34,47,58,77,79,82,89,90,95]],[40,385,[11,56,59,64,65],[35,39,58,62,91,92,95,96]],[92,385,[65],[11,35,39,40,56,58,59,62,64,91,95,96]],[19,296,[32,45,57,77,82,83],[56,78,93,94,96]],[56,296,[77,82,83],[19,32,45,57,78,93,94,96]],[83,296,[19,32,56,77,78,94,96],[45,57,82,93]],[93,296,[57],[19,32,45,56,77,78,82,83,94,96]],[84,416,[19,39,56,78,93,96],[59,65,94]],[94,416,[65],[19,39,56,59,78,84,93,96]],[40,450,[79],[]],[79,450,[40],[]],[57,553,[46],[]],[48,780,[83],[]],[83,780,[48],[]],[52,800,[84],[57,61,65,83]],[57,800,[84],[52,61,65,83]],[61,800,[83],[52,57,65,84]],[65,800,[83],[52,57,61,84]],[83,800,[61,65,84],[52,57]],[84,800,[52,57,83],[61,65]],[53,836,[],[]],[65,673,[60],[]],[62,464,[],[]],[63,848,[],[]],[64,912,[84],[]],[84,912,[64],[]],[77,354,[],[]],[82,356,[],[]]],\"edges\":[[40,[10,34,40,47,53,58,62,63,77,79,82,89,90,95,96]],[44,[48,52,53,57,61,63,64,65,83,84]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00030.record057" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00030.record057\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-27,-4],[-27,-6],[-27,-15],[-27,-26],[-29,-11],[-31,-4],[-31,-7],[-31,-8],[-31,-9],[-31,-16],[-31,-20],[-31,-26],[-31,-27],[-33,-29],[-33,-30],[-34,-8],[-34,-11],[-34,-27],[-34,-29],[-35,-30],[-36,-8],[-36,-11],[-36,-27],[-36,-29],[-37,-30],[-1,2,4,6,9,12,15,16,34,35],[-11,2,4,6,15,16,35],[-1,8,14,21,22],[-5,14,21,22],[-17,14,22],[-32,14],[-38,22],[-1,25,27,28],[-11,25,27],[-27,1,11,28,33],[-39],[-8,2,15,18,23,24],[-35,24],[-2,-8,-23],[-2,-3,-27],[-3,4,9,16,25,28,29],[-15,25,28,29],[-29,3,4,15,25,26,37,39],[-36,16],[-30,3,7,15,26,36,39],[-37,24],[-8,27],[-27,8],[-16,10],[-12,29],[-29,12],[-13,30],[-16,30],[-20,29],[-24,29],[-29,20,24,30],[-30,13,16,29],[-14],[-24,19],[-21],[-22],[-23,30],[-30,23],[-25],[-28],[-8,40],[-9,41],[-12,41],[-18,42],[-23,42],[-27,43],[-10,44],[-13,44],[-29,44],[-16,45],[-19,45],[-24,46],[-30,47],[-41,48],[-40,48],[-40,-41,49],[-44,50],[-43,-44,51],[-51,52],[-42,-50,52],[-42,-51,53],[-48,-52,54],[-49,-52,55],[-49,-53,56],[-47,57],[-46,57],[-57,58],[-45,-57,59],[-58,60],[-59,61],[-54,-61,62],[-55,-60,62],[-56,62],[-62],[-63,31,32,33,34,35,36,37,39],[-33,63],[-34,63],[-35,63],[-37,63],[1,5,8,11,14,17,21,22,25,27,28,32,33,38,39],[12,13,14,16,20,22,23,24,29,30]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":10,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":4}],\"rules\":[{\"tag\":\"incompatible\",\"a\":79,\"b\":32},{\"tag\":\"incompatible\",\"a\":79,\"b\":35},{\"tag\":\"incompatible\",\"a\":79,\"b\":56},{\"tag\":\"incompatible\",\"a\":79,\"b\":78},{\"tag\":\"incompatible\",\"a\":83,\"b\":47},{\"tag\":\"incompatible\",\"a\":85,\"b\":32},{\"tag\":\"incompatible\",\"a\":85,\"b\":39},{\"tag\":\"incompatible\",\"a\":85,\"b\":40},{\"tag\":\"incompatible\",\"a\":85,\"b\":45},{\"tag\":\"incompatible\",\"a\":85,\"b\":57},{\"tag\":\"incompatible\",\"a\":85,\"b\":61},{\"tag\":\"incompatible\",\"a\":85,\"b\":78},{\"tag\":\"incompatible\",\"a\":85,\"b\":79},{\"tag\":\"incompatible\",\"a\":90,\"b\":83},{\"tag\":\"incompatible\",\"a\":90,\"b\":84},{\"tag\":\"incompatible\",\"a\":91,\"b\":40},{\"tag\":\"incompatible\",\"a\":91,\"b\":47},{\"tag\":\"incompatible\",\"a\":91,\"b\":79},{\"tag\":\"incompatible\",\"a\":91,\"b\":83},{\"tag\":\"incompatible\",\"a\":92,\"b\":84},{\"tag\":\"incompatible\",\"a\":93,\"b\":40},{\"tag\":\"incompatible\",\"a\":93,\"b\":47},{\"tag\":\"incompatible\",\"a\":93,\"b\":79},{\"tag\":\"incompatible\",\"a\":93,\"b\":83},{\"tag\":\"incompatible\",\"a\":94,\"b\":84},{\"tag\":\"mate\",\"ridge\":265,\"a\":10,\"owners\":[11,32,35,45,48,56,57,91,92]},{\"tag\":\"mate\",\"ridge\":265,\"a\":47,\"owners\":[11,32,35,56,57,92]},{\"tag\":\"mate\",\"ridge\":321,\"a\":10,\"owners\":[40,53,62,63]},{\"tag\":\"mate\",\"ridge\":321,\"a\":34,\"owners\":[53,62,63]},{\"tag\":\"mate\",\"ridge\":321,\"a\":58,\"owners\":[53,63]},{\"tag\":\"mate\",\"ridge\":321,\"a\":89,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":321,\"a\":95,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":328,\"a\":10,\"owners\":[77,79,82]},{\"tag\":\"mate\",\"ridge\":328,\"a\":47,\"owners\":[77,79]},{\"tag\":\"mate\",\"ridge\":328,\"a\":79,\"owners\":[10,47,82,90]},{\"tag\":\"mate\",\"ridge\":328,\"a\":96,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":385,\"a\":40,\"owners\":[11,56,59,64,65]},{\"tag\":\"mate\",\"ridge\":385,\"a\":92,\"owners\":[65]},{\"tag\":\"three\",\"ridge\":385,\"vertices\":[11,40,64]},{\"tag\":\"three\",\"ridge\":392,\"vertices\":[11,19,79]},{\"tag\":\"mate\",\"ridge\":296,\"a\":19,\"owners\":[32,45,57,77,82,83]},{\"tag\":\"mate\",\"ridge\":296,\"a\":56,\"owners\":[77,82,83]},{\"tag\":\"mate\",\"ridge\":296,\"a\":83,\"owners\":[19,32,56,77,78,94,96]},{\"tag\":\"mate\",\"ridge\":296,\"a\":93,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":416,\"a\":84,\"owners\":[19,39,56,78,93,96]},{\"tag\":\"mate\",\"ridge\":416,\"a\":94,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":450,\"a\":40,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":450,\"a\":79,\"owners\":[40]},{\"tag\":\"mate\",\"ridge\":553,\"a\":57,\"owners\":[46]},{\"tag\":\"mate\",\"ridge\":780,\"a\":48,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":780,\"a\":83,\"owners\":[48]},{\"tag\":\"mate\",\"ridge\":800,\"a\":52,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":800,\"a\":57,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":800,\"a\":61,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":800,\"a\":65,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":800,\"a\":83,\"owners\":[61,65,84]},{\"tag\":\"mate\",\"ridge\":800,\"a\":84,\"owners\":[52,57,83]},{\"tag\":\"mate\",\"ridge\":836,\"a\":53,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":673,\"a\":65,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":464,\"a\":62,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":848,\"a\":63,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":912,\"a\":64,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":912,\"a\":84,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":354,\"a\":77,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":356,\"a\":82,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":40,\"full_literals\":[-8,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":45,\"full_literals\":[-9,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":48,\"full_literals\":[-12,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":59,\"full_literals\":[-18,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":64,\"full_literals\":[-23,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":79,\"full_literals\":[-27,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":46,\"full_literals\":[-10,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":52,\"full_literals\":[-13,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":83,\"full_literals\":[-29,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":57,\"full_literals\":[-16,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":60,\"full_literals\":[-19,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":65,\"full_literals\":[-24,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":84,\"full_literals\":[-30,47]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-40,-41,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-44,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-43,-44,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-51,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-42,-50,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-42,-51,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-48,-52,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-49,-52,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-49,-53,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-47,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-57,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-45,-57,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-58,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-59,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-54,-61,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"groupKind3\",\"a\":4,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-55,-60,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"groupKind3\",\"a\":5,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-56,false,62],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":4,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":4,\"index\":2,\"members\":[85,89,90,91,92,93,94,96],\"full_literals\":[-63,31,32,33,34,35,36,37,39]},{\"tag\":\"group_take\",\"kind\":4,\"index\":2,\"member\":90,\"full_literals\":[-33,63]},{\"tag\":\"group_take\",\"kind\":4,\"index\":2,\"member\":91,\"full_literals\":[-34,63]},{\"tag\":\"group_take\",\"kind\":4,\"index\":2,\"member\":92,\"full_literals\":[-35,63]},{\"tag\":\"group_take\",\"kind\":4,\"index\":2,\"member\":94,\"full_literals\":[-37,63]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[10,34,40,47,53,58,62,63,77,79,82,89,90,95,96]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[48,52,53,57,61,63,64,65,83,84]}]}"
  "p cnf 63 106\n-27 -4 0\n-27 -6 0\n-27 -15 0\n-27 -26 0\n-29 -11 0\n-31 -4 0\n-31 -7 0\n-31 -8 0\n-31 -9 0\n-31 -16 0\n-31 -20 0\n-31 -26 0\n-31 -27 0\n-33 -29 0\n-33 -30 0\n-34 -8 0\n-34 -11 0\n-34 -27 0\n-34 -29 0\n-35 -30 0\n-36 -8 0\n-36 -11 0\n-36 -27 0\n-36 -29 0\n-37 -30 0\n-1 2 4 6 9 12 15 16 34 35 0\n-11 2 4 6 15 16 35 0\n-1 8 14 21 22 0\n-5 14 21 22 0\n-17 14 22 0\n-32 14 0\n-38 22 0\n-1 25 27 28 0\n-11 25 27 0\n-27 1 11 28 33 0\n-39 0\n-8 2 15 18 23 24 0\n-35 24 0\n-2 -8 -23 0\n-2 -3 -27 0\n-3 4 9 16 25 28 29 0\n-15 25 28 29 0\n-29 3 4 15 25 26 37 39 0\n-36 16 0\n-30 3 7 15 26 36 39 0\n-37 24 0\n-8 27 0\n-27 8 0\n-16 10 0\n-12 29 0\n-29 12 0\n-13 30 0\n-16 30 0\n-20 29 0\n-24 29 0\n-29 20 24 30 0\n-30 13 16 29 0\n-14 0\n-24 19 0\n-21 0\n-22 0\n-23 30 0\n-30 23 0\n-25 0\n-28 0\n-8 40 0\n-9 41 0\n-12 41 0\n-18 42 0\n-23 42 0\n-27 43 0\n-10 44 0\n-13 44 0\n-29 44 0\n-16 45 0\n-19 45 0\n-24 46 0\n-30 47 0\n-41 48 0\n-40 48 0\n-40 -41 49 0\n-44 50 0\n-43 -44 51 0\n-51 52 0\n-42 -50 52 0\n-42 -51 53 0\n-48 -52 54 0\n-49 -52 55 0\n-49 -53 56 0\n-47 57 0\n-46 57 0\n-57 58 0\n-45 -57 59 0\n-58 60 0\n-59 61 0\n-54 -61 62 0\n-55 -60 62 0\n-56 62 0\n-62 0\n-63 31 32 33 34 35 36 37 39 0\n-33 63 0\n-34 63 0\n-35 63 0\n-37 63 0\n1 5 8 11 14 17 21 22 25 27 28 32 33 38 39 0\n12 13 14 16 20 22 23 24 29 30 0\n"
  "107 -29 3 4 15 25 26 37 0 36 43 0\n108 -30 3 7 15 26 36 0 36 45 0\n109 -32 0 58 31 0\n110 -38 0 61 32 0\n111 -17 0 61 58 30 0\n112 -5 0 61 58 60 29 0\n113 -56 0 99 98 0\n114 -63 31 33 34 35 36 37 0 109 36 100 0\n115 1 8 11 27 33 0 112 58 111 60 61 64 65 109 110 36 105 0\n116 12 13 16 20 23 24 29 30 0 58 61 106 0\n117 -30 52 0 63 70 85 82 72 73 74 49 57 0\n118 29 30 0 62 53 52 50 54 55 116 0\n119 52 0 65 64 84 117 118 5 14 74 83 71 47 33 115 0\n120 24 30 -63 0 118 19 14 53 44 38 46 56 114 11 0\n121 30 -63 0 119 99 118 51 68 79 87 96 95 120 59 77 76 91 93 0\n122 -29 -63 0 61 60 58 121 25 20 15 5 19 24 114 8 13 28 115 0\n123 -31 36 -63 0 65 64 122 42 121 6 7 9 10 12 41 108 0\n124 -34 33 0 61 60 58 16 17 18 28 115 0\n125 36 -63 0 121 15 124 25 20 123 114 0\n126 -63 0 61 60 58 121 15 125 21 22 23 28 115 0\n127 -33 0 126 101 0\n128 -34 0 126 102 0\n129 -35 0 126 103 0\n130 -37 0 126 104 0\n131 27 0 65 64 127 47 33 34 115 0\n132 -4 0 131 1 0\n133 -6 0 131 2 0\n134 -15 0 131 3 0\n135 -26 0 131 4 0\n136 8 0 131 48 0\n137 43 0 131 71 0\n138 40 0 136 66 0\n139 48 0 138 80 0\n140 54 0 139 119 87 0\n141 -61 0 140 99 96 0\n142 -59 0 141 95 0\n143 30 0 130 132 64 135 137 131 138 119 113 99 136 134 62 118 51 74 107 68 83 40 81 88 89 97 86 94 69 92 37 91 77 0\n144 23 0 143 63 0\n145 47 0 143 78 0\n146 -2 0 144 136 39 0\n147 57 0 145 90 0\n148 58 0 147 92 0\n149 -45 0 147 142 93 0\n150 60 0 148 94 0\n151 -16 0 149 75 0\n152 -55 0 150 99 97 0\n153 -11 0 151 132 133 134 146 129 27 0\n154 -49 0 152 119 88 0\n155 1 0 153 131 65 127 35 0\n156 -41 0 154 138 81 0\n157 -9 0 156 67 0\n158 -12 0 156 68 0\n159 0 158 157 132 133 155 146 134 151 128 129 26 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record057.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record057.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record057.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record057.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record057 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record057.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record057.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record057.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record057.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record057 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record057_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record057_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record057_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record057_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record057_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record057_certificates, Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record057_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record057 Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record057_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record057_validity Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record057_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00030.record057
