module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsSix0Part00054Frames
public import GraphInputsSix0Part00054Leaves
public import GraphInputsSix0Part00054Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00054.record006
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "34ed2f1ec76e3b2eb3aae6b99e5d96e3d8dd795ad3d4bcf93acbd2bdf06d1745707c789d26c9723cb8a6695a1eb86a99a659996559362d876c394e1b91e1783e744f1a659956479a9695655552d4755346d8751d1743d70ea338d9354cd32cc73a2d8b92d4b1ad1b26c5b0ee8761d4789ca719d1725c570dd0f13c2f07d584714a8390e2c471164358341da0ca318e0b12e0709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1249249249249249236d36db6da6db6db6d269b69b49b6d26d249a4db49349369a6d24db492449249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record006 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record006 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record006.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record006.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record006.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 35), (facetIndex 40), (facetIndex 65), (facetIndex 86)]))
 (.branch 2
 (.leaf ([(facetIndex 25), (facetIndex 31), (facetIndex 60), (facetIndex 61), (facetIndex 80), (facetIndex 82)]))
 (.leaf ([(facetIndex 59), (facetIndex 75), (facetIndex 81), (facetIndex 95)]))))
 (.branch 4
 (.leaf ([(facetIndex 24), (facetIndex 30), (facetIndex 54), (facetIndex 79)]))
 (.branch 5
 (.leaf ([(facetIndex 55), (facetIndex 69), (facetIndex 71), (facetIndex 94)]))
 (.leaf ([(facetIndex 44), (facetIndex 49), (facetIndex 91)])))))
 (.branch 9
 (.branch 7
 (.leaf ([(facetIndex 33), (facetIndex 74), (facetIndex 92)]))
 (.branch 8
 (.leaf ([(facetIndex 67), (facetIndex 87), (facetIndex 96)]))
 (.leaf ([(facetIndex 26), (facetIndex 58), (facetIndex 64)]))))
 (.branch 10
 (.leaf ([(facetIndex 36), (facetIndex 68), (facetIndex 76), (facetIndex 77), (facetIndex 78), (facetIndex 85), (facetIndex 90)]))
 (.branch 11
 (.leaf ([(facetIndex 45), (facetIndex 83), (facetIndex 88)]))
 (.leaf ([(facetIndex 46), (facetIndex 89)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "7240659ba7090a121399926004049700800112800430000500ba500000009006013000813z18;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 12
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def groupMembers4 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 1
 (.leaf ([(facetIndex 97), (facetIndex 101), (facetIndex 107), (facetIndex 108), (facetIndex 115), (facetIndex 116), (facetIndex 117), (facetIndex 118)]))
 (.branch 2
 (.leaf ([(facetIndex 98), (facetIndex 99), (facetIndex 100), (facetIndex 102), (facetIndex 103), (facetIndex 104), (facetIndex 106), (facetIndex 110), (facetIndex 111)]))
 (.leaf ([(facetIndex 105), (facetIndex 109), (facetIndex 112), (facetIndex 113), (facetIndex 114)]))))
def groupColors4 : PackedGraphCertificate.Fields :=
  ⟨2, sparse_nat% "2a5819515z31;"⟩
def grouping4 : FacetSat.Grouping data.count where
  count := 3
  members := fun g => groupMembers4.get g
  color := fun c => groupColors4.get c.val
def groupKind4 : List Nat := List.range grouping4.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0002 : List Nat := [0, 1, 2, 3, 4, 5]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [1, 2]
def grouped3_0006 : List Nat := [2]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [3, 4, 5]
def grouped3_0009 : List Nat := [4]
def grouped3_0010 : List Nat := [4, 5]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7, 8]
def grouped3_0014 : List Nat := [6, 7, 8, 9, 10, 11]
def grouped3_0015 : List Nat := [7]
def grouped3_0016 : List Nat := [7, 8]
def grouped3_0017 : List Nat := [8]
def grouped3_0018 : List Nat := [9]
def grouped3_0019 : List Nat := [9, 10, 11]
def grouped3_0020 : List Nat := [10]
def grouped3_0021 : List Nat := [10, 11]
def grouped3_0022 : List Nat := [11]
def grouped4_0023 : List Nat := [0]
def grouped4_0025 : List Nat := [1]
def grouped4_0026 : List Nat := [1, 2]
def grouped4_0027 : List Nat := [2]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record006 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record006_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3, 4]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00054.record006" "{\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"facet\",\"index\":116},{\"tag\":\"facet\",\"index\":117},{\"tag\":\"facet\",\"index\":118},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":11},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0005\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0005\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":4,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":5,\"list_name\":\"groupKind3\"},{\"tag\":\"group\",\"kind\":4,\"index\":0},{\"tag\":\"group\",\"kind\":4,\"index\":1},{\"tag\":\"group\",\"kind\":4,\"index\":2},{\"tag\":\"group_totalizer\",\"kind\":4,\"threshold\":1,\"list_name\":\"grouped4_0026\"},{\"tag\":\"group_totalizer\",\"kind\":4,\"threshold\":1,\"list_name\":\"groupKind4\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00054.record006" 80

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00054.record006" "{\"ridges\":[[6,131],[7,131],[7,641],[7,642],[25,150],[31,389],[32,641],[40,131],[40,393],[41,641],[41,642],[46,386],[47,131],[48,641],[49,386],[49,449],[60,660],[61,641],[61,676],[64,393],[65,664],[67,449],[80,420],[81,162],[81,676],[82,900],[85,386],[86,904],[89,386],[90,386],[91,386],[91,480],[96,480],[100,145],[111,641],[112,641],[113,641],[113,642],[114,641]],\"owners\":[[81,162,[6,43,47,87,89,91,99],[28,48,75,80,97,111,112,114]],[7,641,[60,61,65],[32,41,48,111,112,113,114]],[32,641,[65],[7,41,48,60,61,111,112,113,114]],[41,641,[60,61],[7,32,48,65,111,112,113,114]],[48,641,[60,65],[7,32,41,61,111,112,113,114]],[61,641,[7,41,65,113],[32,48,60,111,112,114]],[111,641,[60],[7,32,41,48,61,65,112,113,114]],[112,641,[],[7,32,41,48,60,61,65,111,113,114]],[113,641,[60,61],[7,32,41,48,65,111,112,114]],[114,641,[60,65],[7,32,41,48,61,111,112,113]],[7,642,[81,82,86],[32,41,48,111,112,113,114]],[41,642,[81,82],[7,32,48,86,111,112,113,114]],[113,642,[81,82],[7,32,41,48,86,111,112,114]],[100,145,[25,46,59,60],[13,35,43,44,57,64,65,66,67,98,112]],[25,150,[75,78],[]],[46,386,[80,82,86,91],[31,40,49,78,85,89,90]],[49,386,[78,80,82,85,86,89],[31,40,46,90,91]],[85,386,[31,49,80,82,91],[40,46,78,86,89,90]],[89,386,[31,40,49,82,86],[46,78,80,85,90,91]],[90,386,[31,40,80,82,86],[46,49,78,85,89,91]],[91,386,[31,40,46,78,82,85,86],[49,80,89,90]],[31,389,[59],[]],[40,393,[64],[]],[64,393,[40],[]],[49,449,[67],[]],[67,449,[49],[]],[60,660,[],[]],[61,676,[81],[]],[81,676,[61],[]],[65,664,[],[]],[80,420,[95],[]],[82,900,[],[]],[86,904,[],[]],[91,480,[96],[]],[96,480,[91],[]]],\"edges\":[[42,[31,40,46,49,59,64,67,78,80,82,85,86,89,90,91,95,96]],[43,[7,32,41,48,60,61,65,81,82,86,111,112,113,114]]],\"groupings\":[3,4]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00054.record006" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00054.record006\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-7,-6],[-15,-3],[-15,-4],[-15,-8],[-15,-13],[-20,-15],[-21,-15],[-30,-15],[-32,-15],[-33,-15],[-34,-6],[-34,-12],[-34,-29],[-35,-29],[-36,-6],[-37,-6],[-37,-12],[-37,-29],[-38,-6],[-38,-12],[-38,-29],[-39,-6],[-39,-12],[-39,-29],[-40,-15],[-41,-15],[-42,-6],[-43,-16],[-44,-15],[-45,-15],[-48,-6],[-48,-12],[-48,-16],[-48,-18],[-48,-24],[-48,-28],[-48,-29],[-48,-31],[-50,-6],[-51,-26],[-51,-27],[-52,-6],[-53,-6],[-1,-2,-6],[-2,-6,-10],[-22,1,8,10,26,27,29,34],[-2,14,15,17],[-5,17],[-7,14,15],[-11,14,17],[-15,2,7,17,48],[-46,14],[-47],[-48,14,15],[-49,14,17],[-2,22,23,25],[-7,22,23],[-48,22,23],[-35,3,9,13,14],[-3,19,20],[-9,21,23,25,29],[-12,20,21,23,24,25,27],[-24,4,12,21,23,29],[-27,4,6,12,23,25],[-28,4,6,21,23,25],[-29,4,6,9,20,23,24,25],[-4,13],[-6,16],[-16,6],[-12,18],[-18,12],[-14],[-15,22],[-22,15],[-17],[-21,30],[-23],[-25],[-29,31],[-31,29],[-6,54],[-55,3,4,14,15,21,23],[-15,55],[-13,56],[-19,56],[-22,56],[-30,56],[-12,57],[-29,57],[-18,58],[-31,58],[-24,59],[-9,60],[-27,60],[-61,55,56],[-56,61],[-55,61],[-55,-56,62],[-62,63],[-54,-62,64],[-57,65],[-65,66],[-63,-66,67],[-64,-66,68],[-58,69],[-69,70],[-60,71],[-71,72],[-59,72],[-70,73],[-70,-72,74],[-67,-74,75],[-68,-73,75],[-75],[-76,32,36,42,43,50,51,52,53],[-77,33,34,35,37,38,39,41,45,46],[-34,77],[-78,40,44,47,48,49],[-79,77,78],[-80,76,79],[80],[4,6,9,12,13,16,18,20,21,23,24,25,27,28,29,30,31],[2,5,7,11,14,15,17,22,23,25,46,47,48,49]],\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"facet\",\"index\":116},{\"tag\":\"facet\",\"index\":117},{\"tag\":\"facet\",\"index\":118},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":11,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group\",\"index\":0,\"kind\":4},{\"tag\":\"group\",\"index\":1,\"kind\":4},{\"tag\":\"group\",\"index\":2,\"kind\":4},{\"tag\":\"group_totalizer\",\"kind\":4},{\"tag\":\"group_totalizer\",\"kind\":4}],\"rules\":[{\"tag\":\"incompatible\",\"a\":41,\"b\":40},{\"tag\":\"incompatible\",\"a\":61,\"b\":25},{\"tag\":\"incompatible\",\"a\":61,\"b\":31},{\"tag\":\"incompatible\",\"a\":61,\"b\":43},{\"tag\":\"incompatible\",\"a\":61,\"b\":59},{\"tag\":\"incompatible\",\"a\":78,\"b\":61},{\"tag\":\"incompatible\",\"a\":80,\"b\":61},{\"tag\":\"incompatible\",\"a\":95,\"b\":61},{\"tag\":\"incompatible\",\"a\":97,\"b\":61},{\"tag\":\"incompatible\",\"a\":98,\"b\":61},{\"tag\":\"incompatible\",\"a\":99,\"b\":40},{\"tag\":\"incompatible\",\"a\":99,\"b\":49},{\"tag\":\"incompatible\",\"a\":99,\"b\":91},{\"tag\":\"incompatible\",\"a\":100,\"b\":91},{\"tag\":\"incompatible\",\"a\":101,\"b\":40},{\"tag\":\"incompatible\",\"a\":102,\"b\":40},{\"tag\":\"incompatible\",\"a\":102,\"b\":49},{\"tag\":\"incompatible\",\"a\":102,\"b\":91},{\"tag\":\"incompatible\",\"a\":103,\"b\":40},{\"tag\":\"incompatible\",\"a\":103,\"b\":49},{\"tag\":\"incompatible\",\"a\":103,\"b\":91},{\"tag\":\"incompatible\",\"a\":104,\"b\":40},{\"tag\":\"incompatible\",\"a\":104,\"b\":49},{\"tag\":\"incompatible\",\"a\":104,\"b\":91},{\"tag\":\"incompatible\",\"a\":105,\"b\":61},{\"tag\":\"incompatible\",\"a\":106,\"b\":61},{\"tag\":\"incompatible\",\"a\":107,\"b\":40},{\"tag\":\"incompatible\",\"a\":108,\"b\":64},{\"tag\":\"incompatible\",\"a\":109,\"b\":61},{\"tag\":\"incompatible\",\"a\":110,\"b\":61},{\"tag\":\"incompatible\",\"a\":113,\"b\":40},{\"tag\":\"incompatible\",\"a\":113,\"b\":49},{\"tag\":\"incompatible\",\"a\":113,\"b\":64},{\"tag\":\"incompatible\",\"a\":113,\"b\":67},{\"tag\":\"incompatible\",\"a\":113,\"b\":85},{\"tag\":\"incompatible\",\"a\":113,\"b\":90},{\"tag\":\"incompatible\",\"a\":113,\"b\":91},{\"tag\":\"incompatible\",\"a\":113,\"b\":96},{\"tag\":\"incompatible\",\"a\":115,\"b\":40},{\"tag\":\"incompatible\",\"a\":116,\"b\":87},{\"tag\":\"incompatible\",\"a\":116,\"b\":89},{\"tag\":\"incompatible\",\"a\":117,\"b\":40},{\"tag\":\"incompatible\",\"a\":118,\"b\":40},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[6,7,40]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[7,40,47]},{\"tag\":\"mate\",\"ridge\":162,\"a\":81,\"owners\":[6,43,47,87,89,91,99]},{\"tag\":\"mate\",\"ridge\":641,\"a\":7,\"owners\":[60,61,65]},{\"tag\":\"mate\",\"ridge\":641,\"a\":32,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":641,\"a\":41,\"owners\":[60,61]},{\"tag\":\"mate\",\"ridge\":641,\"a\":48,\"owners\":[60,65]},{\"tag\":\"mate\",\"ridge\":641,\"a\":61,\"owners\":[7,41,65,113]},{\"tag\":\"mate\",\"ridge\":641,\"a\":111,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":641,\"a\":112,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":641,\"a\":113,\"owners\":[60,61]},{\"tag\":\"mate\",\"ridge\":641,\"a\":114,\"owners\":[60,65]},{\"tag\":\"mate\",\"ridge\":642,\"a\":7,\"owners\":[81,82,86]},{\"tag\":\"mate\",\"ridge\":642,\"a\":41,\"owners\":[81,82]},{\"tag\":\"mate\",\"ridge\":642,\"a\":113,\"owners\":[81,82]},{\"tag\":\"mate\",\"ridge\":145,\"a\":100,\"owners\":[25,46,59,60]},{\"tag\":\"mate\",\"ridge\":150,\"a\":25,\"owners\":[75,78]},{\"tag\":\"mate\",\"ridge\":386,\"a\":46,\"owners\":[80,82,86,91]},{\"tag\":\"mate\",\"ridge\":386,\"a\":49,\"owners\":[78,80,82,85,86,89]},{\"tag\":\"mate\",\"ridge\":386,\"a\":85,\"owners\":[31,49,80,82,91]},{\"tag\":\"mate\",\"ridge\":386,\"a\":89,\"owners\":[31,40,49,82,86]},{\"tag\":\"mate\",\"ridge\":386,\"a\":90,\"owners\":[31,40,80,82,86]},{\"tag\":\"mate\",\"ridge\":386,\"a\":91,\"owners\":[31,40,46,78,82,85,86]},{\"tag\":\"mate\",\"ridge\":389,\"a\":31,\"owners\":[59]},{\"tag\":\"mate\",\"ridge\":393,\"a\":40,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":393,\"a\":64,\"owners\":[40]},{\"tag\":\"mate\",\"ridge\":449,\"a\":49,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":449,\"a\":67,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":660,\"a\":60,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":676,\"a\":61,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":676,\"a\":81,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":664,\"a\":65,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":420,\"a\":80,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":900,\"a\":82,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":904,\"a\":86,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":480,\"a\":91,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":480,\"a\":96,\"owners\":[91]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":40,\"full_literals\":[-6,54]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[25,31,60,61,80,82],\"full_literals\":[-55,3,4,14,15,21,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":61,\"full_literals\":[-15,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":59,\"full_literals\":[-13,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":75,\"full_literals\":[-19,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":81,\"full_literals\":[-22,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":95,\"full_literals\":[-30,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":49,\"full_literals\":[-12,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":91,\"full_literals\":[-29,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":67,\"full_literals\":[-18,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":96,\"full_literals\":[-31,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":85,\"full_literals\":[-24,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":46,\"full_literals\":[-9,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":89,\"full_literals\":[-27,60]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-61,55,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-56,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-55,false,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-55,-56,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-62,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-54,-62,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-57,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-65,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-63,-66,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":3,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-64,-66,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-58,false,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-69,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-60,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-71,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-59,false,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-70,false,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-70,-72,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-67,-74,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":4,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-68,-73,75],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":4,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":4,\"index\":0,\"members\":[97,101,107,108,115,116,117,118],\"full_literals\":[-76,32,36,42,43,50,51,52,53]},{\"tag\":\"group_or\",\"kind\":4,\"index\":1,\"members\":[98,99,100,102,103,104,106,110,111],\"full_literals\":[-77,33,34,35,37,38,39,41,45,46]},{\"tag\":\"group_take\",\"kind\":4,\"index\":1,\"member\":99,\"full_literals\":[-34,77]},{\"tag\":\"group_or\",\"kind\":4,\"index\":2,\"members\":[105,109,112,113,114],\"full_literals\":[-78,40,44,47,48,49]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped4_0025\",\"right_name\":\"grouped4_0027\",\"joined_name\":\"grouped4_0026\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-79,77,78],\"grouped\":true,\"kind\":4},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped4_0023\",\"right_name\":\"grouped4_0026\",\"joined_name\":\"groupKind4\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-80,76,79],\"grouped\":true,\"kind\":4},{\"tag\":\"quota_lower\",\"kind\":4,\"quota\":1,\"grouped\":true},{\"tag\":\"edge\",\"edge\":42,\"owners\":[31,40,46,49,59,64,67,78,80,82,85,86,89,90,91,95,96]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[7,32,41,48,60,61,65,81,82,86,111,112,113,114]}]}"
  "124 -46 0 72 52 0\n125 -5 0 75 48 0\n126 -11 0 75 72 50 0\n127 -49 0 75 72 55 0\n128 -55 3 4 15 21 0 72 77 82 0\n129 -77 33 34 35 37 38 39 41 45 0 124 116 0\n130 -78 40 44 48 0 53 127 118 0\n131 4 6 9 12 13 16 18 20 21 24 27 28 29 30 31 0 77 78 122 0\n132 2 7 15 22 48 0 125 126 72 75 77 78 124 53 127 123 0\n133 61 0 78 77 96 97 86 83 56 57 58 132 0\n134 56 20 0 133 84 85 86 87 95 67 60 73 76 128 0\n135 15 0 75 72 47 49 54 74 132 0\n136 -3 0 135 2 0\n137 -4 0 135 3 0\n138 -8 0 135 4 0\n139 -13 0 135 5 0\n140 -20 0 135 6 0\n141 -21 0 135 7 0\n142 -30 0 135 8 0\n143 -40 0 135 25 0\n144 -44 0 135 29 0\n145 22 0 135 73 0\n146 55 0 135 83 0\n147 56 0 140 134 0\n148 62 0 147 146 98 0\n149 63 0 148 99 0\n150 -48 0 78 77 142 141 140 139 137 31 32 33 34 35 36 37 38 64 61 131 0\n151 -33 0 135 10 0\n152 -41 0 135 26 0\n153 -45 0 135 30 0\n154 -78 0 150 144 143 130 0\n155 6 12 29 0 78 77 142 141 140 139 137 63 71 61 80 69 65 64 131 0\n156 -6 35 -77 0 153 152 151 11 16 19 22 129 0\n157 29 -77 0 141 78 77 72 139 136 153 152 151 61 59 156 155 12 17 20 23 129 0\n158 -77 0 153 152 151 157 13 14 18 21 24 129 0\n159 -32 0 135 9 0\n160 -34 0 158 117 0\n161 -79 0 158 154 119 0\n162 76 0 161 121 120 0\n163 -29 0 149 114 148 78 77 140 137 79 89 91 101 105 102 106 103 110 112 113 111 104 108 109 100 107 92 81 93 66 0\n164 -6 0 150 75 135 162 159 160 163 145 138 1 15 27 39 42 43 68 51 28 44 45 115 40 41 46 0\n165 12 0 164 163 155 0\n166 18 0 165 70 0\n167 57 0 165 88 0\n168 58 0 166 90 0\n169 65 0 167 101 0\n170 69 0 168 105 0\n171 66 0 169 102 0\n172 70 0 170 106 0\n173 67 0 171 149 103 0\n174 -74 0 173 114 112 0\n175 -72 0 174 172 111 0\n176 -71 0 175 108 0\n177 -59 0 175 109 0\n178 -60 0 176 107 0\n179 -24 0 177 92 0\n180 -27 0 178 94 0\n181 0 179 180 141 77 140 78 165 62 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record006.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record006.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record006.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record006.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record006 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record006.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record006.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record006.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record006.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record006 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record006_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record006 Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record006_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record006_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00054.record006
