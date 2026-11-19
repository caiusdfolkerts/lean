module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow26Part00047Frames
public import GraphInputsRow26Part00047Leaves
public import GraphInputsRow26Part00047Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00047.record044
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3d15caab1a56a3a4e8e655876a394e2ba1e4785e0fad1ac4f1aa719566394e4e5a5555354b51d68d534ad8751d176c370ea338f1394d538cd331cf0ba2d4b8ad2b2ae1b46c5b0ee8751c6785d1715c3783d0f23c4f07c3c318a60b951865190e4c5294550d42d0768350cc328e0b42c2b21c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db69b6d36d36da4926924da49249369b6924924d249b492491249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record044 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record044 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record044.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record044.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record044.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 34), (facetIndex 63), (facetIndex 64), (facetIndex 65), (facetIndex 68)]))
 (.leaf ([(facetIndex 27), (facetIndex 81), (facetIndex 86)])))
 (.branch 3
 (.leaf ([(facetIndex 36), (facetIndex 53), (facetIndex 54), (facetIndex 55), (facetIndex 56)]))
 (.leaf ([(facetIndex 31), (facetIndex 35), (facetIndex 50), (facetIndex 66)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 25), (facetIndex 30), (facetIndex 37), (facetIndex 39), (facetIndex 40), (facetIndex 77)]))
 (.leaf ([(facetIndex 57), (facetIndex 58), (facetIndex 59), (facetIndex 69), (facetIndex 70), (facetIndex 71), (facetIndex 72)])))
 (.branch 7
 (.leaf ([(facetIndex 26), (facetIndex 28), (facetIndex 29), (facetIndex 42), (facetIndex 43), (facetIndex 44), (facetIndex 46)]))
 (.leaf ([(facetIndex 41), (facetIndex 45), (facetIndex 60)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "40008020005b680c0007b6a4900c01bedbc8226007363az13;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 62), (facetIndex 73)]))
 (.leaf ([(facetIndex 67), (facetIndex 74), (facetIndex 75), (facetIndex 76)])))
 (.branch 3
 (.leaf ([(facetIndex 83), (facetIndex 91)]))
 (.leaf ([(facetIndex 47), (facetIndex 93)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 32), (facetIndex 38), (facetIndex 61)]))
 (.leaf ([(facetIndex 78), (facetIndex 79), (facetIndex 82)])))
 (.branch 7
 (.leaf ([(facetIndex 85), (facetIndex 89), (facetIndex 92)]))
 (.branch 8
 (.leaf ([(facetIndex 33), (facetIndex 48), (facetIndex 49), (facetIndex 51), (facetIndex 52), (facetIndex 84)]))
 (.leaf ([(facetIndex 80), (facetIndex 87), (facetIndex 88), (facetIndex 90)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "36286880672508550111000000100000400000000770773000000004000074z20;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record044 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record044_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00047.record044" "{\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0030\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":5,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00047.record044" 83

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00047.record044" "{\"ridges\":[[9,322],[10,641],[10,642],[19,536],[20,336],[31,84],[36,641],[36,642],[39,266],[40,536],[44,322],[45,642],[50,322],[50,336],[51,594],[54,641],[54,642],[56,641],[56,642],[59,536],[62,652],[66,84],[67,660],[71,336],[72,536],[73,680],[75,688],[76,720],[83,652],[85,278],[89,90],[91,680],[92,332]],\"owners\":[[39,266,[82],[5,28,42,44,46,79,87,89,90]],[9,322,[82,85,89],[35,44,50,55]],[44,322,[85],[9,35,50,55,82,89]],[50,322,[82],[9,35,44,55,85,89]],[10,641,[62,67,73,75,76],[36,45,54,56]],[36,641,[73,75,76],[10,45,54,56,62,67]],[54,641,[62,67,76],[10,36,45,56,73,75]],[56,641,[62,67,73,75],[10,36,45,54,76]],[10,642,[83,91],[36,45,54,56]],[36,642,[91],[10,45,54,56,83]],[45,642,[],[10,36,54,56,83,91]],[54,642,[83],[10,36,45,56,91]],[56,642,[83,91],[10,36,45,54]],[31,84,[92,93],[14,57,63,65,66,78,84,85]],[66,84,[78,84,93],[14,31,57,63,65,85,92]],[19,536,[80,88,90],[40,59,70,72]],[40,536,[],[19,59,70,72,80,88,90]],[59,536,[88,90],[19,40,70,72,80]],[72,536,[80,88],[19,40,59,70,90]],[20,336,[85,89,92],[50,66,71]],[50,336,[92],[20,66,71,85,89]],[71,336,[85],[20,50,66,89,92]],[85,278,[32,79],[]],[89,90,[38,78],[]],[51,594,[],[]],[92,332,[61,82],[]],[62,652,[83],[]],[83,652,[62],[]],[67,660,[],[]],[73,680,[91],[]],[91,680,[73],[]],[75,688,[],[]],[76,720,[],[]]],\"edges\":[[34,[19,33,40,49,51,52,59,67,70,72,75,76,80,88,90]],[40,[9,20,35,44,50,55,61,66,71,82,85,89,92]],[43,[10,36,45,54,56,62,67,73,75,76,83,91]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00047.record044" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00047.record044\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-26,-8],[-26,-11],[-26,-21],[-27,-11],[-37,-13],[-41,-5],[-41,-7],[-41,-40],[-45,-32],[-46,-6],[-46,-17],[-46,-29],[-46,-44],[-49,-12],[-49,-24],[-49,-46],[-49,-47],[-53,-6],[-53,-17],[-53,-20],[-53,-29],[-53,-34],[-53,-44],[-53,-50],[-55,-49],[-15,45],[-1,45,48,51],[-18,48],[-21,45],[-2,31,33,37,38,39],[-12,37,38,39],[-25,31,33,39],[-27,31,33,37,38],[-2,46,53],[-12,53],[-19],[-25,46],[-27,46,53],[-8,54,55],[-32,41,47,55],[-3,43,50,52],[-16],[-28,50,52],[-36,43,50],[-4,48,51,54],[-21,54],[-35,48],[-48,9,42],[-51,14,41],[-22],[-54,30,45],[-31,46],[-46,31],[-33],[-37,53],[-53,37],[-38],[-39],[-56,6,44,49],[-57,12,24,25,26,27],[-58,8,11,21,32],[-59,5,7,13,15,16,40],[-60,17,19,29],[-61,56],[-62,57],[-62,58],[-63,61],[-63,62],[-64,59],[-65,60],[-66,64,65],[-67,65],[-68,63,67],[-68,66],[68],[-31,69],[-37,69],[-46,70],[-53,70],[-9,71],[-14,71],[-30,71],[-41,72],[-42,72],[-45,72],[-54,73],[-10,74],[-23,74],[-43,75],[-52,75],[-69,76],[-70,77],[-76,-77,78],[-72,79],[-71,79],[-75,80],[-74,80],[-73,-80,81],[-79,-81,82],[-78,-82,83],[-83],[3,10,16,20,22,23,28,33,34,36,38,39,43,50,52],[1,4,11,18,21,26,30,32,35,45,48,51,54],[2,12,19,25,27,31,33,37,38,39,46,53]],\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":55,\"b\":31},{\"tag\":\"incompatible\",\"a\":55,\"b\":35},{\"tag\":\"incompatible\",\"a\":55,\"b\":50},{\"tag\":\"incompatible\",\"a\":56,\"b\":35},{\"tag\":\"incompatible\",\"a\":73,\"b\":37},{\"tag\":\"incompatible\",\"a\":78,\"b\":25},{\"tag\":\"incompatible\",\"a\":78,\"b\":30},{\"tag\":\"incompatible\",\"a\":78,\"b\":77},{\"tag\":\"incompatible\",\"a\":82,\"b\":66},{\"tag\":\"incompatible\",\"a\":83,\"b\":27},{\"tag\":\"incompatible\",\"a\":83,\"b\":41},{\"tag\":\"incompatible\",\"a\":83,\"b\":60},{\"tag\":\"incompatible\",\"a\":83,\"b\":81},{\"tag\":\"incompatible\",\"a\":86,\"b\":36},{\"tag\":\"incompatible\",\"a\":86,\"b\":53},{\"tag\":\"incompatible\",\"a\":86,\"b\":83},{\"tag\":\"incompatible\",\"a\":86,\"b\":84},{\"tag\":\"incompatible\",\"a\":91,\"b\":27},{\"tag\":\"incompatible\",\"a\":91,\"b\":41},{\"tag\":\"incompatible\",\"a\":91,\"b\":49},{\"tag\":\"incompatible\",\"a\":91,\"b\":60},{\"tag\":\"incompatible\",\"a\":91,\"b\":70},{\"tag\":\"incompatible\",\"a\":91,\"b\":81},{\"tag\":\"incompatible\",\"a\":91,\"b\":88},{\"tag\":\"incompatible\",\"a\":93,\"b\":86},{\"tag\":\"mate\",\"ridge\":266,\"a\":39,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":322,\"a\":9,\"owners\":[82,85,89]},{\"tag\":\"mate\",\"ridge\":322,\"a\":44,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":322,\"a\":50,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":641,\"a\":10,\"owners\":[62,67,73,75,76]},{\"tag\":\"mate\",\"ridge\":641,\"a\":36,\"owners\":[73,75,76]},{\"tag\":\"mate\",\"ridge\":641,\"a\":54,\"owners\":[62,67,76]},{\"tag\":\"mate\",\"ridge\":641,\"a\":56,\"owners\":[62,67,73,75]},{\"tag\":\"mate\",\"ridge\":642,\"a\":10,\"owners\":[83,91]},{\"tag\":\"mate\",\"ridge\":642,\"a\":36,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":642,\"a\":45,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":642,\"a\":54,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":642,\"a\":56,\"owners\":[83,91]},{\"tag\":\"mate\",\"ridge\":84,\"a\":31,\"owners\":[92,93]},{\"tag\":\"mate\",\"ridge\":84,\"a\":66,\"owners\":[78,84,93]},{\"tag\":\"mate\",\"ridge\":536,\"a\":19,\"owners\":[80,88,90]},{\"tag\":\"mate\",\"ridge\":536,\"a\":40,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":536,\"a\":59,\"owners\":[88,90]},{\"tag\":\"mate\",\"ridge\":536,\"a\":72,\"owners\":[80,88]},{\"tag\":\"mate\",\"ridge\":336,\"a\":20,\"owners\":[85,89,92]},{\"tag\":\"mate\",\"ridge\":336,\"a\":50,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":336,\"a\":71,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":278,\"a\":85,\"owners\":[32,79]},{\"tag\":\"mate\",\"ridge\":90,\"a\":89,\"owners\":[38,78]},{\"tag\":\"mate\",\"ridge\":594,\"a\":51,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":332,\"a\":92,\"owners\":[61,82]},{\"tag\":\"mate\",\"ridge\":652,\"a\":62,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":652,\"a\":83,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":660,\"a\":67,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":680,\"a\":73,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":680,\"a\":91,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":688,\"a\":75,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":720,\"a\":76,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[27,81,86],\"full_literals\":[-56,6,44,49]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[36,53,54,55,56],\"full_literals\":[-57,12,24,25,26,27]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[31,35,50,66],\"full_literals\":[-58,8,11,21,32]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[25,30,37,39,40,77],\"full_literals\":[-59,5,7,13,15,16,40]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[41,45,60],\"full_literals\":[-60,17,19,29]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-61,false,56],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-62,57,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-62,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-63,61,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-63,false,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-64,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-65,false,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-66,64,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-67,false,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-68,63,67],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-68,false,66],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":62,\"full_literals\":[-31,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":73,\"full_literals\":[-37,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":83,\"full_literals\":[-46,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":91,\"full_literals\":[-53,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":32,\"full_literals\":[-9,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":38,\"full_literals\":[-14,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":61,\"full_literals\":[-30,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":78,\"full_literals\":[-41,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":79,\"full_literals\":[-42,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":82,\"full_literals\":[-45,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":92,\"full_literals\":[-54,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":33,\"full_literals\":[-10,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":52,\"full_literals\":[-23,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":80,\"full_literals\":[-43,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":90,\"full_literals\":[-52,75]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-69,false,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-70,false,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-76,-77,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-72,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-71,false,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0030\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-75,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0030\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-74,false,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-73,-80,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-79,-81,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-78,-82,83],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":4,\"grouped\":true},{\"tag\":\"edge\",\"edge\":34,\"owners\":[19,33,40,49,51,52,59,67,70,72,75,76,80,88,90]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[9,20,35,44,50,55,61,66,71,82,85,89,92]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[10,36,45,54,56,62,67,73,75,76,83,91]}]}"
  "105 -59 5 7 13 15 40 0 42 62 0\n106 -60 17 29 0 36 63 0\n107 66 0 75 74 0\n108 3 10 20 23 28 34 36 43 50 52 0 42 50 54 57 58 102 0\n109 2 12 25 27 31 37 46 53 0 36 54 57 58 104 0\n110 46 53 0 34 37 52 35 55 38 109 0\n111 70 0 78 79 110 0\n112 77 0 111 92 0\n113 31 37 0 57 58 54 30 32 33 53 31 56 109 0\n114 69 0 76 77 113 0\n115 76 0 114 91 0\n116 78 0 115 112 93 0\n117 -82 0 116 101 100 0\n118 -46 0 75 10 11 12 13 16 106 59 70 64 72 67 73 0\n119 53 0 118 110 0\n120 -25 0 118 37 0\n121 -6 0 119 18 0\n122 -17 0 119 19 0\n123 -20 0 119 20 0\n124 -29 0 119 21 0\n125 -34 0 119 22 0\n126 -44 0 119 23 0\n127 -50 0 119 24 0\n128 37 0 119 56 0\n129 -60 0 124 122 106 0\n130 -13 0 128 5 0\n131 -65 0 129 70 0\n132 -67 0 131 72 0\n133 64 0 131 107 71 0\n134 63 0 132 75 73 0\n135 59 0 133 69 0\n136 61 0 134 67 0\n137 62 0 134 68 0\n138 56 0 136 64 0\n139 57 0 137 65 0\n140 58 0 137 66 0\n141 49 0 138 121 126 59 0\n142 -12 0 141 14 0\n143 -24 0 141 15 0\n144 -47 0 141 17 0\n145 -55 0 141 25 0\n146 -32 0 145 144 130 135 9 40 26 6 7 8 105 0\n147 -26 0 146 140 1 2 3 61 0\n148 27 0 147 139 120 142 143 60 0\n149 -11 0 148 4 0\n150 79 0 146 147 149 94 95 83 84 85 80 81 82 49 48 27 29 51 28 45 47 103 0\n151 -81 0 150 117 99 0\n152 54 0 145 146 140 149 46 39 61 0\n153 73 0 152 86 0\n154 -80 0 153 151 98 0\n155 -75 0 154 96 0\n156 -74 0 154 97 0\n157 -43 0 155 89 0\n158 -52 0 155 90 0\n159 -10 0 156 87 0\n160 -23 0 156 88 0\n161 -3 0 157 127 158 41 0\n162 -36 0 157 127 44 0\n163 -28 0 158 127 43 0\n164 0 161 159 123 160 163 125 162 157 127 158 108 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record044.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record044.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record044.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record044.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record044 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record044.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record044.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record044.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record044.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record044 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record044_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record044_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record044_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record044_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record044_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record044_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record044_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record044 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record044_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record044_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record044_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00047.record044
