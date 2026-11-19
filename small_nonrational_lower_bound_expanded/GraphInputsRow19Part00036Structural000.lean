module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow19Part00036Frames
public import GraphInputsRow19Part00036Leaves
public import GraphInputsRow19Part00036Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00036.record000
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "338cd32cc723c4f2b23aa3a4e8d68d93693a2e4ba1e4783e6c4e98e539356354d54d8b52d8751d0f4e334e334cccb8ad2b2ac6b86d1b0ecc789d2785d1725c570de0f43c2f07e322ca2a85a0e139312c5294550d134c328c930cc4b0ac4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db69a6d349a6d369b49a69a4924926d26d2492491249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record000 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record000 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record000.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record000.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record000.data.quota

def groupMembers1 : ConcreteGrowth.Table (List (Fin data.count)) :=
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
 (.branch 18
 (.branch 16
 (.leaf ([(facetIndex 15)]))
 (.branch 17
 (.leaf ([(facetIndex 16)]))
 (.leaf ([(facetIndex 17)]))))
 (.branch 19
 (.leaf ([(facetIndex 18)]))
 (.branch 20
 (.leaf ([(facetIndex 19)]))
 (.leaf ([(facetIndex 20)])))))))
def groupColors1 : PackedGraphCertificate.Fields :=
  ⟨5, sparse_nat% "149ca307b9ac5a928398a418820"⟩
def grouping1 : FacetSat.Grouping data.count where
  count := 21
  members := fun g => groupMembers1.get g
  color := fun c => groupColors1.get c.val
def groupKind1 : List Nat := List.range grouping1.count

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 23), (facetIndex 46), (facetIndex 48), (facetIndex 50)]))
 (.branch 2
 (.leaf ([(facetIndex 41), (facetIndex 51), (facetIndex 54), (facetIndex 57)]))
 (.leaf ([(facetIndex 24), (facetIndex 60), (facetIndex 62), (facetIndex 63)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 42), (facetIndex 65), (facetIndex 68), (facetIndex 70)]))
 (.leaf ([(facetIndex 32), (facetIndex 40), (facetIndex 43), (facetIndex 44)])))
 (.branch 6
 (.leaf ([(facetIndex 21), (facetIndex 25), (facetIndex 26), (facetIndex 27), (facetIndex 28), (facetIndex 29)]))
 (.leaf ([(facetIndex 22), (facetIndex 33), (facetIndex 36), (facetIndex 37), (facetIndex 38), (facetIndex 39)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "c30184820080402000048ccdb603402db6a1a8000000000000000"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 53)]))
 (.leaf ([(facetIndex 56)])))
 (.branch 3
 (.leaf ([(facetIndex 66)]))
 (.branch 4
 (.leaf ([(facetIndex 69)]))
 (.leaf ([(facetIndex 30), (facetIndex 31), (facetIndex 45), (facetIndex 74)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 34), (facetIndex 35), (facetIndex 58), (facetIndex 73)]))
 (.leaf ([(facetIndex 47), (facetIndex 59), (facetIndex 71), (facetIndex 76)])))
 (.branch 8
 (.leaf ([(facetIndex 49), (facetIndex 55), (facetIndex 72)]))
 (.branch 9
 (.leaf ([(facetIndex 52), (facetIndex 61), (facetIndex 75)]))
 (.leaf ([(facetIndex 64), (facetIndex 67)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "68457603092090080650170080070604000000000550044z1e;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped1_0000 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
def grouped1_0002 : List Nat := [10]
def grouped1_0003 : List Nat := [10, 11]
def grouped1_0004 : List Nat := [10, 11, 12, 13, 14]
def grouped1_0005 : List Nat := [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]
def grouped1_0006 : List Nat := [11]
def grouped1_0007 : List Nat := [12]
def grouped1_0008 : List Nat := [12, 13, 14]
def grouped1_0009 : List Nat := [13]
def grouped1_0010 : List Nat := [13, 14]
def grouped1_0011 : List Nat := [14]
def grouped1_0012 : List Nat := [15]
def grouped1_0013 : List Nat := [15, 16, 17]
def grouped1_0014 : List Nat := [15, 16, 17, 18, 19, 20]
def grouped1_0015 : List Nat := [16]
def grouped1_0016 : List Nat := [16, 17]
def grouped1_0017 : List Nat := [17]
def grouped1_0018 : List Nat := [18]
def grouped1_0019 : List Nat := [18, 19, 20]
def grouped1_0020 : List Nat := [19]
def grouped1_0021 : List Nat := [19, 20]
def grouped1_0022 : List Nat := [20]
def grouped2_0023 : List Nat := [0]
def grouped2_0024 : List Nat := [0, 1, 2]
def grouped2_0026 : List Nat := [1]
def grouped2_0027 : List Nat := [1, 2]
def grouped2_0028 : List Nat := [2]
def grouped2_0029 : List Nat := [3]
def grouped2_0030 : List Nat := [3, 4]
def grouped2_0031 : List Nat := [3, 4, 5, 6]
def grouped2_0032 : List Nat := [4]
def grouped2_0033 : List Nat := [5]
def grouped2_0034 : List Nat := [5, 6]
def grouped2_0035 : List Nat := [6]
def grouped3_0036 : List Nat := [0]
def grouped3_0037 : List Nat := [0, 1]
def grouped3_0038 : List Nat := [1]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record000 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record000_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00036.record000" "{\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"group\",\"kind\":1,\"index\":11},{\"tag\":\"group\",\"kind\":1,\"index\":12},{\"tag\":\"group\",\"kind\":1,\"index\":13},{\"tag\":\"group\",\"kind\":1,\"index\":17},{\"tag\":\"group\",\"kind\":1,\"index\":18},{\"tag\":\"group\",\"kind\":1,\"index\":19},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0010\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0008\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0008\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0004\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0004\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0016\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0013\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0021\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0019\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0019\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0014\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0014\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0005\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"groupKind1\"},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0027\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0024\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0030\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0034\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0031\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0037\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00036.record000" 72

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00036.record000" "{\"ridges\":[[6,131],[6,145],[6,146],[7,35],[7,131],[7,161],[13,161],[13,176],[19,176],[21,19],[22,35],[27,146],[32,131],[32,193],[37,162],[40,193],[42,35],[43,146],[43,193],[44,162],[44,193],[44,194],[51,289],[53,145],[53,212],[54,273],[56,161],[56,232],[57,145],[57,161],[65,546],[66,146],[66,212],[68,530],[69,162],[69,232],[70,146],[70,176]],\"owners\":[[21,19,[5,6,41,42,43],[1,26,28,29,33,34,35]],[22,35,[5,7,41,42,44],[3,25,30,31,36,38,39]],[27,146,[19,70],[6,43,66]],[43,146,[19,70],[6,27,66]],[7,161,[13,56,57],[37,44]],[56,161,[7,13,57],[37,44]],[37,162,[19,70],[7,44,69]],[44,162,[19,70],[7,37,69]],[69,162,[7,19,70],[37,44]],[32,193,[56],[8,40,43,44,53]],[40,193,[53],[8,32,43,44,56]],[43,193,[56],[8,32,40,44,53]],[44,193,[53],[8,32,40,43,56]],[44,194,[66],[8,32,40,43,69]],[54,273,[11,28],[14,34,41,46,57]],[51,289,[12,38],[14,30,41,48,57]],[13,176,[19,70],[57]],[19,176,[13,57],[70]],[70,176,[13,57],[19]],[68,530,[17,29],[20,35,42,60,70]],[65,546,[18,39],[20,31,42,62,70]],[53,212,[66],[]],[66,212,[53],[]],[56,232,[69],[]],[69,232,[56],[]]],\"edges\":[[32,[6,13,19,27,43,53,57,66,70]],[36,[7,13,19,37,44,56,57,69,70]]],\"groupings\":[1,2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00036.record000" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00036.record000\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-24,-6],[-25,-9],[-25,-18],[-25,-20],[-25,-22],[-29,-13],[-29,-14],[-29,-15],[-29,-17],[-31,-19],[-31,-20],[-31,-21],[-31,-23],[-31,-27],[-32,-1],[-32,-12],[-32,-18],[-32,-24],[-32,-25],[-33,-28],[-34,-13],[-34,-14],[-34,-16],[-34,-17],[-34,-26],[-35,-30],[-36,-22],[-37,-1],[-37,-12],[-37,-18],[-37,-24],[-37,-25],[-10,1,2,24,25,26],[-11,1,3,24,25,27],[-3,-11,-25],[-2,-3,-17],[-2,-29,-32],[-14,9,37],[-26,9,37],[-2,-34,-37],[-3,6,31,32],[-31,3,6,32],[-3,-6,-31],[-3,-31,-32],[-20,9,37],[-27,9,37],[-36,3,9,37],[-17,31],[-23,29],[-26,31],[-27,29],[-27,34],[-30,4,15],[-28,5,21],[-6,9,37],[-9,6,32],[-37,6,32],[-35,7,16],[-33,8,22],[-29,34],[-34,29],[-31,36],[-36,31],[-4,38],[-5,39],[-6,40],[-7,41],[-8,42],[-9,43],[-38,44],[-40,45],[-45,46],[-39,-45,47],[-46,48],[-47,49],[-44,-46,49],[-41,50],[-50,51],[-43,52],[-52,53],[-42,-52,54],[-53,55],[-54,56],[-51,-53,56],[-48,-56,57],[-49,-55,57],[-57,58],[-58],[-59,24,28,30,32],[-60,25,33,35,37],[-61,17,23,26,27],[-62,10,12,13,14,15,16],[-63,11,18,19,20,21,22],[-64,59],[-65,64],[-66,60],[-66,61],[-67,62],[-67,63],[-68,66],[-68,67],[-69,65],[-69,68],[69],[-70,29],[-29,70],[-71,31],[-31,71],[-72,70,71],[-71,72],[-70,72],[2,6,9,14,26,29,32,34,37],[3,6,9,20,27,31,32,36,37]],\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"group\",\"index\":11,\"kind\":1},{\"tag\":\"group\",\"index\":12,\"kind\":1},{\"tag\":\"group\",\"index\":13,\"kind\":1},{\"tag\":\"group\",\"index\":17,\"kind\":1},{\"tag\":\"group\",\"index\":18,\"kind\":1},{\"tag\":\"group\",\"index\":19,\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":41,\"b\":13},{\"tag\":\"incompatible\",\"a\":42,\"b\":19},{\"tag\":\"incompatible\",\"a\":42,\"b\":33},{\"tag\":\"incompatible\",\"a\":42,\"b\":37},{\"tag\":\"incompatible\",\"a\":42,\"b\":39},{\"tag\":\"incompatible\",\"a\":53,\"b\":26},{\"tag\":\"incompatible\",\"a\":53,\"b\":27},{\"tag\":\"incompatible\",\"a\":53,\"b\":28},{\"tag\":\"incompatible\",\"a\":53,\"b\":32},{\"tag\":\"incompatible\",\"a\":56,\"b\":36},{\"tag\":\"incompatible\",\"a\":56,\"b\":37},{\"tag\":\"incompatible\",\"a\":56,\"b\":38},{\"tag\":\"incompatible\",\"a\":56,\"b\":40},{\"tag\":\"incompatible\",\"a\":56,\"b\":44},{\"tag\":\"incompatible\",\"a\":57,\"b\":5},{\"tag\":\"incompatible\",\"a\":57,\"b\":25},{\"tag\":\"incompatible\",\"a\":57,\"b\":33},{\"tag\":\"incompatible\",\"a\":57,\"b\":41},{\"tag\":\"incompatible\",\"a\":57,\"b\":42},{\"tag\":\"incompatible\",\"a\":65,\"b\":51},{\"tag\":\"incompatible\",\"a\":66,\"b\":26},{\"tag\":\"incompatible\",\"a\":66,\"b\":27},{\"tag\":\"incompatible\",\"a\":66,\"b\":29},{\"tag\":\"incompatible\",\"a\":66,\"b\":32},{\"tag\":\"incompatible\",\"a\":66,\"b\":43},{\"tag\":\"incompatible\",\"a\":68,\"b\":54},{\"tag\":\"incompatible\",\"a\":69,\"b\":39},{\"tag\":\"incompatible\",\"a\":70,\"b\":5},{\"tag\":\"incompatible\",\"a\":70,\"b\":25},{\"tag\":\"incompatible\",\"a\":70,\"b\":33},{\"tag\":\"incompatible\",\"a\":70,\"b\":41},{\"tag\":\"incompatible\",\"a\":70,\"b\":42},{\"tag\":\"mate\",\"ridge\":19,\"a\":21,\"owners\":[5,6,41,42,43]},{\"tag\":\"mate\",\"ridge\":35,\"a\":22,\"owners\":[5,7,41,42,44]},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[7,22,42]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[6,7,32]},{\"tag\":\"three\",\"ridge\":145,\"vertices\":[6,53,57]},{\"tag\":\"mate\",\"ridge\":146,\"a\":27,\"owners\":[19,70]},{\"tag\":\"mate\",\"ridge\":146,\"a\":43,\"owners\":[19,70]},{\"tag\":\"three\",\"ridge\":146,\"vertices\":[6,66,70]},{\"tag\":\"mate\",\"ridge\":161,\"a\":7,\"owners\":[13,56,57]},{\"tag\":\"mate\",\"ridge\":161,\"a\":56,\"owners\":[7,13,57]},{\"tag\":\"three\",\"ridge\":161,\"vertices\":[7,13,56]},{\"tag\":\"three\",\"ridge\":161,\"vertices\":[7,56,57]},{\"tag\":\"mate\",\"ridge\":162,\"a\":37,\"owners\":[19,70]},{\"tag\":\"mate\",\"ridge\":162,\"a\":44,\"owners\":[19,70]},{\"tag\":\"mate\",\"ridge\":162,\"a\":69,\"owners\":[7,19,70]},{\"tag\":\"mate\",\"ridge\":193,\"a\":32,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":193,\"a\":40,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":193,\"a\":43,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":193,\"a\":44,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":194,\"a\":44,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":273,\"a\":54,\"owners\":[11,28]},{\"tag\":\"mate\",\"ridge\":289,\"a\":51,\"owners\":[12,38]},{\"tag\":\"mate\",\"ridge\":176,\"a\":13,\"owners\":[19,70]},{\"tag\":\"mate\",\"ridge\":176,\"a\":19,\"owners\":[13,57]},{\"tag\":\"mate\",\"ridge\":176,\"a\":70,\"owners\":[13,57]},{\"tag\":\"mate\",\"ridge\":530,\"a\":68,\"owners\":[17,29]},{\"tag\":\"mate\",\"ridge\":546,\"a\":65,\"owners\":[18,39]},{\"tag\":\"mate\",\"ridge\":212,\"a\":53,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":212,\"a\":66,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":232,\"a\":56,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":232,\"a\":69,\"owners\":[56]},{\"tag\":\"group_take\",\"kind\":1,\"index\":11,\"member\":11,\"full_literals\":[-4,38]},{\"tag\":\"group_take\",\"kind\":1,\"index\":12,\"member\":12,\"full_literals\":[-5,39]},{\"tag\":\"group_take\",\"kind\":1,\"index\":13,\"member\":13,\"full_literals\":[-6,40]},{\"tag\":\"group_take\",\"kind\":1,\"index\":17,\"member\":17,\"full_literals\":[-7,41]},{\"tag\":\"group_take\",\"kind\":1,\"index\":18,\"member\":18,\"full_literals\":[-8,42]},{\"tag\":\"group_take\",\"kind\":1,\"index\":19,\"member\":19,\"full_literals\":[-9,43]},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0006\",\"joined_name\":\"grouped1_0003\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-38,44],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13],\"right\":[14],\"left_name\":\"grouped1_0009\",\"right_name\":\"grouped1_0011\",\"joined_name\":\"grouped1_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,45],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13,14],\"left_name\":\"grouped1_0007\",\"right_name\":\"grouped1_0010\",\"joined_name\":\"grouped1_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-45,46],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13,14],\"left_name\":\"grouped1_0007\",\"right_name\":\"grouped1_0010\",\"joined_name\":\"grouped1_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-39,-45,47],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13,14],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0008\",\"joined_name\":\"grouped1_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-46,48],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13,14],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0008\",\"joined_name\":\"grouped1_0004\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-47,49],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13,14],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0008\",\"joined_name\":\"grouped1_0004\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-44,-46,49],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16],\"right\":[17],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0017\",\"joined_name\":\"grouped1_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,50],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15],\"right\":[16,17],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-50,51],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[19],\"right\":[20],\"left_name\":\"grouped1_0020\",\"right_name\":\"grouped1_0022\",\"joined_name\":\"grouped1_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-43,false,52],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[18],\"right\":[19,20],\"left_name\":\"grouped1_0018\",\"right_name\":\"grouped1_0021\",\"joined_name\":\"grouped1_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-52,53],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[18],\"right\":[19,20],\"left_name\":\"grouped1_0018\",\"right_name\":\"grouped1_0021\",\"joined_name\":\"grouped1_0019\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-42,-52,54],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16,17],\"right\":[18,19,20],\"left_name\":\"grouped1_0013\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-53,55],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16,17],\"right\":[18,19,20],\"left_name\":\"grouped1_0013\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0014\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-54,56],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16,17],\"right\":[18,19,20],\"left_name\":\"grouped1_0013\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0014\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-51,-53,56],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19,20],\"left_name\":\"grouped1_0004\",\"right_name\":\"grouped1_0014\",\"joined_name\":\"grouped1_0005\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-48,-56,57],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11,12,13,14],\"right\":[15,16,17,18,19,20],\"left_name\":\"grouped1_0004\",\"right_name\":\"grouped1_0014\",\"joined_name\":\"grouped1_0005\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-49,-55,57],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9],\"right\":[10,11,12,13,14,15,16,17,18,19,20],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0005\",\"joined_name\":\"groupKind1\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-57,58],\"grouped\":true,\"kind\":1},{\"tag\":\"quota_upper\",\"kind\":1,\"quota\":2,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[41,51,54,57],\"full_literals\":[-59,24,28,30,32]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[42,65,68,70],\"full_literals\":[-60,25,33,35,37]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[32,40,43,44],\"full_literals\":[-61,17,23,26,27]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[21,25,26,27,28,29],\"full_literals\":[-62,10,12,13,14,15,16]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[22,33,36,37,38,39],\"full_literals\":[-63,11,18,19,20,21,22]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped2_0026\",\"right_name\":\"grouped2_0028\",\"joined_name\":\"grouped2_0027\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-64,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0023\",\"right_name\":\"grouped2_0027\",\"joined_name\":\"grouped2_0024\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-65,false,64],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0029\",\"right_name\":\"grouped2_0032\",\"joined_name\":\"grouped2_0030\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-66,60,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0029\",\"right_name\":\"grouped2_0032\",\"joined_name\":\"grouped2_0030\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-66,false,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0033\",\"right_name\":\"grouped2_0035\",\"joined_name\":\"grouped2_0034\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-67,62,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0033\",\"right_name\":\"grouped2_0035\",\"joined_name\":\"grouped2_0034\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-67,false,63],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0030\",\"right_name\":\"grouped2_0034\",\"joined_name\":\"grouped2_0031\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-68,66,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0030\",\"right_name\":\"grouped2_0034\",\"joined_name\":\"grouped2_0031\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-68,false,67],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0024\",\"right_name\":\"grouped2_0031\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-69,65,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0024\",\"right_name\":\"grouped2_0031\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-69,false,68],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[53],\"full_literals\":[-70,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":53,\"full_literals\":[-29,70]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[56],\"full_literals\":[-71,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":56,\"full_literals\":[-31,71]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0036\",\"right_name\":\"grouped3_0038\",\"joined_name\":\"grouped3_0037\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-72,70,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0036\",\"right_name\":\"grouped3_0038\",\"joined_name\":\"grouped3_0037\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-71,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0036\",\"right_name\":\"grouped3_0038\",\"joined_name\":\"grouped3_0037\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-70,false,72],\"grouped\":true,\"kind\":3},{\"tag\":\"edge\",\"edge\":32,\"owners\":[6,13,19,27,43,53,57,66,70]},{\"tag\":\"edge\",\"edge\":36,\"owners\":[7,13,19,37,44,56,57,69,70]}]}"
  "114 -57 0 88 87 0\n115 65 0 104 102 0\n116 68 0 104 103 0\n117 64 0 115 95 0\n118 66 0 116 100 0\n119 67 0 116 101 0\n120 59 0 117 94 0\n121 60 0 118 96 0\n122 61 0 118 97 0\n123 62 0 119 98 0\n124 63 0 119 99 0\n125 72 0 122 110 111 108 106 48 50 49 51 91 0\n126 34 -32 -37 0 125 124 32 31 30 28 52 60 105 109 107 10 11 12 44 62 34 27 93 0\n127 -34 -37 0 123 32 31 29 28 21 22 23 25 40 61 33 8 92 0\n128 -37 0 125 124 28 30 31 32 127 52 60 126 105 57 109 107 10 11 12 62 43 27 34 93 0\n129 31 36 20 6 27 9 32 0 128 113 41 0\n130 31 -25 0 128 2 55 46 19 4 63 129 0\n131 -25 0 128 124 2 3 4 5 19 55 130 10 12 42 93 35 0\n132 9 32 -31 0 122 128 62 14 13 38 39 55 47 91 36 9 24 112 0\n133 32 -31 0 114 120 131 128 121 62 27 12 132 56 69 1 66 79 71 80 72 82 74 86 85 75 83 73 81 65 68 54 59 89 90 26 0\n134 -31 0 131 124 10 11 12 14 62 27 133 15 17 18 44 34 93 0\n135 -26 0 134 50 0\n136 -36 0 134 63 0\n137 -71 0 134 107 0\n138 70 0 137 125 109 0\n139 29 0 138 105 0\n140 -13 0 139 6 0\n141 -14 0 139 7 0\n142 -15 0 139 8 0\n143 34 0 139 60 0\n144 -16 0 143 23 0\n145 -32 0 139 140 144 142 141 123 135 131 15 16 18 37 92 33 0\n146 -9 0 114 142 145 120 144 131 128 121 56 69 1 66 79 71 80 72 82 74 86 85 76 84 70 78 64 77 53 67 89 58 20 90 0\n147 -20 0 146 128 45 0\n148 -27 0 146 128 46 0\n149 -6 0 146 128 55 0\n150 0 147 148 134 136 149 146 145 129 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record000.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record000.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record000.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record000.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record000 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record000.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record000.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record000.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record000.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record000 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record000_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record000 Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record000_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record000_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00036.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00036.record025
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ce2b4ccab26cb2ac6a5a56a3a4eaa6a5a5635a362da4e8b92e2b9b1566394e479356352d4758b52d2b46d68d9354cd38cd332cd4b8ad2b2ae1b46c5b0ecc789d2729e1725c570de0f43c8f0be2c8384e4c4b14a4a51342d44c9314d0b12c8711c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6db6db6da4da6d36d349269269269b49a6d349a491249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record025 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record025 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record025.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 38), (facetIndex 53), (facetIndex 56)]))
 (.branch 2
 (.leaf ([(facetIndex 17), (facetIndex 20), (facetIndex 59), (facetIndex 60)]))
 (.leaf ([(facetIndex 44), (facetIndex 45), (facetIndex 46), (facetIndex 47)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 18), (facetIndex 22), (facetIndex 23), (facetIndex 28)]))
 (.leaf ([(facetIndex 19), (facetIndex 31), (facetIndex 34), (facetIndex 36)])))
 (.branch 6
 (.leaf ([(facetIndex 25), (facetIndex 37), (facetIndex 49)]))
 (.leaf ([(facetIndex 30), (facetIndex 40), (facetIndex 41), (facetIndex 42)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "12000000284921b602c1009830286c18c8000000000000"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1, 2]
def grouped2_0003 : List Nat := [1, 2]
def grouped2_0004 : List Nat := [3]
def grouped2_0005 : List Nat := [3, 4]
def grouped2_0006 : List Nat := [3, 4, 5, 6]
def grouped2_0007 : List Nat := [4]
def grouped2_0008 : List Nat := [5]
def grouped2_0009 : List Nat := [5, 6]
def grouped2_0010 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record025 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record025_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00036.record025" "{\"atoms\":[{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0005\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00036.record025" 32

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00036.record025" "{\"ridges\":[[25,164],[30,81],[37,176],[41,81],[48,116],[49,164],[52,120],[53,296],[57,170]],\"owners\":[[30,81,[48,51],[5,22,40,41,52,55]],[41,81,[48,51,52],[5,22,30,40,55]],[25,164,[76],[10,45,49,57,61,66]],[49,164,[57,66],[10,25,45,61,76]],[53,296,[58,72],[11,34,46,67,77]],[37,176,[76],[12,49,56,61,73,74]],[57,170,[33],[]],[48,116,[],[]],[52,120,[],[]]],\"edges\":[],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00036.record025" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00036.record025\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-4,-1],[-5,-4],[-10,-8],[-12,-8],[-14,-7],[-18,-14],[-21,-9],[-21,-20],[-22,-21],[-23,-2],[-23,-3],[-23,-15],[-6,13,15],[-11,13,15,16],[-4,23],[-14,19,21],[-17,20,22],[-8,23],[-19,7],[-13],[-16],[-24,9,17,18],[-25,1,2,3,5],[-26,4,8,14],[-27,6,10,11,12],[-28,24],[-29,25],[-30,26],[-30,27],[-31,29],[-31,30],[-32,28],[-32,31],[32]],\"atoms\":[{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":25,\"b\":18},{\"tag\":\"incompatible\",\"a\":28,\"b\":25},{\"tag\":\"incompatible\",\"a\":40,\"b\":37},{\"tag\":\"incompatible\",\"a\":42,\"b\":37},{\"tag\":\"incompatible\",\"a\":49,\"b\":33},{\"tag\":\"incompatible\",\"a\":56,\"b\":49},{\"tag\":\"incompatible\",\"a\":66,\"b\":38},{\"tag\":\"incompatible\",\"a\":66,\"b\":58},{\"tag\":\"incompatible\",\"a\":72,\"b\":66},{\"tag\":\"incompatible\",\"a\":76,\"b\":22},{\"tag\":\"incompatible\",\"a\":76,\"b\":23},{\"tag\":\"incompatible\",\"a\":76,\"b\":51},{\"tag\":\"mate\",\"ridge\":81,\"a\":30,\"owners\":[48,51]},{\"tag\":\"mate\",\"ridge\":81,\"a\":41,\"owners\":[48,51,52]},{\"tag\":\"mate\",\"ridge\":164,\"a\":25,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":164,\"a\":49,\"owners\":[57,66]},{\"tag\":\"mate\",\"ridge\":296,\"a\":53,\"owners\":[58,72]},{\"tag\":\"mate\",\"ridge\":176,\"a\":37,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":170,\"a\":57,\"owners\":[33]},{\"tag\":\"mate\",\"ridge\":116,\"a\":48,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":120,\"a\":52,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[38,53,56],\"full_literals\":[-24,9,17,18]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[18,22,23,28],\"full_literals\":[-25,1,2,3,5]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[25,37,49],\"full_literals\":[-26,4,8,14]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[30,40,41,42],\"full_literals\":[-27,6,10,11,12]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0003\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-28,24,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0004\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0005\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-29,25,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-30,26,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-30,false,27],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-31,29,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0006\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-31,false,30],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-32,28,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-32,false,31],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true}]}"
  "35 28 0 34 32 0\n36 31 0 34 33 0\n37 24 0 35 26 0\n38 29 0 36 30 0\n39 30 0 36 31 0\n40 25 0 38 27 0\n41 26 0 39 28 0\n42 27 0 39 29 0\n43 -14 0 37 5 6 19 16 7 8 9 22 17 0\n44 23 0 43 41 15 18 24 0\n45 -2 0 44 10 0\n46 -3 0 44 11 0\n47 -15 0 44 12 0\n48 -6 0 47 20 13 0\n49 -11 0 47 20 21 14 0\n50 -4 0 45 46 40 1 2 23 0\n51 8 0 50 41 43 24 0\n52 -10 0 51 3 0\n53 -12 0 51 4 0\n54 0 53 52 42 49 48 25 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record025.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record025.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record025.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record025.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record025 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record025.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record025.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record025.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record025.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record025 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record025_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record025_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record025_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record025_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record025_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record025_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record025_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record025 Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record025_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record025_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record025_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00036.record025

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00036.record032
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2f07cccaaa96a3a4e87a699568d9361d8ce2b86e1783ecc6a9966394e4b9695558d5352d4cd2b49d1743dc8ea368f1394d538cd33a2e4b32e2b4acab86d1b16c3b61d4731e2749ca785d1715c3723c4f0bc1f8e1348a8aa498a6864594545582c8b12d0721c47"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b69a6d369b4db6d26da69b6d36db6db4926934d24d269349b249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record032 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record032 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record032.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 22), (facetIndex 54), (facetIndex 56)]))
 (.leaf ([(facetIndex 31), (facetIndex 49), (facetIndex 61)])))
 (.branch 3
 (.leaf ([(facetIndex 25), (facetIndex 70), (facetIndex 73)]))
 (.leaf ([(facetIndex 34), (facetIndex 67), (facetIndex 78)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 18), (facetIndex 21), (facetIndex 27), (facetIndex 28), (facetIndex 29)]))
 (.leaf ([(facetIndex 33), (facetIndex 36), (facetIndex 60), (facetIndex 76)])))
 (.branch 7
 (.leaf ([(facetIndex 19), (facetIndex 37), (facetIndex 38), (facetIndex 39)]))
 (.leaf ([(facetIndex 24)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "c501008060000d000000008000000db50e8224817020d00000000000000"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 16), (facetIndex 17), (facetIndex 50), (facetIndex 52), (facetIndex 66)]))
 (.branch 2
 (.leaf ([(facetIndex 48), (facetIndex 64), (facetIndex 68), (facetIndex 80), (facetIndex 81)]))
 (.leaf ([(facetIndex 20), (facetIndex 23), (facetIndex 32), (facetIndex 42), (facetIndex 43), (facetIndex 44), (facetIndex 65), (facetIndex 69)]))))
 (.branch 4
 (.leaf ([(facetIndex 26), (facetIndex 30), (facetIndex 35), (facetIndex 45), (facetIndex 46), (facetIndex 47), (facetIndex 51), (facetIndex 53)]))
 (.branch 5
 (.leaf ([(facetIndex 40), (facetIndex 55), (facetIndex 57), (facetIndex 58), (facetIndex 59), (facetIndex 62), (facetIndex 63)]))
 (.leaf ([(facetIndex 41), (facetIndex 71), (facetIndex 72), (facetIndex 74), (facetIndex 75), (facetIndex 77), (facetIndex 79)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "9a28b45a110119009208186016da4ac0006020c00c0402000000000000000"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
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

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record032 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record032_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00036.record032" "{\"atoms\":[{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00036.record032" 67

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00036.record032" "{\"ridges\":[[19,133],[21,70],[24,133],[24,164],[25,259],[31,74],[33,515],[34,137],[34,168],[36,515],[49,84],[51,45],[53,177],[60,529],[61,88],[67,168],[68,204],[72,338],[74,114],[76,546],[78,168],[80,108],[81,156]],\"owners\":[[21,70,[66,68],[0,18,27,28,65,69,72]],[19,133,[53,57],[1,24,27,29,50,51,52]],[24,133,[50,52],[1,19,27,29,51,53,57]],[25,259,[32,42,44],[2,22,28,29,35,40,45,47]],[31,74,[66,68],[3,18,37,38,65,74,77]],[34,137,[50,52],[4,19,37,39,51,58,62]],[33,515,[26,46,47],[5,23,36,38,39,41,43,44]],[36,515,[23,43,44],[5,26,33,38,39,41,46,47]],[49,84,[69,72],[6,21,56,65,80]],[61,88,[65,74,80],[8,31,49,77]],[60,529,[23,43,44],[9,33,41,55,61,63]],[24,164,[81],[10,51,53,57,67,73]],[34,168,[81],[12,51,58,62,67,78]],[67,168,[58,62],[12,34,51,78,81]],[78,168,[51,58,81],[12,34,62,67]],[76,546,[26,46,47],[13,36,41,71,78,79]],[51,45,[17,48],[]],[72,338,[42],[]],[81,156,[50],[]],[68,204,[52],[]],[53,177,[58],[]],[80,108,[66],[]],[74,114,[69],[]]],\"edges\":[],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00036.record032" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00036.record032\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-9,-7],[-10,-7],[-11,-7],[-12,-7],[-13,-6],[-15,-13],[-17,-7],[-18,-17],[-20,-17],[-22,-13],[-23,-13],[-24,-7],[-25,-7],[-27,-1],[-27,-2],[-27,-21],[-28,-27],[-30,-27],[-32,-17],[-34,-7],[-35,-15],[-35,-19],[-35,-26],[-35,-28],[-35,-33],[-35,-34],[-38,-27],[-39,-37],[-40,-7],[-41,-14],[-41,-21],[-41,-23],[-42,-41],[-44,-41],[-46,-13],[-46,-36],[-47,-46],[-49,-3],[-49,-38],[-5,38,40],[-4,31,32],[-7,28,30],[-8,14,21,23],[-13,38,40],[-16,28,30],[-15,9,24,25],[-17,6,22,23],[-27,41,43],[-35,37,45,48],[-34,6,22,23],[-7,49],[-16,49],[-39,33,36],[-47,29,33,49],[-46,9,24,25],[-29,2,26],[-43,21],[-49,28],[-40,30],[-31,33],[-48,38],[-45,41],[-50,13,27,35],[-51,8,42,44],[-52,16,39,47],[-53,3,5,10,11,12],[-54,15,17,34,46],[-55,4,18,19,20],[-56,7],[-57,50],[-58,51],[-58,52],[-59,57],[-59,58],[-60,53,54],[-61,54],[-62,55,56],[-63,56],[-64,60],[-64,61,63],[-64,62],[-65,63],[-66,59,65],[-66,64],[66],[-67,1,2,28,30,38],[-2,67],[-28,67],[-30,67],[-38,67]],\"atoms\":[{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":26,\"b\":24},{\"tag\":\"incompatible\",\"a\":27,\"b\":24},{\"tag\":\"incompatible\",\"a\":28,\"b\":24},{\"tag\":\"incompatible\",\"a\":29,\"b\":24},{\"tag\":\"incompatible\",\"a\":31,\"b\":23},{\"tag\":\"incompatible\",\"a\":33,\"b\":31},{\"tag\":\"incompatible\",\"a\":36,\"b\":24},{\"tag\":\"incompatible\",\"a\":37,\"b\":36},{\"tag\":\"incompatible\",\"a\":39,\"b\":36},{\"tag\":\"incompatible\",\"a\":43,\"b\":31},{\"tag\":\"incompatible\",\"a\":44,\"b\":31},{\"tag\":\"incompatible\",\"a\":46,\"b\":24},{\"tag\":\"incompatible\",\"a\":47,\"b\":24},{\"tag\":\"incompatible\",\"a\":49,\"b\":16},{\"tag\":\"incompatible\",\"a\":49,\"b\":17},{\"tag\":\"incompatible\",\"a\":49,\"b\":42},{\"tag\":\"incompatible\",\"a\":50,\"b\":49},{\"tag\":\"incompatible\",\"a\":52,\"b\":49},{\"tag\":\"incompatible\",\"a\":57,\"b\":36},{\"tag\":\"incompatible\",\"a\":60,\"b\":24},{\"tag\":\"incompatible\",\"a\":61,\"b\":33},{\"tag\":\"incompatible\",\"a\":61,\"b\":38},{\"tag\":\"incompatible\",\"a\":61,\"b\":48},{\"tag\":\"incompatible\",\"a\":61,\"b\":50},{\"tag\":\"incompatible\",\"a\":61,\"b\":58},{\"tag\":\"incompatible\",\"a\":61,\"b\":60},{\"tag\":\"incompatible\",\"a\":66,\"b\":49},{\"tag\":\"incompatible\",\"a\":67,\"b\":65},{\"tag\":\"incompatible\",\"a\":68,\"b\":24},{\"tag\":\"incompatible\",\"a\":69,\"b\":32},{\"tag\":\"incompatible\",\"a\":69,\"b\":42},{\"tag\":\"incompatible\",\"a\":69,\"b\":44},{\"tag\":\"incompatible\",\"a\":70,\"b\":69},{\"tag\":\"incompatible\",\"a\":73,\"b\":69},{\"tag\":\"incompatible\",\"a\":76,\"b\":31},{\"tag\":\"incompatible\",\"a\":76,\"b\":62},{\"tag\":\"incompatible\",\"a\":78,\"b\":76},{\"tag\":\"incompatible\",\"a\":81,\"b\":18},{\"tag\":\"incompatible\",\"a\":81,\"b\":66},{\"tag\":\"mate\",\"ridge\":70,\"a\":21,\"owners\":[66,68]},{\"tag\":\"mate\",\"ridge\":133,\"a\":19,\"owners\":[53,57]},{\"tag\":\"mate\",\"ridge\":133,\"a\":24,\"owners\":[50,52]},{\"tag\":\"mate\",\"ridge\":259,\"a\":25,\"owners\":[32,42,44]},{\"tag\":\"mate\",\"ridge\":74,\"a\":31,\"owners\":[66,68]},{\"tag\":\"mate\",\"ridge\":137,\"a\":34,\"owners\":[50,52]},{\"tag\":\"mate\",\"ridge\":515,\"a\":33,\"owners\":[26,46,47]},{\"tag\":\"mate\",\"ridge\":515,\"a\":36,\"owners\":[23,43,44]},{\"tag\":\"mate\",\"ridge\":84,\"a\":49,\"owners\":[69,72]},{\"tag\":\"mate\",\"ridge\":88,\"a\":61,\"owners\":[65,74,80]},{\"tag\":\"mate\",\"ridge\":529,\"a\":60,\"owners\":[23,43,44]},{\"tag\":\"mate\",\"ridge\":164,\"a\":24,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":168,\"a\":34,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":168,\"a\":67,\"owners\":[58,62]},{\"tag\":\"mate\",\"ridge\":168,\"a\":78,\"owners\":[51,58,81]},{\"tag\":\"mate\",\"ridge\":546,\"a\":76,\"owners\":[26,46,47]},{\"tag\":\"mate\",\"ridge\":45,\"a\":51,\"owners\":[17,48]},{\"tag\":\"mate\",\"ridge\":338,\"a\":72,\"owners\":[42]},{\"tag\":\"mate\",\"ridge\":156,\"a\":81,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":204,\"a\":68,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":177,\"a\":53,\"owners\":[58]},{\"tag\":\"mate\",\"ridge\":108,\"a\":80,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":114,\"a\":74,\"owners\":[69]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[31,49,61],\"full_literals\":[-50,13,27,35]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[25,70,73],\"full_literals\":[-51,8,42,44]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[34,67,78],\"full_literals\":[-52,16,39,47]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[18,21,27,28,29],\"full_literals\":[-53,3,5,10,11,12]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[33,36,60,76],\"full_literals\":[-54,15,17,34,46]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[19,37,38,39],\"full_literals\":[-55,4,18,19,20]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[24],\"full_literals\":[-56,7]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-57,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-58,51,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-58,false,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-59,57,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-59,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-60,53,54],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-61,false,54],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-62,55,56],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-63,false,56],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-64,60,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-64,61,63],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-64,false,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-65,false,63],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-66,59,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-66,false,64],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[16,17,50,52,66],\"full_literals\":[-67,1,2,28,30,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":17,\"full_literals\":[-2,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":50,\"full_literals\":[-28,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":52,\"full_literals\":[-30,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":66,\"full_literals\":[-38,67]}]}"
  "91 64 0 85 84 0\n92 60 0 91 79 0\n93 62 0 91 81 0\n94 -41 -51 0 30 31 32 33 34 43 64 0\n95 -27 41 0 16 48 57 0\n96 67 0 85 87 88 89 90 58 59 42 45 61 44 69 78 82 83 73 74 70 71 72 94 62 95 63 23 25 49 56 54 28 65 0\n97 -13 -54 0 5 6 10 11 35 50 47 67 0\n98 -46 16 33 -52 0 36 37 53 65 0\n99 56 27 0 93 91 85 78 77 82 80 83 76 73 74 70 72 97 63 21 22 24 25 26 58 60 52 98 67 8 9 19 68 41 0\n100 -7 0 92 1 2 3 4 7 12 13 20 29 51 46 55 39 67 40 75 38 66 0\n101 -56 0 100 69 0\n102 27 0 101 99 0\n103 -1 0 102 14 0\n104 -2 0 102 15 0\n105 -28 0 102 17 0\n106 -30 0 102 18 0\n107 -38 0 102 27 0\n108 0 107 106 103 104 96 105 86 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record032.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record032.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record032.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record032.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record032 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record032.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record032.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record032.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record032.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record032 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record032_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record032_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record032_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record032_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record032_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record032_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record032_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record032 Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record032_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record032_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record032_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00036.record032
