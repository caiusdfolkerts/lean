module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00145Frames
public import GraphInputsRow29Part00145Leaves
public import GraphInputsRow29Part00145Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00145.record001
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ae1745b29c8f13cb8ab23caaa3aa9a8e8bab1a66a595635a361da8e538ce1ba1e4789e745713c5c9aa5693a5994e4b959555355351d68d534cd8b52d1b49da8ce354cd32cc73a2d4b32e2b2ac6b46e8751cc789d1725c5783d0f23c4f8b11c0f28a8a89a0ea26198368382e079192643951465454354342d074c318c930cc8b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db49b69a49a6da49b4926db6da4926934d249a6924d2493492492489249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record001 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record001 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record001.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record001.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record001.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 44), (facetIndex 62), (facetIndex 67), (facetIndex 91), (facetIndex 93)]))
 (.leaf ([(facetIndex 50), (facetIndex 73), (facetIndex 74), (facetIndex 76), (facetIndex 84)])))
 (.branch 3
 (.leaf ([(facetIndex 57), (facetIndex 64)]))
 (.leaf ([(facetIndex 55), (facetIndex 77), (facetIndex 78), (facetIndex 79), (facetIndex 89)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 85), (facetIndex 90)]))
 (.leaf ([(facetIndex 75), (facetIndex 97), (facetIndex 99), (facetIndex 100), (facetIndex 101)])))
 (.branch 7
 (.leaf ([(facetIndex 105), (facetIndex 106)]))
 (.leaf ([(facetIndex 104), (facetIndex 107)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "fb702da280001180210006d9a4800000200001060004z25;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0002 : List Nat := [0, 1, 2, 3]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [2, 3]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [4]
def grouped3_0009 : List Nat := [4, 5]
def grouped3_0010 : List Nat := [4, 5, 6, 7]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7]
def grouped3_0014 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record001 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record001_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00145.record001" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00145.record001" 60

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00145.record001" "{\"ridges\":[[10,193],[17,321],[17,324],[30,642],[30,648],[42,194],[43,321],[43,324],[44,645],[49,194],[50,330],[51,642],[51,648],[54,193],[55,338],[56,193],[57,673],[63,321],[63,324],[64,645],[67,212],[68,321],[68,324],[69,321],[69,324],[73,232],[74,360],[76,456],[77,240],[78,368],[79,464],[85,330],[86,642],[90,338],[91,660],[93,708],[96,642],[96,648],[98,642],[98,648],[101,736],[104,660],[105,360],[106,368],[107,688]],\"owners\":[[10,193,[62,67,73,76,77,79],[42,49,54,56]],[54,193,[62,73,76],[10,42,49,56,67,77,79]],[56,193,[62,67,76,79],[10,42,49,54,73,77]],[42,194,[97,99,101],[10,49,54,56,84,89,93]],[49,194,[89,93,99,101],[10,42,54,56,84,97]],[17,321,[50,55,74,76,78,79],[43,63,68,69]],[43,321,[74,76,78,79],[17,50,55,63,68,69]],[63,321,[55,78,79],[17,43,50,68,69,74,76]],[68,321,[50,74,76],[17,43,55,63,69,78,79]],[69,321,[50,55,76,79],[17,43,63,68,74,78]],[17,324,[85,90,105,106],[43,63,68,69]],[43,324,[105,106],[17,63,68,69,85,90]],[63,324,[90,106],[17,43,68,69,85,105]],[68,324,[85,105],[17,43,63,69,90,106]],[69,324,[85,90],[17,43,63,68,105,106]],[30,642,[44,57,91,93,100,101],[51,86,96,98]],[51,642,[91,93,100,101],[30,44,57,86,96,98]],[86,642,[57,100,101],[30,44,51,91,93,96,98]],[96,642,[44,57,93,101],[30,51,86,91,98,100]],[98,642,[44,91,93],[30,51,57,86,96,100,101]],[30,648,[64,75,104,107],[51,86,96,98]],[51,648,[104,107],[30,64,75,86,96,98]],[96,648,[64,75],[30,51,86,98,104,107]],[98,648,[64,104],[30,51,75,86,96,107]],[44,645,[64],[]],[64,645,[44],[]],[50,330,[85],[]],[85,330,[50],[]],[55,338,[90],[]],[90,338,[55],[]],[57,673,[75],[]],[67,212,[89],[]],[73,232,[97],[]],[74,360,[105],[]],[105,360,[74],[]],[76,456,[],[]],[77,240,[99],[]],[78,368,[106],[]],[106,368,[78],[]],[79,464,[],[]],[91,660,[104],[]],[104,660,[91],[]],[93,708,[],[]],[107,688,[100],[]],[101,736,[],[]]],\"edges\":[[39,[10,42,49,54,56,62,67,73,76,77,79,84,89,93,97,99,101]],[40,[17,43,50,55,63,68,69,74,76,78,79,85,90,105,106]],[43,[30,44,51,57,64,75,86,91,93,96,98,100,101,104,107]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00145.record001" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00145.record001\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-40,-14],[-40,-27],[-1,14,17,20,23,24,26],[-10,14,20,23],[-12,14,17,23,26],[-4,35,37,39],[-7,30,33,37,39],[-2,8,11,21,23,25,26],[-5,21,23,25,26],[-15,11,25,26],[-18,8,21,23],[-19,8,11,23,26],[-2,28,31,41,42],[-5,41,42],[-15,31,42],[-18,28,41],[-19,28,31],[-3,6,13,32,33,38,39],[-9,32,33,38,39],[-29,13,38,39],[-34,6,13,33,39],[-36,6,32,33],[-3,16,22,40,43],[-9,40,43],[-34,16,22],[-36,16,40],[-6,16],[-16,6],[-8,28],[-28,8],[-11,31],[-31,11],[-13,22],[-17,30],[-20,35],[-21,41],[-41,21],[-23],[-24,37],[-25,42],[-42,25],[-26],[-32,40],[-40,32],[-33],[-43,38],[-39],[-6,44],[-32,44],[-8,45],[-21,45],[-16,46],[-11,47],[-25,47],[-30,47],[-28,48],[-31,48],[-22,49],[-35,49],[-37,49],[-38,49],[-41,50],[-42,50],[-45,51],[-44,51],[-47,52],[-46,52],[-52,53],[-51,53],[-51,-52,54],[-49,55],[-48,55],[-48,-49,56],[-50,57],[-57,58],[-55,58],[-55,-57,59],[-56,59],[-53,-59,60],[-54,-58,60],[-60],[1,4,7,10,12,14,17,20,23,24,26,27,30,33,35,37,39],[2,5,8,11,15,18,19,21,23,25,26,28,31,41,42],[3,6,9,13,16,22,29,32,33,34,36,38,39,40,43]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":104,\"b\":62},{\"tag\":\"incompatible\",\"a\":104,\"b\":84},{\"tag\":\"mate\",\"ridge\":193,\"a\":10,\"owners\":[62,67,73,76,77,79]},{\"tag\":\"mate\",\"ridge\":193,\"a\":54,\"owners\":[62,73,76]},{\"tag\":\"mate\",\"ridge\":193,\"a\":56,\"owners\":[62,67,76,79]},{\"tag\":\"mate\",\"ridge\":194,\"a\":42,\"owners\":[97,99,101]},{\"tag\":\"mate\",\"ridge\":194,\"a\":49,\"owners\":[89,93,99,101]},{\"tag\":\"mate\",\"ridge\":321,\"a\":17,\"owners\":[50,55,74,76,78,79]},{\"tag\":\"mate\",\"ridge\":321,\"a\":43,\"owners\":[74,76,78,79]},{\"tag\":\"mate\",\"ridge\":321,\"a\":63,\"owners\":[55,78,79]},{\"tag\":\"mate\",\"ridge\":321,\"a\":68,\"owners\":[50,74,76]},{\"tag\":\"mate\",\"ridge\":321,\"a\":69,\"owners\":[50,55,76,79]},{\"tag\":\"mate\",\"ridge\":324,\"a\":17,\"owners\":[85,90,105,106]},{\"tag\":\"mate\",\"ridge\":324,\"a\":43,\"owners\":[105,106]},{\"tag\":\"mate\",\"ridge\":324,\"a\":63,\"owners\":[90,106]},{\"tag\":\"mate\",\"ridge\":324,\"a\":68,\"owners\":[85,105]},{\"tag\":\"mate\",\"ridge\":324,\"a\":69,\"owners\":[85,90]},{\"tag\":\"mate\",\"ridge\":642,\"a\":30,\"owners\":[44,57,91,93,100,101]},{\"tag\":\"mate\",\"ridge\":642,\"a\":51,\"owners\":[91,93,100,101]},{\"tag\":\"mate\",\"ridge\":642,\"a\":86,\"owners\":[57,100,101]},{\"tag\":\"mate\",\"ridge\":642,\"a\":96,\"owners\":[44,57,93,101]},{\"tag\":\"mate\",\"ridge\":642,\"a\":98,\"owners\":[44,91,93]},{\"tag\":\"mate\",\"ridge\":648,\"a\":30,\"owners\":[64,75,104,107]},{\"tag\":\"mate\",\"ridge\":648,\"a\":51,\"owners\":[104,107]},{\"tag\":\"mate\",\"ridge\":648,\"a\":96,\"owners\":[64,75]},{\"tag\":\"mate\",\"ridge\":648,\"a\":98,\"owners\":[64,104]},{\"tag\":\"mate\",\"ridge\":645,\"a\":44,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":645,\"a\":64,\"owners\":[44]},{\"tag\":\"mate\",\"ridge\":330,\"a\":50,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":330,\"a\":85,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":338,\"a\":55,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":338,\"a\":90,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":673,\"a\":57,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":212,\"a\":67,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":232,\"a\":73,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":360,\"a\":74,\"owners\":[105]},{\"tag\":\"mate\",\"ridge\":360,\"a\":105,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":456,\"a\":76,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":240,\"a\":77,\"owners\":[99]},{\"tag\":\"mate\",\"ridge\":368,\"a\":78,\"owners\":[106]},{\"tag\":\"mate\",\"ridge\":368,\"a\":106,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":464,\"a\":79,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":660,\"a\":91,\"owners\":[104]},{\"tag\":\"mate\",\"ridge\":660,\"a\":104,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":708,\"a\":93,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":688,\"a\":107,\"owners\":[100]},{\"tag\":\"mate\",\"ridge\":736,\"a\":101,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":44,\"full_literals\":[-6,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":91,\"full_literals\":[-32,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":50,\"full_literals\":[-8,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":74,\"full_literals\":[-21,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":64,\"full_literals\":[-16,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":55,\"full_literals\":[-11,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":78,\"full_literals\":[-25,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":89,\"full_literals\":[-30,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":85,\"full_literals\":[-28,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":90,\"full_literals\":[-31,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":75,\"full_literals\":[-22,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":97,\"full_literals\":[-35,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":99,\"full_literals\":[-37,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":100,\"full_literals\":[-38,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":105,\"full_literals\":[-41,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":106,\"full_literals\":[-42,50]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-45,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-47,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-52,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-51,false,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-51,-52,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-49,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-48,false,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-48,-49,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-50,false,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-57,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-55,false,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-55,-57,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-56,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-53,-59,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-54,-58,60],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":39,\"owners\":[10,42,49,54,56,62,67,73,76,77,79,84,89,93,97,99,101]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[17,43,50,55,63,68,69,74,76,78,79,85,90,105,106]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[30,44,51,57,64,75,86,91,93,96,98,100,101,104,107]}]}"
  "p cnf 60 84\n-40 -14 0\n-40 -27 0\n-1 14 17 20 23 24 26 0\n-10 14 20 23 0\n-12 14 17 23 26 0\n-4 35 37 39 0\n-7 30 33 37 39 0\n-2 8 11 21 23 25 26 0\n-5 21 23 25 26 0\n-15 11 25 26 0\n-18 8 21 23 0\n-19 8 11 23 26 0\n-2 28 31 41 42 0\n-5 41 42 0\n-15 31 42 0\n-18 28 41 0\n-19 28 31 0\n-3 6 13 32 33 38 39 0\n-9 32 33 38 39 0\n-29 13 38 39 0\n-34 6 13 33 39 0\n-36 6 32 33 0\n-3 16 22 40 43 0\n-9 40 43 0\n-34 16 22 0\n-36 16 40 0\n-6 16 0\n-16 6 0\n-8 28 0\n-28 8 0\n-11 31 0\n-31 11 0\n-13 22 0\n-17 30 0\n-20 35 0\n-21 41 0\n-41 21 0\n-23 0\n-24 37 0\n-25 42 0\n-42 25 0\n-26 0\n-32 40 0\n-40 32 0\n-33 0\n-43 38 0\n-39 0\n-6 44 0\n-32 44 0\n-8 45 0\n-21 45 0\n-16 46 0\n-11 47 0\n-25 47 0\n-30 47 0\n-28 48 0\n-31 48 0\n-22 49 0\n-35 49 0\n-37 49 0\n-38 49 0\n-41 50 0\n-42 50 0\n-45 51 0\n-44 51 0\n-47 52 0\n-46 52 0\n-52 53 0\n-51 53 0\n-51 -52 54 0\n-49 55 0\n-48 55 0\n-48 -49 56 0\n-50 57 0\n-57 58 0\n-55 58 0\n-55 -57 59 0\n-56 59 0\n-53 -59 60 0\n-54 -58 60 0\n-60 0\n1 4 7 10 12 14 17 20 23 24 26 27 30 33 35 37 39 0\n2 5 8 11 15 18 19 21 23 25 26 28 31 41 42 0\n3 6 9 13 16 22 29 32 33 34 36 38 39 40 43 0\n"
  "85 1 4 7 10 12 14 17 20 24 27 30 35 37 0 38 42 45 47 82 0\n86 2 5 8 11 15 18 19 21 25 28 31 41 42 0 38 42 83 0\n87 3 6 9 13 16 22 29 32 34 36 38 40 43 0 45 47 84 0\n88 53 0 42 38 68 69 66 64 53 54 50 51 32 12 41 10 9 30 37 8 11 86 0\n89 -59 0 88 81 79 0\n90 -56 0 89 78 0\n91 -40 30 49 0 45 47 42 38 60 7 34 39 59 35 6 1 2 3 5 4 85 0\n92 52 49 0 47 58 33 61 20 46 66 67 55 52 27 25 91 24 43 26 23 87 0\n93 49 54 0 47 45 58 61 33 46 20 92 70 65 48 49 28 21 44 22 19 18 87 0\n94 -49 0 90 89 71 73 77 56 57 74 29 31 17 62 63 36 13 16 14 40 15 86 0\n95 54 0 94 93 0\n96 -58 0 95 81 80 0\n97 -57 0 96 75 0\n98 -55 0 96 76 0\n99 -50 0 97 74 0\n100 -48 0 98 72 0\n101 -41 0 99 62 0\n102 -42 0 99 63 0\n103 -28 0 100 56 0\n104 -31 0 100 57 0\n105 -21 0 101 36 0\n106 -2 0 101 104 103 102 13 0\n107 -18 0 101 103 16 0\n108 -5 0 101 102 14 0\n109 -25 0 102 40 0\n110 -15 0 102 104 15 0\n111 -8 0 103 29 0\n112 -11 0 104 31 0\n113 -19 0 104 103 17 0\n114 0 107 110 108 112 106 111 113 105 109 103 104 101 102 86 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record001.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record001.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record001.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record001.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record001 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record001.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record001.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record001.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record001.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record001 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record001_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record001 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record001_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record001_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00145.record001
