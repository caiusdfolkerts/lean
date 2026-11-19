module
prelude
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow26Part00074Frames
public import GraphInputsRow26Part00074Leaves
public import GraphInputsRow26Part00074Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00074.record017
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "19c570dc1f2726687a999964d8b61d98e9386e4789e1783e9c599564d91e595554d54d4b51d58d9354d3346d4749d1743d98d9394e334ccb31cd8b92c6b16c3bc1e8761e4749ca719d1725c570de0f13c2f07e644689a8990e23a611c51926459916251950d2344d88d1324c3342c8b06e0741c8709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6d34db69b49b4924db6d249249349a4926d24924924d2491249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record017 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record017 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record017.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 31), (facetIndex 37), (facetIndex 40), (facetIndex 45), (facetIndex 49), (facetIndex 55), (facetIndex 87)]))
 (.branch 2
 (.leaf ([(facetIndex 60), (facetIndex 65), (facetIndex 71), (facetIndex 75)]))
 (.leaf ([(facetIndex 32), (facetIndex 61), (facetIndex 62), (facetIndex 63), (facetIndex 64)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 29), (facetIndex 57), (facetIndex 58), (facetIndex 59), (facetIndex 72), (facetIndex 73), (facetIndex 74)]))
 (.leaf ([(facetIndex 33), (facetIndex 44), (facetIndex 50), (facetIndex 51), (facetIndex 52), (facetIndex 54)])))
 (.branch 6
 (.leaf ([(facetIndex 48), (facetIndex 78), (facetIndex 79), (facetIndex 82), (facetIndex 89)]))
 (.leaf ([(facetIndex 30), (facetIndex 35), (facetIndex 36), (facetIndex 38), (facetIndex 39), (facetIndex 41), (facetIndex 42), (facetIndex 43)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "28000140b402db20000a4916d8104905004db0d86c22198z15;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 34), (facetIndex 46), (facetIndex 47), (facetIndex 53)]))
 (.branch 2
 (.leaf ([(facetIndex 77), (facetIndex 80), (facetIndex 81), (facetIndex 90)]))
 (.leaf ([(facetIndex 56), (facetIndex 66), (facetIndex 67), (facetIndex 68), (facetIndex 69), (facetIndex 70), (facetIndex 83)]))))
 (.branch 4
 (.leaf ([(facetIndex 76), (facetIndex 84), (facetIndex 85), (facetIndex 86), (facetIndex 92), (facetIndex 93)]))
 (.branch 5
 (.leaf ([(facetIndex 91), (facetIndex 94)]))
 (.leaf ([(facetIndex 88)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "11b8450db40900b000092480000002z2a;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1, 2]
def grouped2_0003 : List Nat := [1]
def grouped2_0004 : List Nat := [1, 2]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [3, 4]
def grouped2_0007 : List Nat := [3, 4, 5, 6]
def grouped2_0008 : List Nat := [5]
def grouped2_0009 : List Nat := [5, 6]
def grouped2_0010 : List Nat := [6]
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1, 2]
def grouped3_0014 : List Nat := [1]
def grouped3_0015 : List Nat := [1, 2]
def grouped3_0016 : List Nat := [2]
def grouped3_0017 : List Nat := [3]
def grouped3_0018 : List Nat := [3, 4, 5]
def grouped3_0019 : List Nat := [4]
def grouped3_0020 : List Nat := [4, 5]
def grouped3_0021 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record017 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record017_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00074.record017" "{\"atoms\":[{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":4,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00074.record017" 50

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00074.record017" "{\"ridges\":[[46,106],[47,586],[53,594],[60,76],[65,112],[71,88],[77,86],[92,212],[93,340]],\"owners\":[[60,76,[77,81,92,93],[12,31,57,61,62,63,80,91]],[71,88,[77,92,93],[18,45,57,72,73,88,91]],[65,112,[88,90],[21,49,71,75,83,91]],[77,86,[34,83],[]],[46,106,[80,88],[]],[47,586,[81],[]],[53,594,[90],[]],[92,212,[68],[]],[93,340,[69],[]]],\"edges\":[],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00074.record017" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00074.record017\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-3,-1],[-4,-3],[-5,-3],[-7,-3],[-8,-3],[-10,-3],[-11,-3],[-12,-3],[-24,-14],[-25,-2],[-25,-6],[-25,-9],[-25,-13],[-25,-16],[-25,-18],[-26,-2],[-26,-6],[-26,-9],[-26,-13],[-26,-16],[-26,-18],[-27,-2],[-27,-6],[-27,-9],[-27,-13],[-27,-16],[-27,-18],[-29,-25],[-29,-26],[-29,-27],[-30,-2],[-30,-6],[-30,-9],[-30,-13],[-30,-16],[-30,-18],[-30,-29],[-31,-2],[-31,-6],[-31,-9],[-31,-13],[-31,-16],[-31,-18],[-31,-29],[-19,25,27,32,33],[-23,25,32,33],[-20,30,31],[-25,3,28],[-14,26,30],[-15,27],[-17,31],[-32,21],[-33,22],[-34,2,6,9,13,16,18,29],[-35,19,20,23,24],[-36,1,4,5,7,8,10,11,12],[-37,35],[-38,34],[-38,37],[-39,36],[-40,39],[-41,38],[-41,40],[41],[-42,3,14,15,17],[-43,25,26,27,31],[-26,43],[-27,43],[-31,43],[-21,44],[-22,44],[-28,44],[-45,30],[-46,43],[-43,-44,46],[-47,42,46],[-48,45],[-49,48],[-50,47,49],[50]],\"atoms\":[{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":34,\"b\":30},{\"tag\":\"incompatible\",\"a\":35,\"b\":34},{\"tag\":\"incompatible\",\"a\":36,\"b\":34},{\"tag\":\"incompatible\",\"a\":38,\"b\":34},{\"tag\":\"incompatible\",\"a\":39,\"b\":34},{\"tag\":\"incompatible\",\"a\":41,\"b\":34},{\"tag\":\"incompatible\",\"a\":42,\"b\":34},{\"tag\":\"incompatible\",\"a\":43,\"b\":34},{\"tag\":\"incompatible\",\"a\":75,\"b\":46},{\"tag\":\"incompatible\",\"a\":77,\"b\":31},{\"tag\":\"incompatible\",\"a\":77,\"b\":37},{\"tag\":\"incompatible\",\"a\":77,\"b\":40},{\"tag\":\"incompatible\",\"a\":77,\"b\":45},{\"tag\":\"incompatible\",\"a\":77,\"b\":49},{\"tag\":\"incompatible\",\"a\":77,\"b\":55},{\"tag\":\"incompatible\",\"a\":80,\"b\":31},{\"tag\":\"incompatible\",\"a\":80,\"b\":37},{\"tag\":\"incompatible\",\"a\":80,\"b\":40},{\"tag\":\"incompatible\",\"a\":80,\"b\":45},{\"tag\":\"incompatible\",\"a\":80,\"b\":49},{\"tag\":\"incompatible\",\"a\":80,\"b\":55},{\"tag\":\"incompatible\",\"a\":81,\"b\":31},{\"tag\":\"incompatible\",\"a\":81,\"b\":37},{\"tag\":\"incompatible\",\"a\":81,\"b\":40},{\"tag\":\"incompatible\",\"a\":81,\"b\":45},{\"tag\":\"incompatible\",\"a\":81,\"b\":49},{\"tag\":\"incompatible\",\"a\":81,\"b\":55},{\"tag\":\"incompatible\",\"a\":87,\"b\":77},{\"tag\":\"incompatible\",\"a\":87,\"b\":80},{\"tag\":\"incompatible\",\"a\":87,\"b\":81},{\"tag\":\"incompatible\",\"a\":88,\"b\":31},{\"tag\":\"incompatible\",\"a\":88,\"b\":37},{\"tag\":\"incompatible\",\"a\":88,\"b\":40},{\"tag\":\"incompatible\",\"a\":88,\"b\":45},{\"tag\":\"incompatible\",\"a\":88,\"b\":49},{\"tag\":\"incompatible\",\"a\":88,\"b\":55},{\"tag\":\"incompatible\",\"a\":88,\"b\":87},{\"tag\":\"incompatible\",\"a\":90,\"b\":31},{\"tag\":\"incompatible\",\"a\":90,\"b\":37},{\"tag\":\"incompatible\",\"a\":90,\"b\":40},{\"tag\":\"incompatible\",\"a\":90,\"b\":45},{\"tag\":\"incompatible\",\"a\":90,\"b\":49},{\"tag\":\"incompatible\",\"a\":90,\"b\":55},{\"tag\":\"incompatible\",\"a\":90,\"b\":87},{\"tag\":\"mate\",\"ridge\":76,\"a\":60,\"owners\":[77,81,92,93]},{\"tag\":\"mate\",\"ridge\":88,\"a\":71,\"owners\":[77,92,93]},{\"tag\":\"mate\",\"ridge\":112,\"a\":65,\"owners\":[88,90]},{\"tag\":\"mate\",\"ridge\":86,\"a\":77,\"owners\":[34,83]},{\"tag\":\"mate\",\"ridge\":106,\"a\":46,\"owners\":[80,88]},{\"tag\":\"mate\",\"ridge\":586,\"a\":47,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":594,\"a\":53,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":212,\"a\":92,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":340,\"a\":93,\"owners\":[69]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[31,37,40,45,49,55,87],\"full_literals\":[-34,2,6,9,13,16,18,29]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[60,65,71,75],\"full_literals\":[-35,19,20,23,24]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[30,35,36,38,39,41,42,43],\"full_literals\":[-36,1,4,5,7,8,10,11,12]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-37,35,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-38,34,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-38,false,37],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-39,false,36],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-40,false,39],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-41,38,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-41,false,40],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[34,46,47,53],\"full_literals\":[-42,3,14,15,17]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[77,80,81,90],\"full_literals\":[-43,25,26,27,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":80,\"full_literals\":[-26,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":81,\"full_literals\":[-27,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":90,\"full_literals\":[-31,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":68,\"full_literals\":[-21,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":69,\"full_literals\":[-22,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":83,\"full_literals\":[-28,44]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[88],\"full_literals\":[-45,30]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-46,43,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-43,-44,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-47,42,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-48,false,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-49,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-50,47,49],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":4,\"grouped\":true}]}"
  "81 38 0 64 62 0\n82 40 0 64 63 0\n83 34 0 81 58 0\n84 37 0 81 59 0\n85 39 0 82 61 0\n86 35 0 84 57 0\n87 36 0 85 60 0\n88 -30 0 83 31 32 33 34 35 36 37 54 0\n89 -45 0 88 73 0\n90 -48 0 89 77 0\n91 -49 0 90 78 0\n92 47 0 91 80 79 0\n93 -3 0 87 1 2 3 4 5 6 7 8 56 0\n94 43 -42 0 88 93 67 68 69 49 50 51 65 0\n95 27 31 46 0 92 88 93 86 47 51 76 94 75 71 53 72 48 70 52 46 50 45 65 55 9 0\n96 -27 0 83 22 23 24 25 26 27 30 54 0\n97 -31 0 83 38 39 40 41 42 43 44 54 0\n98 46 0 97 96 95 0\n99 43 0 98 74 0\n100 -25 0 83 10 11 12 13 14 15 28 54 0\n101 26 0 100 97 99 96 66 0\n102 -2 0 101 16 0\n103 -6 0 101 17 0\n104 -9 0 101 18 0\n105 -13 0 101 19 0\n106 -16 0 101 20 0\n107 -18 0 101 21 0\n108 -29 0 101 29 0\n109 0 107 108 83 102 103 104 105 106 54 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record017.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record017.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record017.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record017.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record017 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record017.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record017.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record017.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record017.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record017 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record017_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record017_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record017_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record017_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record017_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record017_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record017_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record017 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record017_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record017_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record017_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00074.record017
