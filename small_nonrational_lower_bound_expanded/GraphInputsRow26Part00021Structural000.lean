module
prelude
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow26Part00021Frames
public import GraphInputsRow26Part00021Leaves
public import GraphInputsRow26Part00021Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00021.record074
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3626c9aa66b26998e6c58d64d8b6c38ce4b8ae4789ed85b16a599c966539715355352d70d3352d2b51d27743b0f2368e6358f1364cd34ccb3c2d8b32d2b2af0731e2749ca785d1725c570de0f43c8f13c2f3891a26a461981e38519266451941dc0e4330d2328c6344c9342c8b06e0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36d349b6db6d26da6936db6da492492492492492492492492249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record074 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record074 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record074.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 46), (facetIndex 51), (facetIndex 55), (facetIndex 72), (facetIndex 89)]))
 (.branch 2
 (.leaf ([(facetIndex 31), (facetIndex 36), (facetIndex 39), (facetIndex 42), (facetIndex 60), (facetIndex 77)]))
 (.leaf ([(facetIndex 40), (facetIndex 54), (facetIndex 56), (facetIndex 70), (facetIndex 87)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 30), (facetIndex 35), (facetIndex 38), (facetIndex 41), (facetIndex 59), (facetIndex 69), (facetIndex 76), (facetIndex 86)]))
 (.leaf ([(facetIndex 43), (facetIndex 45), (facetIndex 48), (facetIndex 50), (facetIndex 57)])))
 (.branch 6
 (.leaf ([(facetIndex 44), (facetIndex 47), (facetIndex 49), (facetIndex 52), (facetIndex 53), (facetIndex 58)]))
 (.leaf ([(facetIndex 28), (facetIndex 29), (facetIndex 32), (facetIndex 33), (facetIndex 34), (facetIndex 37)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "4c000000b0000980000017620ad12ca2585a2f17b62f6z15;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 71), (facetIndex 75)]))
 (.leaf ([(facetIndex 88), (facetIndex 92)])))
 (.branch 3
 (.leaf ([(facetIndex 61), (facetIndex 63), (facetIndex 65), (facetIndex 67)]))
 (.leaf ([(facetIndex 73), (facetIndex 74)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 78), (facetIndex 80), (facetIndex 82), (facetIndex 84)]))
 (.leaf ([(facetIndex 90), (facetIndex 91)])))
 (.branch 7
 (.leaf ([(facetIndex 62), (facetIndex 64), (facetIndex 66), (facetIndex 68)]))
 (.leaf ([(facetIndex 79), (facetIndex 81), (facetIndex 83), (facetIndex 85)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b4103cf3cf000d800659659z2e;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1, 2]
def grouped2_0003 : List Nat := [1]
def grouped2_0004 : List Nat := [1, 2]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [3]
def grouped2_0007 : List Nat := [3, 4]
def grouped2_0008 : List Nat := [3, 4, 5, 6]
def grouped2_0009 : List Nat := [4]
def grouped2_0010 : List Nat := [5, 6]
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1]
def grouped3_0013 : List Nat := [0, 1, 2, 3]
def grouped3_0015 : List Nat := [1]
def grouped3_0016 : List Nat := [2]
def grouped3_0017 : List Nat := [2, 3]
def grouped3_0018 : List Nat := [3]
def grouped3_0019 : List Nat := [4]
def grouped3_0020 : List Nat := [4, 5]
def grouped3_0021 : List Nat := [4, 5, 6, 7]
def grouped3_0022 : List Nat := [5]
def grouped3_0023 : List Nat := [6, 7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record074 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record074_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00021.record074" "{\"atoms\":[{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":4,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00021.record074" 51

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00021.record074" "{\"ridges\":[[61,172],[63,204],[65,180],[67,212],[73,424],[74,432]],\"owners\":[[61,172,[78],[]],[63,204,[80],[]],[65,180,[82],[]],[67,212,[84],[]],[73,424,[90],[]],[74,432,[91],[]]],\"edges\":[],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00021.record074" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00021.record074\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-18,-4],[-18,-8],[-18,-10],[-18,-17],[-22,-4],[-22,-8],[-22,-10],[-22,-17],[-24,-1],[-24,-2],[-24,-3],[-24,-5],[-24,-11],[-24,-16],[-24,-23],[-25,-1],[-25,-2],[-25,-3],[-25,-5],[-25,-11],[-25,-16],[-25,-23],[-26,-1],[-26,-2],[-26,-3],[-26,-5],[-26,-11],[-26,-16],[-26,-23],[-27,-1],[-27,-2],[-27,-3],[-27,-5],[-27,-11],[-27,-16],[-27,-23],[-28,-24],[-28,-25],[-28,-26],[-28,-27],[-29,-18],[-29,-22],[-31,-6],[-31,-7],[-31,-9],[-31,-19],[-31,-30],[-32,-6],[-32,-7],[-32,-9],[-32,-19],[-32,-30],[-12,24],[-13,25],[-14,26],[-15,27],[-20,31],[-21,32],[-33,6,7,9,19,30],[-34,4,8,10,17,29],[-35,1,2,3,5,11,16,23,28],[-36,34],[-37,33],[-37,36],[-38,35],[-39,38],[-40,37],[-40,39],[40],[-41,18,22],[-42,12,13,14,15],[-43,20,21],[-44,24,25,26,27],[-45,31,32],[-46,41],[-47,42,43],[-48,46,47],[-49,44,45],[-50,49],[-51,48,50],[51]],\"atoms\":[{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":71,\"b\":40},{\"tag\":\"incompatible\",\"a\":71,\"b\":54},{\"tag\":\"incompatible\",\"a\":71,\"b\":56},{\"tag\":\"incompatible\",\"a\":71,\"b\":70},{\"tag\":\"incompatible\",\"a\":75,\"b\":40},{\"tag\":\"incompatible\",\"a\":75,\"b\":54},{\"tag\":\"incompatible\",\"a\":75,\"b\":56},{\"tag\":\"incompatible\",\"a\":75,\"b\":70},{\"tag\":\"incompatible\",\"a\":78,\"b\":30},{\"tag\":\"incompatible\",\"a\":78,\"b\":35},{\"tag\":\"incompatible\",\"a\":78,\"b\":38},{\"tag\":\"incompatible\",\"a\":78,\"b\":41},{\"tag\":\"incompatible\",\"a\":78,\"b\":59},{\"tag\":\"incompatible\",\"a\":78,\"b\":69},{\"tag\":\"incompatible\",\"a\":78,\"b\":76},{\"tag\":\"incompatible\",\"a\":80,\"b\":30},{\"tag\":\"incompatible\",\"a\":80,\"b\":35},{\"tag\":\"incompatible\",\"a\":80,\"b\":38},{\"tag\":\"incompatible\",\"a\":80,\"b\":41},{\"tag\":\"incompatible\",\"a\":80,\"b\":59},{\"tag\":\"incompatible\",\"a\":80,\"b\":69},{\"tag\":\"incompatible\",\"a\":80,\"b\":76},{\"tag\":\"incompatible\",\"a\":82,\"b\":30},{\"tag\":\"incompatible\",\"a\":82,\"b\":35},{\"tag\":\"incompatible\",\"a\":82,\"b\":38},{\"tag\":\"incompatible\",\"a\":82,\"b\":41},{\"tag\":\"incompatible\",\"a\":82,\"b\":59},{\"tag\":\"incompatible\",\"a\":82,\"b\":69},{\"tag\":\"incompatible\",\"a\":82,\"b\":76},{\"tag\":\"incompatible\",\"a\":84,\"b\":30},{\"tag\":\"incompatible\",\"a\":84,\"b\":35},{\"tag\":\"incompatible\",\"a\":84,\"b\":38},{\"tag\":\"incompatible\",\"a\":84,\"b\":41},{\"tag\":\"incompatible\",\"a\":84,\"b\":59},{\"tag\":\"incompatible\",\"a\":84,\"b\":69},{\"tag\":\"incompatible\",\"a\":84,\"b\":76},{\"tag\":\"incompatible\",\"a\":86,\"b\":78},{\"tag\":\"incompatible\",\"a\":86,\"b\":80},{\"tag\":\"incompatible\",\"a\":86,\"b\":82},{\"tag\":\"incompatible\",\"a\":86,\"b\":84},{\"tag\":\"incompatible\",\"a\":87,\"b\":71},{\"tag\":\"incompatible\",\"a\":87,\"b\":75},{\"tag\":\"incompatible\",\"a\":90,\"b\":46},{\"tag\":\"incompatible\",\"a\":90,\"b\":51},{\"tag\":\"incompatible\",\"a\":90,\"b\":55},{\"tag\":\"incompatible\",\"a\":90,\"b\":72},{\"tag\":\"incompatible\",\"a\":90,\"b\":89},{\"tag\":\"incompatible\",\"a\":91,\"b\":46},{\"tag\":\"incompatible\",\"a\":91,\"b\":51},{\"tag\":\"incompatible\",\"a\":91,\"b\":55},{\"tag\":\"incompatible\",\"a\":91,\"b\":72},{\"tag\":\"incompatible\",\"a\":91,\"b\":89},{\"tag\":\"mate\",\"ridge\":172,\"a\":61,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":204,\"a\":63,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":180,\"a\":65,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":212,\"a\":67,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":424,\"a\":73,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":432,\"a\":74,\"owners\":[91]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[46,51,55,72,89],\"full_literals\":[-33,6,7,9,19,30]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[40,54,56,70,87],\"full_literals\":[-34,4,8,10,17,29]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[30,35,38,41,59,69,76,86],\"full_literals\":[-35,1,2,3,5,11,16,23,28]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-36,false,34],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-37,33,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-37,false,36],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-38,35,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-39,38,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-40,37,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-40,false,39],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[71,75],\"full_literals\":[-41,18,22]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[61,63,65,67],\"full_literals\":[-42,12,13,14,15]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[73,74],\"full_literals\":[-43,20,21]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[78,80,82,84],\"full_literals\":[-44,24,25,26,27]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[90,91],\"full_literals\":[-45,31,32]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-46,41,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-47,42,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-48,46,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-49,44,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-50,49,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-51,48,50],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":4,\"grouped\":true}]}"
  "82 37 0 69 67 0\n83 39 0 69 68 0\n84 33 0 82 63 0\n85 36 0 82 64 0\n86 38 0 83 66 0\n87 34 0 85 62 0\n88 35 0 86 65 0\n89 -24 0 88 9 10 11 12 13 14 15 37 61 0\n90 -12 0 89 53 0\n91 -25 0 88 16 17 18 19 20 21 22 38 61 0\n92 -13 0 91 54 0\n93 -26 0 88 23 24 25 26 27 28 29 39 61 0\n94 -14 0 93 55 0\n95 -27 0 88 30 31 32 33 34 35 36 40 61 0\n96 -15 0 95 56 0\n97 -44 0 95 89 91 93 73 0\n98 -42 0 96 90 92 94 71 0\n99 -31 0 84 43 44 45 46 47 59 0\n100 -20 0 99 57 0\n101 -32 0 84 48 49 50 51 52 59 0\n102 -21 0 101 58 0\n103 -45 0 101 99 74 0\n104 -43 0 102 100 72 0\n105 -49 0 103 97 78 0\n106 -47 0 104 98 76 0\n107 -50 0 105 79 0\n108 48 0 107 81 80 0\n109 46 0 108 106 77 0\n110 41 0 109 75 0\n111 -17 0 110 4 8 70 0\n112 -18 29 0 111 87 1 2 3 60 0\n113 29 0 110 111 87 112 70 5 6 7 60 0\n114 -18 0 113 41 0\n115 -22 0 113 42 0\n116 0 114 115 110 70 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record074.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record074.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record074.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record074.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record074 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record074.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record074.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record074.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record074.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record074 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record074_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record074_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record074_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record074_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record074_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record074_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record074_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record074 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record074_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record074_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record074_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00021.record074
