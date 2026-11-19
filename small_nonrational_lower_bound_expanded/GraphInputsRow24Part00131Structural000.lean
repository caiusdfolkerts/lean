module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00131Frames
public import GraphInputsRow24Part00131Leaves
public import GraphInputsRow24Part00131Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record003
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "15c56a3a99a5655a366394e4b91e2785e0f9598e665955558d58d5352d4749d1743dd0ea398d538cd8b52e2b4ae1b46c9b16c3b61e4731e2749c6785d1725c3713cac948aa518a61590e2382e07a512a545294554348d0b41d90d4388ca384c5342c8b0ac1b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6934924936d2692492492492492492492492449249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record003 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record003 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record003.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 39), (facetIndex 42), (facetIndex 44), (facetIndex 69), (facetIndex 82)]))
 (.leaf ([(facetIndex 52), (facetIndex 55), (facetIndex 57), (facetIndex 58)])))
 (.branch 3
 (.leaf ([(facetIndex 35), (facetIndex 47), (facetIndex 53), (facetIndex 56), (facetIndex 59)]))
 (.leaf ([(facetIndex 60), (facetIndex 61), (facetIndex 62), (facetIndex 63), (facetIndex 64), (facetIndex 65), (facetIndex 66)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 73), (facetIndex 74), (facetIndex 75), (facetIndex 76), (facetIndex 77), (facetIndex 78), (facetIndex 79)]))
 (.leaf ([(facetIndex 46), (facetIndex 48), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 54)])))
 (.branch 7
 (.leaf ([(facetIndex 38), (facetIndex 40), (facetIndex 43), (facetIndex 68), (facetIndex 81)]))
 (.leaf ([(facetIndex 36), (facetIndex 37), (facetIndex 41), (facetIndex 45)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "309249200060db6db44a351b6d578c3e1bf4z1a;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 72)]))
 (.branch 2
 (.leaf ([(facetIndex 85)]))
 (.leaf ([(facetIndex 86)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 67), (facetIndex 70)]))
 (.leaf ([(facetIndex 71), (facetIndex 80)])))
 (.branch 6
 (.leaf ([(facetIndex 83)]))
 (.leaf ([(facetIndex 84)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "8ea040000008c06z32;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
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
def grouped3_0016 : List Nat := [0, 1, 2]
def grouped3_0018 : List Nat := [1]
def grouped3_0019 : List Nat := [1, 2]
def grouped3_0020 : List Nat := [2]
def grouped3_0021 : List Nat := [3]
def grouped3_0022 : List Nat := [3, 4]
def grouped3_0023 : List Nat := [3, 4, 5, 6]
def grouped3_0024 : List Nat := [4]
def grouped3_0025 : List Nat := [5]
def grouped3_0026 : List Nat := [5, 6]
def grouped3_0027 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record003 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record003_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record003" "{\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record003" 71

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record003" "{\"ridges\":[[12,35],[37,131],[41,35],[42,546],[45,259],[48,26],[48,131],[51,259],[52,545],[54,131],[55,546],[56,259],[57,35],[57,545],[58,131],[58,545],[59,259],[70,612],[71,568],[74,26],[76,26],[77,266],[84,26],[84,568]],\"owners\":[[48,131,[4,12,43,45,58],[8,37,54]],[54,131,[4,12,37,43,58],[8,45,48]],[77,266,[9,49,53,54,85],[28,51,76,78,79]],[52,545,[67,70],[13,42,55,57,58,71]],[57,545,[67,71],[13,42,52,55,58,70]],[58,545,[67,70,71],[13,42,52,55,57]],[42,546,[84],[13,52,55,57,58,80,83]],[55,546,[83],[13,42,52,57,58,80,84]],[70,612,[83],[]],[71,568,[84],[]],[84,568,[71],[]]],\"edges\":[],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record003" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record003\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-6,-4],[-10,-1],[-12,-10],[-13,-5],[-13,-6],[-13,-10],[-14,-4],[-14,-13],[-16,-6],[-17,-2],[-17,-6],[-17,-16],[-18,-4],[-18,-7],[-18,-16],[-20,-10],[-20,-16],[-22,-14],[-22,-18],[-22,-20],[-23,-14],[-23,-22],[-25,-18],[-26,-25],[-27,-10],[-27,-20],[-28,-9],[-28,-12],[-28,-26],[-29,-8],[-29,-13],[-30,-18],[-31,-29],[-36,-17],[-39,-14],[-40,-14],[-41,-18],[-42,-29],[-43,-8],[-43,-13],[-43,-31],[-43,-42],[-44,-5],[-44,-15],[-44,-19],[-44,-21],[-44,-24],[-44,-34],[-3,-10,-26],[-17,1,3,12,14,27],[-23,1,3,6,12,27],[-6,-23,-27],[-14,-20,-25],[-14,-20,-28],[-17,-35,-44],[-17,-37,-44],[-38,2,18,22,23,45],[-21,29,32],[-26,29,33],[-27,29,32,33],[-11,44],[-24,43],[-32,43],[-33,44],[-44,33],[-46,8,11,13,31,42],[-47,21,24,26,27],[-48,4,16,22,25,28],[-49,34,35,36,37,38,39,40],[-50,15,17,18,19,20,23],[-51,7,9,12,30,41],[-52,5,6,10,14],[-53,46],[-53,47],[-54,48],[-55,53],[-55,54],[-56,49],[-56,50],[-57,51],[-57,52],[-58,56],[-58,57],[-59,55],[-59,58],[59],[-45,60],[-61,29,32],[-33,62],[-63,43],[-64,44],[-44,64],[-60,65],[-65,66],[-62,67],[-68,61],[-69,63,64],[-64,69],[-70,68,69],[-67,-69,70],[-66,-70,71],[-71]],\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":37,\"b\":35},{\"tag\":\"incompatible\",\"a\":41,\"b\":4},{\"tag\":\"incompatible\",\"a\":43,\"b\":41},{\"tag\":\"incompatible\",\"a\":44,\"b\":36},{\"tag\":\"incompatible\",\"a\":44,\"b\":37},{\"tag\":\"incompatible\",\"a\":44,\"b\":41},{\"tag\":\"incompatible\",\"a\":45,\"b\":35},{\"tag\":\"incompatible\",\"a\":45,\"b\":44},{\"tag\":\"incompatible\",\"a\":47,\"b\":37},{\"tag\":\"incompatible\",\"a\":48,\"b\":9},{\"tag\":\"incompatible\",\"a\":48,\"b\":37},{\"tag\":\"incompatible\",\"a\":48,\"b\":47},{\"tag\":\"incompatible\",\"a\":49,\"b\":35},{\"tag\":\"incompatible\",\"a\":49,\"b\":38},{\"tag\":\"incompatible\",\"a\":49,\"b\":47},{\"tag\":\"incompatible\",\"a\":51,\"b\":41},{\"tag\":\"incompatible\",\"a\":51,\"b\":47},{\"tag\":\"incompatible\",\"a\":53,\"b\":45},{\"tag\":\"incompatible\",\"a\":53,\"b\":49},{\"tag\":\"incompatible\",\"a\":53,\"b\":51},{\"tag\":\"incompatible\",\"a\":54,\"b\":45},{\"tag\":\"incompatible\",\"a\":54,\"b\":53},{\"tag\":\"incompatible\",\"a\":56,\"b\":49},{\"tag\":\"incompatible\",\"a\":57,\"b\":56},{\"tag\":\"incompatible\",\"a\":58,\"b\":41},{\"tag\":\"incompatible\",\"a\":58,\"b\":51},{\"tag\":\"incompatible\",\"a\":59,\"b\":40},{\"tag\":\"incompatible\",\"a\":59,\"b\":43},{\"tag\":\"incompatible\",\"a\":59,\"b\":57},{\"tag\":\"incompatible\",\"a\":67,\"b\":39},{\"tag\":\"incompatible\",\"a\":67,\"b\":44},{\"tag\":\"incompatible\",\"a\":68,\"b\":49},{\"tag\":\"incompatible\",\"a\":69,\"b\":67},{\"tag\":\"incompatible\",\"a\":75,\"b\":48},{\"tag\":\"incompatible\",\"a\":78,\"b\":45},{\"tag\":\"incompatible\",\"a\":79,\"b\":45},{\"tag\":\"incompatible\",\"a\":81,\"b\":49},{\"tag\":\"incompatible\",\"a\":82,\"b\":67},{\"tag\":\"incompatible\",\"a\":83,\"b\":39},{\"tag\":\"incompatible\",\"a\":83,\"b\":44},{\"tag\":\"incompatible\",\"a\":83,\"b\":69},{\"tag\":\"incompatible\",\"a\":83,\"b\":82},{\"tag\":\"incompatible\",\"a\":84,\"b\":36},{\"tag\":\"incompatible\",\"a\":84,\"b\":46},{\"tag\":\"incompatible\",\"a\":84,\"b\":50},{\"tag\":\"incompatible\",\"a\":84,\"b\":52},{\"tag\":\"incompatible\",\"a\":84,\"b\":55},{\"tag\":\"incompatible\",\"a\":84,\"b\":73},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[12,41,57]},{\"tag\":\"mate\",\"ridge\":131,\"a\":48,\"owners\":[4,12,43,45,58]},{\"tag\":\"mate\",\"ridge\":131,\"a\":54,\"owners\":[4,12,37,43,58]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[37,54,58]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[45,51,56]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[45,51,59]},{\"tag\":\"three\",\"ridge\":26,\"vertices\":[48,74,84]},{\"tag\":\"three\",\"ridge\":26,\"vertices\":[48,76,84]},{\"tag\":\"mate\",\"ridge\":266,\"a\":77,\"owners\":[9,49,53,54,85]},{\"tag\":\"mate\",\"ridge\":545,\"a\":52,\"owners\":[67,70]},{\"tag\":\"mate\",\"ridge\":545,\"a\":57,\"owners\":[67,71]},{\"tag\":\"mate\",\"ridge\":545,\"a\":58,\"owners\":[67,70,71]},{\"tag\":\"mate\",\"ridge\":546,\"a\":42,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":546,\"a\":55,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":612,\"a\":70,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":568,\"a\":71,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":568,\"a\":84,\"owners\":[71]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[39,42,44,69,82],\"full_literals\":[-46,8,11,13,31,42]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[52,55,57,58],\"full_literals\":[-47,21,24,26,27]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[35,47,53,56,59],\"full_literals\":[-48,4,16,22,25,28]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[73,74,75,76,77,78,79],\"full_literals\":[-49,34,35,36,37,38,39,40]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[46,48,49,50,51,54],\"full_literals\":[-50,15,17,18,19,20,23]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[38,40,43,68,81],\"full_literals\":[-51,7,9,12,30,41]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[36,37,41,45],\"full_literals\":[-52,5,6,10,14]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-53,46,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-53,false,47],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-54,48,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-55,53,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-55,false,54],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-56,49,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-56,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-57,51,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-57,false,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-58,56,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-58,false,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-59,55,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-59,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":85,\"full_literals\":[-45,60]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[67,70],\"full_literals\":[-61,29,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":71,\"full_literals\":[-33,62]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[83],\"full_literals\":[-63,43]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[84],\"full_literals\":[-64,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":84,\"full_literals\":[-44,64]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-60,false,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-65,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-62,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-68,61,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-69,63,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-64,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-70,68,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-67,-69,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-66,-70,71],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true}]}"
  "103 55 0 86 84 0\n104 58 0 86 85 0\n105 53 0 103 76 0\n106 54 0 103 77 0\n107 56 0 104 82 0\n108 57 0 104 83 0\n109 46 0 105 73 0\n110 47 0 105 74 0\n111 48 0 106 75 0\n112 49 0 107 78 0\n113 50 0 107 79 0\n114 51 0 108 80 0\n115 52 0 108 81 0\n116 -18 0 111 114 13 14 15 19 23 32 37 68 27 28 71 0\n117 -27 14 -44 0 115 116 113 45 44 43 25 26 72 11 52 70 0\n118 -6 -26 -44 0 111 116 113 29 24 45 44 1 9 11 68 20 22 70 0\n119 14 -44 0 110 115 116 113 47 46 45 44 43 117 67 118 72 2 3 16 49 50 51 70 0\n120 -16 -44 0 116 113 119 21 45 44 12 17 70 0\n121 -17 -44 45 0 116 112 119 36 35 21 18 48 10 34 55 56 57 69 0\n122 -44 45 0 116 113 111 44 45 119 7 18 21 120 121 70 53 54 68 0\n123 -43 11 0 109 39 40 41 42 66 0\n124 -70 0 102 109 101 94 93 87 122 61 91 123 63 90 97 99 96 88 30 31 33 38 66 0\n125 -13 0 115 4 5 6 8 72 0\n126 29 44 0 110 61 123 63 62 64 58 59 60 67 0\n127 44 0 125 109 61 126 30 38 66 33 0\n128 33 0 127 65 0\n129 64 0 127 92 0\n130 62 0 128 89 0\n131 69 0 129 98 0\n132 67 0 130 95 0\n133 0 132 131 124 100 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record003.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record003.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record003.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record003.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record003 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record003.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record003.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record003.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record003.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record003 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record003_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record003 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record003_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record003_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record004
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "34c9715c2f2aa9695a2ea66959562da4e538ae8791e2785e0f999564b9994b59354d8b52d2b49d1743d98d5334cb392d4b8ad1b16c3b91d4789ca719d1725c3783d0f23c4f5522c4722a2a89a91a2615a0e0b81e544a946499515151550d0b41d28c9314c8b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "da69b49269a4924926da49249a49b492492492492249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record004 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record004 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record004.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record004.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record004.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 44), (facetIndex 47), (facetIndex 67), (facetIndex 72), (facetIndex 79), (facetIndex 82)]))
 (.leaf ([(facetIndex 71), (facetIndex 74), (facetIndex 77), (facetIndex 78)])))
 (.branch 3
 (.leaf ([(facetIndex 36), (facetIndex 37), (facetIndex 45), (facetIndex 50), (facetIndex 51)]))
 (.branch 4
 (.leaf ([(facetIndex 46), (facetIndex 54), (facetIndex 56), (facetIndex 64), (facetIndex 66)]))
 (.leaf ([(facetIndex 34), (facetIndex 57), (facetIndex 58), (facetIndex 59)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 32), (facetIndex 38), (facetIndex 55), (facetIndex 60), (facetIndex 65), (facetIndex 68), (facetIndex 84)]))
 (.leaf ([(facetIndex 39), (facetIndex 40), (facetIndex 41)])))
 (.branch 8
 (.leaf ([(facetIndex 42), (facetIndex 52), (facetIndex 70), (facetIndex 76)]))
 (.branch 9
 (.leaf ([(facetIndex 33), (facetIndex 35), (facetIndex 69)]))
 (.leaf ([(facetIndex 43)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "50000011701001785035300054443530722000320976665228485z20;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 62)]))
 (.leaf ([(facetIndex 75)])))
 (.branch 3
 (.leaf ([(facetIndex 83)]))
 (.leaf ([(facetIndex 49), (facetIndex 53)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 61), (facetIndex 63)]))
 (.leaf ([(facetIndex 48), (facetIndex 81), (facetIndex 86)])))
 (.branch 7
 (.leaf ([(facetIndex 73), (facetIndex 85)]))
 (.leaf ([(facetIndex 80)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "17042f00023000000082000001801dz24;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
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
def grouped3_0020 : List Nat := [0, 1]
def grouped3_0021 : List Nat := [0, 1, 2, 3]
def grouped3_0023 : List Nat := [1]
def grouped3_0024 : List Nat := [2]
def grouped3_0025 : List Nat := [2, 3]
def grouped3_0026 : List Nat := [3]
def grouped3_0027 : List Nat := [4]
def grouped3_0028 : List Nat := [4, 5]
def grouped3_0029 : List Nat := [4, 5, 6, 7]
def grouped3_0030 : List Nat := [5]
def grouped3_0031 : List Nat := [6]
def grouped3_0032 : List Nat := [6, 7]
def grouped3_0033 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record004 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record004_matrix_checked

def leafCount : Nat := 1
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaf0000 : List (Fin data.count) := [(facetIndex 15), (facetIndex 18), (facetIndex 22), (facetIndex 30), (facetIndex 50), (facetIndex 52), (facetIndex 53), (facetIndex 58), (facetIndex 63), (facetIndex 66), (facetIndex 69), (facetIndex 77), (facetIndex 82), (facetIndex 84)]
theorem leaf0000_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0000 = true := by
  decide +kernel
theorem leaf0000_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0000 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0000_counts_checked
def leavesTable : ConcreteGrowth.Table (List (Fin data.count)) :=
(.leaf (leaf0000))
def leaves (j : Fin leafCount) : List (Fin data.count) := leavesTable.get j.val

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record004" "{\"atoms\":[{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0017\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0017\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0032\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0029\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record004" 105

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record004" "{\"ridges\":[[2,7],[6,137],[7,67],[9,35],[9,161],[11,37],[13,69],[18,137],[18,161],[19,81],[23,82],[25,70],[25,580],[27,168],[31,84],[32,11],[32,67],[33,7],[33,137],[34,11],[36,37],[39,67],[39,69],[39,70],[40,161],[43,7],[43,580],[49,67],[49,578],[49,585],[50,161],[51,67],[52,67],[53,67],[53,609],[58,37],[59,41],[61,69],[61,585],[63,37],[63,609],[66,137],[72,168],[74,578],[76,70],[77,578],[78,580],[81,600],[82,168],[82,522],[82,552],[84,324],[85,600],[86,840]],\"owners\":[[32,11,[4,5,6,46,47],[0,34,35,45,48,49]],[34,11,[4,5,6,45,47,49],[0,32,35,46,48]],[9,35,[2,5,36,39,41,44,47,53],[50]],[11,37,[2,36,39,40,41,62,63],[54,57,58,59]],[59,41,[5,18,44,64],[11,47,54,58]],[19,81,[7,13,45,51,55],[65]],[23,82,[7,45,51,52,80,81],[68,76,77]],[9,161,[18,57,62,64],[40,50]],[18,161,[9,40,50,62],[57,64]],[40,161,[18,64],[9,50,57,62]],[50,161,[18,57],[9,40,62,64]],[31,84,[13,23,55,68,77,85],[84]],[84,324,[15,42],[31,60,73,76,86]],[27,168,[18,57,64,83],[72,79,82]],[72,168,[18,64],[27,57,79,82,83]],[82,168,[18,57,64,83],[27,72,79]],[82,522,[22,35,49,71,74,81],[28,47]],[49,578,[25,77,78],[43,53,74,81]],[74,578,[53],[25,43,49,77,78,81]],[77,578,[49,53],[25,43,74,78,81]],[25,580,[61,63,85,86],[43,74,77,78]],[43,580,[85,86],[25,61,63,74,77,78]],[78,580,[61,85,86],[25,43,63,74,77]],[82,552,[30,59],[28,47]],[49,585,[61],[]],[61,585,[49],[]],[53,609,[63],[]],[63,609,[53],[]],[81,600,[85],[]],[85,600,[81],[]],[86,840,[],[]]],\"edges\":[[4,[2,5,9,11,18,36,39,40,41,44,47,50,53,54,57,58,59,62,63,64]],[31,[7,13,19,23,31,45,51,52,55,65,68,76,77,80,81,84,85]],[36,[9,18,27,40,50,57,62,64,72,75,79,82,83]],[41,[25,43,49,53,61,63,74,77,78,81,85,86]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record004" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record004\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-19,-3],[-20,-19],[-25,-18],[-25,-19],[-25,-24],[-26,-19],[-28,-20],[-28,-24],[-29,-21],[-29,-22],[-29,-25],[-29,-27],[-30,-19],[-32,-19],[-33,-3],[-33,-29],[-34,-19],[-34,-21],[-34,-27],[-34,-31],[-35,-19],[-37,-20],[-37,-24],[-37,-36],[-38,-21],[-38,-25],[-38,-26],[-38,-27],[-38,-33],[-39,-19],[-39,-20],[-40,-34],[-41,-19],[-42,-10],[-42,-19],[-42,-26],[-43,-19],[-43,-39],[-44,-29],[-44,-34],[-44,-38],[-45,-34],[-45,-43],[-46,-20],[-46,-28],[-46,-43],[-48,-28],[-49,-19],[-49,-22],[-49,-35],[-49,-42],[-50,-34],[-51,-40],[-51,-50],[-53,-34],[-54,-2],[-54,-23],[-54,-26],[-54,-30],[-54,-31],[-54,-32],[-54,-41],[-54,-42],[-54,-47],[-54,-52],[-54,-53],[-55,-21],[-55,-54],[-56,-54],[-57,-3],[-57,-54],[-58,-50],[-59,-54],[-60,-20],[-60,-24],[-60,-40],[-61,-25],[-61,-60],[-62,-21],[-62,-25],[-62,-27],[-62,-29],[-63,-54],[-64,-34],[-65,-54],[-66,-3],[-67,-54],[-68,-34],[-68,-58],[-68,-60],[-69,-18],[-69,-40],[-69,-45],[-69,-50],[-69,-53],[-69,-55],[-69,-56],[-69,-60],[-69,-68],[-1,-19,-29],[-18,2,3,4,32,33],[-20,2,3,4,31,33,34],[-6,1,3,22,25,27,30,33,38],[-7,1,22,25,26,27,47,48],[-22,-43,-48],[-5,-25,-34],[-18,-36,-38],[-25,-34,-36],[-25,-34,-37],[-8,-25,-46],[-14,-25,-60],[-44,3,10,30,49],[-4,-10,-51],[-10,-19,-51],[-11,5,8,31,36,40],[-13,5,31,36,37,64,65],[-6,10,42,47,49],[-10,6,26,35,47],[-26,10,49],[-35,10,42],[-17,8,13,40,53,61,69],[-68,9,28],[-15,10,42,49,67],[-57,10,49],[-66,10,42,49,67],[-66,12,21,34,56,58,65],[-34,14,61,62],[-58,38],[-61,34,38],[-14,46,48,69,70],[-29,69,70],[-62,46,69,70],[-66,16,44],[-34,46],[-46,34],[-38,48],[-48,38],[-65,69],[-69,65],[-70],[-71,30,33,52,57,63,66],[-72,56,58,61,62],[-73,22,23,31,35,36],[-74,32,39,41,49,51],[-75,20,42,43,44],[-76,18,24,40,45,50,53,68],[-77,25,26,27],[-78,28,37,55,60],[-79,19,21,54],[-80,29],[-81,71],[-81,72],[-82,74],[-82,75],[-83,73],[-83,82],[-84,81],[-84,83],[-85,76,77],[-86,76],[-86,77],[-87,79,80],[-88,79],[-88,80],[-89,78,87],[-90,78,88],[-90,87],[-91,88],[-92,85,91],[-92,86,90],[-93,86,91],[-92,89],[-93,90],[-94,84,93],[-94,92],[94],[-47,95],[-96,34,38],[-34,96],[-38,96],[-65,97],[-69,98],[-95,99],[-96,100],[-100,101],[-99,101],[-97,102],[-98,103],[-102,-103,104],[-101,-104,105],[-105],[-9,-10,-12,-16,-35,-37,-38,-43,-48,-51,-54,-61,-66,-68],[1,3,6,7,10,22,25,26,27,30,33,35,38,39,42,43,44,47,48,49],[5,8,11,13,17,31,36,37,40,50,53,60,61,64,65,68,69],[6,10,15,26,35,42,47,49,57,59,63,66,67],[14,29,34,38,46,48,58,61,62,65,69,70]],\"atoms\":[{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":33,\"b\":5},{\"tag\":\"incompatible\",\"a\":34,\"b\":33},{\"tag\":\"incompatible\",\"a\":39,\"b\":32},{\"tag\":\"incompatible\",\"a\":39,\"b\":33},{\"tag\":\"incompatible\",\"a\":39,\"b\":38},{\"tag\":\"incompatible\",\"a\":40,\"b\":33},{\"tag\":\"incompatible\",\"a\":42,\"b\":34},{\"tag\":\"incompatible\",\"a\":42,\"b\":38},{\"tag\":\"incompatible\",\"a\":43,\"b\":35},{\"tag\":\"incompatible\",\"a\":43,\"b\":36},{\"tag\":\"incompatible\",\"a\":43,\"b\":39},{\"tag\":\"incompatible\",\"a\":43,\"b\":41},{\"tag\":\"incompatible\",\"a\":44,\"b\":33},{\"tag\":\"incompatible\",\"a\":46,\"b\":33},{\"tag\":\"incompatible\",\"a\":47,\"b\":5},{\"tag\":\"incompatible\",\"a\":47,\"b\":43},{\"tag\":\"incompatible\",\"a\":49,\"b\":33},{\"tag\":\"incompatible\",\"a\":49,\"b\":35},{\"tag\":\"incompatible\",\"a\":49,\"b\":41},{\"tag\":\"incompatible\",\"a\":49,\"b\":45},{\"tag\":\"incompatible\",\"a\":50,\"b\":33},{\"tag\":\"incompatible\",\"a\":52,\"b\":34},{\"tag\":\"incompatible\",\"a\":52,\"b\":38},{\"tag\":\"incompatible\",\"a\":52,\"b\":51},{\"tag\":\"incompatible\",\"a\":53,\"b\":35},{\"tag\":\"incompatible\",\"a\":53,\"b\":39},{\"tag\":\"incompatible\",\"a\":53,\"b\":40},{\"tag\":\"incompatible\",\"a\":53,\"b\":41},{\"tag\":\"incompatible\",\"a\":53,\"b\":47},{\"tag\":\"incompatible\",\"a\":54,\"b\":33},{\"tag\":\"incompatible\",\"a\":54,\"b\":34},{\"tag\":\"incompatible\",\"a\":55,\"b\":49},{\"tag\":\"incompatible\",\"a\":56,\"b\":33},{\"tag\":\"incompatible\",\"a\":57,\"b\":18},{\"tag\":\"incompatible\",\"a\":57,\"b\":33},{\"tag\":\"incompatible\",\"a\":57,\"b\":40},{\"tag\":\"incompatible\",\"a\":58,\"b\":33},{\"tag\":\"incompatible\",\"a\":58,\"b\":54},{\"tag\":\"incompatible\",\"a\":59,\"b\":43},{\"tag\":\"incompatible\",\"a\":59,\"b\":49},{\"tag\":\"incompatible\",\"a\":59,\"b\":53},{\"tag\":\"incompatible\",\"a\":60,\"b\":49},{\"tag\":\"incompatible\",\"a\":60,\"b\":58},{\"tag\":\"incompatible\",\"a\":61,\"b\":34},{\"tag\":\"incompatible\",\"a\":61,\"b\":42},{\"tag\":\"incompatible\",\"a\":61,\"b\":58},{\"tag\":\"incompatible\",\"a\":63,\"b\":42},{\"tag\":\"incompatible\",\"a\":64,\"b\":33},{\"tag\":\"incompatible\",\"a\":64,\"b\":36},{\"tag\":\"incompatible\",\"a\":64,\"b\":50},{\"tag\":\"incompatible\",\"a\":64,\"b\":57},{\"tag\":\"incompatible\",\"a\":65,\"b\":49},{\"tag\":\"incompatible\",\"a\":66,\"b\":55},{\"tag\":\"incompatible\",\"a\":66,\"b\":65},{\"tag\":\"incompatible\",\"a\":68,\"b\":49},{\"tag\":\"incompatible\",\"a\":69,\"b\":4},{\"tag\":\"incompatible\",\"a\":69,\"b\":37},{\"tag\":\"incompatible\",\"a\":69,\"b\":40},{\"tag\":\"incompatible\",\"a\":69,\"b\":44},{\"tag\":\"incompatible\",\"a\":69,\"b\":45},{\"tag\":\"incompatible\",\"a\":69,\"b\":46},{\"tag\":\"incompatible\",\"a\":69,\"b\":56},{\"tag\":\"incompatible\",\"a\":69,\"b\":57},{\"tag\":\"incompatible\",\"a\":69,\"b\":62},{\"tag\":\"incompatible\",\"a\":69,\"b\":67},{\"tag\":\"incompatible\",\"a\":69,\"b\":68},{\"tag\":\"incompatible\",\"a\":70,\"b\":35},{\"tag\":\"incompatible\",\"a\":70,\"b\":69},{\"tag\":\"incompatible\",\"a\":71,\"b\":69},{\"tag\":\"incompatible\",\"a\":72,\"b\":5},{\"tag\":\"incompatible\",\"a\":72,\"b\":69},{\"tag\":\"incompatible\",\"a\":74,\"b\":65},{\"tag\":\"incompatible\",\"a\":75,\"b\":69},{\"tag\":\"incompatible\",\"a\":76,\"b\":34},{\"tag\":\"incompatible\",\"a\":76,\"b\":38},{\"tag\":\"incompatible\",\"a\":76,\"b\":55},{\"tag\":\"incompatible\",\"a\":77,\"b\":39},{\"tag\":\"incompatible\",\"a\":77,\"b\":76},{\"tag\":\"incompatible\",\"a\":78,\"b\":35},{\"tag\":\"incompatible\",\"a\":78,\"b\":39},{\"tag\":\"incompatible\",\"a\":78,\"b\":41},{\"tag\":\"incompatible\",\"a\":78,\"b\":43},{\"tag\":\"incompatible\",\"a\":79,\"b\":69},{\"tag\":\"incompatible\",\"a\":80,\"b\":49},{\"tag\":\"incompatible\",\"a\":81,\"b\":69},{\"tag\":\"incompatible\",\"a\":82,\"b\":5},{\"tag\":\"incompatible\",\"a\":83,\"b\":69},{\"tag\":\"incompatible\",\"a\":84,\"b\":49},{\"tag\":\"incompatible\",\"a\":84,\"b\":74},{\"tag\":\"incompatible\",\"a\":84,\"b\":76},{\"tag\":\"incompatible\",\"a\":85,\"b\":32},{\"tag\":\"incompatible\",\"a\":85,\"b\":55},{\"tag\":\"incompatible\",\"a\":85,\"b\":60},{\"tag\":\"incompatible\",\"a\":85,\"b\":65},{\"tag\":\"incompatible\",\"a\":85,\"b\":68},{\"tag\":\"incompatible\",\"a\":85,\"b\":70},{\"tag\":\"incompatible\",\"a\":85,\"b\":71},{\"tag\":\"incompatible\",\"a\":85,\"b\":76},{\"tag\":\"incompatible\",\"a\":85,\"b\":84},{\"tag\":\"three\",\"ridge\":7,\"vertices\":[2,33,43]},{\"tag\":\"mate\",\"ridge\":11,\"a\":32,\"owners\":[4,5,6,46,47]},{\"tag\":\"mate\",\"ridge\":11,\"a\":34,\"owners\":[4,5,6,45,47,49]},{\"tag\":\"mate\",\"ridge\":35,\"a\":9,\"owners\":[2,5,36,39,41,44,47,53]},{\"tag\":\"mate\",\"ridge\":37,\"a\":11,\"owners\":[2,36,39,40,41,62,63]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[36,58,63]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[7,39,49]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[32,51,53]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[39,49,51]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[39,49,52]},{\"tag\":\"three\",\"ridge\":69,\"vertices\":[13,39,61]},{\"tag\":\"three\",\"ridge\":70,\"vertices\":[25,39,76]},{\"tag\":\"mate\",\"ridge\":41,\"a\":59,\"owners\":[5,18,44,64]},{\"tag\":\"three\",\"ridge\":137,\"vertices\":[6,18,66]},{\"tag\":\"three\",\"ridge\":137,\"vertices\":[18,33,66]},{\"tag\":\"mate\",\"ridge\":81,\"a\":19,\"owners\":[7,13,45,51,55]},{\"tag\":\"mate\",\"ridge\":82,\"a\":23,\"owners\":[7,45,51,52,80,81]},{\"tag\":\"mate\",\"ridge\":161,\"a\":9,\"owners\":[18,57,62,64]},{\"tag\":\"mate\",\"ridge\":161,\"a\":18,\"owners\":[9,40,50,62]},{\"tag\":\"mate\",\"ridge\":161,\"a\":40,\"owners\":[18,64]},{\"tag\":\"mate\",\"ridge\":161,\"a\":50,\"owners\":[18,57]},{\"tag\":\"mate\",\"ridge\":84,\"a\":31,\"owners\":[13,23,55,68,77,85]},{\"tag\":\"mate\",\"ridge\":324,\"a\":84,\"owners\":[15,42]},{\"tag\":\"mate\",\"ridge\":168,\"a\":27,\"owners\":[18,57,64,83]},{\"tag\":\"mate\",\"ridge\":168,\"a\":72,\"owners\":[18,64]},{\"tag\":\"mate\",\"ridge\":168,\"a\":82,\"owners\":[18,57,64,83]},{\"tag\":\"mate\",\"ridge\":522,\"a\":82,\"owners\":[22,35,49,71,74,81]},{\"tag\":\"mate\",\"ridge\":578,\"a\":49,\"owners\":[25,77,78]},{\"tag\":\"mate\",\"ridge\":578,\"a\":74,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":578,\"a\":77,\"owners\":[49,53]},{\"tag\":\"mate\",\"ridge\":580,\"a\":25,\"owners\":[61,63,85,86]},{\"tag\":\"mate\",\"ridge\":580,\"a\":43,\"owners\":[85,86]},{\"tag\":\"mate\",\"ridge\":580,\"a\":78,\"owners\":[61,85,86]},{\"tag\":\"mate\",\"ridge\":552,\"a\":82,\"owners\":[30,59]},{\"tag\":\"mate\",\"ridge\":585,\"a\":49,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":585,\"a\":61,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":609,\"a\":53,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":609,\"a\":63,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":600,\"a\":81,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":600,\"a\":85,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":840,\"a\":86,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[44,47,67,72,79,82],\"full_literals\":[-71,30,33,52,57,63,66]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[71,74,77,78],\"full_literals\":[-72,56,58,61,62]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[36,37,45,50,51],\"full_literals\":[-73,22,23,31,35,36]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[46,54,56,64,66],\"full_literals\":[-74,32,39,41,49,51]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[34,57,58,59],\"full_literals\":[-75,20,42,43,44]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[32,38,55,60,65,68,84],\"full_literals\":[-76,18,24,40,45,50,53,68]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[39,40,41],\"full_literals\":[-77,25,26,27]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[42,52,70,76],\"full_literals\":[-78,28,37,55,60]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[33,35,69],\"full_literals\":[-79,19,21,54]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[43],\"full_literals\":[-80,29]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-81,71,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-81,false,72],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0008\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-82,74,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-82,false,75],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-83,73,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-83,false,82],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-84,81,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-84,false,83],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-85,76,77],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-86,76,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-86,false,77],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0018\",\"joined_name\":\"grouped2_0017\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-87,79,80],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0018\",\"joined_name\":\"grouped2_0017\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-88,79,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0018\",\"joined_name\":\"grouped2_0017\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-88,false,80],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-89,78,87],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-90,78,88],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-90,false,87],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-91,false,88],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-92,85,91],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-92,86,90],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-93,86,91],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-92,false,89],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-93,false,90],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-94,84,93],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-94,false,92],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":62,\"full_literals\":[-47,95]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[49,53],\"full_literals\":[-96,34,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":49,\"full_literals\":[-34,96]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":53,\"full_literals\":[-38,96]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":81,\"full_literals\":[-65,97]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":85,\"full_literals\":[-69,98]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-95,false,99],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0025\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-96,100],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-100,101],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-99,false,101],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-97,102],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0031\",\"right_name\":\"grouped3_0033\",\"joined_name\":\"grouped3_0032\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-98,false,103],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0028\",\"right_name\":\"grouped3_0032\",\"joined_name\":\"grouped3_0029\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-102,-103,104],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-101,-104,105],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"block\",\"leaf\":0,\"vertices\":[15,18,22,30,50,52,53,58,63,66,69,77,82,84]},{\"tag\":\"edge\",\"edge\":4,\"owners\":[2,5,9,11,18,36,39,40,41,44,47,50,53,54,57,58,59,62,63,64]},{\"tag\":\"edge\",\"edge\":31,\"owners\":[7,13,19,23,31,45,51,52,55,65,68,76,77,80,81,84,85]},{\"tag\":\"edge\",\"edge\":36,\"owners\":[9,18,27,40,50,57,62,64,72,75,79,82,83]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[25,43,49,53,61,63,74,77,78,81,85,86]}]}"
  "197 92 0 176 175 0\n198 89 0 197 172 0\n199 14 29 34 38 46 48 58 61 62 65 69 0 140 196 0\n200 69 96 0 140 179 180 129 137 128 135 131 138 132 130 199 0\n201 88 -93 -69 0 173 99 98 96 95 94 93 92 91 168 166 171 160 146 8 23 148 0\n202 39 49 1 3 6 7 35 22 25 26 27 30 38 33 42 43 44 47 48 0 193 118 0\n203 -88 101 0 185 184 200 139 85 180 137 186 183 177 163 164 150 9 10 11 12 16 39 149 1 6 13 21 30 35 37 48 100 103 104 202 0\n204 -20 101 0 176 198 185 184 179 180 129 128 200 97 203 201 174 157 152 142 82 150 79 139 85 98 96 2 7 22 149 148 162 165 0\n205 -42 101 0 176 197 185 184 179 180 129 128 200 97 203 201 174 157 152 142 82 150 81 80 79 139 85 35 36 149 147 162 161 167 170 0\n206 87 -69 0 198 197 99 98 96 95 94 93 92 91 167 165 170 160 146 8 23 148 0\n207 49 101 0 176 205 185 184 200 203 201 174 158 156 154 204 139 85 179 180 129 128 97 157 152 142 79 82 150 206 162 149 37 145 33 30 14 13 1 153 144 114 112 0\n208 101 0 176 185 184 179 180 128 129 200 97 139 85 203 201 174 157 152 142 79 82 150 206 162 149 207 48 0\n209 -104 0 208 191 190 0\n210 -69 0 209 139 182 181 188 187 189 0\n211 -29 0 210 140 131 0\n212 -65 0 210 138 0\n213 96 0 210 200 0\n214 -80 0 211 150 0\n215 -88 0 214 164 0\n216 -91 0 215 168 0\n217 85 0 216 197 169 0\n218 -44 0 213 40 41 178 0\n219 -19 0 213 218 216 176 2 4 6 17 35 37 178 145 28 154 147 156 161 158 171 174 0\n220 -28 0 213 45 47 134 136 178 0\n221 -55 -79 0 219 67 68 149 0\n222 -54 10 49 0 124 119 63 64 73 83 87 117 120 123 125 195 0\n223 -21 0 213 18 25 178 0\n224 -27 0 213 19 28 178 0\n225 10 49 0 213 224 197 214 223 219 119 222 149 162 167 170 160 161 147 3 5 26 178 32 42 52 55 88 146 0\n226 -25 0 213 210 212 26 77 80 178 20 32 52 55 84 88 108 109 127 134 106 116 111 110 115 121 194 0\n227 -46 -75 42 0 218 44 46 145 0\n228 -24 -90 0 215 214 220 167 162 221 166 23 75 148 0\n229 77 3 30 39 49 0 217 197 216 215 176 214 219 140 210 213 218 212 223 220 225 34 161 159 170 171 167 166 174 162 157 158 221 149 151 152 155 156 56 57 60 61 62 65 66 69 71 83 153 154 144 53 54 113 227 134 132 178 29 136 102 101 141 145 133 43 105 228 146 89 90 122 142 126 148 192 24 143 0\n230 -26 42 0 213 223 219 214 176 27 58 178 149 134 162 227 167 154 173 156 174 158 0\n231 30 39 49 0 216 176 224 226 197 214 219 223 225 34 230 147 161 170 167 162 149 83 65 171 174 157 151 229 15 70 86 141 0\n232 49 0 226 224 197 216 176 214 223 219 218 225 34 230 147 161 170 171 167 174 162 158 149 156 154 59 231 31 38 145 0\n233 -22 0 232 49 0\n234 -35 0 232 50 0\n235 -42 0 232 51 0\n236 -26 0 235 230 0\n237 -77 0 236 224 226 147 0\n238 -86 0 237 161 0\n239 76 0 237 217 159 0\n240 90 0 238 197 170 0\n241 -93 0 238 216 171 0\n242 87 0 240 167 0\n243 78 0 240 215 166 0\n244 -24 0 240 228 0\n245 84 0 241 176 174 0\n246 79 0 242 214 162 0\n247 81 0 245 157 0\n248 83 0 245 158 0\n249 -55 0 246 221 0\n250 54 0 246 219 223 149 0\n251 72 0 247 152 0\n252 73 0 248 155 0\n253 82 0 248 156 0\n254 -23 0 250 57 0\n255 -31 0 250 60 0\n256 -53 0 250 66 0\n257 -56 0 250 69 0\n258 36 0 252 233 255 254 234 143 0\n259 75 0 253 154 0\n260 -37 0 258 24 0\n261 -46 0 259 235 227 0\n262 60 0 260 220 243 249 148 0\n263 -34 0 261 134 0\n264 -62 0 261 210 140 132 0\n265 -20 0 262 74 0\n266 -40 0 262 76 0\n267 -61 0 262 78 0\n268 -68 0 262 90 0\n269 38 0 263 213 178 0\n270 43 0 265 235 259 218 145 0\n271 58 0 267 257 264 251 142 0\n272 -18 0 269 258 107 0\n273 -45 0 270 43 0\n274 -50 0 271 72 0\n275 0 273 272 256 266 268 274 239 244 146 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record004.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record004.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record004.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record004.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record004 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeafTable : ConcreteGrowth.Table (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record004.l) :=
(.leaf (⟨0, by decide⟩))
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record004.l := originalLeafTable.get j.val
def orbitWordTable : ConcreteGrowth.Table (List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record004.g)) :=
(.leaf ([]))
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record004.g) := orbitWordTable.get j.val
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record004.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record004.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record004 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record004_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record004 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record004_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record004_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record009
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "9b15c2f26a568bad1aa699996558b69394e8b8ae1b91e2785e0fa69564b9d16a599595554b59354d8b4ad1b51d2745d0f743a8e6364d532ce4b52e2b2ac6b46c9b16c3bc1e8761cc749c6785c570de0f43c8f91946898a6458961382e07a4551625295152544d0b41d90d4388ca344c9312c2b06e0741c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6d24924924924db492492492492492492492492492492489249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record009 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record009 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record009.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 37), (facetIndex 38), (facetIndex 39), (facetIndex 43), (facetIndex 57), (facetIndex 72), (facetIndex 90)]))
 (.leaf ([(facetIndex 40), (facetIndex 41), (facetIndex 44), (facetIndex 59), (facetIndex 74), (facetIndex 92)])))
 (.branch 3
 (.leaf ([(facetIndex 42), (facetIndex 45), (facetIndex 60), (facetIndex 75), (facetIndex 93)]))
 (.leaf ([(facetIndex 34), (facetIndex 48), (facetIndex 51), (facetIndex 63), (facetIndex 66), (facetIndex 81), (facetIndex 84)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 36), (facetIndex 52), (facetIndex 54), (facetIndex 67), (facetIndex 69), (facetIndex 85), (facetIndex 87)]))
 (.leaf ([(facetIndex 35), (facetIndex 49), (facetIndex 53), (facetIndex 64), (facetIndex 68), (facetIndex 82), (facetIndex 86)])))
 (.branch 7
 (.leaf ([(facetIndex 46), (facetIndex 55), (facetIndex 61), (facetIndex 70), (facetIndex 79), (facetIndex 88)]))
 (.branch 8
 (.leaf ([(facetIndex 47), (facetIndex 56), (facetIndex 62), (facetIndex 71), (facetIndex 80), (facetIndex 89)]))
 (.leaf ([(facetIndex 50), (facetIndex 58), (facetIndex 65), (facetIndex 73), (facetIndex 83), (facetIndex 91)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "218076454385376000218076454385376218076454385376210211000453z22;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 76)]))
 (.leaf ([(facetIndex 77)])))
 (.branch 3
 (.leaf ([(facetIndex 78)]))
 (.leaf ([(facetIndex 94)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 95)]))
 (.leaf ([(facetIndex 96)])))
 (.branch 7
 (.leaf ([(facetIndex 97)]))
 (.branch 8
 (.leaf ([(facetIndex 98)]))
 (.leaf ([(facetIndex 99)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "87654300000000000000021z4d;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [4]
def grouped2_0007 : List Nat := [4, 5]
def grouped2_0008 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0009 : List Nat := [5]
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7, 8]
def grouped2_0012 : List Nat := [7]
def grouped2_0013 : List Nat := [7, 8]
def grouped2_0014 : List Nat := [8]
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record009 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record009_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record009" "{\"atoms\":[{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0030\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record009" 80

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record009" "{\"ridges\":[[77,344],[78,616],[95,344],[97,184],[98,344]],\"owners\":[[97,184,[76,94],[]],[77,344,[95,98],[]],[95,344,[77,98],[]],[98,344,[77,95],[]],[78,616,[96,99],[]]],\"edges\":[],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record009" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record009\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-28,-1],[-28,-4],[-28,-6],[-28,-9],[-28,-13],[-28,-16],[-28,-18],[-28,-21],[-28,-25],[-31,-28],[-33,-28],[-36,-28],[-40,-28],[-43,-1],[-43,-4],[-43,-6],[-43,-9],[-43,-13],[-43,-16],[-43,-18],[-43,-21],[-43,-25],[-43,-31],[-43,-33],[-43,-36],[-43,-40],[-44,-2],[-44,-5],[-44,-7],[-44,-11],[-44,-14],[-44,-17],[-44,-19],[-44,-23],[-44,-26],[-44,-32],[-44,-34],[-44,-38],[-44,-41],[-45,-3],[-45,-8],[-45,-10],[-45,-12],[-45,-15],[-45,-20],[-45,-22],[-45,-24],[-45,-27],[-45,-35],[-45,-37],[-45,-39],[-45,-42],[-47,-2],[-47,-5],[-47,-7],[-47,-11],[-47,-14],[-47,-17],[-47,-19],[-47,-23],[-47,-26],[-47,-32],[-47,-34],[-47,-38],[-47,-41],[-48,-3],[-48,-8],[-48,-10],[-48,-12],[-48,-15],[-48,-20],[-48,-22],[-48,-24],[-48,-27],[-48,-35],[-48,-37],[-48,-39],[-48,-42],[-46,28,43],[-29,44,47],[-44,29,47],[-47,29,44],[-30,45,48],[-49,1,6,9,18,21,33,36],[-50,3,10,12,22,24,37,39],[-51,2,7,11,19,23,34,38],[-52,4,13,16,25,31,40],[-53,5,14,17,26,32,41],[-54,8,15,20,27,35,42],[-55,49],[-56,55],[-57,50],[-57,51],[-58,53],[-58,54],[-59,52],[-59,58],[-60,57,59],[-61,59],[-62,56,61],[-62,60],[62],[-63,28],[-28,63],[-64,29],[-29,64],[-65,30],[-66,43],[-43,66],[-67,44],[-44,67],[-68,45],[-69,46],[-70,47],[-71,63,64],[-64,71],[-63,71],[-72,65,66],[-66,72],[-73,71,72],[-72,73],[-71,73],[-74,67,68],[-67,74],[-75,70],[-76,69,75],[-77,74,76],[-74,-76,78],[-79,73,77],[-78,80],[-73,-77,80],[79],[-80]],\"atoms\":[{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":76,\"b\":34},{\"tag\":\"incompatible\",\"a\":76,\"b\":46},{\"tag\":\"incompatible\",\"a\":76,\"b\":48},{\"tag\":\"incompatible\",\"a\":76,\"b\":51},{\"tag\":\"incompatible\",\"a\":76,\"b\":55},{\"tag\":\"incompatible\",\"a\":76,\"b\":61},{\"tag\":\"incompatible\",\"a\":76,\"b\":63},{\"tag\":\"incompatible\",\"a\":76,\"b\":66},{\"tag\":\"incompatible\",\"a\":76,\"b\":70},{\"tag\":\"incompatible\",\"a\":79,\"b\":76},{\"tag\":\"incompatible\",\"a\":81,\"b\":76},{\"tag\":\"incompatible\",\"a\":84,\"b\":76},{\"tag\":\"incompatible\",\"a\":88,\"b\":76},{\"tag\":\"incompatible\",\"a\":94,\"b\":34},{\"tag\":\"incompatible\",\"a\":94,\"b\":46},{\"tag\":\"incompatible\",\"a\":94,\"b\":48},{\"tag\":\"incompatible\",\"a\":94,\"b\":51},{\"tag\":\"incompatible\",\"a\":94,\"b\":55},{\"tag\":\"incompatible\",\"a\":94,\"b\":61},{\"tag\":\"incompatible\",\"a\":94,\"b\":63},{\"tag\":\"incompatible\",\"a\":94,\"b\":66},{\"tag\":\"incompatible\",\"a\":94,\"b\":70},{\"tag\":\"incompatible\",\"a\":94,\"b\":79},{\"tag\":\"incompatible\",\"a\":94,\"b\":81},{\"tag\":\"incompatible\",\"a\":94,\"b\":84},{\"tag\":\"incompatible\",\"a\":94,\"b\":88},{\"tag\":\"incompatible\",\"a\":95,\"b\":35},{\"tag\":\"incompatible\",\"a\":95,\"b\":47},{\"tag\":\"incompatible\",\"a\":95,\"b\":49},{\"tag\":\"incompatible\",\"a\":95,\"b\":53},{\"tag\":\"incompatible\",\"a\":95,\"b\":56},{\"tag\":\"incompatible\",\"a\":95,\"b\":62},{\"tag\":\"incompatible\",\"a\":95,\"b\":64},{\"tag\":\"incompatible\",\"a\":95,\"b\":68},{\"tag\":\"incompatible\",\"a\":95,\"b\":71},{\"tag\":\"incompatible\",\"a\":95,\"b\":80},{\"tag\":\"incompatible\",\"a\":95,\"b\":82},{\"tag\":\"incompatible\",\"a\":95,\"b\":86},{\"tag\":\"incompatible\",\"a\":95,\"b\":89},{\"tag\":\"incompatible\",\"a\":96,\"b\":36},{\"tag\":\"incompatible\",\"a\":96,\"b\":50},{\"tag\":\"incompatible\",\"a\":96,\"b\":52},{\"tag\":\"incompatible\",\"a\":96,\"b\":54},{\"tag\":\"incompatible\",\"a\":96,\"b\":58},{\"tag\":\"incompatible\",\"a\":96,\"b\":65},{\"tag\":\"incompatible\",\"a\":96,\"b\":67},{\"tag\":\"incompatible\",\"a\":96,\"b\":69},{\"tag\":\"incompatible\",\"a\":96,\"b\":73},{\"tag\":\"incompatible\",\"a\":96,\"b\":83},{\"tag\":\"incompatible\",\"a\":96,\"b\":85},{\"tag\":\"incompatible\",\"a\":96,\"b\":87},{\"tag\":\"incompatible\",\"a\":96,\"b\":91},{\"tag\":\"incompatible\",\"a\":98,\"b\":35},{\"tag\":\"incompatible\",\"a\":98,\"b\":47},{\"tag\":\"incompatible\",\"a\":98,\"b\":49},{\"tag\":\"incompatible\",\"a\":98,\"b\":53},{\"tag\":\"incompatible\",\"a\":98,\"b\":56},{\"tag\":\"incompatible\",\"a\":98,\"b\":62},{\"tag\":\"incompatible\",\"a\":98,\"b\":64},{\"tag\":\"incompatible\",\"a\":98,\"b\":68},{\"tag\":\"incompatible\",\"a\":98,\"b\":71},{\"tag\":\"incompatible\",\"a\":98,\"b\":80},{\"tag\":\"incompatible\",\"a\":98,\"b\":82},{\"tag\":\"incompatible\",\"a\":98,\"b\":86},{\"tag\":\"incompatible\",\"a\":98,\"b\":89},{\"tag\":\"incompatible\",\"a\":99,\"b\":36},{\"tag\":\"incompatible\",\"a\":99,\"b\":50},{\"tag\":\"incompatible\",\"a\":99,\"b\":52},{\"tag\":\"incompatible\",\"a\":99,\"b\":54},{\"tag\":\"incompatible\",\"a\":99,\"b\":58},{\"tag\":\"incompatible\",\"a\":99,\"b\":65},{\"tag\":\"incompatible\",\"a\":99,\"b\":67},{\"tag\":\"incompatible\",\"a\":99,\"b\":69},{\"tag\":\"incompatible\",\"a\":99,\"b\":73},{\"tag\":\"incompatible\",\"a\":99,\"b\":83},{\"tag\":\"incompatible\",\"a\":99,\"b\":85},{\"tag\":\"incompatible\",\"a\":99,\"b\":87},{\"tag\":\"incompatible\",\"a\":99,\"b\":91},{\"tag\":\"mate\",\"ridge\":184,\"a\":97,\"owners\":[76,94]},{\"tag\":\"mate\",\"ridge\":344,\"a\":77,\"owners\":[95,98]},{\"tag\":\"mate\",\"ridge\":344,\"a\":95,\"owners\":[77,98]},{\"tag\":\"mate\",\"ridge\":344,\"a\":98,\"owners\":[77,95]},{\"tag\":\"mate\",\"ridge\":616,\"a\":78,\"owners\":[96,99]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[34,48,51,63,66,81,84],\"full_literals\":[-49,1,6,9,18,21,33,36]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[36,52,54,67,69,85,87],\"full_literals\":[-50,3,10,12,22,24,37,39]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[35,49,53,64,68,82,86],\"full_literals\":[-51,2,7,11,19,23,34,38]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[46,55,61,70,79,88],\"full_literals\":[-52,4,13,16,25,31,40]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[47,56,62,71,80,89],\"full_literals\":[-53,5,14,17,26,32,41]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[50,58,65,73,83,91],\"full_literals\":[-54,8,15,20,27,35,42]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-55,false,49],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-56,false,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-57,50,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-57,false,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-58,53,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-58,false,54],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-59,52,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-59,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-60,57,59],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-61,false,59],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-62,56,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-62,false,60],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[76],\"full_literals\":[-63,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":76,\"full_literals\":[-28,63]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[77],\"full_literals\":[-64,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":77,\"full_literals\":[-29,64]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[78],\"full_literals\":[-65,30]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[94],\"full_literals\":[-66,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":94,\"full_literals\":[-43,66]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[95],\"full_literals\":[-67,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":95,\"full_literals\":[-44,67]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[96],\"full_literals\":[-68,45]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[97],\"full_literals\":[-69,46]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[98],\"full_literals\":[-70,47]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-71,63,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-64,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-72,65,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-66,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-73,71,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-72,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-71,false,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-74,67,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-67,false,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0030\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-75,70,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-76,69,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-77,74,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-74,-76,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-79,73,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-78,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-73,-77,80],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true}]}"
  "134 60 0 102 101 0\n135 -78 0 133 130 0\n136 -76 73 0 135 122 117 104 121 119 109 79 113 116 106 126 128 125 124 114 111 82 0\n137 -47 0 134 53 54 55 56 57 58 59 60 61 62 63 64 65 86 88 93 94 98 97 0\n138 -45 0 134 40 41 42 43 44 45 46 47 48 49 50 51 52 85 89 92 95 98 97 0\n139 -68 0 138 112 0\n140 -77 0 133 139 137 131 122 136 116 127 106 123 81 110 0\n141 73 0 140 132 129 0\n142 -44 0 134 27 28 29 30 31 32 33 34 35 36 37 38 39 86 88 93 94 98 97 0\n143 -29 0 142 137 80 0\n144 -64 0 143 105 0\n145 -48 0 134 66 67 68 69 70 71 72 73 74 75 76 77 78 85 89 92 95 98 97 0\n146 -30 0 145 138 83 0\n147 -65 0 146 107 0\n148 -28 0 102 1 2 3 4 5 6 7 8 9 10 11 12 13 84 87 90 96 91 99 100 0\n149 -63 0 148 103 0\n150 -71 0 149 144 115 0\n151 72 0 150 141 120 0\n152 66 0 151 147 118 0\n153 43 0 152 108 0\n154 -1 0 153 14 0\n155 -4 0 153 15 0\n156 -6 0 153 16 0\n157 -9 0 153 17 0\n158 -13 0 153 18 0\n159 -16 0 153 19 0\n160 -18 0 153 20 0\n161 -21 0 153 21 0\n162 -25 0 153 22 0\n163 -31 0 153 23 0\n164 -33 0 153 24 0\n165 -36 0 153 25 0\n166 -40 0 153 26 0\n167 -49 0 165 154 157 161 156 160 164 84 0\n168 -52 0 166 155 158 159 162 163 87 0\n169 -55 0 167 90 0\n170 -59 0 168 96 0\n171 -56 0 169 91 0\n172 -61 0 170 99 0\n173 0 171 172 102 100 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record009.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record009.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record009.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record009.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record009 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record009.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record009.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record009.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record009.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record009 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record009_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record009 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record009_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record009_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record009

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record012
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "570bc568bad1aa6959568d8b69394e8b8ae4789e1783e9c669564b91e745a96558d4b59354d3362d2b51d2743dd0ea394d538cd332ce4b52e2b46c9b16f07a1d8791d4789ca785c9715c3783d0f13c2f5505c2a83a4588e079512a4590e645515151548d1341d88ca344c3322c2b06e0741c8705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1369b69b6da4926d249a6d24d249a6924da492492492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record012 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record012 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record012.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record012.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record012.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 45), (facetIndex 46), (facetIndex 58), (facetIndex 59), (facetIndex 71), (facetIndex 72)]))
 (.leaf ([(facetIndex 34), (facetIndex 48), (facetIndex 51), (facetIndex 52), (facetIndex 53), (facetIndex 56)])))
 (.branch 3
 (.leaf ([(facetIndex 31), (facetIndex 63), (facetIndex 64), (facetIndex 65), (facetIndex 68), (facetIndex 70)]))
 (.leaf ([(facetIndex 30), (facetIndex 76), (facetIndex 78), (facetIndex 80), (facetIndex 90)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 35), (facetIndex 60), (facetIndex 77), (facetIndex 79), (facetIndex 86), (facetIndex 93)]))
 (.leaf ([(facetIndex 32), (facetIndex 33), (facetIndex 36), (facetIndex 37), (facetIndex 40), (facetIndex 41), (facetIndex 42), (facetIndex 43), (facetIndex 44)])))
 (.branch 7
 (.leaf ([(facetIndex 38), (facetIndex 39), (facetIndex 61)]))
 (.leaf ([(facetIndex 47), (facetIndex 54), (facetIndex 73)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "200c01000038e30380820124340011c9201e05b6ddad86d4cz16;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 74), (facetIndex 75)]))
 (.branch 2
 (.leaf ([(facetIndex 49), (facetIndex 50), (facetIndex 55), (facetIndex 57)]))
 (.leaf ([(facetIndex 62), (facetIndex 66), (facetIndex 67), (facetIndex 69)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 82), (facetIndex 83), (facetIndex 87), (facetIndex 89)]))
 (.leaf ([(facetIndex 81), (facetIndex 84), (facetIndex 85), (facetIndex 88)])))
 (.branch 6
 (.leaf ([(facetIndex 91)]))
 (.leaf ([(facetIndex 92)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6a1c6246e0000000010480080008200048z24;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4, 5]
def grouped2_0003 : List Nat := [4, 5, 6, 7]
def grouped2_0004 : List Nat := [6]
def grouped2_0005 : List Nat := [6, 7]
def grouped2_0006 : List Nat := [7]
def grouped3_0007 : List Nat := [0]
def grouped3_0008 : List Nat := [0, 1, 2]
def grouped3_0010 : List Nat := [1]
def grouped3_0011 : List Nat := [1, 2]
def grouped3_0012 : List Nat := [2]
def grouped3_0013 : List Nat := [3]
def grouped3_0014 : List Nat := [3, 4]
def grouped3_0015 : List Nat := [3, 4, 5, 6]
def grouped3_0016 : List Nat := [4]
def grouped3_0017 : List Nat := [5, 6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record012 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record012_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record012" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0005\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record012" 39

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record012" "{\"ridges\":[[11,546],[18,577],[39,546],[41,580],[48,546],[50,586],[53,546],[56,546],[57,834],[62,556],[65,577],[67,564],[68,577],[69,676],[70,577],[74,616],[75,624],[83,586],[87,594],[89,834]],\"owners\":[[11,546,[81,85,88],[39,48,53,56]],[39,546,[],[11,48,53,56,81,85,88]],[48,546,[85,88],[11,39,53,56,81]],[53,546,[81,88],[11,39,48,56,85]],[56,546,[81,85],[11,39,48,53,88]],[18,577,[50,55,57,74,75],[41,65,68,70]],[65,577,[55,57,75],[18,41,50,68,70,74]],[68,577,[50,57,74],[18,41,55,65,70,75]],[70,577,[50,55,74,75],[18,41,57,65,68]],[41,580,[],[18,65,68,70,83,87,89]],[50,586,[83],[]],[83,586,[50],[]],[87,594,[55],[]],[57,834,[89],[]],[89,834,[57],[]],[62,556,[81],[]],[67,564,[85],[]],[69,676,[88],[]],[74,616,[],[]],[75,624,[],[]]],\"edges\":[[38,[11,39,48,53,56,62,67,69,74,75,81,85,88]],[41,[18,41,50,55,57,65,68,70,74,75,83,87,89]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record012" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record012\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-7,-6],[-10,-5],[-10,-9],[-13,-7],[-19,-10],[-22,-7],[-1,22,24,26],[-3],[-6,24,26],[-8,22,26],[-11,22,24],[-2,7,10,12,20,21],[-14,10,12,21],[-16,7,12,20],[-18,7,10,20,21],[-4],[-7,23],[-23,7],[-25,10],[-12,27],[-27,12],[-13,22],[-15,24],[-17,26],[-20],[-21],[-28,5,9,19],[-29,28],[-30,29],[-31,30],[31],[-7,32],[-10,32],[-12,32],[-23,33],[-27,33],[-22,34],[-24,34],[-26,34],[-32,35],[-35,36],[-33,-34,37],[-37,38],[-36,-38,39],[-39],[1,3,6,8,11,13,15,17,20,21,22,24,26],[2,4,7,10,12,14,16,18,20,21,23,25,27]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":50,\"b\":48},{\"tag\":\"incompatible\",\"a\":55,\"b\":47},{\"tag\":\"incompatible\",\"a\":55,\"b\":54},{\"tag\":\"incompatible\",\"a\":62,\"b\":50},{\"tag\":\"incompatible\",\"a\":73,\"b\":55},{\"tag\":\"incompatible\",\"a\":81,\"b\":50},{\"tag\":\"mate\",\"ridge\":546,\"a\":11,\"owners\":[81,85,88]},{\"tag\":\"mate\",\"ridge\":546,\"a\":39,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":546,\"a\":48,\"owners\":[85,88]},{\"tag\":\"mate\",\"ridge\":546,\"a\":53,\"owners\":[81,88]},{\"tag\":\"mate\",\"ridge\":546,\"a\":56,\"owners\":[81,85]},{\"tag\":\"mate\",\"ridge\":577,\"a\":18,\"owners\":[50,55,57,74,75]},{\"tag\":\"mate\",\"ridge\":577,\"a\":65,\"owners\":[55,57,75]},{\"tag\":\"mate\",\"ridge\":577,\"a\":68,\"owners\":[50,57,74]},{\"tag\":\"mate\",\"ridge\":577,\"a\":70,\"owners\":[50,55,74,75]},{\"tag\":\"mate\",\"ridge\":580,\"a\":41,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":586,\"a\":50,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":586,\"a\":83,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":594,\"a\":87,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":834,\"a\":57,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":834,\"a\":89,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":556,\"a\":62,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":564,\"a\":67,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":676,\"a\":69,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":616,\"a\":74,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":624,\"a\":75,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[47,54,73],\"full_literals\":[-28,5,9,19]},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0004\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0005\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-29,false,28],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-30,false,29],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0003\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-31,false,30],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":50,\"full_literals\":[-7,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":55,\"full_literals\":[-10,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":57,\"full_literals\":[-12,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":83,\"full_literals\":[-23,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":89,\"full_literals\":[-27,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":81,\"full_literals\":[-22,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":85,\"full_literals\":[-24,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":88,\"full_literals\":[-26,34]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-32,false,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-35,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-33,-34,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-37,false,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-36,-38,39],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":38,\"owners\":[11,39,48,53,56,62,67,69,74,75,81,85,88]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[18,41,50,55,57,65,68,70,74,75,83,87,89]}]}"
  "48 30 0 31 30 0\n49 29 0 48 29 0\n50 28 0 49 28 0\n51 1 6 8 11 13 15 17 22 24 26 0 8 25 26 46 0\n52 2 7 10 12 14 16 18 23 25 27 0 16 25 26 47 0\n53 7 12 10 0 26 25 12 14 15 18 19 21 13 52 0\n54 32 0 32 33 34 53 0\n55 35 0 54 40 0\n56 36 0 55 41 0\n57 -38 0 56 45 44 0\n58 -37 0 57 43 0\n59 -7 0 58 1 4 6 17 35 42 38 39 23 11 7 24 10 51 0\n60 -10 0 50 2 3 5 27 0\n61 12 0 60 59 53 0\n62 27 0 61 20 0\n63 33 0 62 36 0\n64 -34 0 63 58 42 0\n65 -22 0 64 37 0\n66 -24 0 64 38 0\n67 -26 0 64 39 0\n68 -13 0 65 22 0\n69 -6 0 66 67 9 0\n70 -15 0 66 23 0\n71 -11 0 66 65 11 0\n72 -1 0 66 65 67 7 0\n73 -17 0 67 24 0\n74 -8 0 67 65 10 0\n75 0 74 71 72 69 68 70 73 65 66 67 51 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record012.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record012.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record012.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record012.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record012 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record012.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record012.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record012.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record012.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record012 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record012_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record012 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record012_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record012_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record012

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record013
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ab25c5715a999569394e8b91e2785e0fb49aa659566a5996555568d9354d8751d2745d0f66362e4b52e2b4ac9b16c3b91d4731e2719d1725c3783d0f13e2c2b1522a91a298562382e079518a4a946645894a51560d2342d0754328d1314d0b22c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "4da69b4924d34924934924d3492492492492449249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record013 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record013 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record013.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record013.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record013.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 55), (facetIndex 62), (facetIndex 66), (facetIndex 69), (facetIndex 83)]))
 (.leaf ([(facetIndex 36), (facetIndex 37), (facetIndex 46), (facetIndex 48), (facetIndex 49), (facetIndex 50), (facetIndex 53)])))
 (.branch 3
 (.leaf ([(facetIndex 59), (facetIndex 61), (facetIndex 64), (facetIndex 65)]))
 (.leaf ([(facetIndex 40), (facetIndex 44), (facetIndex 47), (facetIndex 58), (facetIndex 63), (facetIndex 74), (facetIndex 78)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 35), (facetIndex 51), (facetIndex 56), (facetIndex 67), (facetIndex 72), (facetIndex 80)]))
 (.leaf ([(facetIndex 71), (facetIndex 73), (facetIndex 75)])))
 (.branch 7
 (.leaf ([(facetIndex 38), (facetIndex 39), (facetIndex 41), (facetIndex 42), (facetIndex 43), (facetIndex 45)]))
 (.leaf ([(facetIndex 57)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "40c0aeca008126104fc008849673db3d898z1a;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4]
def grouped2_0003 : List Nat := [4, 5]
def grouped2_0004 : List Nat := [4, 5, 6, 7]
def grouped2_0005 : List Nat := [5]
def grouped2_0006 : List Nat := [6]
def grouped2_0007 : List Nat := [6, 7]
def grouped2_0008 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record013 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record013_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record013" "{\"atoms\":[{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record013" 32

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record013" "{\"ridges\":[[23,521],[34,524],[50,521],[52,586],[69,521],[70,840],[75,524],[82,600]],\"owners\":[[23,521,[16,37,52,59,61,62,68,70],[50,69]],[50,521,[16,59,61,62,68,70],[23,37,52,69]],[69,521,[16,37,52,59,61,68,70],[23,50,62]],[34,524,[16,37,59,61,62,77,82],[75,83]],[75,524,[16,59,61,62,82],[34,37,77,83]],[52,586,[77],[]],[82,600,[68],[]],[70,840,[],[]]],\"edges\":[[29,[16,23,34,37,50,52,59,61,62,68,69,70,75,77,82,83]]],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record013" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record013\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-10,-1],[-10,-4],[-10,-5],[-10,-9],[-11,-10],[-12,-10],[-13,-10],[-15,-7],[-15,-14],[-19,-15],[-20,-10],[-22,-18],[-23,-15],[-25,-18],[-2,1,5,8,11,12,13,15,17],[-6,1,11,12,13,15,17],[-16,1,5,8,11,12,15,17],[-3,1,5,11,12,13,22,24],[-21,1,11,12,13,24],[-8,22],[-24,15],[-17],[-26,4,7,9,14,19,23],[-27,18,20,21],[-28,10],[-29,26],[-29,27],[-30,28],[-31,29],[-31,30],[-32,31],[32],[1,2,3,5,6,8,11,12,13,15,16,17,21,22,24,25]],\"atoms\":[{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":57,\"b\":16},{\"tag\":\"incompatible\",\"a\":57,\"b\":35},{\"tag\":\"incompatible\",\"a\":57,\"b\":37},{\"tag\":\"incompatible\",\"a\":57,\"b\":56},{\"tag\":\"incompatible\",\"a\":59,\"b\":57},{\"tag\":\"incompatible\",\"a\":61,\"b\":57},{\"tag\":\"incompatible\",\"a\":62,\"b\":57},{\"tag\":\"incompatible\",\"a\":68,\"b\":51},{\"tag\":\"incompatible\",\"a\":68,\"b\":67},{\"tag\":\"incompatible\",\"a\":72,\"b\":68},{\"tag\":\"incompatible\",\"a\":73,\"b\":57},{\"tag\":\"incompatible\",\"a\":77,\"b\":71},{\"tag\":\"incompatible\",\"a\":80,\"b\":68},{\"tag\":\"incompatible\",\"a\":83,\"b\":71},{\"tag\":\"mate\",\"ridge\":521,\"a\":23,\"owners\":[16,37,52,59,61,62,68,70]},{\"tag\":\"mate\",\"ridge\":521,\"a\":50,\"owners\":[16,59,61,62,68,70]},{\"tag\":\"mate\",\"ridge\":521,\"a\":69,\"owners\":[16,37,52,59,61,68,70]},{\"tag\":\"mate\",\"ridge\":524,\"a\":34,\"owners\":[16,37,59,61,62,77,82]},{\"tag\":\"mate\",\"ridge\":524,\"a\":75,\"owners\":[16,59,61,62,82]},{\"tag\":\"mate\",\"ridge\":586,\"a\":52,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":600,\"a\":82,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":840,\"a\":70,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[35,51,56,67,72,80],\"full_literals\":[-26,4,7,9,14,19,23]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[71,73,75],\"full_literals\":[-27,18,20,21]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[57],\"full_literals\":[-28,10]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-29,26,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-29,false,27],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-30,false,28],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-31,29,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-31,false,30],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-32,false,31],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"edge\",\"edge\":29,\"owners\":[16,23,34,37,50,52,59,61,62,68,69,70,75,77,82,83]}]}"
  "34 31 0 32 31 0\n35 29 0 34 29 0\n36 30 0 34 30 0\n37 26 0 35 26 0\n38 27 0 35 27 0\n39 28 0 36 28 0\n40 10 0 39 25 0\n41 -1 0 40 1 0\n42 -4 0 40 2 0\n43 -5 0 40 3 0\n44 -9 0 40 4 0\n45 -11 0 40 5 0\n46 -12 0 40 6 0\n47 -13 0 40 7 0\n48 -20 0 40 11 0\n49 2 3 6 8 15 16 21 22 24 25 0 41 43 45 46 47 22 33 0\n50 -15 0 42 44 37 8 9 10 13 23 0\n51 -24 0 50 21 0\n52 -6 0 50 45 46 47 41 22 16 0\n53 -21 0 51 45 46 47 41 19 0\n54 18 0 53 38 48 24 0\n55 -22 0 54 12 0\n56 -25 0 54 14 0\n57 -8 0 55 20 0\n58 -3 0 55 43 45 46 47 41 51 18 0\n59 -2 0 57 43 41 45 46 47 50 22 15 0\n60 -16 0 57 43 41 45 46 50 22 17 0\n61 0 59 58 52 57 50 60 53 55 51 56 49 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record013.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record013.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record013.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record013.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record013 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record013.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record013.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record013.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record013.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record013 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record013_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record013 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record013_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record013_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00131.record013
