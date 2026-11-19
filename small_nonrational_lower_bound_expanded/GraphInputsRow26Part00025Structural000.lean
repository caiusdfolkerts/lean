module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow26Part00025Frames
public import GraphInputsRow26Part00025Leaves
public import GraphInputsRow26Part00025Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00025.record043
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "f4c723c3cb1a4e8e6c58d62d876c38ce8791e0f8f1c66394e4e5c5695356352d475c364d3362d8751d0f4e3c4d9334d332cc73c2d4b32d2b86d1b0ef0729e1745c5783d0f23c1f1b06a31866258361382ec47091a4c519615254358344d0b4c318d1324c3342c4b0ac8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db69a49a6d34da492492493492492492693492492249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record043 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record043 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record043.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record043.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record043.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 33), (facetIndex 36), (facetIndex 45), (facetIndex 59), (facetIndex 76)]))
 (.leaf ([(facetIndex 34), (facetIndex 35), (facetIndex 44), (facetIndex 46), (facetIndex 47)])))
 (.branch 3
 (.leaf ([(facetIndex 57), (facetIndex 58), (facetIndex 60), (facetIndex 61)]))
 (.leaf ([(facetIndex 37), (facetIndex 38), (facetIndex 63), (facetIndex 64), (facetIndex 66), (facetIndex 67)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 32), (facetIndex 41), (facetIndex 42), (facetIndex 55), (facetIndex 71), (facetIndex 73)]))
 (.leaf ([(facetIndex 49), (facetIndex 50), (facetIndex 52), (facetIndex 53)])))
 (.branch 7
 (.leaf ([(facetIndex 39), (facetIndex 54), (facetIndex 68), (facetIndex 79), (facetIndex 82)]))
 (.leaf ([(facetIndex 48), (facetIndex 51), (facetIndex 62), (facetIndex 65), (facetIndex 78), (facetIndex 80)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "187dc00208066fb7d20909adf6f241120cd8244z18;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 72)]))
 (.leaf ([(facetIndex 85)])))
 (.branch 3
 (.leaf ([(facetIndex 88)]))
 (.leaf ([(facetIndex 40), (facetIndex 43), (facetIndex 56)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 74), (facetIndex 75), (facetIndex 77)]))
 (.leaf ([(facetIndex 81), (facetIndex 84), (facetIndex 87)])))
 (.branch 7
 (.leaf ([(facetIndex 69), (facetIndex 70)]))
 (.leaf ([(facetIndex 83), (facetIndex 86)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "2bcde280209001b0000000003000000000603z1e;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
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
def grouped2_0008 : List Nat := [4, 5, 6, 7]
def grouped2_0009 : List Nat := [5]
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7]
def grouped2_0012 : List Nat := [7]
def grouped3_0013 : List Nat := [0]
def grouped3_0014 : List Nat := [0, 1]
def grouped3_0015 : List Nat := [0, 1, 2, 3]
def grouped3_0017 : List Nat := [1]
def grouped3_0018 : List Nat := [2]
def grouped3_0019 : List Nat := [2, 3]
def grouped3_0020 : List Nat := [3]
def grouped3_0021 : List Nat := [4, 5]
def grouped3_0022 : List Nat := [4, 5, 6, 7]
def grouped3_0023 : List Nat := [6]
def grouped3_0024 : List Nat := [6, 7]
def grouped3_0025 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record043 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record043_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00025.record043" "{\"atoms\":[{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":4,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00025.record043" 77

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00025.record043" "{\"ridges\":[[7,265],[18,529],[22,521],[23,273],[34,266],[38,532],[44,265],[46,265],[47,266],[52,273],[52,274],[53,784],[60,521],[60,524],[64,529],[66,529],[67,532],[69,273],[69,312],[70,521],[70,568],[77,524],[81,274],[83,274],[83,312],[86,524],[86,568],[88,240]],\"owners\":[[7,265,[22,56,61,69,71],[34,42,44,46]],[44,265,[22,56,61,71],[7,34,42,46,69]],[46,265,[22,56,61,69,71],[7,34,42,44]],[34,266,[83,84],[7,42,44,46,47,74,77]],[47,266,[74,83],[7,34,42,44,46,77,84]],[18,529,[23,43,53,70,71],[38,57,64,66]],[64,529,[23,43,53,71],[18,38,57,66,70]],[66,529,[23,43,53,70,71],[18,38,57,64]],[38,532,[86,87],[18,57,64,66,67,75,81]],[67,532,[75,86],[18,38,57,64,66,81,87]],[53,784,[87],[23,67,71,81,84]],[69,312,[83],[]],[83,312,[69],[]],[70,568,[86],[]],[86,568,[70],[]],[88,240,[72,85],[]]],\"edges\":[[28,[7,22,34,42,44,46,47,56,61,69,71,74,77,83,84,87]],[34,[18,23,38,43,53,57,64,66,67,70,71,75,81,84,86,87]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00025.record043" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00025.record043\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-16,-8],[-21,-16],[-33,-16],[-34,-5],[-34,-9],[-34,-10],[-34,-11],[-34,-17],[-34,-20],[-34,-22],[-34,-24],[-35,-5],[-35,-9],[-35,-10],[-35,-22],[-35,-23],[-35,-24],[-35,-25],[-35,-27],[-35,-34],[-36,-34],[-36,-35],[-37,-8],[-37,-15],[-37,-18],[-37,-21],[-37,-28],[-37,-30],[-37,-33],[-38,-34],[-38,-35],[-39,-35],[-40,-34],[-42,-37],[-43,-16],[-43,-37],[-44,-37],[-46,-16],[-46,-37],[-47,-35],[-48,-34],[-48,-35],[-49,-8],[-49,-15],[-49,-18],[-49,-21],[-49,-28],[-49,-30],[-49,-33],[-49,-42],[-49,-43],[-49,-44],[-49,-46],[-51,-34],[-51,-35],[-1,3,23,27,34,36],[-12,3,23,27,36],[-13,3,23,27,34,36],[-6,47,48],[-14,39,47],[-4,-19,-34],[-19,-45,-47],[-3,-26,-35],[-26,-41,-50],[-2,4,11,20,35,36],[-29,4,11,20,36],[-31,4,11,20,35,36],[-7,50,51],[-32,40,50],[-20,51],[-34,47],[-47,34],[-35,50],[-50,35],[-52,37,49],[-53,24,25,26,27],[-54,5,9,10,22,36,38],[-55,16,17,19,20],[-56,8,21,33,43,46],[-57,15,18,28,30,42,44],[-58,53],[-59,58],[-60,54,55],[-61,54],[-62,56,57],[-63,56],[-64,60],[-64,61,63],[-65,61],[-64,62],[-66,59,65],[-66,64],[66],[-67,37],[-68,49],[-69,52],[-70,34,35],[-34,70],[-71,47,50],[-72,67,68],[-73,69],[-74,72,73],[-75,70,71],[-76,75],[-77,74,76],[77],[1,3,6,10,12,13,14,23,27,34,36,39,41,47,48,51],[2,4,7,11,20,24,29,31,32,35,36,40,45,48,50,51]],\"atoms\":[{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":49,\"b\":39},{\"tag\":\"incompatible\",\"a\":54,\"b\":49},{\"tag\":\"incompatible\",\"a\":68,\"b\":49},{\"tag\":\"incompatible\",\"a\":69,\"b\":32},{\"tag\":\"incompatible\",\"a\":69,\"b\":41},{\"tag\":\"incompatible\",\"a\":69,\"b\":42},{\"tag\":\"incompatible\",\"a\":69,\"b\":43},{\"tag\":\"incompatible\",\"a\":69,\"b\":50},{\"tag\":\"incompatible\",\"a\":69,\"b\":53},{\"tag\":\"incompatible\",\"a\":69,\"b\":55},{\"tag\":\"incompatible\",\"a\":69,\"b\":57},{\"tag\":\"incompatible\",\"a\":70,\"b\":32},{\"tag\":\"incompatible\",\"a\":70,\"b\":41},{\"tag\":\"incompatible\",\"a\":70,\"b\":42},{\"tag\":\"incompatible\",\"a\":70,\"b\":55},{\"tag\":\"incompatible\",\"a\":70,\"b\":56},{\"tag\":\"incompatible\",\"a\":70,\"b\":57},{\"tag\":\"incompatible\",\"a\":70,\"b\":58},{\"tag\":\"incompatible\",\"a\":70,\"b\":61},{\"tag\":\"incompatible\",\"a\":70,\"b\":69},{\"tag\":\"incompatible\",\"a\":71,\"b\":69},{\"tag\":\"incompatible\",\"a\":71,\"b\":70},{\"tag\":\"incompatible\",\"a\":72,\"b\":39},{\"tag\":\"incompatible\",\"a\":72,\"b\":48},{\"tag\":\"incompatible\",\"a\":72,\"b\":51},{\"tag\":\"incompatible\",\"a\":72,\"b\":54},{\"tag\":\"incompatible\",\"a\":72,\"b\":62},{\"tag\":\"incompatible\",\"a\":72,\"b\":65},{\"tag\":\"incompatible\",\"a\":72,\"b\":68},{\"tag\":\"incompatible\",\"a\":73,\"b\":69},{\"tag\":\"incompatible\",\"a\":73,\"b\":70},{\"tag\":\"incompatible\",\"a\":74,\"b\":70},{\"tag\":\"incompatible\",\"a\":75,\"b\":69},{\"tag\":\"incompatible\",\"a\":78,\"b\":72},{\"tag\":\"incompatible\",\"a\":79,\"b\":49},{\"tag\":\"incompatible\",\"a\":79,\"b\":72},{\"tag\":\"incompatible\",\"a\":80,\"b\":72},{\"tag\":\"incompatible\",\"a\":82,\"b\":49},{\"tag\":\"incompatible\",\"a\":82,\"b\":72},{\"tag\":\"incompatible\",\"a\":83,\"b\":70},{\"tag\":\"incompatible\",\"a\":84,\"b\":69},{\"tag\":\"incompatible\",\"a\":84,\"b\":70},{\"tag\":\"incompatible\",\"a\":85,\"b\":39},{\"tag\":\"incompatible\",\"a\":85,\"b\":48},{\"tag\":\"incompatible\",\"a\":85,\"b\":51},{\"tag\":\"incompatible\",\"a\":85,\"b\":54},{\"tag\":\"incompatible\",\"a\":85,\"b\":62},{\"tag\":\"incompatible\",\"a\":85,\"b\":65},{\"tag\":\"incompatible\",\"a\":85,\"b\":68},{\"tag\":\"incompatible\",\"a\":85,\"b\":78},{\"tag\":\"incompatible\",\"a\":85,\"b\":79},{\"tag\":\"incompatible\",\"a\":85,\"b\":80},{\"tag\":\"incompatible\",\"a\":85,\"b\":82},{\"tag\":\"incompatible\",\"a\":87,\"b\":69},{\"tag\":\"incompatible\",\"a\":87,\"b\":70},{\"tag\":\"mate\",\"ridge\":265,\"a\":7,\"owners\":[22,56,61,69,71]},{\"tag\":\"mate\",\"ridge\":265,\"a\":44,\"owners\":[22,56,61,71]},{\"tag\":\"mate\",\"ridge\":265,\"a\":46,\"owners\":[22,56,61,69,71]},{\"tag\":\"mate\",\"ridge\":266,\"a\":34,\"owners\":[83,84]},{\"tag\":\"mate\",\"ridge\":266,\"a\":47,\"owners\":[74,83]},{\"tag\":\"three\",\"ridge\":273,\"vertices\":[23,52,69]},{\"tag\":\"three\",\"ridge\":274,\"vertices\":[52,81,83]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[22,60,70]},{\"tag\":\"three\",\"ridge\":524,\"vertices\":[60,77,86]},{\"tag\":\"mate\",\"ridge\":529,\"a\":18,\"owners\":[23,43,53,70,71]},{\"tag\":\"mate\",\"ridge\":529,\"a\":64,\"owners\":[23,43,53,71]},{\"tag\":\"mate\",\"ridge\":529,\"a\":66,\"owners\":[23,43,53,70,71]},{\"tag\":\"mate\",\"ridge\":532,\"a\":38,\"owners\":[86,87]},{\"tag\":\"mate\",\"ridge\":532,\"a\":67,\"owners\":[75,86]},{\"tag\":\"mate\",\"ridge\":784,\"a\":53,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":312,\"a\":69,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":312,\"a\":83,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":568,\"a\":70,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":568,\"a\":86,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":240,\"a\":88,\"owners\":[72,85]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[57,58,60,61],\"full_literals\":[-53,24,25,26,27]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[32,41,42,55,71,73],\"full_literals\":[-54,5,9,10,22,36,38]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[49,50,52,53],\"full_literals\":[-55,16,17,19,20]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[39,54,68,79,82],\"full_literals\":[-56,8,21,33,43,46]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[48,51,62,65,78,80],\"full_literals\":[-57,15,18,28,30,42,44]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-58,53,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-59,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-60,54,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-61,54,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-62,56,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-63,56,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-64,60,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-64,61,63],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-65,61,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-64,false,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-66,59,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-66,false,64],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[72],\"full_literals\":[-67,37]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[85],\"full_literals\":[-68,49]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[88],\"full_literals\":[-69,52]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[69,70],\"full_literals\":[-70,34,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":69,\"full_literals\":[-34,70]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[83,86],\"full_literals\":[-71,47,50]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-72,67,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-73,69,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-74,72,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-75,70,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-76,false,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-77,74,76],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":4,\"grouped\":true},{\"tag\":\"edge\",\"edge\":28,\"owners\":[7,22,34,42,44,46,47,56,61,69,71,74,77,83,84,87]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[18,23,38,43,53,57,64,66,67,70,71,75,81,84,86,87]}]}"
  "109 64 0 93 92 0\n110 60 0 109 87 0\n111 62 0 109 90 0\n112 -16 -56 0 1 2 3 35 38 79 0\n113 -20 -70 0 9 70 97 55 0\n114 49 37 -74 0 94 95 75 100 96 102 101 0\n115 -49 -56 33 0 43 46 51 53 79 0\n116 -56 -74 33 0 115 114 23 26 36 39 79 0\n117 70 -75 50 0 98 103 72 99 0\n118 -34 -19 51 48 40 32 20 11 7 24 35 0 74 21 71 61 62 65 66 67 108 0\n119 -44 -74 0 37 52 114 0\n120 -49 15 44 -57 0 45 47 48 50 80 0\n121 15 -57 -74 0 119 120 114 25 27 28 34 80 0\n122 -57 -74 0 121 24 44 114 0\n123 -74 33 0 111 116 85 122 0\n124 -70 35 0 110 109 74 113 97 4 5 6 7 8 10 11 21 30 33 41 54 77 69 68 83 84 118 88 78 86 112 0\n125 -74 0 123 29 49 114 0\n126 76 0 125 106 105 0\n127 75 0 126 104 0\n128 35 0 127 74 124 117 0\n129 -5 0 128 12 0\n130 -9 0 128 13 0\n131 -10 0 128 14 0\n132 -22 0 128 15 0\n133 -23 0 128 16 0\n134 -24 0 128 17 0\n135 -25 0 128 18 0\n136 -27 0 128 19 0\n137 -34 0 128 20 0\n138 -36 0 128 22 0\n139 -38 0 128 31 0\n140 -39 0 128 32 0\n141 -47 0 128 40 0\n142 -48 0 128 42 0\n143 -51 0 128 55 0\n144 50 0 128 73 0\n145 -54 0 139 129 131 130 132 138 77 0\n146 -14 0 140 141 60 0\n147 -6 0 142 141 59 0\n148 -61 0 145 84 0\n149 -65 0 148 89 0\n150 59 0 149 93 91 0\n151 58 0 150 82 0\n152 53 0 151 81 0\n153 26 0 152 136 135 134 76 0\n154 -3 0 153 128 63 0\n155 -41 0 153 144 64 0\n156 -1 0 154 133 136 137 138 56 0\n157 -12 0 154 133 136 138 57 0\n158 -13 0 154 133 137 138 136 58 0\n159 0 158 154 147 131 157 138 146 156 133 140 137 136 155 141 142 143 107 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record043.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record043.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record043.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record043.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record043 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record043.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record043.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record043.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record043.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record043 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record043_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record043_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record043_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record043_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record043_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record043_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record043_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record043 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record043_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record043_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record043_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00025.record043
