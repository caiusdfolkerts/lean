module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow31Part00103Frames
public import GraphInputsRow31Part00103Leaves
public import GraphInputsRow31Part00103Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00103.record003
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2f0ba2d8ae2783e2e4b52b49d0f49b31c9723c4f07cb48f2b28eaa6a5a3693a2e87ab18e6a5a56359362d8769394e4ba1e17ad13c6c93a699964d94e4b91e6c539695954d54d4b51d64d5352d8745d64cd34cc7352ccb4acab26c5b51cc749ca725c579306c8711c0f0e22c86a4683a199160d90e1382e078e12c46946439195150d50d1342d074c328c6344c930cd0b12c2b06d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db6db49249a69b69269b6924924d34db4934db492492492492492492249249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record003 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record003 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record003.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record003.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record003.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 44), (facetIndex 45), (facetIndex 50), (facetIndex 51), (facetIndex 56), (facetIndex 57), (facetIndex 58), (facetIndex 59)]))
 (.leaf ([(facetIndex 60), (facetIndex 61), (facetIndex 83), (facetIndex 84), (facetIndex 106), (facetIndex 107), (facetIndex 108), (facetIndex 109), (facetIndex 110)])))
 (.branch 3
 (.leaf ([(facetIndex 49), (facetIndex 55), (facetIndex 63), (facetIndex 86)]))
 (.leaf ([(facetIndex 64), (facetIndex 87), (facetIndex 111)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 46), (facetIndex 48), (facetIndex 66), (facetIndex 71), (facetIndex 89), (facetIndex 94)]))
 (.leaf ([(facetIndex 52), (facetIndex 54), (facetIndex 74), (facetIndex 79), (facetIndex 97), (facetIndex 102)])))
 (.branch 7
 (.leaf ([(facetIndex 47), (facetIndex 53), (facetIndex 62), (facetIndex 67), (facetIndex 75), (facetIndex 85), (facetIndex 90), (facetIndex 98)]))
 (.leaf ([(facetIndex 65), (facetIndex 73), (facetIndex 81), (facetIndex 88), (facetIndex 96), (facetIndex 104)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6492471401af1001a76b1238a00d78800d3b589000575014dz23;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 69), (facetIndex 70), (facetIndex 78)]))
 (.leaf ([(facetIndex 72), (facetIndex 77), (facetIndex 80)])))
 (.branch 3
 (.leaf ([(facetIndex 92), (facetIndex 93), (facetIndex 101)]))
 (.branch 4
 (.leaf ([(facetIndex 95), (facetIndex 100), (facetIndex 103)]))
 (.leaf ([(facetIndex 113), (facetIndex 114), (facetIndex 119)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 116), (facetIndex 118), (facetIndex 121)]))
 (.leaf ([(facetIndex 68), (facetIndex 76), (facetIndex 82), (facetIndex 105), (facetIndex 122)])))
 (.branch 8
 (.leaf ([(facetIndex 91), (facetIndex 99)]))
 (.branch 9
 (.leaf ([(facetIndex 112), (facetIndex 117)]))
 (.leaf ([(facetIndex 115), (facetIndex 120)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "6594585944800000060302370003022700000000601001600010006z44;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4]
def grouped2_0003 : List Nat := [4, 5]
def grouped2_0004 : List Nat := [4, 5, 6, 7]
def grouped2_0005 : List Nat := [5]
def grouped2_0006 : List Nat := [6]
def grouped2_0007 : List Nat := [6, 7]
def grouped2_0008 : List Nat := [7]
def grouped3_0009 : List Nat := [0]
def grouped3_0010 : List Nat := [0, 1]
def grouped3_0011 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0013 : List Nat := [1]
def grouped3_0014 : List Nat := [2]
def grouped3_0015 : List Nat := [2, 3, 4]
def grouped3_0016 : List Nat := [3]
def grouped3_0017 : List Nat := [3, 4]
def grouped3_0018 : List Nat := [4]
def grouped3_0019 : List Nat := [5]
def grouped3_0020 : List Nat := [5, 6]
def grouped3_0021 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0022 : List Nat := [6]
def grouped3_0023 : List Nat := [7]
def grouped3_0024 : List Nat := [7, 8, 9]
def grouped3_0025 : List Nat := [8]
def grouped3_0026 : List Nat := [8, 9]
def grouped3_0027 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record003 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record003_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00103.record003" "{\"atoms\":[{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"facet\",\"index\":116},{\"tag\":\"facet\",\"index\":117},{\"tag\":\"facet\",\"index\":118},{\"tag\":\"facet\",\"index\":119},{\"tag\":\"facet\",\"index\":120},{\"tag\":\"facet\",\"index\":121},{\"tag\":\"facet\",\"index\":122},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00103.record003" 77

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00103.record003" "{\"ridges\":[[68,212],[70,656],[72,704],[76,216],[78,656],[80,704],[82,656],[82,704],[91,212],[93,646],[93,656],[95,646],[99,216],[101,650],[101,656],[103,650],[105,594],[105,704],[112,212],[114,656],[114,676],[115,212],[115,656],[116,676],[116,704],[117,216],[119,656],[119,680],[120,216],[120,656],[121,680],[121,704],[122,624],[122,704]],\"owners\":[[68,212,[91,112,115],[]],[91,212,[68,112,115],[]],[112,212,[68,91,115],[]],[115,212,[68,91,112],[]],[70,656,[101,105,119,120,122],[78,82,93,114,115]],[78,656,[93,105,114,115,122],[70,82,101,119,120]],[82,656,[93,101,114,119],[70,78,105,115,120,122]],[93,656,[78,82,119,120,122],[70,101,105,114,115]],[101,656,[70,82,114,115,122],[78,93,105,119,120]],[114,656,[78,82,101,105,120],[70,93,115,119,122]],[115,656,[78,101,119],[70,82,93,105,114,120,122]],[119,656,[70,82,93,105,115],[78,101,114,120,122]],[120,656,[70,93,114],[78,82,101,105,115,119,122]],[72,704,[103,105,120,121,122],[80,82,95,115,116]],[80,704,[95,105,115,116,122],[72,82,103,120,121]],[82,704,[95,103,116,121],[72,80,105,115,120,122]],[105,704,[72,80,116,121],[82,95,103,115,120,122]],[116,704,[80,82,103,105,120],[72,95,115,121,122]],[121,704,[72,82,95,105,115],[80,103,116,120,122]],[122,704,[72,80,95,103],[82,105,115,116,120,121]],[76,216,[99,117,120],[]],[99,216,[76,117,120],[]],[117,216,[76,99,120],[]],[120,216,[76,99,117],[]],[105,594,[92,100],[]],[93,646,[95],[]],[95,646,[93],[]],[101,650,[103],[]],[103,650,[101],[]],[122,624,[113,118],[]],[114,676,[116],[]],[116,676,[114],[]],[119,680,[121],[]],[121,680,[119],[]]],\"edges\":[[43,[70,72,78,80,82,93,95,101,103,105,114,115,116,119,120,121,122]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00103.record003" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00103.record003\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-25,-1],[-25,-2],[-25,-6],[-25,-9],[-25,-20],[-25,-24],[-32,-3],[-32,-4],[-32,-12],[-32,-15],[-32,-27],[-32,-31],[-34,-5],[-34,-11],[-34,-17],[-34,-19],[-34,-26],[-34,-33],[-7,21,35,38],[-21,7,35,38],[-35,7,21,38],[-38,7,21,35],[-8,30,34,42,43,45],[-14,23,34,37,38,45],[-18,23,30,37,42],[-23,14,18,42,43,45],[-30,8,18,37,38,45],[-37,14,18,30,34,43],[-38,14,30,42],[-42,8,18,23,34,38],[-43,8,23,37],[-10,32,34,43,44,45],[-16,25,34,38,39,45],[-18,25,32,39,44],[-34,10,16,39,44],[-39,16,18,32,34,43],[-44,10,18,25,34,38],[-45,10,16,25,32],[-13,28,40,43],[-28,13,40,43],[-40,13,28,43],[-43,13,28,40],[-34,22,29],[-23,25],[-25,23],[-30,32],[-32,30],[-45,36,41],[-37,39],[-39,37],[-42,44],[-44,42],[-46,1,2,6,9,20,24],[-47,3,4,12,15,27,31],[-48,5,11,17,19,26,33],[-49,46],[-49,47],[-50,48],[-51,49],[-51,50],[-52,51],[52],[-8,53],[-14,53],[-10,54],[-16,54],[-22,55],[-23,55],[-30,55],[-25,56],[-29,56],[-32,56],[-36,57],[-37,57],[-42,57],[-39,58],[-41,58],[-44,58],[-59,7,13,18,34,45],[-7,59],[-13,59],[-18,59],[-34,59],[-45,59],[-60,21,28],[-21,60],[-28,60],[-61,35,40],[-35,61],[-40,61],[-62,38,43],[-38,62],[-43,62],[-54,63],[-53,63],[-57,64],[-56,64],[-64,65],[-55,65],[-55,-64,66],[-65,67],[-66,68],[-63,67],[-63,-65,68],[-59,69],[-58,69],[-58,-59,70],[-71,61,62],[-62,71],[-61,71],[-61,-62,72],[-73,60,71],[-71,73],[-72,74],[-60,73],[-60,-71,74],[-74,76],[-69,75],[-69,-73,76],[-70,76],[-67,-76,77],[-68,-75,77],[-77],[8,10,14,16,18,23,25,30,32,34,37,38,39,42,43,44,45]],\"atoms\":[{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"facet\",\"index\":116},{\"tag\":\"facet\",\"index\":117},{\"tag\":\"facet\",\"index\":118},{\"tag\":\"facet\",\"index\":119},{\"tag\":\"facet\",\"index\":120},{\"tag\":\"facet\",\"index\":121},{\"tag\":\"facet\",\"index\":122},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":95,\"b\":46},{\"tag\":\"incompatible\",\"a\":95,\"b\":48},{\"tag\":\"incompatible\",\"a\":95,\"b\":66},{\"tag\":\"incompatible\",\"a\":95,\"b\":71},{\"tag\":\"incompatible\",\"a\":95,\"b\":89},{\"tag\":\"incompatible\",\"a\":95,\"b\":94},{\"tag\":\"incompatible\",\"a\":103,\"b\":52},{\"tag\":\"incompatible\",\"a\":103,\"b\":54},{\"tag\":\"incompatible\",\"a\":103,\"b\":74},{\"tag\":\"incompatible\",\"a\":103,\"b\":79},{\"tag\":\"incompatible\",\"a\":103,\"b\":97},{\"tag\":\"incompatible\",\"a\":103,\"b\":102},{\"tag\":\"incompatible\",\"a\":105,\"b\":65},{\"tag\":\"incompatible\",\"a\":105,\"b\":73},{\"tag\":\"incompatible\",\"a\":105,\"b\":81},{\"tag\":\"incompatible\",\"a\":105,\"b\":88},{\"tag\":\"incompatible\",\"a\":105,\"b\":96},{\"tag\":\"incompatible\",\"a\":105,\"b\":104},{\"tag\":\"mate\",\"ridge\":212,\"a\":68,\"owners\":[91,112,115]},{\"tag\":\"mate\",\"ridge\":212,\"a\":91,\"owners\":[68,112,115]},{\"tag\":\"mate\",\"ridge\":212,\"a\":112,\"owners\":[68,91,115]},{\"tag\":\"mate\",\"ridge\":212,\"a\":115,\"owners\":[68,91,112]},{\"tag\":\"mate\",\"ridge\":656,\"a\":70,\"owners\":[101,105,119,120,122]},{\"tag\":\"mate\",\"ridge\":656,\"a\":78,\"owners\":[93,105,114,115,122]},{\"tag\":\"mate\",\"ridge\":656,\"a\":82,\"owners\":[93,101,114,119]},{\"tag\":\"mate\",\"ridge\":656,\"a\":93,\"owners\":[78,82,119,120,122]},{\"tag\":\"mate\",\"ridge\":656,\"a\":101,\"owners\":[70,82,114,115,122]},{\"tag\":\"mate\",\"ridge\":656,\"a\":114,\"owners\":[78,82,101,105,120]},{\"tag\":\"mate\",\"ridge\":656,\"a\":115,\"owners\":[78,101,119]},{\"tag\":\"mate\",\"ridge\":656,\"a\":119,\"owners\":[70,82,93,105,115]},{\"tag\":\"mate\",\"ridge\":656,\"a\":120,\"owners\":[70,93,114]},{\"tag\":\"mate\",\"ridge\":704,\"a\":72,\"owners\":[103,105,120,121,122]},{\"tag\":\"mate\",\"ridge\":704,\"a\":80,\"owners\":[95,105,115,116,122]},{\"tag\":\"mate\",\"ridge\":704,\"a\":82,\"owners\":[95,103,116,121]},{\"tag\":\"mate\",\"ridge\":704,\"a\":105,\"owners\":[72,80,116,121]},{\"tag\":\"mate\",\"ridge\":704,\"a\":116,\"owners\":[80,82,103,105,120]},{\"tag\":\"mate\",\"ridge\":704,\"a\":121,\"owners\":[72,82,95,105,115]},{\"tag\":\"mate\",\"ridge\":704,\"a\":122,\"owners\":[72,80,95,103]},{\"tag\":\"mate\",\"ridge\":216,\"a\":76,\"owners\":[99,117,120]},{\"tag\":\"mate\",\"ridge\":216,\"a\":99,\"owners\":[76,117,120]},{\"tag\":\"mate\",\"ridge\":216,\"a\":117,\"owners\":[76,99,120]},{\"tag\":\"mate\",\"ridge\":216,\"a\":120,\"owners\":[76,99,117]},{\"tag\":\"mate\",\"ridge\":594,\"a\":105,\"owners\":[92,100]},{\"tag\":\"mate\",\"ridge\":646,\"a\":93,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":646,\"a\":95,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":650,\"a\":101,\"owners\":[103]},{\"tag\":\"mate\",\"ridge\":650,\"a\":103,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":624,\"a\":122,\"owners\":[113,118]},{\"tag\":\"mate\",\"ridge\":676,\"a\":114,\"owners\":[116]},{\"tag\":\"mate\",\"ridge\":676,\"a\":116,\"owners\":[114]},{\"tag\":\"mate\",\"ridge\":680,\"a\":119,\"owners\":[121]},{\"tag\":\"mate\",\"ridge\":680,\"a\":121,\"owners\":[119]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[46,48,66,71,89,94],\"full_literals\":[-46,1,2,6,9,20,24]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[52,54,74,79,97,102],\"full_literals\":[-47,3,4,12,15,27,31]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[65,73,81,88,96,104],\"full_literals\":[-48,5,11,17,19,26,33]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-49,46,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-49,false,47],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-50,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-51,49,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-51,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-52,false,51],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":70,\"full_literals\":[-8,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":78,\"full_literals\":[-14,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":72,\"full_literals\":[-10,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":80,\"full_literals\":[-16,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":92,\"full_literals\":[-22,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":93,\"full_literals\":[-23,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":101,\"full_literals\":[-30,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":95,\"full_literals\":[-25,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":100,\"full_literals\":[-29,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":103,\"full_literals\":[-32,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":113,\"full_literals\":[-36,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":114,\"full_literals\":[-37,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":119,\"full_literals\":[-42,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":116,\"full_literals\":[-39,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":118,\"full_literals\":[-41,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":121,\"full_literals\":[-44,58]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[68,76,82,105,122],\"full_literals\":[-59,7,13,18,34,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":68,\"full_literals\":[-7,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":76,\"full_literals\":[-13,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":82,\"full_literals\":[-18,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":105,\"full_literals\":[-34,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":122,\"full_literals\":[-45,59]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[91,99],\"full_literals\":[-60,21,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":91,\"full_literals\":[-21,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":99,\"full_literals\":[-28,60]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[112,117],\"full_literals\":[-61,35,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":112,\"full_literals\":[-35,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":117,\"full_literals\":[-40,61]},{\"tag\":\"group_or\",\"kind\":3,\"index\":9,\"members\":[115,120],\"full_literals\":[-62,38,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":115,\"full_literals\":[-38,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":120,\"full_literals\":[-43,62]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-54,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-57,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-56,false,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-64,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-55,false,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-55,-64,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-65,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-66,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-63,-65,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-59,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-58,false,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-58,-59,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-71,61,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-62,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-61,false,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-61,-62,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-73,60,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-71,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-72,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-60,false,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-60,-71,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-74,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-69,false,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-69,-73,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-70,false,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-67,-76,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-68,-75,77],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":43,\"owners\":[70,72,78,80,82,93,95,101,103,105,114,115,116,119,120,121,122]}]}"
  "125 51 0 62 61 0\n126 49 0 125 59 0\n127 50 0 125 60 0\n128 46 0 126 56 0\n129 47 0 126 57 0\n130 48 0 127 58 0\n131 67 0 101 103 98 99 94 95 96 97 67 68 69 65 66 63 64 74 75 70 71 72 43 25 38 31 29 50 52 124 0\n132 -76 0 131 123 121 0\n133 -74 0 132 117 0\n134 -70 0 132 120 0\n135 -72 0 133 114 0\n136 62 -71 59 0 133 116 87 86 81 80 92 93 108 21 41 88 0\n137 -71 59 0 133 135 81 80 116 86 87 136 111 89 90 22 42 91 0\n138 -73 0 132 119 105 80 81 137 109 110 112 92 93 89 90 20 40 85 0\n139 -71 0 138 113 0\n140 -60 0 138 115 0\n141 -62 0 139 109 0\n142 -61 0 139 110 0\n143 -21 0 140 86 0\n144 -28 0 140 87 0\n145 -38 0 141 92 0\n146 -43 0 141 93 0\n147 -35 0 142 89 0\n148 -40 0 142 90 0\n149 -7 0 143 147 145 19 0\n150 -13 0 144 148 146 39 0\n151 65 59 0 146 145 84 83 82 98 99 96 97 68 69 74 75 70 72 24 23 50 52 33 32 124 0\n152 64 14 8 16 10 45 34 18 0 146 145 96 97 74 75 70 72 50 27 52 26 124 0\n153 59 68 0 146 145 102 82 83 84 151 104 94 95 65 66 63 64 152 100 68 69 45 30 47 28 37 36 124 0\n154 -64 68 0 134 150 149 153 107 78 51 76 49 102 98 100 104 68 69 94 25 45 47 65 66 35 38 79 0\n155 -34 0 130 13 14 15 16 17 18 55 0\n156 -59 0 134 123 155 150 149 105 107 118 76 77 78 122 154 96 97 73 70 72 48 34 79 0\n157 -18 0 156 82 0\n158 -45 0 156 84 0\n159 68 0 156 153 0\n160 -75 0 159 123 122 0\n161 -69 0 160 118 0\n162 -58 0 161 106 0\n163 -39 0 162 76 0\n164 -44 0 162 78 0\n165 -37 0 163 49 0\n166 -42 0 164 51 0\n167 25 32 0 164 146 166 163 158 165 155 157 145 46 23 32 44 33 24 124 0\n168 -25 0 128 1 2 3 4 5 6 53 0\n169 32 0 168 167 0\n170 -3 0 169 7 0\n171 -4 0 169 8 0\n172 -12 0 169 9 0\n173 -15 0 169 10 0\n174 -27 0 169 11 0\n175 -31 0 169 12 0\n176 0 172 173 129 171 170 174 175 54 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record003.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record003.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record003.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record003.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record003 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record003.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record003.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record003.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record003.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record003 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record003_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record003 Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record003_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record003_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00103.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00103.record008
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2b89e29c9713c2f07ca6a5a4e8ba1e8e6659361d94e4b8ae2785eb86b19c6a99a719a66598e5392e479b14e5a5595955351d68d9354d4b4ad8749d176c338e9364e534cc73a2e4b52d2b2ae1b26c5b61d4731d2715c8f2d06c4703c2c86a4683a29866458960d90e1382e07a912c6491a6194643929465454950d50d1342d074a318d1324c3342c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36da49b49249249269b49249269269349249349349a492492492249249249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record008 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record008 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record008.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record008.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record008.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 68), (facetIndex 83), (facetIndex 95)]))
 (.leaf ([(facetIndex 61), (facetIndex 76), (facetIndex 92)])))
 (.branch 3
 (.leaf ([(facetIndex 64), (facetIndex 79), (facetIndex 93)]))
 (.branch 4
 (.leaf ([(facetIndex 109), (facetIndex 114), (facetIndex 116)]))
 (.leaf ([(facetIndex 108), (facetIndex 113), (facetIndex 115)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "38e001c000000000011000000000401000000002008z2d;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 5
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0003 : List Nat := [1]
def grouped3_0004 : List Nat := [2]
def grouped3_0005 : List Nat := [2, 3, 4]
def grouped3_0006 : List Nat := [3]
def grouped3_0007 : List Nat := [3, 4]
def grouped3_0008 : List Nat := [4]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record008 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record008_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00103.record008" "{\"atoms\":[{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"facet\",\"index\":116},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0005\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00103.record008" 32

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00103.record008" "{\"ridges\":[[28,577],[30,641],[60,577],[64,594],[66,641],[68,706],[75,577],[79,596],[81,641],[83,708],[88,584],[89,656],[91,577],[93,624],[94,641],[95,736],[108,594],[109,650],[113,596],[114,652],[115,624],[116,680]],\"owners\":[[28,577,[64,68,79,83,93,95],[60,75,88,91]],[60,577,[79,83,93,95],[28,64,68,75,88,91]],[75,577,[64,68,93,95],[28,60,79,83,88,91]],[91,577,[64,68,79,83],[28,60,75,88,93,95]],[88,584,[],[28,60,75,91,108,113,115]],[30,641,[61,68,76,83,92,95],[66,81,89,94]],[66,641,[76,83,92,95],[30,61,68,81,89,94]],[81,641,[61,68,92,95],[30,66,76,83,89,94]],[94,641,[61,68,76,83],[30,66,81,89,92,95]],[89,656,[],[30,66,81,94,109,114,116]],[109,650,[61],[]],[64,594,[108],[]],[108,594,[64],[]],[68,706,[],[]],[114,652,[76],[]],[79,596,[113],[]],[113,596,[79],[]],[83,708,[],[]],[116,680,[92],[]],[93,624,[115],[]],[115,624,[93],[]],[95,736,[],[]]],\"edges\":[[41,[28,60,64,68,75,79,83,88,91,93,95,108,113,115]],[43,[30,61,66,68,76,81,83,89,92,94,95,109,114,116]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00103.record008" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00103.record008\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,5,7,10,12,17,19],[-3,10,12,17,19],[-8,5,7,17,19],[-15,5,7,10,12],[-13],[-2,4,7,9,12,16,19],[-6,9,12,16,19],[-11,4,7,16,19],[-18,4,7,9,12],[-14],[-21,4],[-5,20],[-20,5],[-7],[-23,9],[-10,22],[-22,10],[-12],[-25,16],[-17,24],[-24,17],[-19],[-4,26],[-9,26],[-16,26],[-27,5,10,17],[-5,27],[-10,27],[-17,27],[-20,28],[-22,28],[-24,28],[-26,29],[-28,30],[-27,-30,31],[-29,-31,32],[-32],[1,3,5,7,8,10,12,13,15,17,19,20,22,24],[2,4,6,7,9,11,12,14,16,18,19,21,23,25]],\"atoms\":[{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"facet\",\"index\":116},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":577,\"a\":28,\"owners\":[64,68,79,83,93,95]},{\"tag\":\"mate\",\"ridge\":577,\"a\":60,\"owners\":[79,83,93,95]},{\"tag\":\"mate\",\"ridge\":577,\"a\":75,\"owners\":[64,68,93,95]},{\"tag\":\"mate\",\"ridge\":577,\"a\":91,\"owners\":[64,68,79,83]},{\"tag\":\"mate\",\"ridge\":584,\"a\":88,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":641,\"a\":30,\"owners\":[61,68,76,83,92,95]},{\"tag\":\"mate\",\"ridge\":641,\"a\":66,\"owners\":[76,83,92,95]},{\"tag\":\"mate\",\"ridge\":641,\"a\":81,\"owners\":[61,68,92,95]},{\"tag\":\"mate\",\"ridge\":641,\"a\":94,\"owners\":[61,68,76,83]},{\"tag\":\"mate\",\"ridge\":656,\"a\":89,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":650,\"a\":109,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":594,\"a\":64,\"owners\":[108]},{\"tag\":\"mate\",\"ridge\":594,\"a\":108,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":706,\"a\":68,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":652,\"a\":114,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":596,\"a\":79,\"owners\":[113]},{\"tag\":\"mate\",\"ridge\":596,\"a\":113,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":708,\"a\":83,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":680,\"a\":116,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":624,\"a\":93,\"owners\":[115]},{\"tag\":\"mate\",\"ridge\":624,\"a\":115,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":736,\"a\":95,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":61,\"full_literals\":[-4,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":76,\"full_literals\":[-9,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":92,\"full_literals\":[-16,26]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[64,79,93],\"full_literals\":[-27,5,10,17]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":64,\"full_literals\":[-5,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":79,\"full_literals\":[-10,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":93,\"full_literals\":[-17,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":108,\"full_literals\":[-20,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":113,\"full_literals\":[-22,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":115,\"full_literals\":[-24,28]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0003\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-26,29],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-28,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0005\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-27,-30,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-29,-31,32],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":41,\"owners\":[28,60,64,68,75,79,83,88,91,93,95,108,113,115]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[30,61,66,68,76,81,83,89,92,94,95,109,114,116]}]}"
  "40 1 3 5 8 10 15 17 20 22 24 0 14 18 5 22 38 0\n41 2 4 6 9 11 16 18 21 23 25 0 14 18 10 22 39 0\n42 26 0 22 18 14 23 24 25 11 15 9 19 8 7 6 41 0\n43 29 0 42 33 0\n44 -31 0 43 37 36 0\n45 27 0 22 18 14 27 28 29 13 17 4 21 3 2 1 40 0\n46 -30 0 45 44 35 0\n47 -28 0 46 34 0\n48 -20 0 47 30 0\n49 -22 0 47 31 0\n50 -24 0 47 32 0\n51 -5 0 48 12 0\n52 -10 0 49 16 0\n53 -17 0 50 20 0\n54 0 53 52 51 45 26 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record008.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record008.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record008.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record008.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record008 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record008.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record008.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record008.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record008.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record008 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record008_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record008 Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record008_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record008_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00103.record008
