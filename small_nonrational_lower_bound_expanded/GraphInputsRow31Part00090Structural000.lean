module
prelude
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow31Part00090Frames
public import GraphInputsRow31Part00090Leaves
public import GraphInputsRow31Part00090Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00090.record001
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3c2b8ad2729aa9a8ea66a5a36a3a2e9c669a6639996958d68d8b64b86e4785ef06e1b45c96a6693a599964d98e4b9715a5994e565655356352d52d1b51d17783d0ec370ea368e6338e9364e5334e332cd8b92d4b32e2b4acab1ae1b46c9b16c3b61e4751cc789d2729c6785d1725c570dd0f13c2f07eb05303cb09c2a8a928c8b25283a518364384e0b81eb05c1a86918c4b152439514354344d0b41d"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "24936db6926db6d24924926db6d24db6da4924da49b69b69369b6db6da6d36db6db492449249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090.record001 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090.record001 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090.record001.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 71), (facetIndex 87), (facetIndex 96), (facetIndex 99)]))
 (.leaf ([(facetIndex 31), (facetIndex 32), (facetIndex 33), (facetIndex 34), (facetIndex 75), (facetIndex 76), (facetIndex 77), (facetIndex 78)])))
 (.branch 3
 (.leaf ([(facetIndex 35), (facetIndex 48), (facetIndex 61), (facetIndex 62), (facetIndex 79), (facetIndex 80), (facetIndex 88), (facetIndex 89)]))
 (.leaf ([(facetIndex 100), (facetIndex 101), (facetIndex 102), (facetIndex 103)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 45), (facetIndex 58), (facetIndex 112), (facetIndex 121)]))
 (.leaf ([(facetIndex 104), (facetIndex 105), (facetIndex 113), (facetIndex 114)])))
 (.branch 7
 (.leaf ([(facetIndex 72), (facetIndex 122), (facetIndex 123), (facetIndex 124)]))
 (.leaf ([(facetIndex 66), (facetIndex 70), (facetIndex 97), (facetIndex 98)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6da000016c00002d6db1f80000120000024492061c01c00901000000020200000004492z17;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2, 3]
def grouped2_0006 : List Nat := [4]
def grouped2_0007 : List Nat := [4, 5]
def grouped2_0008 : List Nat := [4, 5, 6, 7]
def grouped2_0009 : List Nat := [5]
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7]
def grouped2_0012 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090.record001 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090.record001_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00090.record001" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":116},{\"tag\":\"facet\",\"index\":119},{\"tag\":\"facet\",\"index\":120},{\"tag\":\"facet\",\"index\":121},{\"tag\":\"facet\",\"index\":122},{\"tag\":\"facet\",\"index\":123},{\"tag\":\"facet\",\"index\":124},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00090.record001" 67

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00090.record001" "{\"ridges\":[[23,530],[61,161],[62,530],[73,771],[87,385],[96,385],[97,577],[121,386],[122,578],[123,162],[123,546],[123,578]],\"owners\":[[61,161,[11,84,86,93,95,98],[8,41,54,67,69,70,79,88]],[87,385,[60,65,69,74,92,95],[12,47,71,83,86,96,99]],[96,385,[47,65,69,74,83,86],[12,60,71,87,92,95,99]],[97,577,[46,59,68,73,85,94],[13,64,72,82,91,98,99]],[123,162,[22,41,54,61,69,104,111,113,120],[25,67,70,109,118]],[23,530,[24,39,52,64,66,107,116,122],[62,105,114]],[62,530,[24,107,116,122],[23,39,52,64,66,105,114]],[123,546,[23,43,56,62,105,114],[25,68,70,110,119]],[121,386,[47,65,69,74,108,111],[26,60,71,112,117,120,124]],[122,578,[46,59,68,73,110,119],[27,64,72,107,116,123,124]],[123,578,[46,59,64,73,107,116],[27,68,72,110,119,122,124]],[73,771,[74],[]]],\"edges\":[],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00090.record001" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00090.record001\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-9,-8],[-14,-9],[-15,-8],[-15,-14],[-16,-8],[-16,-14],[-20,-5],[-20,-7],[-20,-9],[-20,-11],[-20,-13],[-20,-15],[-21,-20],[-23,-8],[-23,-9],[-23,-14],[-23,-15],[-23,-21],[-23,-22],[-24,-20],[-24,-23],[-25,-8],[-25,-9],[-25,-14],[-25,-15],[-26,-20],[-26,-21],[-26,-23],[-26,-24],[-28,-21],[-28,-24],[-33,-8],[-33,-10],[-33,-14],[-38,-8],[-38,-12],[-38,-14],[-38,-35],[-38,-37],[-39,-1],[-39,-19],[-39,-26],[-39,-28],[-40,-22],[-40,-26],[-40,-28],[-41,-39],[-41,-40],[-43,-2],[-44,-39],[-45,-33],[-46,-40],[-47,-33],[-48,-6],[-48,-10],[-48,-25],[-48,-29],[-48,-30],[-48,-32],[-48,-33],[-48,-42],[-48,-47],[-49,-38],[-50,-2],[-51,-39],[-52,-40],[-53,-38],[-54,-16],[-54,-25],[-54,-34],[-54,-37],[-54,-38],[-55,-21],[-55,-24],[-55,-39],[-56,-4],[-56,-21],[-56,-24],[-56,-31],[-56,-36],[-56,-40],[-57,-41],[-57,-48],[-57,-54],[-17,1,30,32,35,37,40],[-33,16,20,23,28,34,37],[-38,10,20,23,28,29,32],[-39,9,15,22,27,31,36],[-56,2,6,12,17,23,42,47,49,53],[-3,4,5,11,19,21,44,51,55],[-18,4,44,51,55],[-56,3,7,13,18,43,50],[-54,10,20,23,28,45,47],[-55,9,15,22,27,46,52],[-56,9,15,19,27,44,51],[-27,28],[-58,25,33,38,41],[-59,8,14,48,54],[-60,26,55,56,57],[-61,21,24,39,40],[-62,58],[-63,62],[-64,59],[-65,60],[-65,61],[-66,64],[-66,65],[-67,63],[-67,66],[67]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":116},{\"tag\":\"facet\",\"index\":119},{\"tag\":\"facet\",\"index\":120},{\"tag\":\"facet\",\"index\":121},{\"tag\":\"facet\",\"index\":122},{\"tag\":\"facet\",\"index\":123},{\"tag\":\"facet\",\"index\":124},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":46,\"b\":45},{\"tag\":\"incompatible\",\"a\":58,\"b\":46},{\"tag\":\"incompatible\",\"a\":59,\"b\":45},{\"tag\":\"incompatible\",\"a\":59,\"b\":58},{\"tag\":\"incompatible\",\"a\":60,\"b\":45},{\"tag\":\"incompatible\",\"a\":60,\"b\":58},{\"tag\":\"incompatible\",\"a\":65,\"b\":39},{\"tag\":\"incompatible\",\"a\":65,\"b\":43},{\"tag\":\"incompatible\",\"a\":65,\"b\":46},{\"tag\":\"incompatible\",\"a\":65,\"b\":52},{\"tag\":\"incompatible\",\"a\":65,\"b\":56},{\"tag\":\"incompatible\",\"a\":65,\"b\":59},{\"tag\":\"incompatible\",\"a\":66,\"b\":65},{\"tag\":\"incompatible\",\"a\":69,\"b\":45},{\"tag\":\"incompatible\",\"a\":69,\"b\":46},{\"tag\":\"incompatible\",\"a\":69,\"b\":58},{\"tag\":\"incompatible\",\"a\":69,\"b\":59},{\"tag\":\"incompatible\",\"a\":69,\"b\":66},{\"tag\":\"incompatible\",\"a\":69,\"b\":68},{\"tag\":\"incompatible\",\"a\":70,\"b\":65},{\"tag\":\"incompatible\",\"a\":70,\"b\":69},{\"tag\":\"incompatible\",\"a\":71,\"b\":45},{\"tag\":\"incompatible\",\"a\":71,\"b\":46},{\"tag\":\"incompatible\",\"a\":71,\"b\":58},{\"tag\":\"incompatible\",\"a\":71,\"b\":59},{\"tag\":\"incompatible\",\"a\":72,\"b\":65},{\"tag\":\"incompatible\",\"a\":72,\"b\":66},{\"tag\":\"incompatible\",\"a\":72,\"b\":69},{\"tag\":\"incompatible\",\"a\":72,\"b\":70},{\"tag\":\"incompatible\",\"a\":74,\"b\":66},{\"tag\":\"incompatible\",\"a\":74,\"b\":70},{\"tag\":\"incompatible\",\"a\":87,\"b\":45},{\"tag\":\"incompatible\",\"a\":87,\"b\":47},{\"tag\":\"incompatible\",\"a\":87,\"b\":58},{\"tag\":\"incompatible\",\"a\":96,\"b\":45},{\"tag\":\"incompatible\",\"a\":96,\"b\":54},{\"tag\":\"incompatible\",\"a\":96,\"b\":58},{\"tag\":\"incompatible\",\"a\":96,\"b\":93},{\"tag\":\"incompatible\",\"a\":96,\"b\":95},{\"tag\":\"incompatible\",\"a\":97,\"b\":11},{\"tag\":\"incompatible\",\"a\":97,\"b\":64},{\"tag\":\"incompatible\",\"a\":97,\"b\":72},{\"tag\":\"incompatible\",\"a\":97,\"b\":74},{\"tag\":\"incompatible\",\"a\":98,\"b\":68},{\"tag\":\"incompatible\",\"a\":98,\"b\":72},{\"tag\":\"incompatible\",\"a\":98,\"b\":74},{\"tag\":\"incompatible\",\"a\":99,\"b\":97},{\"tag\":\"incompatible\",\"a\":99,\"b\":98},{\"tag\":\"incompatible\",\"a\":105,\"b\":22},{\"tag\":\"incompatible\",\"a\":107,\"b\":97},{\"tag\":\"incompatible\",\"a\":108,\"b\":87},{\"tag\":\"incompatible\",\"a\":110,\"b\":98},{\"tag\":\"incompatible\",\"a\":111,\"b\":87},{\"tag\":\"incompatible\",\"a\":112,\"b\":41},{\"tag\":\"incompatible\",\"a\":112,\"b\":47},{\"tag\":\"incompatible\",\"a\":112,\"b\":71},{\"tag\":\"incompatible\",\"a\":112,\"b\":83},{\"tag\":\"incompatible\",\"a\":112,\"b\":84},{\"tag\":\"incompatible\",\"a\":112,\"b\":86},{\"tag\":\"incompatible\",\"a\":112,\"b\":87},{\"tag\":\"incompatible\",\"a\":112,\"b\":104},{\"tag\":\"incompatible\",\"a\":112,\"b\":111},{\"tag\":\"incompatible\",\"a\":113,\"b\":96},{\"tag\":\"incompatible\",\"a\":114,\"b\":22},{\"tag\":\"incompatible\",\"a\":116,\"b\":97},{\"tag\":\"incompatible\",\"a\":119,\"b\":98},{\"tag\":\"incompatible\",\"a\":120,\"b\":96},{\"tag\":\"incompatible\",\"a\":121,\"b\":60},{\"tag\":\"incompatible\",\"a\":121,\"b\":71},{\"tag\":\"incompatible\",\"a\":121,\"b\":92},{\"tag\":\"incompatible\",\"a\":121,\"b\":95},{\"tag\":\"incompatible\",\"a\":121,\"b\":96},{\"tag\":\"incompatible\",\"a\":122,\"b\":66},{\"tag\":\"incompatible\",\"a\":122,\"b\":70},{\"tag\":\"incompatible\",\"a\":122,\"b\":97},{\"tag\":\"incompatible\",\"a\":123,\"b\":24},{\"tag\":\"incompatible\",\"a\":123,\"b\":66},{\"tag\":\"incompatible\",\"a\":123,\"b\":70},{\"tag\":\"incompatible\",\"a\":123,\"b\":85},{\"tag\":\"incompatible\",\"a\":123,\"b\":94},{\"tag\":\"incompatible\",\"a\":123,\"b\":98},{\"tag\":\"incompatible\",\"a\":124,\"b\":99},{\"tag\":\"incompatible\",\"a\":124,\"b\":112},{\"tag\":\"incompatible\",\"a\":124,\"b\":121},{\"tag\":\"mate\",\"ridge\":161,\"a\":61,\"owners\":[11,84,86,93,95,98]},{\"tag\":\"mate\",\"ridge\":385,\"a\":87,\"owners\":[60,65,69,74,92,95]},{\"tag\":\"mate\",\"ridge\":385,\"a\":96,\"owners\":[47,65,69,74,83,86]},{\"tag\":\"mate\",\"ridge\":577,\"a\":97,\"owners\":[46,59,68,73,85,94]},{\"tag\":\"mate\",\"ridge\":162,\"a\":123,\"owners\":[22,41,54,61,69,104,111,113,120]},{\"tag\":\"mate\",\"ridge\":530,\"a\":23,\"owners\":[24,39,52,64,66,107,116,122]},{\"tag\":\"mate\",\"ridge\":530,\"a\":62,\"owners\":[24,107,116,122]},{\"tag\":\"mate\",\"ridge\":546,\"a\":123,\"owners\":[23,43,56,62,105,114]},{\"tag\":\"mate\",\"ridge\":386,\"a\":121,\"owners\":[47,65,69,74,108,111]},{\"tag\":\"mate\",\"ridge\":578,\"a\":122,\"owners\":[46,59,68,73,110,119]},{\"tag\":\"mate\",\"ridge\":578,\"a\":123,\"owners\":[46,59,64,73,107,116]},{\"tag\":\"mate\",\"ridge\":771,\"a\":73,\"owners\":[74]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[71,87,96,99],\"full_literals\":[-58,25,33,38,41]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[45,58,112,121],\"full_literals\":[-59,8,14,48,54]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[72,122,123,124],\"full_literals\":[-60,26,55,56,57]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[66,70,97,98],\"full_literals\":[-61,21,24,39,40]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-62,58,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-63,62,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-64,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-65,60,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-65,false,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-66,64,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-66,false,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-67,63,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-67,false,66],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true}]}"
  "111 63 0 110 108 0\n112 66 0 110 109 0\n113 62 0 111 102 0\n114 64 0 112 106 0\n115 65 0 112 107 0\n116 58 0 113 101 0\n117 59 0 114 103 0\n118 60 0 115 104 0\n119 61 0 115 105 0\n120 -33 48 54 0 117 32 34 98 0\n121 -38 48 54 0 117 35 37 98 0\n122 -38 48 0 72 121 0\n123 -16 48 0 117 5 6 68 98 0\n124 -28 0 119 30 31 43 46 100 0\n125 -27 0 124 96 0\n126 -21 57 0 118 27 73 77 99 0\n127 -24 57 0 118 29 74 78 99 0\n128 23 40 -48 0 116 118 119 124 83 126 127 100 75 65 50 42 99 76 91 60 56 47 97 39 40 59 58 38 85 67 63 36 41 62 61 57 55 54 87 89 7 8 10 11 49 64 90 92 0\n129 40 -48 0 119 118 125 83 127 126 100 41 42 50 65 75 99 128 15 17 95 0\n130 -23 -48 0 118 125 83 129 45 81 99 66 52 44 15 17 94 0\n131 -48 0 116 118 124 125 55 56 57 59 60 83 129 44 45 48 52 66 81 97 99 130 87 9 12 94 0\n132 -38 0 131 122 0\n133 -16 0 131 123 0\n134 -9 23 41 0 131 117 132 116 133 124 1 2 9 23 98 97 70 71 86 0\n135 23 -55 0 119 125 131 117 132 116 133 124 73 74 75 100 66 52 48 44 134 94 3 4 12 25 98 97 70 71 86 0\n136 -55 0 119 125 73 74 75 100 44 52 66 135 15 17 94 0\n137 -23 0 131 117 136 118 125 119 14 15 16 17 18 19 21 28 98 84 99 79 80 81 88 100 0\n138 -33 20 0 131 137 124 33 51 53 120 93 0\n139 -25 0 131 117 22 24 69 98 0\n140 -41 39 0 119 48 82 126 127 100 0\n141 39 0 132 139 116 131 136 118 119 140 97 120 138 84 13 20 26 99 100 81 0\n142 -19 0 141 41 0\n143 -26 0 141 42 0\n144 -41 0 141 47 0\n145 -44 0 141 50 0\n146 -51 0 141 65 0\n147 33 0 144 116 139 132 97 0\n148 54 0 147 131 120 0\n149 20 0 147 138 0\n150 -57 0 148 84 0\n151 -9 0 144 137 134 0\n152 56 0 150 118 136 143 99 0\n153 -15 0 149 12 0\n154 0 152 153 146 145 151 125 142 95 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090.record001.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090.record001.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090.record001.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090.record001.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090.record001 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090.record001.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090.record001.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090.record001.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090.record001.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090.record001 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090.record001_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090.record001 Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090.record001_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090.record001_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00090.record001
