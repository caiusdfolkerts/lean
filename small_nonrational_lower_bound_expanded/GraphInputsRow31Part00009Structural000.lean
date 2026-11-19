module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow31Part00009Frames
public import GraphInputsRow31Part00009Leaves
public import GraphInputsRow31Part00009Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record001
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "278e92d4ad274e332c9b29c9723c1f3a26cb8ad2b2a9a99a4e87ae1ac6c9aa669a66358b61db0ea398e93a2e4b86e27ba16c789d27299a5994e479e16c5c96a569665354b51d70da358d9362d4b46d275a364cd34ccb31cd8b52c6b46c9b61cc749ca719d0f23f289322c1703c4a85a0e896158361382e0792916439254550d44d0b41d60d2324c530cd0b12c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6da4d24db69b49b6db4936d24936da6d26db6d24db492492492492492491249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record001 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record001 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record001.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record001.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record001.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 70), (facetIndex 96), (facetIndex 116)]))
 (.leaf ([(facetIndex 60), (facetIndex 61), (facetIndex 74), (facetIndex 87), (facetIndex 110)])))
 (.branch 3
 (.leaf ([(facetIndex 78), (facetIndex 86), (facetIndex 100), (facetIndex 104)]))
 (.branch 4
 (.leaf ([(facetIndex 77), (facetIndex 103)]))
 (.leaf ([(facetIndex 66), (facetIndex 92), (facetIndex 114)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 75), (facetIndex 101), (facetIndex 118)]))
 (.branch 7
 (.leaf ([(facetIndex 67), (facetIndex 68), (facetIndex 79), (facetIndex 94), (facetIndex 115)]))
 (.leaf ([(facetIndex 80), (facetIndex 93), (facetIndex 105), (facetIndex 106)]))))
 (.branch 9
 (.leaf ([(facetIndex 62), (facetIndex 88), (facetIndex 113), (facetIndex 117)]))
 (.branch 10
 (.leaf ([(facetIndex 69), (facetIndex 95)]))
 (.leaf ([(facetIndex 71), (facetIndex 97)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "580648001000772305200a0967400081200000762305100a09664000811z3c;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 11
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [2, 3, 4]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [3, 4]
def grouped3_0009 : List Nat := [4]
def grouped3_0010 : List Nat := [5]
def grouped3_0011 : List Nat := [5, 6, 7]
def grouped3_0012 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped3_0013 : List Nat := [6]
def grouped3_0014 : List Nat := [6, 7]
def grouped3_0015 : List Nat := [7]
def grouped3_0016 : List Nat := [8, 9, 10]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record001 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record001_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record001" "{\"atoms\":[{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"facet\",\"index\":116},{\"tag\":\"facet\",\"index\":117},{\"tag\":\"facet\",\"index\":118},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record001" 50

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record001" "{\"ridges\":[[35,580],[59,580],[66,609],[70,705],[71,896],[75,609],[77,833],[85,580],[92,610],[96,706],[97,896],[101,610],[103,834],[109,580],[110,664],[111,584],[113,396],[114,624],[115,688],[116,720],[117,896],[118,624]],\"owners\":[[35,580,[66,70,92,96,114,116],[59,85,109,111]],[59,580,[92,96,114,116],[35,66,70,85,109,111]],[85,580,[66,70,114,116],[35,59,92,96,109,111]],[109,580,[66,70,92,96],[35,59,85,111,114,116]],[111,584,[77,103],[35,59,75,85,101,109,118]],[113,396,[60,86],[]],[66,609,[75],[]],[75,609,[66],[]],[70,705,[],[]],[71,896,[104,106],[78,80,97,113,117]],[97,896,[78,80],[71,104,106,113,117]],[117,896,[78,104],[71,80,97,106,113]],[77,833,[],[]],[92,610,[101],[]],[101,610,[92],[]],[96,706,[],[]],[103,834,[],[]],[110,664,[],[]],[114,624,[118],[]],[118,624,[114],[]],[115,688,[],[]],[116,720,[],[]]],\"edges\":[[41,[35,59,66,70,75,77,85,92,96,101,103,109,111,114,116,118]],[43,[61,68,70,71,78,80,87,94,96,97,104,106,110,113,115,116,117]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record001" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record001\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,5,7,16,18,28,30],[-2,16,18,28,30],[-13,5,7,28,30],[-24,5,7,16,18],[-26,10,21],[-27,3,14],[-5,9],[-9,5],[-7],[-8,22,23],[-19,11,12],[-31,11,22],[-10],[-16,20],[-20,16],[-18],[-21],[-25],[-28,32],[-32,28],[-29],[-30],[-3,33],[-4,33],[-15,33],[-11,34],[-14,34],[-22,34],[-35,5,16,28],[-5,35],[-16,35],[-28,35],[-9,36],[-20,36],[-32,36],[-6,37],[-17,37],[-12,38],[-23,38],[-33,39],[-35,40],[-40,41],[-34,-40,42],[-41,43],[-42,44],[-39,-41,44],[-38,45],[-37,45],[-36,46],[-36,-45,47],[-46,48],[-47,49],[-43,-49,50],[-44,-48,50],[-50],[1,2,5,7,9,10,13,16,18,20,21,24,26,28,30,32],[4,6,7,8,11,12,15,17,18,19,22,23,25,27,29,30,31]],\"atoms\":[{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"facet\",\"index\":116},{\"tag\":\"facet\",\"index\":117},{\"tag\":\"facet\",\"index\":118},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":580,\"a\":35,\"owners\":[66,70,92,96,114,116]},{\"tag\":\"mate\",\"ridge\":580,\"a\":59,\"owners\":[92,96,114,116]},{\"tag\":\"mate\",\"ridge\":580,\"a\":85,\"owners\":[66,70,114,116]},{\"tag\":\"mate\",\"ridge\":580,\"a\":109,\"owners\":[66,70,92,96]},{\"tag\":\"mate\",\"ridge\":584,\"a\":111,\"owners\":[77,103]},{\"tag\":\"mate\",\"ridge\":396,\"a\":113,\"owners\":[60,86]},{\"tag\":\"mate\",\"ridge\":609,\"a\":66,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":609,\"a\":75,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":705,\"a\":70,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":896,\"a\":71,\"owners\":[104,106]},{\"tag\":\"mate\",\"ridge\":896,\"a\":97,\"owners\":[78,80]},{\"tag\":\"mate\",\"ridge\":896,\"a\":117,\"owners\":[78,104]},{\"tag\":\"mate\",\"ridge\":833,\"a\":77,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":610,\"a\":92,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":610,\"a\":101,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":706,\"a\":96,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":834,\"a\":103,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":664,\"a\":110,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":624,\"a\":114,\"owners\":[118]},{\"tag\":\"mate\",\"ridge\":624,\"a\":118,\"owners\":[114]},{\"tag\":\"mate\",\"ridge\":688,\"a\":115,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":720,\"a\":116,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":60,\"full_literals\":[-3,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":61,\"full_literals\":[-4,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":87,\"full_literals\":[-15,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":78,\"full_literals\":[-11,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":86,\"full_literals\":[-14,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":104,\"full_literals\":[-22,34]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[66,92,114],\"full_literals\":[-35,5,16,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":66,\"full_literals\":[-5,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":92,\"full_literals\":[-16,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":114,\"full_literals\":[-28,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":75,\"full_literals\":[-9,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":101,\"full_literals\":[-20,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":118,\"full_literals\":[-32,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":68,\"full_literals\":[-6,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":94,\"full_literals\":[-17,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":80,\"full_literals\":[-12,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":106,\"full_literals\":[-23,38]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-33,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-35,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-40,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-34,-40,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-42,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-39,-41,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-38,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-37,false,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-36,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-36,-45,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0012\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-47,false,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-43,-49,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-44,-48,50],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":41,\"owners\":[35,59,66,70,75,77,85,92,96,101,103,109,111,114,116,118]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[61,68,70,71,78,80,87,94,96,97,104,106,110,113,115,116,117]}]}"
  "58 -26 0 17 13 5 0\n59 1 2 5 9 13 16 20 24 28 32 0 9 13 16 17 58 22 56 0\n60 4 6 8 11 12 15 17 19 22 23 27 31 0 9 16 18 21 22 57 0\n61 35 0 22 16 9 30 31 32 8 15 4 20 3 2 1 59 0\n62 40 0 61 41 0\n63 41 0 62 42 0\n64 43 0 63 44 0\n65 -49 0 64 55 53 0\n66 -47 0 65 52 0\n67 45 44 0 63 62 45 43 27 46 40 23 6 28 26 12 25 24 47 48 38 39 36 37 11 10 60 0\n68 36 0 61 33 34 35 7 14 19 29 0\n69 46 0 68 49 0\n70 -45 0 68 66 50 0\n71 48 0 69 51 0\n72 44 0 70 67 0\n73 0 72 71 55 54 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record001.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record001.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record001.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record001.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record001 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record001.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record001.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record001.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record001.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record001 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record001_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record001 Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record001_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record001_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "354cd274b32ac9b19cd4b329cacaaaa6a66b86d1ac6c9aa699b1665a5655a364d876a398e938ce8b8ae1b91e2785e0f999e1745b1725a9665655554d58d334ad4749de0f43b0f23a8e6364d534cd8b32cab46c9bc1e8761e4751cc789d2729c6745c9715c3743c8f13c2f07c78e12641d06c1703ce0a621c86a1683a1c4691643961465454550d48d1342d0758318d1314c3322c4b0ac1b"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "369b4db4da69b6d36db69b6db4da4d36da4924924db69249249b4db6da4d2692449249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record005.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record005.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record005.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 62), (facetIndex 67), (facetIndex 76), (facetIndex 81)]))
 (.leaf ([(facetIndex 44), (facetIndex 87), (facetIndex 94), (facetIndex 101), (facetIndex 108), (facetIndex 111)])))
 (.branch 3
 (.leaf ([(facetIndex 115), (facetIndex 118)]))
 (.leaf ([(facetIndex 54), (facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 58)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 43), (facetIndex 59), (facetIndex 60), (facetIndex 61)]))
 (.leaf ([(facetIndex 68), (facetIndex 69), (facetIndex 70), (facetIndex 71), (facetIndex 72)])))
 (.branch 7
 (.leaf ([(facetIndex 73), (facetIndex 74), (facetIndex 75)]))
 (.leaf ([(facetIndex 35), (facetIndex 36), (facetIndex 37), (facetIndex 38), (facetIndex 40), (facetIndex 41), (facetIndex 51), (facetIndex 83), (facetIndex 84), (facetIndex 106)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "804002011c0008000040000207e00000db5b6d0000248db6c0e0000183f1ffez1a;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 39), (facetIndex 42), (facetIndex 82)]))
 (.branch 2
 (.leaf ([(facetIndex 85), (facetIndex 86), (facetIndex 107)]))
 (.leaf ([(facetIndex 92), (facetIndex 99), (facetIndex 114)]))))
 (.branch 4
 (.leaf ([(facetIndex 89), (facetIndex 109), (facetIndex 110)]))
 (.branch 5
 (.leaf ([(facetIndex 96), (facetIndex 112), (facetIndex 113)]))
 (.leaf ([(facetIndex 91), (facetIndex 116), (facetIndex 117)])))))
 (.branch 9
 (.branch 7
 (.leaf ([(facetIndex 98), (facetIndex 119), (facetIndex 120)]))
 (.branch 8
 (.leaf ([(facetIndex 47), (facetIndex 63), (facetIndex 64), (facetIndex 65), (facetIndex 66)]))
 (.leaf ([(facetIndex 50), (facetIndex 77), (facetIndex 78), (facetIndex 79), (facetIndex 80)]))))
 (.branch 10
 (.leaf ([(facetIndex 45), (facetIndex 46), (facetIndex 48), (facetIndex 49), (facetIndex 52), (facetIndex 93), (facetIndex 100)]))
 (.branch 11
 (.leaf ([(facetIndex 53), (facetIndex 88), (facetIndex 90), (facetIndex 95), (facetIndex 97)]))
 (.leaf ([(facetIndex 102), (facetIndex 103), (facetIndex 104), (facetIndex 105)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "660550244033010bbbb0926a4a0925a3a0110000888800000000007777000000000a90899799z2d;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 12
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
def grouped3_0017 : List Nat := [0, 1, 2, 3, 4, 5]
def grouped3_0018 : List Nat := [1]
def grouped3_0019 : List Nat := [1, 2]
def grouped3_0020 : List Nat := [2]
def grouped3_0021 : List Nat := [3]
def grouped3_0022 : List Nat := [3, 4, 5]
def grouped3_0023 : List Nat := [4]
def grouped3_0024 : List Nat := [4, 5]
def grouped3_0025 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record005_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"facet\",\"index\":116},{\"tag\":\"facet\",\"index\":117},{\"tag\":\"facet\",\"index\":118},{\"tag\":\"facet\",\"index\":119},{\"tag\":\"facet\",\"index\":120},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record005" 115

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record005" "{\"ridges\":[[27,386],[27,770],[28,52],[29,84],[33,388],[33,772],[36,44],[37,69],[38,138],[38,140],[43,274],[49,261],[51,261],[51,386],[51,388],[54,138],[55,274],[56,138],[57,138],[58,138],[59,274],[60,273],[62,546],[62,578],[64,801],[67,770],[73,52],[73,261],[73,273],[73,276],[74,84],[74,261],[74,276],[75,276],[78,261],[81,261],[81,896],[82,273],[82,408],[83,28],[83,52],[84,28],[84,84],[86,270],[93,526],[105,326],[107,386],[107,408],[108,578],[111,546],[112,816],[114,276],[114,388],[114,408],[115,580],[118,52],[118,84],[119,276],[119,816],[120,848]],\"owners\":[[38,138,[107,109,110],[3,54,56,57,58,85,88,90,92,93]],[54,138,[88,90,92,93,109,110],[3,38,56,57,58,85,107]],[56,138,[85,90,92,93,107,110],[3,38,54,57,58,88,109]],[57,138,[85,88,92,93,107,109],[3,38,54,56,58,90,110]],[58,138,[85,88,90,93,109,110],[3,38,54,56,57,92,107]],[43,274,[107,112,113],[6,55,59,60,61,86,95,97,99,100]],[55,274,[95,97,99,100,112,113],[6,43,59,60,61,86,107]],[59,274,[86,97,99,100,107,113],[6,43,55,60,61,95,112]],[83,28,[9,29,68,69,114],[28,35,84,85,86]],[84,28,[9,28,68,69,114],[29,35,83,85,86]],[36,44,[28,30,115,116],[10,70,83,87,88,89]],[37,69,[14,16,74,76,79,80],[11,41,44,48,49,50,71]],[38,140,[114,116,117],[12,68,70,71,72,85,88,90,92,93]],[73,276,[86,97,99,100,114,120],[15,43,69,74,75,95,119]],[74,276,[86,95,99,100,114,119],[15,43,69,73,75,97,120]],[75,276,[86,95,97,100,119,120],[15,43,69,73,74,99,114]],[62,546,[89,96,102,103,109,112],[26,47,63,64,101,108,111]],[111,546,[47,63,64,89,102,103,109],[26,62,96,101,108,112]],[62,578,[91,98,104,105,110,113],[26,50,65,66,101,108,111]],[108,578,[50,65,66,98,104,105,113],[26,62,91,101,110,111]],[27,770,[53,64,66,100,103,105,112,113],[67,106]],[67,770,[100,103,105,112,113],[27,53,64,66,106]],[81,896,[27],[33,67]],[115,580,[50,79,80,98,104,105,120],[32,76,91,101,117,118]],[33,772,[53,78,80,100,103,105,119,120],[81,106]],[86,270,[39,92],[]],[105,326,[49,97],[]],[64,801,[78],[]],[82,408,[107,114],[]],[107,408,[82,114],[]],[114,408,[82,107],[]],[93,526,[89,91],[]],[112,816,[119],[]],[119,816,[112],[]],[120,848,[113],[]]],\"edges\":[[44,[27,33,53,64,66,67,78,80,81,100,103,105,106,112,113,119,120]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-23,-22],[-24,-10],[-24,-11],[-26,-10],[-26,-11],[-27,-10],[-27,-11],[-31,-22],[-34,-29],[-37,-21],[-37,-22],[-37,-31],[-37,-35],[-37,-36],[-40,-10],[-40,-11],[-40,-12],[-41,-10],[-41,-11],[-41,-12],[-42,-12],[-42,-25],[-42,-28],[-43,-1],[-43,-2],[-43,-9],[-43,-14],[-43,-15],[-43,-38],[-43,-39],[-44,-1],[-44,-9],[-44,-14],[-44,-15],[-44,-17],[-44,-30],[-44,-36],[-44,-38],[-44,-39],[-45,-13],[-45,-16],[-45,-22],[-47,-29],[-48,-33],[-48,-34],[-49,-44],[-50,-22],[-50,-23],[-50,-34],[-50,-36],[-50,-45],[-50,-48],[-50,-49],[-51,-22],[-52,-18],[-52,-23],[-53,-18],[-53,-19],[-53,-21],[-54,-45],[-55,-22],[-55,-52],[-56,-52],[-56,-53],[-58,-53],[-61,-37],[-63,-52],[-63,-53],[-64,-9],[-64,-10],[-64,-11],[-64,-14],[-64,-15],[-64,-22],[-64,-52],[-64,-53],[-66,-9],[-66,-10],[-66,-11],[-66,-14],[-66,-15],[-66,-22],[-66,-44],[-66,-52],[-66,-53],[-67,-53],[-68,-22],[-68,-37],[-68,-52],[-69,-9],[-69,-10],[-69,-11],[-69,-12],[-69,-14],[-69,-15],[-69,-22],[-69,-52],[-69,-53],[-70,-52],[-70,-53],[-71,-53],[-72,-22],[-72,-43],[-72,-52],[-72,-53],[-73,-53],[-73,-72],[-74,-9],[-74,-10],[-74,-11],[-74,-14],[-74,-15],[-74,-44],[-74,-52],[-74,-53],[-74,-55],[-75,-18],[-75,-37],[-75,-50],[-75,-56],[-75,-57],[-75,-58],[-75,-59],[-75,-60],[-75,-63],[-75,-64],[-75,-65],[-75,-66],[-75,-67],[-75,-69],[-75,-70],[-75,-71],[-75,-72],[-75,-73],[-76,-37],[-77,-32],[-78,-77],[-79,-77],[-80,-32],[-80,-65],[-81,-29],[-81,-80],[-82,-44],[-82,-80],[-83,-31],[-83,-45],[-83,-50],[-83,-55],[-84,-18],[-84,-46],[-84,-56],[-84,-58],[-84,-60],[-84,-63],[-84,-70],[-84,-77],[-84,-78],[-84,-79],[-85,-77],[-85,-84],[-86,-77],[-86,-84],[-87,-3],[-87,-7],[-87,-18],[-87,-46],[-87,-56],[-87,-63],[-87,-67],[-87,-70],[-87,-80],[-87,-81],[-87,-82],[-87,-84],[-88,-80],[-89,-44],[-89,-80],[-12,76,78,79],[-24,57,59,61,62,78,79],[-26,54,59,61,62,76,79],[-27,54,57,61,62,76,78],[-28,54,57,59,62,78,79],[-30,-43,-51],[-17,76,81,82],[-25,64,66,68,69,81,82],[-29,55,66,68,69,76,82],[-4,-22,-76],[-52,1,6,38,39,83],[-53,1,5,38,39,83],[-10,5,7,84,85],[-11,2,3,44,46,48,49],[-12,83,85,86],[-5,-43,-87],[-43,-52,-87],[-6,-44,-87],[-44,-53,-87],[-20,-43,-50],[-22,-44,-47],[-43,55,66,68,69,83,89],[-44,55,64,68,69,83,88],[-45,55,64,66,69,88,89],[-44,-83,-88],[-8,-22,-83],[-32,58,65,71,72,78,81],[-80,19,33,34,58,71,72,78],[-32,60,67,73,74,79,82],[-77,21,35,36,67,73,74,82],[-4,23,34,36,69,72,74,81,82],[-37,69,72,74,81,82],[-50,4],[-84,21,48,49,67,73,74,89],[-8,23,47,49,69,72,74,88,89],[-55,13,61],[-74,20,66],[-34,47],[-51,76,83],[-76,51,83],[-83,51,76],[-62,58,60],[-81,88],[-88,81],[-89,82],[-90,32,37,46,50],[-91,18,56,63,70,77,80],[-92,84,87],[-93,24,25,26,27,28],[-94,17,29,30,31],[-95,38,39,40,41,42],[-96,43,44,45],[-97,9,10,11,12,14,15,22,52,53,75],[-98,90],[-98,91],[-99,92],[-99,93],[-100,98],[-100,99],[-101,94],[-101,95],[-102,96],[-102,97],[-103,101],[-103,102],[-104,100],[-104,103],[104],[-105,13,16,51],[-106,54,55,76],[-54,106],[-55,106],[-76,106],[-107,61,68,83],[-61,107],[-68,107],[-83,107],[-108,58,78,79],[-58,108],[-78,108],[-79,108],[-109,65,81,82],[-81,109],[-82,109],[-110,60,85,86],[-60,110],[-85,110],[-86,110],[-111,106,107],[-107,111],[-106,111],[-112,105,111],[-111,112],[-113,109,110],[-110,113],[-109,113],[-114,108,113],[-113,114],[-108,114],[-115,112,114],[-114,115],[-112,115],[4,8,23,34,36,37,47,49,50,69,72,74,75,81,82,88,89]],\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"facet\",\"index\":116},{\"tag\":\"facet\",\"index\":117},{\"tag\":\"facet\",\"index\":118},{\"tag\":\"facet\",\"index\":119},{\"tag\":\"facet\",\"index\":120},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":53,\"b\":51},{\"tag\":\"incompatible\",\"a\":54,\"b\":36},{\"tag\":\"incompatible\",\"a\":54,\"b\":37},{\"tag\":\"incompatible\",\"a\":56,\"b\":36},{\"tag\":\"incompatible\",\"a\":56,\"b\":37},{\"tag\":\"incompatible\",\"a\":57,\"b\":36},{\"tag\":\"incompatible\",\"a\":57,\"b\":37},{\"tag\":\"incompatible\",\"a\":61,\"b\":51},{\"tag\":\"incompatible\",\"a\":64,\"b\":59},{\"tag\":\"incompatible\",\"a\":67,\"b\":50},{\"tag\":\"incompatible\",\"a\":67,\"b\":51},{\"tag\":\"incompatible\",\"a\":67,\"b\":61},{\"tag\":\"incompatible\",\"a\":67,\"b\":65},{\"tag\":\"incompatible\",\"a\":67,\"b\":66},{\"tag\":\"incompatible\",\"a\":70,\"b\":36},{\"tag\":\"incompatible\",\"a\":70,\"b\":37},{\"tag\":\"incompatible\",\"a\":70,\"b\":38},{\"tag\":\"incompatible\",\"a\":71,\"b\":36},{\"tag\":\"incompatible\",\"a\":71,\"b\":37},{\"tag\":\"incompatible\",\"a\":71,\"b\":38},{\"tag\":\"incompatible\",\"a\":72,\"b\":38},{\"tag\":\"incompatible\",\"a\":72,\"b\":55},{\"tag\":\"incompatible\",\"a\":72,\"b\":58},{\"tag\":\"incompatible\",\"a\":73,\"b\":9},{\"tag\":\"incompatible\",\"a\":73,\"b\":14},{\"tag\":\"incompatible\",\"a\":73,\"b\":35},{\"tag\":\"incompatible\",\"a\":73,\"b\":40},{\"tag\":\"incompatible\",\"a\":73,\"b\":41},{\"tag\":\"incompatible\",\"a\":73,\"b\":68},{\"tag\":\"incompatible\",\"a\":73,\"b\":69},{\"tag\":\"incompatible\",\"a\":74,\"b\":9},{\"tag\":\"incompatible\",\"a\":74,\"b\":35},{\"tag\":\"incompatible\",\"a\":74,\"b\":40},{\"tag\":\"incompatible\",\"a\":74,\"b\":41},{\"tag\":\"incompatible\",\"a\":74,\"b\":43},{\"tag\":\"incompatible\",\"a\":74,\"b\":60},{\"tag\":\"incompatible\",\"a\":74,\"b\":66},{\"tag\":\"incompatible\",\"a\":74,\"b\":68},{\"tag\":\"incompatible\",\"a\":74,\"b\":69},{\"tag\":\"incompatible\",\"a\":75,\"b\":39},{\"tag\":\"incompatible\",\"a\":75,\"b\":42},{\"tag\":\"incompatible\",\"a\":75,\"b\":51},{\"tag\":\"incompatible\",\"a\":78,\"b\":59},{\"tag\":\"incompatible\",\"a\":79,\"b\":63},{\"tag\":\"incompatible\",\"a\":79,\"b\":64},{\"tag\":\"incompatible\",\"a\":80,\"b\":74},{\"tag\":\"incompatible\",\"a\":81,\"b\":51},{\"tag\":\"incompatible\",\"a\":81,\"b\":53},{\"tag\":\"incompatible\",\"a\":81,\"b\":64},{\"tag\":\"incompatible\",\"a\":81,\"b\":66},{\"tag\":\"incompatible\",\"a\":81,\"b\":75},{\"tag\":\"incompatible\",\"a\":81,\"b\":79},{\"tag\":\"incompatible\",\"a\":81,\"b\":80},{\"tag\":\"incompatible\",\"a\":82,\"b\":51},{\"tag\":\"incompatible\",\"a\":83,\"b\":44},{\"tag\":\"incompatible\",\"a\":83,\"b\":53},{\"tag\":\"incompatible\",\"a\":84,\"b\":44},{\"tag\":\"incompatible\",\"a\":84,\"b\":47},{\"tag\":\"incompatible\",\"a\":84,\"b\":50},{\"tag\":\"incompatible\",\"a\":85,\"b\":75},{\"tag\":\"incompatible\",\"a\":86,\"b\":51},{\"tag\":\"incompatible\",\"a\":86,\"b\":83},{\"tag\":\"incompatible\",\"a\":87,\"b\":83},{\"tag\":\"incompatible\",\"a\":87,\"b\":84},{\"tag\":\"incompatible\",\"a\":89,\"b\":84},{\"tag\":\"incompatible\",\"a\":92,\"b\":67},{\"tag\":\"incompatible\",\"a\":94,\"b\":83},{\"tag\":\"incompatible\",\"a\":94,\"b\":84},{\"tag\":\"incompatible\",\"a\":95,\"b\":35},{\"tag\":\"incompatible\",\"a\":95,\"b\":36},{\"tag\":\"incompatible\",\"a\":95,\"b\":37},{\"tag\":\"incompatible\",\"a\":95,\"b\":40},{\"tag\":\"incompatible\",\"a\":95,\"b\":41},{\"tag\":\"incompatible\",\"a\":95,\"b\":51},{\"tag\":\"incompatible\",\"a\":95,\"b\":83},{\"tag\":\"incompatible\",\"a\":95,\"b\":84},{\"tag\":\"incompatible\",\"a\":97,\"b\":35},{\"tag\":\"incompatible\",\"a\":97,\"b\":36},{\"tag\":\"incompatible\",\"a\":97,\"b\":37},{\"tag\":\"incompatible\",\"a\":97,\"b\":40},{\"tag\":\"incompatible\",\"a\":97,\"b\":41},{\"tag\":\"incompatible\",\"a\":97,\"b\":51},{\"tag\":\"incompatible\",\"a\":97,\"b\":74},{\"tag\":\"incompatible\",\"a\":97,\"b\":83},{\"tag\":\"incompatible\",\"a\":97,\"b\":84},{\"tag\":\"incompatible\",\"a\":98,\"b\":84},{\"tag\":\"incompatible\",\"a\":99,\"b\":51},{\"tag\":\"incompatible\",\"a\":99,\"b\":67},{\"tag\":\"incompatible\",\"a\":99,\"b\":83},{\"tag\":\"incompatible\",\"a\":100,\"b\":35},{\"tag\":\"incompatible\",\"a\":100,\"b\":36},{\"tag\":\"incompatible\",\"a\":100,\"b\":37},{\"tag\":\"incompatible\",\"a\":100,\"b\":38},{\"tag\":\"incompatible\",\"a\":100,\"b\":40},{\"tag\":\"incompatible\",\"a\":100,\"b\":41},{\"tag\":\"incompatible\",\"a\":100,\"b\":51},{\"tag\":\"incompatible\",\"a\":100,\"b\":83},{\"tag\":\"incompatible\",\"a\":100,\"b\":84},{\"tag\":\"incompatible\",\"a\":101,\"b\":83},{\"tag\":\"incompatible\",\"a\":101,\"b\":84},{\"tag\":\"incompatible\",\"a\":102,\"b\":84},{\"tag\":\"incompatible\",\"a\":103,\"b\":51},{\"tag\":\"incompatible\",\"a\":103,\"b\":73},{\"tag\":\"incompatible\",\"a\":103,\"b\":83},{\"tag\":\"incompatible\",\"a\":103,\"b\":84},{\"tag\":\"incompatible\",\"a\":104,\"b\":84},{\"tag\":\"incompatible\",\"a\":104,\"b\":103},{\"tag\":\"incompatible\",\"a\":105,\"b\":35},{\"tag\":\"incompatible\",\"a\":105,\"b\":36},{\"tag\":\"incompatible\",\"a\":105,\"b\":37},{\"tag\":\"incompatible\",\"a\":105,\"b\":40},{\"tag\":\"incompatible\",\"a\":105,\"b\":41},{\"tag\":\"incompatible\",\"a\":105,\"b\":74},{\"tag\":\"incompatible\",\"a\":105,\"b\":83},{\"tag\":\"incompatible\",\"a\":105,\"b\":84},{\"tag\":\"incompatible\",\"a\":105,\"b\":86},{\"tag\":\"incompatible\",\"a\":106,\"b\":44},{\"tag\":\"incompatible\",\"a\":106,\"b\":67},{\"tag\":\"incompatible\",\"a\":106,\"b\":81},{\"tag\":\"incompatible\",\"a\":106,\"b\":87},{\"tag\":\"incompatible\",\"a\":106,\"b\":88},{\"tag\":\"incompatible\",\"a\":106,\"b\":89},{\"tag\":\"incompatible\",\"a\":106,\"b\":90},{\"tag\":\"incompatible\",\"a\":106,\"b\":91},{\"tag\":\"incompatible\",\"a\":106,\"b\":94},{\"tag\":\"incompatible\",\"a\":106,\"b\":95},{\"tag\":\"incompatible\",\"a\":106,\"b\":96},{\"tag\":\"incompatible\",\"a\":106,\"b\":97},{\"tag\":\"incompatible\",\"a\":106,\"b\":98},{\"tag\":\"incompatible\",\"a\":106,\"b\":100},{\"tag\":\"incompatible\",\"a\":106,\"b\":101},{\"tag\":\"incompatible\",\"a\":106,\"b\":102},{\"tag\":\"incompatible\",\"a\":106,\"b\":103},{\"tag\":\"incompatible\",\"a\":106,\"b\":104},{\"tag\":\"incompatible\",\"a\":107,\"b\":67},{\"tag\":\"incompatible\",\"a\":108,\"b\":62},{\"tag\":\"incompatible\",\"a\":109,\"b\":108},{\"tag\":\"incompatible\",\"a\":110,\"b\":108},{\"tag\":\"incompatible\",\"a\":111,\"b\":62},{\"tag\":\"incompatible\",\"a\":111,\"b\":96},{\"tag\":\"incompatible\",\"a\":112,\"b\":59},{\"tag\":\"incompatible\",\"a\":112,\"b\":111},{\"tag\":\"incompatible\",\"a\":113,\"b\":74},{\"tag\":\"incompatible\",\"a\":113,\"b\":111},{\"tag\":\"incompatible\",\"a\":114,\"b\":61},{\"tag\":\"incompatible\",\"a\":114,\"b\":75},{\"tag\":\"incompatible\",\"a\":114,\"b\":81},{\"tag\":\"incompatible\",\"a\":114,\"b\":86},{\"tag\":\"incompatible\",\"a\":115,\"b\":44},{\"tag\":\"incompatible\",\"a\":115,\"b\":76},{\"tag\":\"incompatible\",\"a\":115,\"b\":87},{\"tag\":\"incompatible\",\"a\":115,\"b\":89},{\"tag\":\"incompatible\",\"a\":115,\"b\":91},{\"tag\":\"incompatible\",\"a\":115,\"b\":94},{\"tag\":\"incompatible\",\"a\":115,\"b\":101},{\"tag\":\"incompatible\",\"a\":115,\"b\":108},{\"tag\":\"incompatible\",\"a\":115,\"b\":109},{\"tag\":\"incompatible\",\"a\":115,\"b\":110},{\"tag\":\"incompatible\",\"a\":116,\"b\":108},{\"tag\":\"incompatible\",\"a\":116,\"b\":115},{\"tag\":\"incompatible\",\"a\":117,\"b\":108},{\"tag\":\"incompatible\",\"a\":117,\"b\":115},{\"tag\":\"incompatible\",\"a\":118,\"b\":16},{\"tag\":\"incompatible\",\"a\":118,\"b\":30},{\"tag\":\"incompatible\",\"a\":118,\"b\":44},{\"tag\":\"incompatible\",\"a\":118,\"b\":76},{\"tag\":\"incompatible\",\"a\":118,\"b\":87},{\"tag\":\"incompatible\",\"a\":118,\"b\":94},{\"tag\":\"incompatible\",\"a\":118,\"b\":98},{\"tag\":\"incompatible\",\"a\":118,\"b\":101},{\"tag\":\"incompatible\",\"a\":118,\"b\":111},{\"tag\":\"incompatible\",\"a\":118,\"b\":112},{\"tag\":\"incompatible\",\"a\":118,\"b\":113},{\"tag\":\"incompatible\",\"a\":118,\"b\":115},{\"tag\":\"incompatible\",\"a\":119,\"b\":111},{\"tag\":\"incompatible\",\"a\":120,\"b\":74},{\"tag\":\"incompatible\",\"a\":120,\"b\":111},{\"tag\":\"mate\",\"ridge\":138,\"a\":38,\"owners\":[107,109,110]},{\"tag\":\"mate\",\"ridge\":138,\"a\":54,\"owners\":[88,90,92,93,109,110]},{\"tag\":\"mate\",\"ridge\":138,\"a\":56,\"owners\":[85,90,92,93,107,110]},{\"tag\":\"mate\",\"ridge\":138,\"a\":57,\"owners\":[85,88,92,93,107,109]},{\"tag\":\"mate\",\"ridge\":138,\"a\":58,\"owners\":[85,88,90,93,109,110]},{\"tag\":\"three\",\"ridge\":273,\"vertices\":[60,73,82]},{\"tag\":\"mate\",\"ridge\":274,\"a\":43,\"owners\":[107,112,113]},{\"tag\":\"mate\",\"ridge\":274,\"a\":55,\"owners\":[95,97,99,100,112,113]},{\"tag\":\"mate\",\"ridge\":274,\"a\":59,\"owners\":[86,97,99,100,107,113]},{\"tag\":\"three\",\"ridge\":386,\"vertices\":[27,51,107]},{\"tag\":\"mate\",\"ridge\":28,\"a\":83,\"owners\":[9,29,68,69,114]},{\"tag\":\"mate\",\"ridge\":28,\"a\":84,\"owners\":[9,28,68,69,114]},{\"tag\":\"mate\",\"ridge\":44,\"a\":36,\"owners\":[28,30,115,116]},{\"tag\":\"mate\",\"ridge\":69,\"a\":37,\"owners\":[14,16,74,76,79,80]},{\"tag\":\"mate\",\"ridge\":140,\"a\":38,\"owners\":[114,116,117]},{\"tag\":\"three\",\"ridge\":52,\"vertices\":[28,73,118]},{\"tag\":\"three\",\"ridge\":52,\"vertices\":[73,83,118]},{\"tag\":\"three\",\"ridge\":84,\"vertices\":[29,74,118]},{\"tag\":\"three\",\"ridge\":84,\"vertices\":[74,84,118]},{\"tag\":\"three\",\"ridge\":261,\"vertices\":[49,73,81]},{\"tag\":\"three\",\"ridge\":261,\"vertices\":[51,74,78]},{\"tag\":\"mate\",\"ridge\":276,\"a\":73,\"owners\":[86,97,99,100,114,120]},{\"tag\":\"mate\",\"ridge\":276,\"a\":74,\"owners\":[86,95,99,100,114,119]},{\"tag\":\"mate\",\"ridge\":276,\"a\":75,\"owners\":[86,95,97,100,119,120]},{\"tag\":\"three\",\"ridge\":276,\"vertices\":[74,114,119]},{\"tag\":\"three\",\"ridge\":388,\"vertices\":[33,51,114]},{\"tag\":\"mate\",\"ridge\":546,\"a\":62,\"owners\":[89,96,102,103,109,112]},{\"tag\":\"mate\",\"ridge\":546,\"a\":111,\"owners\":[47,63,64,89,102,103,109]},{\"tag\":\"mate\",\"ridge\":578,\"a\":62,\"owners\":[91,98,104,105,110,113]},{\"tag\":\"mate\",\"ridge\":578,\"a\":108,\"owners\":[50,65,66,98,104,105,113]},{\"tag\":\"mate\",\"ridge\":770,\"a\":27,\"owners\":[53,64,66,100,103,105,112,113]},{\"tag\":\"mate\",\"ridge\":770,\"a\":67,\"owners\":[100,103,105,112,113]},{\"tag\":\"mate\",\"ridge\":896,\"a\":81,\"owners\":[27]},{\"tag\":\"mate\",\"ridge\":580,\"a\":115,\"owners\":[50,79,80,98,104,105,120]},{\"tag\":\"mate\",\"ridge\":772,\"a\":33,\"owners\":[53,78,80,100,103,105,119,120]},{\"tag\":\"mate\",\"ridge\":270,\"a\":86,\"owners\":[39,92]},{\"tag\":\"mate\",\"ridge\":326,\"a\":105,\"owners\":[49,97]},{\"tag\":\"mate\",\"ridge\":801,\"a\":64,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":408,\"a\":82,\"owners\":[107,114]},{\"tag\":\"mate\",\"ridge\":408,\"a\":107,\"owners\":[82,114]},{\"tag\":\"mate\",\"ridge\":408,\"a\":114,\"owners\":[82,107]},{\"tag\":\"mate\",\"ridge\":526,\"a\":93,\"owners\":[89,91]},{\"tag\":\"mate\",\"ridge\":816,\"a\":112,\"owners\":[119]},{\"tag\":\"mate\",\"ridge\":816,\"a\":119,\"owners\":[112]},{\"tag\":\"mate\",\"ridge\":848,\"a\":120,\"owners\":[113]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[62,67,76,81],\"full_literals\":[-90,32,37,46,50]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[44,87,94,101,108,111],\"full_literals\":[-91,18,56,63,70,77,80]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[115,118],\"full_literals\":[-92,84,87]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[54,55,56,57,58],\"full_literals\":[-93,24,25,26,27,28]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[43,59,60,61],\"full_literals\":[-94,17,29,30,31]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[68,69,70,71,72],\"full_literals\":[-95,38,39,40,41,42]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[73,74,75],\"full_literals\":[-96,43,44,45]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[35,36,37,38,40,41,51,83,84,106],\"full_literals\":[-97,9,10,11,12,14,15,22,52,53,75]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-98,90,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-98,false,91],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-99,92,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-99,false,93],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-100,98,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-100,false,99],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-101,94,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-101,false,95],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-102,96,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-102,false,97],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-103,101,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-103,false,102],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-104,100,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-104,false,103],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[39,42,82],\"full_literals\":[-105,13,16,51]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[85,86,107],\"full_literals\":[-106,54,55,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":85,\"full_literals\":[-54,106]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":86,\"full_literals\":[-55,106]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":107,\"full_literals\":[-76,106]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[92,99,114],\"full_literals\":[-107,61,68,83]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":92,\"full_literals\":[-61,107]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":99,\"full_literals\":[-68,107]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":114,\"full_literals\":[-83,107]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[89,109,110],\"full_literals\":[-108,58,78,79]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":89,\"full_literals\":[-58,108]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":109,\"full_literals\":[-78,108]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":110,\"full_literals\":[-79,108]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[96,112,113],\"full_literals\":[-109,65,81,82]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":112,\"full_literals\":[-81,109]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":113,\"full_literals\":[-82,109]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[91,116,117],\"full_literals\":[-110,60,85,86]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":91,\"full_literals\":[-60,110]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":116,\"full_literals\":[-85,110]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":117,\"full_literals\":[-86,110]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-111,106,107],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-107,111],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-106,false,111],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-112,105,111],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-111,112],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-113,109,110],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-110,113],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-109,false,113],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-114,108,113],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-113,114],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-108,false,114],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-115,112,114],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-114,115],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-112,false,115],\"grouped\":true,\"kind\":3},{\"tag\":\"edge\",\"edge\":44,\"owners\":[27,33,53,64,66,67,78,80,81,100,103,105,106,112,113,119,120]}]}"
  "281 100 0 245 243 0\n282 103 0 245 244 0\n283 98 0 281 235 0\n284 99 0 281 236 0\n285 101 0 282 241 0\n286 102 0 282 242 0\n287 90 0 283 231 0\n288 91 0 283 232 0\n289 92 0 284 233 0\n290 93 0 284 234 0\n291 94 0 285 237 0\n292 95 0 285 238 0\n293 96 0 286 239 0\n294 97 0 286 240 0\n295 -66 75 12 0 294 77 78 79 80 81 82 84 85 230 0\n296 75 69 44 115 0 293 294 278 275 272 265 264 279 270 267 254 192 273 261 222 260 221 268 249 253 295 199 229 42 201 69 70 71 72 73 75 76 230 0\n297 69 44 115 0 290 279 270 268 250 248 267 253 252 278 275 272 263 276 256 219 273 261 260 258 257 296 121 123 126 128 179 182 181 180 185 226 0\n298 -69 12 0 294 90 91 92 94 95 96 97 98 130 230 0\n299 115 0 294 278 279 275 270 272 273 267 268 264 265 260 253 254 249 221 192 298 297 32 33 34 200 70 71 74 75 76 126 230 0\n300 -22 83 69 -44 0 291 143 83 36 35 8 54 61 87 227 217 186 0\n301 -52 83 69 -44 0 289 288 39 38 31 55 62 63 67 75 89 99 188 200 195 175 225 224 156 0\n302 -10 -44 0 292 290 39 38 2 4 6 15 18 228 22 23 226 0\n303 -22 75 69 -44 0 291 176 143 113 46 37 36 35 1 8 11 47 54 102 198 300 227 215 202 218 203 141 187 280 0\n304 -52 75 69 -44 0 291 176 143 113 46 37 36 35 56 104 301 145 147 202 227 220 9 43 209 208 212 280 0\n305 -53 -44 0 289 288 176 113 46 57 58 59 64 65 68 86 100 101 105 106 196 225 156 157 211 224 44 45 205 0\n306 -11 -44 0 292 290 39 38 3 5 7 16 19 228 22 23 226 0\n307 -12 -44 0 292 39 38 17 20 21 228 0\n308 75 69 -44 0 294 307 306 305 302 34 33 32 303 304 230 0\n309 -87 78 -75 0 287 133 132 127 122 119 118 166 172 223 204 0\n310 -84 -75 -44 0 287 134 129 124 119 118 143 113 150 158 223 206 0\n311 -75 -44 0 289 288 117 120 125 131 310 225 171 309 224 137 0\n312 -44 0 307 311 298 308 0\n313 74 -37 -87 69 0 288 14 13 10 168 167 170 165 171 224 173 172 169 209 207 107 0\n314 -37 -87 69 0 288 294 168 167 170 165 171 224 137 309 138 11 135 178 313 108 109 110 111 112 114 115 230 0\n315 -87 69 0 288 287 293 312 294 163 164 165 166 167 168 170 171 174 224 136 137 159 161 309 314 223 47 51 52 53 147 229 192 24 25 26 27 28 29 30 193 194 191 190 189 230 0\n316 -50 69 0 288 289 312 293 315 225 154 151 155 149 156 224 144 142 162 160 48 49 50 51 119 147 210 229 192 103 197 295 208 214 0\n317 -43 83 69 0 287 288 289 315 225 154 151 155 149 156 224 139 150 316 223 118 158 157 135 178 295 88 177 144 142 103 199 209 116 0\n318 83 69 0 299 287 288 289 312 293 315 225 154 151 155 149 156 224 139 150 316 223 135 88 66 157 152 158 255 160 153 162 262 144 140 142 259 271 274 277 251 216 317 229 40 41 60 213 246 247 269 266 0\n319 69 0 289 288 287 312 293 291 315 225 149 150 151 154 155 156 157 158 224 139 142 144 316 223 12 88 118 135 178 184 295 318 146 148 218 229 186 183 227 0\n320 -12 0 319 93 0\n321 0 319 320 298 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record005.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record005.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record009
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "9e38cb32ac9b19c1f38ab2aaa9a99a1e996559361d98e338ae1b91e27b51cc671e26c9aa669c6599966391e785d16c5c96a599595555351d70da358d934cd8b4ad1b51d27783d0ec3c8ea398d9354d331cf0ba2d8b92ccb8acab1ad1b26d4731d2729c6725d0f1703c1683a61916158362384e0b81ee0689926291643961515154352344d0b41d60d1314c3322c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db4db6d24924924db4926d249b6da49349249249b6da493492492492492249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record009 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record009 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record009.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record009.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record009.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 56), (facetIndex 76), (facetIndex 90), (facetIndex 91)]))
 (.leaf ([(facetIndex 110), (facetIndex 114), (facetIndex 120)])))
 (.branch 3
 (.leaf ([(facetIndex 116)]))
 (.leaf ([(facetIndex 96), (facetIndex 97), (facetIndex 98)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 61), (facetIndex 62), (facetIndex 63), (facetIndex 64), (facetIndex 65)]))
 (.leaf ([(facetIndex 81), (facetIndex 82), (facetIndex 83), (facetIndex 84), (facetIndex 85)])))
 (.branch 7
 (.leaf ([(facetIndex 111), (facetIndex 112), (facetIndex 113)]))
 (.branch 8
 (.leaf ([(facetIndex 117), (facetIndex 118), (facetIndex 119)]))
 (.leaf ([(facetIndex 121)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "8177720166610000000000033300000000005555500000000000000044444z3d;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
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
def grouped3_0010 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7, 8]
def grouped3_0014 : List Nat := [7]
def grouped3_0015 : List Nat := [7, 8]
def grouped3_0016 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record009 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record009_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record009" "{\"atoms\":[{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":117},{\"tag\":\"facet\",\"index\":118},{\"tag\":\"facet\",\"index\":120},{\"tag\":\"facet\",\"index\":121},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record009" 49

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record009" "{\"ridges\":[[24,545],[24,552],[27,896],[51,545],[51,552],[61,610],[62,674],[63,802],[65,834],[66,896],[71,545],[71,552],[81,612],[82,676],[83,804],[85,836],[86,896],[88,545],[88,552],[91,792],[92,545],[92,552],[93,545],[93,552],[95,896],[96,624],[97,816],[98,848],[111,610],[112,674],[117,612],[118,676],[121,624]],\"owners\":[[24,545,[61,62,63,81,82,83,96,97],[51,71,88,92,93]],[51,545,[81,82,83,96,97],[24,61,62,63,71,88,92,93]],[71,545,[61,62,63,96,97],[24,51,81,82,83,88,92,93]],[88,545,[61,62,63,81,82,83],[24,51,71,92,93,96,97]],[92,545,[62,63,82,83,97],[24,51,61,71,81,88,93,96]],[93,545,[61,63,81,83,96,97],[24,51,62,71,82,88,92]],[24,552,[111,112,117,118,121],[51,71,88,92,93]],[51,552,[117,118,121],[24,71,88,92,93,111,112]],[71,552,[111,112,121],[24,51,88,92,93,117,118]],[88,552,[111,112,117,118],[24,51,71,92,93,121]],[92,552,[112,118],[24,51,71,88,93,111,117,121]],[93,552,[111,117,121],[24,51,71,88,92,112,118]],[27,896,[114,120],[66,86,95]],[66,896,[120],[27,86,95,114]],[86,896,[114],[27,66,95,120]],[95,896,[],[27,66,86,114,120]],[61,610,[111],[]],[111,610,[61],[]],[62,674,[112],[]],[112,674,[62],[]],[63,802,[],[]],[65,834,[],[]],[81,612,[117],[]],[117,612,[81],[]],[82,676,[118],[]],[118,676,[82],[]],[83,804,[],[]],[85,836,[],[]],[91,792,[],[]],[96,624,[121],[]],[121,624,[96],[]],[97,816,[],[]],[98,848,[],[]]],\"edges\":[[38,[24,51,61,62,63,71,81,82,83,88,92,93,96,97,111,112,117,118,121]],[44,[27,56,63,65,66,76,83,85,86,91,95,97,98,114,120]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record009" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record009\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,5,6,7,12,13,14,22,23],[-3,12,13,14,22,23],[-10,5,6,7,22,23],[-17,5,6,7,12,13,14],[-19,6,7,13,14,23],[-20,5,7,12,14,22,23],[-1,25,26,28,29,31],[-3,28,29,31],[-10,25,26,31],[-17,25,26,28,29],[-19,26,29],[-20,25,28,31],[-2,27,30],[-9,30],[-16,27],[-21],[-5,25],[-25,5],[-6,26],[-26,6],[-7],[-8],[-12,28],[-28,12],[-13,29],[-29,13],[-14],[-15],[-18],[-22,31],[-31,22],[-23],[-24],[-4,32],[-11,32],[-27,33],[-30,33],[-22,34],[-5,35],[-6,35],[-12,36],[-13,36],[-25,37],[-26,37],[-28,38],[-29,38],[-31,39],[-33,40],[-32,40],[-34,41],[-40,42],[-40,-41,43],[-36,44],[-35,44],[-39,45],[-38,45],[-45,46],[-37,46],[-46,47],[-44,-46,48],[-42,-48,49],[-43,-47,49],[-49],[1,3,5,6,7,10,12,13,14,17,19,20,22,23,25,26,28,29,31],[2,4,7,8,9,11,14,15,16,18,21,23,24,27,30]],\"atoms\":[{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":117},{\"tag\":\"facet\",\"index\":118},{\"tag\":\"facet\",\"index\":120},{\"tag\":\"facet\",\"index\":121},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":545,\"a\":24,\"owners\":[61,62,63,81,82,83,96,97]},{\"tag\":\"mate\",\"ridge\":545,\"a\":51,\"owners\":[81,82,83,96,97]},{\"tag\":\"mate\",\"ridge\":545,\"a\":71,\"owners\":[61,62,63,96,97]},{\"tag\":\"mate\",\"ridge\":545,\"a\":88,\"owners\":[61,62,63,81,82,83]},{\"tag\":\"mate\",\"ridge\":545,\"a\":92,\"owners\":[62,63,82,83,97]},{\"tag\":\"mate\",\"ridge\":545,\"a\":93,\"owners\":[61,63,81,83,96,97]},{\"tag\":\"mate\",\"ridge\":552,\"a\":24,\"owners\":[111,112,117,118,121]},{\"tag\":\"mate\",\"ridge\":552,\"a\":51,\"owners\":[117,118,121]},{\"tag\":\"mate\",\"ridge\":552,\"a\":71,\"owners\":[111,112,121]},{\"tag\":\"mate\",\"ridge\":552,\"a\":88,\"owners\":[111,112,117,118]},{\"tag\":\"mate\",\"ridge\":552,\"a\":92,\"owners\":[112,118]},{\"tag\":\"mate\",\"ridge\":552,\"a\":93,\"owners\":[111,117,121]},{\"tag\":\"mate\",\"ridge\":896,\"a\":27,\"owners\":[114,120]},{\"tag\":\"mate\",\"ridge\":896,\"a\":66,\"owners\":[120]},{\"tag\":\"mate\",\"ridge\":896,\"a\":86,\"owners\":[114]},{\"tag\":\"mate\",\"ridge\":896,\"a\":95,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":610,\"a\":61,\"owners\":[111]},{\"tag\":\"mate\",\"ridge\":610,\"a\":111,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":674,\"a\":62,\"owners\":[112]},{\"tag\":\"mate\",\"ridge\":674,\"a\":112,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":802,\"a\":63,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":834,\"a\":65,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":612,\"a\":81,\"owners\":[117]},{\"tag\":\"mate\",\"ridge\":612,\"a\":117,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":676,\"a\":82,\"owners\":[118]},{\"tag\":\"mate\",\"ridge\":676,\"a\":118,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":804,\"a\":83,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":836,\"a\":85,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":792,\"a\":91,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":624,\"a\":96,\"owners\":[121]},{\"tag\":\"mate\",\"ridge\":624,\"a\":121,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":816,\"a\":97,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":848,\"a\":98,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":56,\"full_literals\":[-4,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":76,\"full_literals\":[-11,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":114,\"full_literals\":[-27,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":120,\"full_literals\":[-30,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":96,\"full_literals\":[-22,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":61,\"full_literals\":[-5,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":62,\"full_literals\":[-6,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":81,\"full_literals\":[-12,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":82,\"full_literals\":[-13,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":111,\"full_literals\":[-25,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":112,\"full_literals\":[-26,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":117,\"full_literals\":[-28,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":118,\"full_literals\":[-29,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":121,\"full_literals\":[-31,39]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-33,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-32,false,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-34,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-40,-41,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-36,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-35,false,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-39,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-45,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-37,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-46,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-44,-46,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-42,-48,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-43,-47,49],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":38,\"owners\":[24,51,61,62,63,71,81,82,83,88,92,93,96,97,111,112,117,118,121]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[27,56,63,65,66,76,83,85,86,91,95,97,98,114,120]}]}"
  "66 1 3 5 6 10 12 13 17 19 20 22 25 26 28 29 31 0 21 27 32 64 0\n67 2 4 9 11 16 27 30 0 21 22 27 28 29 16 32 33 65 0\n68 40 0 48 49 36 37 34 35 15 14 13 67 0\n69 42 0 68 51 0\n70 -48 0 69 63 61 0\n71 44 22 0 27 32 21 31 53 54 41 42 39 40 2 24 1 4 6 26 5 18 3 20 66 0\n72 22 0 70 31 71 60 57 58 56 43 44 45 46 17 9 19 8 23 7 10 12 25 11 66 0\n73 31 0 72 30 0\n74 34 0 72 38 0\n75 39 0 73 47 0\n76 41 0 74 50 0\n77 45 0 75 55 0\n78 43 0 76 68 52 0\n79 46 0 77 57 0\n80 -47 0 78 63 62 0\n81 0 79 80 59 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record009.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record009.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record009.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record009.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record009 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record009.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record009.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record009.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record009.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record009 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record009_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record009 Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record009_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record009_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record009

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record011
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1f272e2b4ab2b2aaaa6a1eb86d1ac6c9aa699876538ce4b8ae1b91e27a71e2749b2729aa6691e785d16c5c96a599475534cd4b4ad1b51d27743b0f23a8e6394e331cf0ba2e4b52ccb8ad2b2ac6b46c9bc1e8791d4731e2749ca719d1725d8c1703ce098a1683a618560d90e2384e0b81ee058916439614550d50d2344d0b41dc0e8360e4388c530cd0b22c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "4d36db49b6da4924934db6d26db692492492492492492492492492491249249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record011 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record011 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record011.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record011.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record011.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 88), (facetIndex 95)]))
 (.leaf ([(facetIndex 110), (facetIndex 117)])))
 (.branch 3
 (.leaf ([(facetIndex 75), (facetIndex 76), (facetIndex 77), (facetIndex 78), (facetIndex 79), (facetIndex 80), (facetIndex 81)]))
 (.leaf ([(facetIndex 97), (facetIndex 98), (facetIndex 99), (facetIndex 100), (facetIndex 101), (facetIndex 102), (facetIndex 103)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 47), (facetIndex 58), (facetIndex 67), (facetIndex 70), (facetIndex 82), (facetIndex 89), (facetIndex 104), (facetIndex 111), (facetIndex 119)]))
 (.leaf ([(facetIndex 68), (facetIndex 69), (facetIndex 71), (facetIndex 72), (facetIndex 73), (facetIndex 74)])))
 (.branch 7
 (.leaf ([(facetIndex 45), (facetIndex 46), (facetIndex 48), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 52), (facetIndex 53), (facetIndex 54), (facetIndex 55)]))
 (.leaf ([(facetIndex 56), (facetIndex 57), (facetIndex 59), (facetIndex 60), (facetIndex 61), (facetIndex 62), (facetIndex 63), (facetIndex 64), (facetIndex 65), (facetIndex 66)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "8080008400046db6d800002000011249256db2d9ffffff3fdb6db69bz22;"⟩
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
def grouped2_0010 : List Nat := [6, 7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record011 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record011_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record011" "{\"atoms\":[{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":117},{\"tag\":\"facet\",\"index\":118},{\"tag\":\"facet\",\"index\":119},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record011" 45

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record011" "{\"ridges\":[[13,545],[50,545],[61,545],[68,545],[71,545],[72,545],[84,676],[85,804],[91,680],[92,808],[105,612],[112,616],[118,624]],\"owners\":[[13,545,[83,84,85,90,91,92,96],[50,61,68,70,71,72]],[50,545,[90,91,92,96],[13,61,68,70,71,72,83,84,85]],[61,545,[83,84,85,96],[13,50,68,70,71,72,90,91,92]],[68,545,[83,84,85,90,91,92],[13,50,61,70,71,72,96]],[71,545,[83,85,90,92,96],[13,50,61,68,70,72,84,91]],[72,545,[83,84,90,91,96],[13,50,61,68,70,71,85,92]],[105,612,[83],[]],[84,676,[106],[]],[85,804,[107],[]],[112,616,[90],[]],[91,680,[113],[]],[92,808,[114],[]],[118,624,[96],[]]],\"edges\":[[38,[13,50,61,68,70,71,72,83,84,85,90,91,92,96,105,106,107,112,113,114,118]]],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record011" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record011\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-9,-7],[-9,-8],[-10,-9],[-11,-9],[-12,-9],[-13,-9],[-15,-2],[-15,-4],[-15,-6],[-15,-14],[-19,-15],[-20,-2],[-20,-4],[-20,-6],[-20,-14],[-20,-19],[-24,-2],[-24,-4],[-24,-6],[-24,-14],[-24,-19],[-25,-15],[-25,-20],[-25,-24],[-27,-18],[-28,-18],[-29,-18],[-29,-27],[-29,-28],[-30,-15],[-30,-20],[-30,-24],[-32,-23],[-33,-23],[-34,-23],[-34,-32],[-34,-33],[-36,-15],[-36,-20],[-36,-24],[-1,15,16,17,20,21,22,24],[-3,20,21,22,24],[-5,15,16,17,24],[-7,15,16,17,20,21,22],[-10,15,17,20,22,24],[-11,15,16,20,21,24],[-26,15],[-16,27],[-17,28],[-31,20],[-21,32],[-22,33],[-35,24],[-37,18,23],[-38,29,34],[-39,2,4,6,9,14,19,25,30,36],[-40,7,8,10,11,12,13],[-41,37],[-41,38],[-42,41],[-43,39],[-43,40],[-44,43],[-45,42],[-45,44],[45],[1,3,5,7,9,10,11,15,16,17,20,21,22,24,26,27,28,31,32,33,35]],\"atoms\":[{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":117},{\"tag\":\"facet\",\"index\":118},{\"tag\":\"facet\",\"index\":119},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":70,\"b\":68},{\"tag\":\"incompatible\",\"a\":70,\"b\":69},{\"tag\":\"incompatible\",\"a\":71,\"b\":70},{\"tag\":\"incompatible\",\"a\":72,\"b\":70},{\"tag\":\"incompatible\",\"a\":73,\"b\":70},{\"tag\":\"incompatible\",\"a\":74,\"b\":70},{\"tag\":\"incompatible\",\"a\":83,\"b\":47},{\"tag\":\"incompatible\",\"a\":83,\"b\":58},{\"tag\":\"incompatible\",\"a\":83,\"b\":67},{\"tag\":\"incompatible\",\"a\":83,\"b\":82},{\"tag\":\"incompatible\",\"a\":89,\"b\":83},{\"tag\":\"incompatible\",\"a\":90,\"b\":47},{\"tag\":\"incompatible\",\"a\":90,\"b\":58},{\"tag\":\"incompatible\",\"a\":90,\"b\":67},{\"tag\":\"incompatible\",\"a\":90,\"b\":82},{\"tag\":\"incompatible\",\"a\":90,\"b\":89},{\"tag\":\"incompatible\",\"a\":96,\"b\":47},{\"tag\":\"incompatible\",\"a\":96,\"b\":58},{\"tag\":\"incompatible\",\"a\":96,\"b\":67},{\"tag\":\"incompatible\",\"a\":96,\"b\":82},{\"tag\":\"incompatible\",\"a\":96,\"b\":89},{\"tag\":\"incompatible\",\"a\":104,\"b\":83},{\"tag\":\"incompatible\",\"a\":104,\"b\":90},{\"tag\":\"incompatible\",\"a\":104,\"b\":96},{\"tag\":\"incompatible\",\"a\":106,\"b\":88},{\"tag\":\"incompatible\",\"a\":107,\"b\":88},{\"tag\":\"incompatible\",\"a\":110,\"b\":88},{\"tag\":\"incompatible\",\"a\":110,\"b\":106},{\"tag\":\"incompatible\",\"a\":110,\"b\":107},{\"tag\":\"incompatible\",\"a\":111,\"b\":83},{\"tag\":\"incompatible\",\"a\":111,\"b\":90},{\"tag\":\"incompatible\",\"a\":111,\"b\":96},{\"tag\":\"incompatible\",\"a\":113,\"b\":95},{\"tag\":\"incompatible\",\"a\":114,\"b\":95},{\"tag\":\"incompatible\",\"a\":117,\"b\":95},{\"tag\":\"incompatible\",\"a\":117,\"b\":113},{\"tag\":\"incompatible\",\"a\":117,\"b\":114},{\"tag\":\"incompatible\",\"a\":119,\"b\":83},{\"tag\":\"incompatible\",\"a\":119,\"b\":90},{\"tag\":\"incompatible\",\"a\":119,\"b\":96},{\"tag\":\"mate\",\"ridge\":545,\"a\":13,\"owners\":[83,84,85,90,91,92,96]},{\"tag\":\"mate\",\"ridge\":545,\"a\":50,\"owners\":[90,91,92,96]},{\"tag\":\"mate\",\"ridge\":545,\"a\":61,\"owners\":[83,84,85,96]},{\"tag\":\"mate\",\"ridge\":545,\"a\":68,\"owners\":[83,84,85,90,91,92]},{\"tag\":\"mate\",\"ridge\":545,\"a\":71,\"owners\":[83,85,90,92,96]},{\"tag\":\"mate\",\"ridge\":545,\"a\":72,\"owners\":[83,84,90,91,96]},{\"tag\":\"mate\",\"ridge\":612,\"a\":105,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":676,\"a\":84,\"owners\":[106]},{\"tag\":\"mate\",\"ridge\":804,\"a\":85,\"owners\":[107]},{\"tag\":\"mate\",\"ridge\":616,\"a\":112,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":680,\"a\":91,\"owners\":[113]},{\"tag\":\"mate\",\"ridge\":808,\"a\":92,\"owners\":[114]},{\"tag\":\"mate\",\"ridge\":624,\"a\":118,\"owners\":[96]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[88,95],\"full_literals\":[-37,18,23]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[110,117],\"full_literals\":[-38,29,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[47,58,67,70,82,89,104,111,119],\"full_literals\":[-39,2,4,6,9,14,19,25,30,36]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[68,69,71,72,73,74],\"full_literals\":[-40,7,8,10,11,12,13]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-41,37,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-41,false,38],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-42,41,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-43,39,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-43,false,40],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-44,43,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-45,42,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-45,false,44],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"edge\",\"edge\":38,\"owners\":[13,50,61,68,70,71,72,83,84,85,90,91,92,96,105,106,107,112,113,114,118]}]}"
  "68 42 0 66 64 0\n69 44 0 66 65 0\n70 41 0 68 60 0\n71 43 0 69 63 0\n72 37 0 70 58 0\n73 38 0 70 59 0\n74 39 0 71 61 0\n75 40 0 71 62 0\n76 21 9 3 5 1 35 11 15 16 17 20 7 22 24 26 27 28 31 32 33 0 67 45 0\n77 21 33 3 5 1 35 11 15 16 17 20 9 7 24 26 27 28 31 32 0 76 52 0\n78 -9 0 75 1 2 3 4 5 6 57 0\n79 -27 0 72 73 25 28 54 55 35 0\n80 -16 0 79 48 0\n81 -28 0 72 73 26 29 54 55 35 0\n82 -17 0 81 49 0\n83 -32 0 72 73 33 36 54 55 27 0\n84 -21 0 83 51 0\n85 -33 0 72 73 34 37 54 55 27 0\n86 -22 0 85 52 0\n87 15 20 24 0 86 82 81 79 78 80 84 85 83 42 50 53 47 43 46 41 44 77 0\n88 -15 0 78 74 7 8 9 10 11 22 30 38 56 0\n89 -20 0 78 74 12 13 14 15 16 23 31 39 56 0\n90 24 0 89 88 87 0\n91 -2 0 90 17 0\n92 -4 0 90 18 0\n93 -6 0 90 19 0\n94 -14 0 90 20 0\n95 -19 0 90 21 0\n96 -25 0 90 24 0\n97 -30 0 90 32 0\n98 -36 0 90 40 0\n99 0 92 97 74 91 93 94 95 96 78 98 56 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record011.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record011.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record011.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record011.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record011 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record011.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record011.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record011.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record011.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record011 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record011_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record011 Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record011_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record011_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record011

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record018
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3a4ad1ac9707c6a93a1eb86b19a6a5a562d8766392e2b86ee8731ac7496a719965391e785b1725a95a5a56352d475c358d9352d2b46d87783d0ec3c4e9394d332cc7362d4b2ac6b46f07a1d8791cc749c6785c9743c8f9505c0f1a24a85a0e8a6158361382e07b81686514a4590e685914a5854550d44d0b41d60d2328c530cd0b12c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db4924da6926924db4d249349249b49249b6d2492493492492489249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record018 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record018 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record018.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record018.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record018.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 42), (facetIndex 43), (facetIndex 53), (facetIndex 54), (facetIndex 55), (facetIndex 56), (facetIndex 57)]))
 (.leaf ([(facetIndex 67), (facetIndex 71), (facetIndex 74), (facetIndex 85), (facetIndex 107)])))
 (.branch 3
 (.leaf ([(facetIndex 76), (facetIndex 79), (facetIndex 91)]))
 (.branch 4
 (.leaf ([(facetIndex 45), (facetIndex 49), (facetIndex 51), (facetIndex 61), (facetIndex 66), (facetIndex 98)]))
 (.leaf ([(facetIndex 48), (facetIndex 81)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 60), (facetIndex 84), (facetIndex 104)]))
 (.leaf ([(facetIndex 44), (facetIndex 59), (facetIndex 75), (facetIndex 77), (facetIndex 97)])))
 (.branch 8
 (.leaf ([(facetIndex 47), (facetIndex 69), (facetIndex 87), (facetIndex 93), (facetIndex 105)]))
 (.branch 9
 (.leaf ([(facetIndex 46), (facetIndex 58), (facetIndex 68), (facetIndex 83), (facetIndex 92), (facetIndex 96), (facetIndex 103), (facetIndex 106)]))
 (.leaf ([(facetIndex 50), (facetIndex 70), (facetIndex 78), (facetIndex 82), (facetIndex 94), (facetIndex 100)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "1875800903680978200070158940296261001978130000356800000039347836z2c;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 73), (facetIndex 86), (facetIndex 88)]))
 (.leaf ([(facetIndex 52), (facetIndex 72), (facetIndex 80)])))
 (.branch 3
 (.leaf ([(facetIndex 89), (facetIndex 90), (facetIndex 110)]))
 (.leaf ([(facetIndex 95), (facetIndex 102)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 108)]))
 (.leaf ([(facetIndex 62), (facetIndex 109)])))
 (.branch 7
 (.leaf ([(facetIndex 63), (facetIndex 64), (facetIndex 65), (facetIndex 99)]))
 (.leaf ([(facetIndex 101)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "ac0000f8c00600090000001000001000036d40000001z27;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3, 4]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [3, 4]
def grouped2_0007 : List Nat := [4]
def grouped2_0008 : List Nat := [5, 6]
def grouped2_0009 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0010 : List Nat := [7]
def grouped2_0011 : List Nat := [7, 8, 9]
def grouped2_0012 : List Nat := [8]
def grouped2_0013 : List Nat := [8, 9]
def grouped2_0014 : List Nat := [9]
def grouped3_0015 : List Nat := [0]
def grouped3_0016 : List Nat := [0, 1]
def grouped3_0017 : List Nat := [0, 1, 2, 3]
def grouped3_0019 : List Nat := [1]
def grouped3_0020 : List Nat := [2]
def grouped3_0021 : List Nat := [2, 3]
def grouped3_0022 : List Nat := [3]
def grouped3_0023 : List Nat := [4]
def grouped3_0024 : List Nat := [4, 5]
def grouped3_0025 : List Nat := [4, 5, 6, 7]
def grouped3_0026 : List Nat := [5]
def grouped3_0027 : List Nat := [6]
def grouped3_0028 : List Nat := [6, 7]
def grouped3_0029 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record018 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record018_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record018" "{\"atoms\":[{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record018" 76

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record018" "{\"ridges\":[[19,517],[21,517],[22,517],[26,529],[28,769],[28,896],[41,580],[51,644],[52,774],[61,577],[63,786],[65,834],[66,769],[66,896],[67,517],[72,396],[73,780],[79,644],[80,517],[80,804],[82,896],[85,529],[86,792],[88,840],[89,688],[90,816],[91,769],[91,896],[98,532],[102,774],[107,532],[110,644],[110,804]],\"owners\":[[26,529,[19,45,62,63,67,76,77,86,89,90],[61,85]],[85,529,[19,45,62,63,76,77,89,90],[26,61,67,86]],[98,532,[19,67,76,77,109],[41,45,99,107]],[107,532,[19,45,76,77,99,109],[41,67,98]],[61,577,[21,71,81,88],[26,49,64,65,85]],[41,580,[21,49,71,81,101],[98,107]],[51,644,[109,110],[22,77,79,81,82,99,101,102]],[79,644,[99,101,102],[22,51,77,81,82,109,110]],[110,644,[22,51,77,81,99,101],[79,82,102,109]],[28,769,[52,63,65,73,80,86,88,90],[66,82,91]],[66,769,[73,80,86,88,90],[28,52,63,65,82,91]],[91,769,[52,63,65,73,86,88],[28,66,80,82,90]],[28,896,[102,110],[66,82,91]],[66,896,[110],[28,82,91,102]],[82,896,[],[28,66,91,102,110]],[91,896,[102],[28,66,82,110]],[52,774,[102],[]],[102,774,[52],[]],[63,786,[],[]],[65,834,[],[]],[72,396,[95,108],[]],[73,780,[],[]],[80,804,[110],[]],[110,804,[80],[]],[86,792,[],[]],[88,840,[],[]],[89,688,[109],[]],[90,816,[],[]]],\"edges\":[[34,[19,26,41,45,61,62,63,67,76,77,85,86,89,90,98,99,107,109]],[44,[28,52,63,65,66,73,80,82,86,88,90,91,102,110]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record018" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record018\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-8,-7],[-9,-8],[-11,-8],[-12,-8],[-20,-8],[-27,-24],[-28,-12],[-28,-27],[-42,-7],[-42,-9],[-42,-10],[-42,-13],[-42,-19],[-42,-25],[-42,-36],[-42,-38],[-42,-40],[-44,-12],[-44,-27],[-46,-10],[-46,-19],[-46,-23],[-46,-25],[-46,-36],[-46,-40],[-1,-3,-27],[-2,-3,-27],[-3,-18,-27],[-4,1,7,14,15,18,23,24,31,33,34],[-30,1,7,14,15,23,24,33,34],[-38,1,18,23,24,45],[-43,1,7,23,24,39,45],[-13,2,20,28,32],[-6,2,9,20,28,41],[-11,45,46],[-26,39,41,42],[-46,3,11,24,28,39,41],[-5,12,15,16,22,27,31,32,34],[-17,22,27,31,32,34],[-35,12,15,16,22,31,32],[-5,42,46],[-17,46],[-29],[-35,42],[-12,42],[-42,12],[-15],[-16],[-21,37,44],[-22],[-27,46],[-46,27],[-31],[-32],[-33,45],[-34],[-47,23,26,35],[-48,7,9,11,13,17,38],[-49,8,28],[-50,10,19,25,29,36,40],[-51,48,49],[-52,49],[-53,47,52],[-53,51],[-54,53],[-55,50],[-56,55],[-57,56],[-58,54,57],[58],[-59,22,31,32],[-60,12,21,27],[-12,60],[-27,60],[-61,33,34,46],[-46,61],[-37,62],[-42,62],[-44,63],[-14,64],[-45,64],[-39,65],[-41,66],[-67,59,60],[-60,67],[-68,61,62],[-62,68],[-61,68],[-61,-62,69],[-70,67,68],[-68,70],[-67,70],[-67,-68,71],[-67,-69,72],[-64,73],[-63,73],[-66,74],[-65,74],[-74,75],[-73,75],[-71,-75,76],[-72,76],[-76],[1,4,6,7,13,14,15,18,23,24,30,31,33,34,38,39,43,45],[5,12,15,16,17,22,27,29,31,32,34,35,42,46]],\"atoms\":[{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":48,\"b\":45},{\"tag\":\"incompatible\",\"a\":49,\"b\":48},{\"tag\":\"incompatible\",\"a\":51,\"b\":48},{\"tag\":\"incompatible\",\"a\":52,\"b\":48},{\"tag\":\"incompatible\",\"a\":71,\"b\":48},{\"tag\":\"incompatible\",\"a\":80,\"b\":77},{\"tag\":\"incompatible\",\"a\":81,\"b\":52},{\"tag\":\"incompatible\",\"a\":81,\"b\":80},{\"tag\":\"incompatible\",\"a\":102,\"b\":45},{\"tag\":\"incompatible\",\"a\":102,\"b\":49},{\"tag\":\"incompatible\",\"a\":102,\"b\":50},{\"tag\":\"incompatible\",\"a\":102,\"b\":61},{\"tag\":\"incompatible\",\"a\":102,\"b\":70},{\"tag\":\"incompatible\",\"a\":102,\"b\":78},{\"tag\":\"incompatible\",\"a\":102,\"b\":94},{\"tag\":\"incompatible\",\"a\":102,\"b\":98},{\"tag\":\"incompatible\",\"a\":102,\"b\":100},{\"tag\":\"incompatible\",\"a\":108,\"b\":52},{\"tag\":\"incompatible\",\"a\":108,\"b\":80},{\"tag\":\"incompatible\",\"a\":110,\"b\":50},{\"tag\":\"incompatible\",\"a\":110,\"b\":70},{\"tag\":\"incompatible\",\"a\":110,\"b\":76},{\"tag\":\"incompatible\",\"a\":110,\"b\":78},{\"tag\":\"incompatible\",\"a\":110,\"b\":94},{\"tag\":\"incompatible\",\"a\":110,\"b\":100},{\"tag\":\"three\",\"ridge\":517,\"vertices\":[19,22,80]},{\"tag\":\"three\",\"ridge\":517,\"vertices\":[21,22,80]},{\"tag\":\"three\",\"ridge\":517,\"vertices\":[22,67,80]},{\"tag\":\"mate\",\"ridge\":529,\"a\":26,\"owners\":[19,45,62,63,67,76,77,86,89,90]},{\"tag\":\"mate\",\"ridge\":529,\"a\":85,\"owners\":[19,45,62,63,76,77,89,90]},{\"tag\":\"mate\",\"ridge\":532,\"a\":98,\"owners\":[19,67,76,77,109]},{\"tag\":\"mate\",\"ridge\":532,\"a\":107,\"owners\":[19,45,76,77,99,109]},{\"tag\":\"mate\",\"ridge\":577,\"a\":61,\"owners\":[21,71,81,88]},{\"tag\":\"mate\",\"ridge\":580,\"a\":41,\"owners\":[21,49,71,81,101]},{\"tag\":\"mate\",\"ridge\":644,\"a\":51,\"owners\":[109,110]},{\"tag\":\"mate\",\"ridge\":644,\"a\":79,\"owners\":[99,101,102]},{\"tag\":\"mate\",\"ridge\":644,\"a\":110,\"owners\":[22,51,77,81,99,101]},{\"tag\":\"mate\",\"ridge\":769,\"a\":28,\"owners\":[52,63,65,73,80,86,88,90]},{\"tag\":\"mate\",\"ridge\":769,\"a\":66,\"owners\":[73,80,86,88,90]},{\"tag\":\"mate\",\"ridge\":769,\"a\":91,\"owners\":[52,63,65,73,86,88]},{\"tag\":\"mate\",\"ridge\":896,\"a\":28,\"owners\":[102,110]},{\"tag\":\"mate\",\"ridge\":896,\"a\":66,\"owners\":[110]},{\"tag\":\"mate\",\"ridge\":896,\"a\":82,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":896,\"a\":91,\"owners\":[102]},{\"tag\":\"mate\",\"ridge\":774,\"a\":52,\"owners\":[102]},{\"tag\":\"mate\",\"ridge\":774,\"a\":102,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":786,\"a\":63,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":834,\"a\":65,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":396,\"a\":72,\"owners\":[95,108]},{\"tag\":\"mate\",\"ridge\":780,\"a\":73,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":804,\"a\":80,\"owners\":[110]},{\"tag\":\"mate\",\"ridge\":804,\"a\":110,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":792,\"a\":86,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":840,\"a\":88,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":688,\"a\":89,\"owners\":[109]},{\"tag\":\"mate\",\"ridge\":816,\"a\":90,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[76,79,91],\"full_literals\":[-47,23,26,35]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[45,49,51,61,66,98],\"full_literals\":[-48,7,9,11,13,17,38]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[48,81],\"full_literals\":[-49,8,28]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[50,70,78,82,94,100],\"full_literals\":[-50,10,19,25,29,36,40]},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-51,48,49],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-52,false,49],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-53,47,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-53,false,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-54,false,53],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-55,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-56,false,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-57,false,56],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-58,54,57],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[73,86,88],\"full_literals\":[-59,22,31,32]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[52,72,80],\"full_literals\":[-60,12,21,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":52,\"full_literals\":[-12,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":80,\"full_literals\":[-27,60]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[89,90,110],\"full_literals\":[-61,33,34,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":110,\"full_literals\":[-46,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":95,\"full_literals\":[-37,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":102,\"full_literals\":[-42,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":108,\"full_literals\":[-44,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":62,\"full_literals\":[-14,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":109,\"full_literals\":[-45,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":99,\"full_literals\":[-39,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":101,\"full_literals\":[-41,66]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-67,59,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-60,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-68,61,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-62,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-61,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-61,-62,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-70,67,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-68,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-67,false,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-67,-68,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-67,-69,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-64,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-66,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-65,false,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-74,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-73,false,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-71,-75,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-72,false,76],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":34,\"owners\":[19,26,41,45,61,62,63,67,76,77,85,86,89,90,98,99,107,109]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[28,52,63,65,66,73,80,82,86,88,90,91,102,110]}]}"
  "106 -50 10 19 25 36 40 0 43 60 0\n107 -59 0 50 53 54 71 0\n108 -61 33 46 0 56 75 0\n109 -67 60 0 107 84 0\n110 -72 0 103 102 0\n111 1 4 6 7 13 14 18 23 24 30 33 38 39 43 45 0 47 53 56 104 0\n112 5 12 17 27 35 42 46 0 47 48 50 43 53 54 56 105 0\n113 70 0 91 92 87 88 85 78 76 73 74 44 42 41 112 0\n114 68 44 0 113 87 88 90 77 78 76 109 49 45 51 72 0\n115 60 0 56 54 53 50 48 47 73 74 40 46 39 52 38 112 0\n116 67 0 115 85 0\n117 68 0 87 88 114 78 76 18 19 44 42 41 112 0\n118 -69 0 116 110 94 0\n119 71 0 117 116 93 0\n120 -75 0 119 103 101 0\n121 -74 0 120 99 0\n122 -73 0 120 100 0\n123 -66 0 121 97 0\n124 -65 0 121 98 0\n125 -64 0 122 95 0\n126 -63 0 122 96 0\n127 -41 0 123 83 0\n128 -39 0 124 82 0\n129 -14 0 125 80 0\n130 -45 0 125 81 0\n131 -44 0 126 79 0\n132 -33 0 130 55 0\n133 62 0 117 131 115 70 53 56 47 127 54 130 128 132 129 77 78 86 49 44 45 36 108 72 20 21 22 23 24 25 6 8 57 106 66 67 68 69 65 63 62 59 1 2 3 5 37 26 27 28 31 29 30 32 34 33 111 0\n134 -61 0 133 118 89 0\n135 -46 0 134 76 0\n136 -17 0 135 42 0\n137 -27 0 135 51 0\n138 -11 0 135 130 35 0\n139 42 0 135 137 136 44 45 41 112 0\n140 -7 0 139 9 0\n141 -9 0 139 10 0\n142 -10 0 139 11 0\n143 -13 0 139 12 0\n144 -19 0 139 13 0\n145 -25 0 139 14 0\n146 -36 0 139 15 0\n147 -38 0 139 16 0\n148 -40 0 139 17 0\n149 12 0 139 46 0\n150 -50 0 145 142 144 146 148 106 0\n151 -48 0 147 141 138 140 143 136 58 0\n152 -8 0 149 4 0\n153 -28 0 149 7 0\n154 -55 0 150 66 0\n155 -49 0 152 153 59 0\n156 -56 0 154 67 0\n157 -51 0 155 151 61 0\n158 -57 0 156 68 0\n159 -53 0 157 64 0\n160 54 0 158 70 69 0\n161 0 160 159 65 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record018.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record018.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record018.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record018.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record018 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record018.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record018.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record018.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record018.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record018 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record018_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record018_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record018_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record018_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record018_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record018_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record018_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record018 Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record018_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record018_validity Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record018_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00009.record018
