module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00138Frames
public import GraphInputsRow29Part00138Leaves
public import GraphInputsRow29Part00138Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00138.record013
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "6e174ab26ca725c4f0bc1f2e2b48f2aaa6aa6a5a4e8ba1eaa699a96959362d876a3a4e8b92e2b86e8791e2785e0f9b15c4f16a5994e4b91e565555352d475a364d2b46d2745d0f6c338cd34ccb31ce8b92d2b1ad1b16c3ba1e4749ca745c970de0f43c8f13d2c4728a2a89a9186615a0e0b81e4a4a94649949465454554342d074a318c9314c8b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db4db6d34da6d34da4924924936d249a49a6d249349a49a492692492491249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record013 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record013 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record013.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record013.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record013.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 56), (facetIndex 74), (facetIndex 103), (facetIndex 104)]))
 (.leaf ([(facetIndex 43), (facetIndex 65), (facetIndex 92), (facetIndex 94)])))
 (.branch 3
 (.leaf ([(facetIndex 49), (facetIndex 69), (facetIndex 98), (facetIndex 100)]))
 (.leaf ([(facetIndex 63), (facetIndex 89), (facetIndex 109), (facetIndex 111)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 62), (facetIndex 95), (facetIndex 108), (facetIndex 110)]))
 (.leaf ([(facetIndex 53), (facetIndex 75), (facetIndex 76), (facetIndex 102), (facetIndex 105), (facetIndex 106)])))
 (.branch 7
 (.leaf ([(facetIndex 90), (facetIndex 112), (facetIndex 113)]))
 (.leaf ([(facetIndex 97)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "3671c1681420b8841198000000005a000100087000000280100002z20;"⟩
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
def grouped3_0012 : List Nat := [6, 7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record013 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record013_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00138.record013" "{\"atoms\":[{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00138.record013" 39

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00138.record013" "{\"ridges\":[[24,522],[27,580],[30,642],[30,648],[36,522],[42,580],[49,585],[50,642],[50,648],[56,705],[62,585],[63,645],[81,522],[85,522],[86,580],[87,648],[91,580],[93,580],[98,600],[99,642],[99,648],[100,616],[101,642],[101,648],[103,720],[104,736],[108,600],[109,660],[110,616],[111,676]],\"owners\":[[24,522,[30,49,50,98,99,100,101],[36,81,85,86]],[36,522,[30,98,99,100,101],[24,49,50,81,85,86]],[81,522,[30,49,50,100,101],[24,36,85,86,98,99]],[85,522,[30,49,50,98,99],[24,36,81,86,100,101]],[27,580,[62,108,110],[42,86,91,93]],[42,580,[108,110],[27,62,86,91,93]],[86,580,[],[27,42,62,91,93,108,110]],[91,580,[62,110],[27,42,86,93,108]],[93,580,[62,108],[27,42,86,91,110]],[30,642,[43,56,92,94,103,104],[50,87,99,101]],[50,642,[92,94,103,104],[30,43,56,87,99,101]],[99,642,[43,56,94,104],[30,50,87,92,101,103]],[101,642,[43,56,92,103],[30,50,87,94,99,104]],[30,648,[63,109,111],[50,87,99,101]],[50,648,[109,111],[30,63,87,99,101]],[87,648,[],[30,50,63,99,101,109,111]],[99,648,[63,111],[30,50,87,101,109]],[101,648,[63,109],[30,50,87,99,111]],[63,645,[43],[]],[49,585,[62],[]],[62,585,[49],[]],[56,705,[],[]],[109,660,[92],[]],[111,676,[94],[]],[98,600,[108],[]],[108,600,[98],[]],[100,616,[110],[]],[110,616,[100],[]],[103,720,[],[]],[104,736,[],[]]],\"edges\":[[29,[24,30,36,49,50,62,63,81,85,86,87,98,99,100,101,108,109,110,111]],[41,[27,42,49,56,62,86,91,93,98,100,103,104,108,110]],[43,[30,43,50,56,63,87,92,94,99,101,103,104,109,111]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00138.record013" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00138.record013\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,3,7,8,20,21,22,23],[-4,3,20,21,22,23],[-12,3,7,8,22,23],[-13,3,7,8,20,21],[-2,10,26,28],[-5,26,28],[-14],[-16,10,28],[-18,10,26],[-3,6,9,17,19,24,25],[-8,17,19,24,25],[-21,6,9,19,25],[-23,6,9,17,24],[-3,11,27,29],[-8,27,29],[-15],[-21,11,29],[-23,11,27],[-11,6],[-7,10],[-10,7],[-9],[-27,17],[-29,19],[-20,26],[-26,20],[-22,28],[-28,22],[-24],[-25],[-6,30],[-17,30],[-19,30],[-7,31],[-20,31],[-22,31],[-11,32],[-27,32],[-29,32],[-10,33],[-26,33],[-28,33],[-30,34],[-32,35],[-31,35],[-34,-35,36],[-33,37],[-37,38],[-36,-38,39],[-39],[1,3,4,7,8,10,11,12,13,14,15,20,21,22,23,26,27,28,29],[2,5,7,9,10,14,16,18,20,22,24,25,26,28],[3,6,8,9,11,15,17,19,21,23,24,25,27,29]],\"atoms\":[{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":522,\"a\":24,\"owners\":[30,49,50,98,99,100,101]},{\"tag\":\"mate\",\"ridge\":522,\"a\":36,\"owners\":[30,98,99,100,101]},{\"tag\":\"mate\",\"ridge\":522,\"a\":81,\"owners\":[30,49,50,100,101]},{\"tag\":\"mate\",\"ridge\":522,\"a\":85,\"owners\":[30,49,50,98,99]},{\"tag\":\"mate\",\"ridge\":580,\"a\":27,\"owners\":[62,108,110]},{\"tag\":\"mate\",\"ridge\":580,\"a\":42,\"owners\":[108,110]},{\"tag\":\"mate\",\"ridge\":580,\"a\":86,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":580,\"a\":91,\"owners\":[62,110]},{\"tag\":\"mate\",\"ridge\":580,\"a\":93,\"owners\":[62,108]},{\"tag\":\"mate\",\"ridge\":642,\"a\":30,\"owners\":[43,56,92,94,103,104]},{\"tag\":\"mate\",\"ridge\":642,\"a\":50,\"owners\":[92,94,103,104]},{\"tag\":\"mate\",\"ridge\":642,\"a\":99,\"owners\":[43,56,94,104]},{\"tag\":\"mate\",\"ridge\":642,\"a\":101,\"owners\":[43,56,92,103]},{\"tag\":\"mate\",\"ridge\":648,\"a\":30,\"owners\":[63,109,111]},{\"tag\":\"mate\",\"ridge\":648,\"a\":50,\"owners\":[109,111]},{\"tag\":\"mate\",\"ridge\":648,\"a\":87,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":648,\"a\":99,\"owners\":[63,111]},{\"tag\":\"mate\",\"ridge\":648,\"a\":101,\"owners\":[63,109]},{\"tag\":\"mate\",\"ridge\":645,\"a\":63,\"owners\":[43]},{\"tag\":\"mate\",\"ridge\":585,\"a\":49,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":585,\"a\":62,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":705,\"a\":56,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":660,\"a\":109,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":676,\"a\":111,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":600,\"a\":98,\"owners\":[108]},{\"tag\":\"mate\",\"ridge\":600,\"a\":108,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":616,\"a\":100,\"owners\":[110]},{\"tag\":\"mate\",\"ridge\":616,\"a\":110,\"owners\":[100]},{\"tag\":\"mate\",\"ridge\":720,\"a\":103,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":736,\"a\":104,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":43,\"full_literals\":[-6,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":92,\"full_literals\":[-17,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":94,\"full_literals\":[-19,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":49,\"full_literals\":[-7,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":98,\"full_literals\":[-20,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":100,\"full_literals\":[-22,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":63,\"full_literals\":[-11,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":109,\"full_literals\":[-27,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":111,\"full_literals\":[-29,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":62,\"full_literals\":[-10,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":108,\"full_literals\":[-26,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":110,\"full_literals\":[-28,33]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-30,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-32,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-31,false,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-34,-35,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-33,false,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-37,false,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-36,-38,39],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":29,\"owners\":[24,30,36,49,50,62,63,81,85,86,87,98,99,100,101,108,109,110,111]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[27,42,49,56,62,86,91,93,98,100,103,104,108,110]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[30,43,50,56,63,87,92,94,99,101,103,104,109,111]}]}"
  "p cnf 39 53\n-1 3 7 8 20 21 22 23 0\n-4 3 20 21 22 23 0\n-12 3 7 8 22 23 0\n-13 3 7 8 20 21 0\n-2 10 26 28 0\n-5 26 28 0\n-14 0\n-16 10 28 0\n-18 10 26 0\n-3 6 9 17 19 24 25 0\n-8 17 19 24 25 0\n-21 6 9 19 25 0\n-23 6 9 17 24 0\n-3 11 27 29 0\n-8 27 29 0\n-15 0\n-21 11 29 0\n-23 11 27 0\n-11 6 0\n-7 10 0\n-10 7 0\n-9 0\n-27 17 0\n-29 19 0\n-20 26 0\n-26 20 0\n-22 28 0\n-28 22 0\n-24 0\n-25 0\n-6 30 0\n-17 30 0\n-19 30 0\n-7 31 0\n-20 31 0\n-22 31 0\n-11 32 0\n-27 32 0\n-29 32 0\n-10 33 0\n-26 33 0\n-28 33 0\n-30 34 0\n-32 35 0\n-31 35 0\n-34 -35 36 0\n-33 37 0\n-37 38 0\n-36 -38 39 0\n-39 0\n1 3 4 7 8 10 11 12 13 14 15 20 21 22 23 26 27 28 29 0\n2 5 7 9 10 14 16 18 20 22 24 25 26 28 0\n3 6 8 9 11 15 17 19 21 23 24 25 27 29 0\n"
  "54 1 3 4 7 8 10 11 12 13 20 21 22 23 26 27 28 29 0 7 16 51 0\n55 2 5 7 10 16 18 20 22 26 28 0 22 7 29 30 52 0\n56 3 6 8 11 17 19 21 23 27 29 0 22 16 29 30 53 0\n57 35 0 44 45 37 38 39 34 35 36 15 14 18 17 21 26 28 1 2 3 4 54 0\n58 30 0 29 30 22 31 32 33 19 11 23 10 13 24 12 56 0\n59 34 0 58 43 0\n60 36 0 59 57 46 0\n61 -38 0 60 50 49 0\n62 -37 0 61 48 0\n63 -33 0 62 47 0\n64 -10 0 63 40 0\n65 -26 0 63 41 0\n66 -28 0 63 42 0\n67 -7 0 64 20 0\n68 -5 0 65 66 6 0\n69 -20 0 65 25 0\n70 -2 0 65 64 66 5 0\n71 -18 0 65 64 9 0\n72 -22 0 66 27 0\n73 -16 0 66 64 8 0\n74 0 70 73 65 64 66 71 69 72 68 67 55 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record013.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record013.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record013.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record013.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record013 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record013.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record013.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record013.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record013.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record013 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record013_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record013 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record013_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record013_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00138.record013

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00138.record014
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "b92d43d2ac9b29c9713c2f07c6c9723c93a2e87ab18e6359362d876a3a4e4b8ae1b91e2785e0fae1b45b15c4f1aa669a66594e4b91e6c5a966539695954d54d4b51d68d9362d4b4ad1b61d4749d1743db0da358ce364d5334d332cc73a2e4b2ac6b26c5b0ee8791cc749d170de0f43c8f13d2a468a6198961582e0792946685914a5194951560d0b41d48ca318d1324c5342c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6db6db69b69349b4924936db6db4da49249a49249249269249249b492492492491249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record014 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record014 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record014.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record014.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record014.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 48), (facetIndex 49), (facetIndex 59)]))
 (.leaf ([(facetIndex 84), (facetIndex 85), (facetIndex 91)])))
 (.branch 3
 (.leaf ([(facetIndex 86), (facetIndex 87), (facetIndex 92)]))
 (.leaf ([(facetIndex 100), (facetIndex 101), (facetIndex 107)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 117), (facetIndex 118), (facetIndex 122)]))
 (.leaf ([(facetIndex 119), (facetIndex 120), (facetIndex 123)])))
 (.branch 7
 (.leaf ([(facetIndex 73), (facetIndex 81), (facetIndex 82), (facetIndex 88), (facetIndex 89), (facetIndex 90)]))
 (.branch 8
 (.leaf ([(facetIndex 104), (facetIndex 108), (facetIndex 109), (facetIndex 111), (facetIndex 112), (facetIndex 113)]))
 (.leaf ([(facetIndex 114), (facetIndex 115), (facetIndex 116), (facetIndex 121)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "548554488877707730070033000000021666221106600000006z49;"⟩
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
def grouped3_0012 : List Nat := [6, 7, 8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record014 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record014_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00138.record014" "{\"atoms\":[{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":117},{\"tag\":\"facet\",\"index\":118},{\"tag\":\"facet\",\"index\":119},{\"tag\":\"facet\",\"index\":120},{\"tag\":\"facet\",\"index\":122},{\"tag\":\"facet\",\"index\":123},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00138.record014" 45

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00138.record014" "{\"ridges\":[[16,521],[16,524],[21,577],[22,641],[36,521],[36,524],[41,577],[41,580],[42,641],[42,644],[48,586],[49,650],[59,577],[59,706],[64,521],[64,524],[68,521],[69,521],[69,524],[69,577],[70,521],[70,524],[70,641],[75,577],[76,641],[78,577],[79,641],[80,577],[80,641],[80,644],[84,577],[84,600],[85,664],[86,616],[87,680],[91,720],[92,736],[100,586],[101,650],[107,706],[117,600],[118,664],[119,616],[120,680],[122,720],[123,736]],\"owners\":[[16,521,[48,49,84,85,86,87],[36,64,68,69,70]],[36,521,[84,85,86,87],[16,48,49,64,68,69,70]],[64,521,[48,49,86,87],[16,36,68,69,70,84,85]],[68,521,[48,49,84,85],[16,36,64,69,70,86,87]],[69,521,[49,85,87],[16,36,48,64,68,70,84,86]],[70,521,[48,84,86],[16,36,49,64,68,69,85,87]],[16,524,[100,101,117,118,119,120],[36,64,68,69,70]],[36,524,[117,118,119,120],[16,64,68,69,70,100,101]],[64,524,[100,101,119,120],[16,36,68,69,70,117,118]],[69,524,[101,118,120],[16,36,64,68,70,100,117,119]],[70,524,[100,117,119],[16,36,64,68,69,101,118,120]],[21,577,[48,59,84,86,91,92],[41,69,75,78,80]],[41,577,[84,86,91,92],[21,48,59,69,75,78,80]],[59,577,[21,69,75,78,84,86],[41,48,80,91,92]],[69,577,[59,91,92],[21,41,48,75,78,80,84,86]],[75,577,[48,59,86,92],[21,41,69,78,80,84,91]],[78,577,[48,59,84,91],[21,41,69,75,80,86,92]],[80,577,[48,84,86],[21,41,59,69,75,78,91,92]],[84,577,[21,41,59,78,80,92],[48,69,75,86,91]],[41,580,[117,119,122,123],[21,69,75,78,80,100,107]],[22,641,[49,59,85,87,91,92],[42,70,76,79,80]],[42,641,[85,87,91,92],[22,49,59,70,76,79,80]],[70,641,[59,91,92],[22,42,49,76,79,80,85,87]],[76,641,[49,59,87,92],[22,42,70,79,80,85,91]],[79,641,[49,59,85,91],[22,42,70,76,80,87,92]],[80,641,[49,85,87],[22,42,59,70,76,79,91,92]],[42,644,[118,120,122,123],[22,70,76,79,80,101,107]],[80,644,[101,118,120],[22,42,70,76,79,107,122,123]],[48,586,[100],[]],[100,586,[48],[]],[49,650,[101],[]],[101,650,[49],[]],[59,706,[107],[]],[107,706,[59],[]],[84,600,[117],[]],[117,600,[84],[]],[85,664,[118],[]],[118,664,[85],[]],[86,616,[119],[]],[119,616,[86],[]],[87,680,[120],[]],[120,680,[87],[]],[91,720,[122],[]],[122,720,[91],[]],[92,736,[123],[]],[123,736,[92],[]]],\"edges\":[[29,[16,36,48,49,64,68,69,70,84,85,86,87,100,101,117,118,119,120]],[41,[21,41,48,59,69,75,78,80,84,86,91,92,100,107,117,119,122,123]],[43,[22,42,49,59,70,76,79,80,85,87,91,92,101,107,118,120,122,123]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00138.record014" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00138.record014\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-8,-7],[-9,-7],[-9,-8],[-13,-2],[-13,-5],[-14,-13],[-16,-13],[-20,-19],[-23,-19],[-23,-20],[-25,-8],[-27,-7],[-27,-8],[-28,-20],[-28,-23],[-30,-24],[-31,-21],[-31,-24],[-31,-30],[-32,-20],[-33,-30],[-33,-31],[-1,7,8,19,20,21,22],[-4,19,20,21,22],[-10,7,8,21,22],[-11,7,8,19,20],[-12,8,20,22],[-13,7,19,21],[-1,25,26,28,29,30,31],[-4,28,29,30,31],[-10,25,26,30,31],[-12,26,29,31],[-13,25,28,30],[-2,7,9,19,21,23,24],[-5,19,21,23,24],[-9,2,12,14,16,19,21],[-12,9,23,24],[-14,7,9,21,24],[-16,7,9,19,23],[-18,7,19,21],[-19,2,5,9,16,18,24],[-5,28,30,32,33],[-3,8,9,20,22,23,24],[-6,20,22,23,24],[-13,9,23,24],[-15,8,9,22,24],[-17,8,9,20,23],[-18,8,20,22],[-6,29,31,32,33],[-18,26,29,31],[-7,25],[-25,7],[-8,26],[-26,8],[-9,27],[-27,9],[-19,28],[-28,19],[-20,29],[-29,20],[-21,30],[-30,21],[-22,31],[-31,22],[-23,32],[-32,23],[-24,33],[-33,24],[-7,34],[-8,34],[-9,34],[-19,35],[-20,35],[-23,35],[-21,36],[-22,36],[-24,36],[-25,37],[-26,37],[-27,37],[-28,38],[-29,38],[-32,38],[-30,39],[-31,39],[-33,39],[-35,40],[-34,40],[-37,41],[-36,41],[-40,-41,42],[-39,43],[-38,43],[-43,44],[-42,-44,45],[-45],[1,4,7,8,10,11,12,13,19,20,21,22,25,26,28,29,30,31],[2,5,7,9,12,14,16,18,19,21,23,24,25,27,28,30,32,33],[3,6,8,9,13,15,17,18,20,22,23,24,26,27,29,31,32,33]],\"atoms\":[{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":117},{\"tag\":\"facet\",\"index\":118},{\"tag\":\"facet\",\"index\":119},{\"tag\":\"facet\",\"index\":120},{\"tag\":\"facet\",\"index\":122},{\"tag\":\"facet\",\"index\":123},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":49,\"b\":48},{\"tag\":\"incompatible\",\"a\":59,\"b\":48},{\"tag\":\"incompatible\",\"a\":59,\"b\":49},{\"tag\":\"incompatible\",\"a\":70,\"b\":21},{\"tag\":\"incompatible\",\"a\":70,\"b\":41},{\"tag\":\"incompatible\",\"a\":75,\"b\":70},{\"tag\":\"incompatible\",\"a\":78,\"b\":70},{\"tag\":\"incompatible\",\"a\":85,\"b\":84},{\"tag\":\"incompatible\",\"a\":91,\"b\":84},{\"tag\":\"incompatible\",\"a\":91,\"b\":85},{\"tag\":\"incompatible\",\"a\":100,\"b\":49},{\"tag\":\"incompatible\",\"a\":107,\"b\":48},{\"tag\":\"incompatible\",\"a\":107,\"b\":49},{\"tag\":\"incompatible\",\"a\":117,\"b\":85},{\"tag\":\"incompatible\",\"a\":117,\"b\":91},{\"tag\":\"incompatible\",\"a\":119,\"b\":92},{\"tag\":\"incompatible\",\"a\":120,\"b\":86},{\"tag\":\"incompatible\",\"a\":120,\"b\":92},{\"tag\":\"incompatible\",\"a\":120,\"b\":119},{\"tag\":\"incompatible\",\"a\":122,\"b\":85},{\"tag\":\"incompatible\",\"a\":123,\"b\":119},{\"tag\":\"incompatible\",\"a\":123,\"b\":120},{\"tag\":\"mate\",\"ridge\":521,\"a\":16,\"owners\":[48,49,84,85,86,87]},{\"tag\":\"mate\",\"ridge\":521,\"a\":36,\"owners\":[84,85,86,87]},{\"tag\":\"mate\",\"ridge\":521,\"a\":64,\"owners\":[48,49,86,87]},{\"tag\":\"mate\",\"ridge\":521,\"a\":68,\"owners\":[48,49,84,85]},{\"tag\":\"mate\",\"ridge\":521,\"a\":69,\"owners\":[49,85,87]},{\"tag\":\"mate\",\"ridge\":521,\"a\":70,\"owners\":[48,84,86]},{\"tag\":\"mate\",\"ridge\":524,\"a\":16,\"owners\":[100,101,117,118,119,120]},{\"tag\":\"mate\",\"ridge\":524,\"a\":36,\"owners\":[117,118,119,120]},{\"tag\":\"mate\",\"ridge\":524,\"a\":64,\"owners\":[100,101,119,120]},{\"tag\":\"mate\",\"ridge\":524,\"a\":69,\"owners\":[101,118,120]},{\"tag\":\"mate\",\"ridge\":524,\"a\":70,\"owners\":[100,117,119]},{\"tag\":\"mate\",\"ridge\":577,\"a\":21,\"owners\":[48,59,84,86,91,92]},{\"tag\":\"mate\",\"ridge\":577,\"a\":41,\"owners\":[84,86,91,92]},{\"tag\":\"mate\",\"ridge\":577,\"a\":59,\"owners\":[21,69,75,78,84,86]},{\"tag\":\"mate\",\"ridge\":577,\"a\":69,\"owners\":[59,91,92]},{\"tag\":\"mate\",\"ridge\":577,\"a\":75,\"owners\":[48,59,86,92]},{\"tag\":\"mate\",\"ridge\":577,\"a\":78,\"owners\":[48,59,84,91]},{\"tag\":\"mate\",\"ridge\":577,\"a\":80,\"owners\":[48,84,86]},{\"tag\":\"mate\",\"ridge\":577,\"a\":84,\"owners\":[21,41,59,78,80,92]},{\"tag\":\"mate\",\"ridge\":580,\"a\":41,\"owners\":[117,119,122,123]},{\"tag\":\"mate\",\"ridge\":641,\"a\":22,\"owners\":[49,59,85,87,91,92]},{\"tag\":\"mate\",\"ridge\":641,\"a\":42,\"owners\":[85,87,91,92]},{\"tag\":\"mate\",\"ridge\":641,\"a\":70,\"owners\":[59,91,92]},{\"tag\":\"mate\",\"ridge\":641,\"a\":76,\"owners\":[49,59,87,92]},{\"tag\":\"mate\",\"ridge\":641,\"a\":79,\"owners\":[49,59,85,91]},{\"tag\":\"mate\",\"ridge\":641,\"a\":80,\"owners\":[49,85,87]},{\"tag\":\"mate\",\"ridge\":644,\"a\":42,\"owners\":[118,120,122,123]},{\"tag\":\"mate\",\"ridge\":644,\"a\":80,\"owners\":[101,118,120]},{\"tag\":\"mate\",\"ridge\":586,\"a\":48,\"owners\":[100]},{\"tag\":\"mate\",\"ridge\":586,\"a\":100,\"owners\":[48]},{\"tag\":\"mate\",\"ridge\":650,\"a\":49,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":650,\"a\":101,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":706,\"a\":59,\"owners\":[107]},{\"tag\":\"mate\",\"ridge\":706,\"a\":107,\"owners\":[59]},{\"tag\":\"mate\",\"ridge\":600,\"a\":84,\"owners\":[117]},{\"tag\":\"mate\",\"ridge\":600,\"a\":117,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":664,\"a\":85,\"owners\":[118]},{\"tag\":\"mate\",\"ridge\":664,\"a\":118,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":616,\"a\":86,\"owners\":[119]},{\"tag\":\"mate\",\"ridge\":616,\"a\":119,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":680,\"a\":87,\"owners\":[120]},{\"tag\":\"mate\",\"ridge\":680,\"a\":120,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":720,\"a\":91,\"owners\":[122]},{\"tag\":\"mate\",\"ridge\":720,\"a\":122,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":736,\"a\":92,\"owners\":[123]},{\"tag\":\"mate\",\"ridge\":736,\"a\":123,\"owners\":[92]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":48,\"full_literals\":[-7,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":49,\"full_literals\":[-8,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":59,\"full_literals\":[-9,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":84,\"full_literals\":[-19,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":85,\"full_literals\":[-20,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":91,\"full_literals\":[-23,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":86,\"full_literals\":[-21,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":87,\"full_literals\":[-22,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":92,\"full_literals\":[-24,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":100,\"full_literals\":[-25,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":101,\"full_literals\":[-26,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":107,\"full_literals\":[-27,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":117,\"full_literals\":[-28,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":118,\"full_literals\":[-29,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":122,\"full_literals\":[-32,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":119,\"full_literals\":[-30,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":120,\"full_literals\":[-31,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":123,\"full_literals\":[-33,39]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-35,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-34,false,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-37,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-36,false,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-40,-41,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-39,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-43,false,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-42,-44,45],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":29,\"owners\":[16,36,48,49,64,68,69,70,84,85,86,87,100,101,117,118,119,120]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[21,41,48,59,69,75,78,80,84,86,91,92,100,107,117,119,122,123]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[22,42,49,59,70,76,79,80,85,87,91,92,101,107,118,120,122,123]}]}"
  "p cnf 45 99\n-8 -7 0\n-9 -7 0\n-9 -8 0\n-13 -2 0\n-13 -5 0\n-14 -13 0\n-16 -13 0\n-20 -19 0\n-23 -19 0\n-23 -20 0\n-25 -8 0\n-27 -7 0\n-27 -8 0\n-28 -20 0\n-28 -23 0\n-30 -24 0\n-31 -21 0\n-31 -24 0\n-31 -30 0\n-32 -20 0\n-33 -30 0\n-33 -31 0\n-1 7 8 19 20 21 22 0\n-4 19 20 21 22 0\n-10 7 8 21 22 0\n-11 7 8 19 20 0\n-12 8 20 22 0\n-13 7 19 21 0\n-1 25 26 28 29 30 31 0\n-4 28 29 30 31 0\n-10 25 26 30 31 0\n-12 26 29 31 0\n-13 25 28 30 0\n-2 7 9 19 21 23 24 0\n-5 19 21 23 24 0\n-9 2 12 14 16 19 21 0\n-12 9 23 24 0\n-14 7 9 21 24 0\n-16 7 9 19 23 0\n-18 7 19 21 0\n-19 2 5 9 16 18 24 0\n-5 28 30 32 33 0\n-3 8 9 20 22 23 24 0\n-6 20 22 23 24 0\n-13 9 23 24 0\n-15 8 9 22 24 0\n-17 8 9 20 23 0\n-18 8 20 22 0\n-6 29 31 32 33 0\n-18 26 29 31 0\n-7 25 0\n-25 7 0\n-8 26 0\n-26 8 0\n-9 27 0\n-27 9 0\n-19 28 0\n-28 19 0\n-20 29 0\n-29 20 0\n-21 30 0\n-30 21 0\n-22 31 0\n-31 22 0\n-23 32 0\n-32 23 0\n-24 33 0\n-33 24 0\n-7 34 0\n-8 34 0\n-9 34 0\n-19 35 0\n-20 35 0\n-23 35 0\n-21 36 0\n-22 36 0\n-24 36 0\n-25 37 0\n-26 37 0\n-27 37 0\n-28 38 0\n-29 38 0\n-32 38 0\n-30 39 0\n-31 39 0\n-33 39 0\n-35 40 0\n-34 40 0\n-37 41 0\n-36 41 0\n-40 -41 42 0\n-39 43 0\n-38 43 0\n-43 44 0\n-42 -44 45 0\n-45 0\n1 4 7 8 10 11 12 13 19 20 21 22 25 26 28 29 30 31 0\n2 5 7 9 12 14 16 18 19 21 23 24 25 27 28 30 32 33 0\n3 6 8 9 13 15 17 18 20 22 23 24 26 27 29 31 32 33 0\n"
  "100 30 31 40 0 88 70 54 87 73 60 32 63 72 69 26 52 58 61 30 31 29 33 97 0\n101 31 40 0 87 74 73 88 70 71 47 56 54 66 60 63 50 100 16 21 45 44 46 43 99 0\n102 40 0 87 88 72 74 69 71 58 66 52 56 39 101 17 18 19 22 35 40 38 34 37 98 0\n103 23 13 20 41 0 89 79 53 90 76 48 60 80 55 77 46 68 64 66 44 43 47 99 0\n104 13 20 41 0 89 79 53 90 76 27 60 64 78 51 75 25 62 103 9 15 23 24 26 97 0\n105 20 41 0 89 80 55 79 53 78 51 90 77 76 75 48 104 4 5 7 28 41 0\n106 41 0 89 90 78 80 75 77 51 55 62 38 68 105 8 10 14 20 35 40 34 39 37 98 0\n107 42 0 106 102 91 0\n108 -44 0 107 96 95 0\n109 -43 0 108 94 0\n110 -39 0 109 92 0\n111 -38 0 109 93 0\n112 -30 0 110 84 0\n113 -31 0 110 85 0\n114 -33 0 110 86 0\n115 -28 0 111 81 0\n116 -29 0 111 82 0\n117 -32 0 111 83 0\n118 -21 0 112 61 0\n119 -22 0 113 63 0\n120 -24 0 114 67 0\n121 -19 0 115 57 0\n122 -5 0 115 112 117 114 42 0\n123 -4 0 115 112 116 113 30 0\n124 -20 0 116 59 0\n125 -23 0 117 65 0\n126 -6 0 117 114 116 113 49 0\n127 7 13 8 0 113 112 116 115 121 124 119 118 123 27 54 52 25 23 26 97 0\n128 13 8 0 114 113 116 120 119 124 126 117 125 48 54 127 2 12 46 43 47 99 0\n129 8 0 124 119 125 120 118 121 27 128 4 6 7 45 36 0\n130 -7 0 129 1 0\n131 -9 0 129 3 0\n132 -25 0 129 11 0\n133 -27 0 129 13 0\n134 -18 0 130 118 121 40 0\n135 -12 0 131 120 125 37 0\n136 -14 0 131 118 130 120 38 0\n137 -2 0 131 121 118 130 125 120 34 0\n138 -16 0 131 121 130 125 39 0\n139 0 137 131 115 122 125 130 138 134 121 118 136 120 132 133 135 112 117 114 98 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record014.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record014.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record014.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record014.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record014 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record014.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record014.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record014.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record014.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record014 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record014_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record014_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record014_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record014_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record014_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record014_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record014_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record014 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record014_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record014_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record014_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00138.record014

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00138.record015
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "f44f0bc1f2e2b49b25c8f2aaa6aa6a5a4e8ba1eac6398d64d8b61da8e9392e2b86e4789e1783eb86d16c5713c6a99a699965392e479b14e5355352d475a364d4b4ad1b51d2745d0f6c3a8da398d6338e9364e5354cd34ccb31cf0ba2e4b8acab1ae1b26c5b0ee8791cc749d170de0f43c8f13d2a468a6198961582e07929464a5194951542d0768390d2328c6344c9314e0b42c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db6db6db4db49a4da49249b6db6da6da4d26d2492492492492492492492492492491249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record015 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record015 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record015.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record015.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record015.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 74), (facetIndex 75), (facetIndex 81)]))
 (.leaf ([(facetIndex 85), (facetIndex 86), (facetIndex 92)])))
 (.branch 3
 (.leaf ([(facetIndex 87), (facetIndex 88), (facetIndex 93)]))
 (.leaf ([(facetIndex 101), (facetIndex 102), (facetIndex 108)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 112), (facetIndex 113), (facetIndex 119)]))
 (.leaf ([(facetIndex 114), (facetIndex 115), (facetIndex 120)])))
 (.branch 7
 (.leaf ([(facetIndex 78), (facetIndex 82), (facetIndex 83), (facetIndex 89), (facetIndex 90), (facetIndex 91)]))
 (.branch 8
 (.leaf ([(facetIndex 105), (facetIndex 109), (facetIndex 110), (facetIndex 116), (facetIndex 117), (facetIndex 118)]))
 (.leaf ([(facetIndex 121), (facetIndex 122), (facetIndex 123), (facetIndex 124)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "88885477755440773007003300000002166622110660006z4e;"⟩
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
def grouped3_0012 : List Nat := [6, 7, 8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record015 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record015_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00138.record015" "{\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"facet\",\"index\":119},{\"tag\":\"facet\",\"index\":120},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00138.record015" 46

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00138.record015" "{\"ridges\":[[8,521],[15,577],[16,641],[16,642],[36,521],[36,522],[41,577],[41,578],[42,641],[42,642],[46,521],[49,521],[50,521],[50,577],[50,578],[51,521],[51,641],[51,642],[52,521],[58,577],[60,641],[60,642],[63,577],[65,641],[66,577],[66,642],[74,588],[75,652],[81,708],[85,521],[85,600],[86,664],[87,616],[88,680],[92,720],[93,736],[101,588],[102,522],[102,652],[108,708],[112,600],[113,664],[114,616],[115,680],[119,720],[120,736]],\"owners\":[[8,521,[74,75,85,86,87,88],[36,46,49,50,51,52]],[36,521,[85,86,87,88],[8,46,49,50,51,52,74,75]],[46,521,[74,75,87,88],[8,36,49,50,51,52,85,86]],[49,521,[74,75,85,86],[8,36,46,50,51,52,87,88]],[50,521,[75,86,88],[8,36,46,49,51,52,74,85,87]],[51,521,[74,85,87],[8,36,46,49,50,52,75,86,88]],[52,521,[74,75,85,86,87,88],[8,36,46,49,50,51]],[85,521,[8,36,49,51,52,75,88],[46,50,74,86,87]],[36,522,[112,113,114,115],[8,46,49,50,51,52,101,102]],[102,522,[8,46,49,50,52,112,114],[36,51,101,113,115]],[15,577,[74,81,85,87,92,93],[41,50,58,63,66]],[41,577,[85,87,92,93],[15,50,58,63,66,74,81]],[50,577,[81,92,93],[15,41,58,63,66,74,85,87]],[58,577,[74,81,87,93],[15,41,50,63,66,85,92]],[63,577,[74,81,85,92],[15,41,50,58,66,87,93]],[66,577,[74,85,87],[15,41,50,58,63,81,92,93]],[41,578,[112,114,119,120],[15,50,58,63,66,101,108]],[50,578,[108,119,120],[15,41,58,63,66,101,112,114]],[16,641,[75,81,86,88,92,93],[42,51,60,65,66]],[42,641,[86,88,92,93],[16,51,60,65,66,75,81]],[51,641,[81,92,93],[16,42,60,65,66,75,86,88]],[60,641,[75,81,88,93],[16,42,51,65,66,86,92]],[65,641,[75,81,86,92],[16,42,51,60,66,88,93]],[16,642,[102,108,113,115,119,120],[42,51,60,65,66]],[42,642,[113,115,119,120],[16,51,60,65,66,102,108]],[51,642,[108,119,120],[16,42,60,65,66,102,113,115]],[60,642,[102,108,115,120],[16,42,51,65,66,113,119]],[66,642,[102,113,115],[16,42,51,60,65,108,119,120]],[74,588,[101],[]],[101,588,[74],[]],[75,652,[102],[]],[102,652,[75],[]],[81,708,[108],[]],[108,708,[81],[]],[85,600,[112],[]],[112,600,[85],[]],[86,664,[113],[]],[113,664,[86],[]],[87,616,[114],[]],[114,616,[87],[]],[88,680,[115],[]],[115,680,[88],[]],[92,720,[119],[]],[119,720,[92],[]],[93,736,[120],[]],[120,736,[93],[]]],\"edges\":[[29,[8,36,46,49,50,51,52,74,75,85,86,87,88,101,102,112,113,114,115]],[41,[15,41,50,58,63,66,74,81,85,87,92,93,101,108,112,114,119,120]],[43,[16,42,51,60,65,66,75,81,86,88,92,93,102,108,113,115,119,120]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00138.record015" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00138.record015\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-16,-1],[-16,-4],[-16,-7],[-16,-8],[-16,-11],[-18,-17],[-19,-17],[-19,-18],[-21,-20],[-24,-20],[-24,-21],[-26,-18],[-26,-19],[-27,-19],[-29,-24],[-30,-20],[-30,-24],[-32,-22],[-32,-31],[-34,-22],[-34,-23],[-34,-31],[-34,-32],[-1,17,18,20,21,22,23],[-4,20,21,22,23],[-7,17,18,22,23],[-8,17,18,20,21],[-9,18,21,23],[-10,17,20,22],[-11,17,18,20,21,22,23],[-20,1,4,8,10,11,18,23],[-4,29,30,31,32],[-27,1,7,8,9,11,29,31],[-2,17,19,20,22,24,25],[-5,20,22,24,25],[-9,19,24,25],[-12,17,19,22,25],[-14,17,19,20,24],[-16,17,20,22],[-5,29,31,33,34],[-9,28,33,34],[-3,18,19,21,23,24,25],[-6,21,23,24,25],[-10,19,24,25],[-13,18,19,23,25],[-15,18,19,21,24],[-3,27,28,30,32,33,34],[-6,30,32,33,34],[-10,28,33,34],[-13,27,28,32,34],[-16,27,30,32],[-17,26],[-26,17],[-18,27],[-27,18],[-19,28],[-28,19],[-20,29],[-29,20],[-21,30],[-30,21],[-22,31],[-31,22],[-23,32],[-32,23],[-24,33],[-33,24],[-25,34],[-34,25],[-17,35],[-18,35],[-19,35],[-20,36],[-21,36],[-24,36],[-22,37],[-23,37],[-25,37],[-26,38],[-27,38],[-28,38],[-29,39],[-30,39],[-33,39],[-31,40],[-32,40],[-34,40],[-36,41],[-35,41],[-38,42],[-37,42],[-41,-42,43],[-40,44],[-39,44],[-44,45],[-43,-45,46],[-46],[1,4,7,8,9,10,11,17,18,20,21,22,23,26,27,29,30,31,32],[2,5,9,12,14,16,17,19,20,22,24,25,26,28,29,31,33,34],[3,6,10,13,15,16,18,19,21,23,24,25,27,28,30,32,33,34]],\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"facet\",\"index\":119},{\"tag\":\"facet\",\"index\":120},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":66,\"b\":8},{\"tag\":\"incompatible\",\"a\":66,\"b\":36},{\"tag\":\"incompatible\",\"a\":66,\"b\":46},{\"tag\":\"incompatible\",\"a\":66,\"b\":49},{\"tag\":\"incompatible\",\"a\":66,\"b\":52},{\"tag\":\"incompatible\",\"a\":75,\"b\":74},{\"tag\":\"incompatible\",\"a\":81,\"b\":74},{\"tag\":\"incompatible\",\"a\":81,\"b\":75},{\"tag\":\"incompatible\",\"a\":86,\"b\":85},{\"tag\":\"incompatible\",\"a\":92,\"b\":85},{\"tag\":\"incompatible\",\"a\":92,\"b\":86},{\"tag\":\"incompatible\",\"a\":101,\"b\":75},{\"tag\":\"incompatible\",\"a\":101,\"b\":81},{\"tag\":\"incompatible\",\"a\":102,\"b\":81},{\"tag\":\"incompatible\",\"a\":112,\"b\":92},{\"tag\":\"incompatible\",\"a\":113,\"b\":85},{\"tag\":\"incompatible\",\"a\":113,\"b\":92},{\"tag\":\"incompatible\",\"a\":115,\"b\":87},{\"tag\":\"incompatible\",\"a\":115,\"b\":114},{\"tag\":\"incompatible\",\"a\":120,\"b\":87},{\"tag\":\"incompatible\",\"a\":120,\"b\":88},{\"tag\":\"incompatible\",\"a\":120,\"b\":114},{\"tag\":\"incompatible\",\"a\":120,\"b\":115},{\"tag\":\"mate\",\"ridge\":521,\"a\":8,\"owners\":[74,75,85,86,87,88]},{\"tag\":\"mate\",\"ridge\":521,\"a\":36,\"owners\":[85,86,87,88]},{\"tag\":\"mate\",\"ridge\":521,\"a\":46,\"owners\":[74,75,87,88]},{\"tag\":\"mate\",\"ridge\":521,\"a\":49,\"owners\":[74,75,85,86]},{\"tag\":\"mate\",\"ridge\":521,\"a\":50,\"owners\":[75,86,88]},{\"tag\":\"mate\",\"ridge\":521,\"a\":51,\"owners\":[74,85,87]},{\"tag\":\"mate\",\"ridge\":521,\"a\":52,\"owners\":[74,75,85,86,87,88]},{\"tag\":\"mate\",\"ridge\":521,\"a\":85,\"owners\":[8,36,49,51,52,75,88]},{\"tag\":\"mate\",\"ridge\":522,\"a\":36,\"owners\":[112,113,114,115]},{\"tag\":\"mate\",\"ridge\":522,\"a\":102,\"owners\":[8,46,49,50,52,112,114]},{\"tag\":\"mate\",\"ridge\":577,\"a\":15,\"owners\":[74,81,85,87,92,93]},{\"tag\":\"mate\",\"ridge\":577,\"a\":41,\"owners\":[85,87,92,93]},{\"tag\":\"mate\",\"ridge\":577,\"a\":50,\"owners\":[81,92,93]},{\"tag\":\"mate\",\"ridge\":577,\"a\":58,\"owners\":[74,81,87,93]},{\"tag\":\"mate\",\"ridge\":577,\"a\":63,\"owners\":[74,81,85,92]},{\"tag\":\"mate\",\"ridge\":577,\"a\":66,\"owners\":[74,85,87]},{\"tag\":\"mate\",\"ridge\":578,\"a\":41,\"owners\":[112,114,119,120]},{\"tag\":\"mate\",\"ridge\":578,\"a\":50,\"owners\":[108,119,120]},{\"tag\":\"mate\",\"ridge\":641,\"a\":16,\"owners\":[75,81,86,88,92,93]},{\"tag\":\"mate\",\"ridge\":641,\"a\":42,\"owners\":[86,88,92,93]},{\"tag\":\"mate\",\"ridge\":641,\"a\":51,\"owners\":[81,92,93]},{\"tag\":\"mate\",\"ridge\":641,\"a\":60,\"owners\":[75,81,88,93]},{\"tag\":\"mate\",\"ridge\":641,\"a\":65,\"owners\":[75,81,86,92]},{\"tag\":\"mate\",\"ridge\":642,\"a\":16,\"owners\":[102,108,113,115,119,120]},{\"tag\":\"mate\",\"ridge\":642,\"a\":42,\"owners\":[113,115,119,120]},{\"tag\":\"mate\",\"ridge\":642,\"a\":51,\"owners\":[108,119,120]},{\"tag\":\"mate\",\"ridge\":642,\"a\":60,\"owners\":[102,108,115,120]},{\"tag\":\"mate\",\"ridge\":642,\"a\":66,\"owners\":[102,113,115]},{\"tag\":\"mate\",\"ridge\":588,\"a\":74,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":588,\"a\":101,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":652,\"a\":75,\"owners\":[102]},{\"tag\":\"mate\",\"ridge\":652,\"a\":102,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":708,\"a\":81,\"owners\":[108]},{\"tag\":\"mate\",\"ridge\":708,\"a\":108,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":600,\"a\":85,\"owners\":[112]},{\"tag\":\"mate\",\"ridge\":600,\"a\":112,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":664,\"a\":86,\"owners\":[113]},{\"tag\":\"mate\",\"ridge\":664,\"a\":113,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":616,\"a\":87,\"owners\":[114]},{\"tag\":\"mate\",\"ridge\":616,\"a\":114,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":680,\"a\":88,\"owners\":[115]},{\"tag\":\"mate\",\"ridge\":680,\"a\":115,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":720,\"a\":92,\"owners\":[119]},{\"tag\":\"mate\",\"ridge\":720,\"a\":119,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":736,\"a\":93,\"owners\":[120]},{\"tag\":\"mate\",\"ridge\":736,\"a\":120,\"owners\":[93]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":74,\"full_literals\":[-17,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":75,\"full_literals\":[-18,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":81,\"full_literals\":[-19,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":85,\"full_literals\":[-20,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":86,\"full_literals\":[-21,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":92,\"full_literals\":[-24,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":87,\"full_literals\":[-22,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":88,\"full_literals\":[-23,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":93,\"full_literals\":[-25,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":101,\"full_literals\":[-26,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":102,\"full_literals\":[-27,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":108,\"full_literals\":[-28,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":112,\"full_literals\":[-29,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":113,\"full_literals\":[-30,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":119,\"full_literals\":[-33,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":114,\"full_literals\":[-31,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":115,\"full_literals\":[-32,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":120,\"full_literals\":[-34,40]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-36,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-35,false,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-38,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-37,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-41,-42,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-40,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-39,false,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-43,-45,46],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":29,\"owners\":[8,36,46,49,50,51,52,74,75,85,86,87,88,101,102,112,113,114,115]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[15,41,50,58,63,66,74,81,85,87,92,93,101,108,112,114,119,120]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[16,42,51,60,65,66,75,81,86,88,92,93,102,108,113,115,119,120]}]}"
  "p cnf 46 100\n-16 -1 0\n-16 -4 0\n-16 -7 0\n-16 -8 0\n-16 -11 0\n-18 -17 0\n-19 -17 0\n-19 -18 0\n-21 -20 0\n-24 -20 0\n-24 -21 0\n-26 -18 0\n-26 -19 0\n-27 -19 0\n-29 -24 0\n-30 -20 0\n-30 -24 0\n-32 -22 0\n-32 -31 0\n-34 -22 0\n-34 -23 0\n-34 -31 0\n-34 -32 0\n-1 17 18 20 21 22 23 0\n-4 20 21 22 23 0\n-7 17 18 22 23 0\n-8 17 18 20 21 0\n-9 18 21 23 0\n-10 17 20 22 0\n-11 17 18 20 21 22 23 0\n-20 1 4 8 10 11 18 23 0\n-4 29 30 31 32 0\n-27 1 7 8 9 11 29 31 0\n-2 17 19 20 22 24 25 0\n-5 20 22 24 25 0\n-9 19 24 25 0\n-12 17 19 22 25 0\n-14 17 19 20 24 0\n-16 17 20 22 0\n-5 29 31 33 34 0\n-9 28 33 34 0\n-3 18 19 21 23 24 25 0\n-6 21 23 24 25 0\n-10 19 24 25 0\n-13 18 19 23 25 0\n-15 18 19 21 24 0\n-3 27 28 30 32 33 34 0\n-6 30 32 33 34 0\n-10 28 33 34 0\n-13 27 28 32 34 0\n-16 27 30 32 0\n-17 26 0\n-26 17 0\n-18 27 0\n-27 18 0\n-19 28 0\n-28 19 0\n-20 29 0\n-29 20 0\n-21 30 0\n-30 21 0\n-22 31 0\n-31 22 0\n-23 32 0\n-32 23 0\n-24 33 0\n-33 24 0\n-25 34 0\n-34 25 0\n-17 35 0\n-18 35 0\n-19 35 0\n-20 36 0\n-21 36 0\n-24 36 0\n-22 37 0\n-23 37 0\n-25 37 0\n-26 38 0\n-27 38 0\n-28 38 0\n-29 39 0\n-30 39 0\n-33 39 0\n-31 40 0\n-32 40 0\n-34 40 0\n-36 41 0\n-35 41 0\n-38 42 0\n-37 42 0\n-41 -42 43 0\n-40 44 0\n-39 44 0\n-44 45 0\n-43 -45 46 0\n-46 0\n1 4 7 8 9 10 11 17 18 20 21 22 23 26 27 29 30 31 32 0\n2 5 9 12 14 16 17 19 20 22 24 25 26 28 29 31 33 34 0\n3 6 10 13 15 16 18 19 21 23 24 25 27 28 30 32 33 34 0\n"
  "101 32 34 41 0 89 72 57 88 75 67 49 68 74 71 46 55 61 64 48 50 51 47 100 0\n102 34 41 0 89 72 57 70 53 88 75 73 38 67 59 68 41 101 18 19 35 34 37 39 99 0\n103 41 0 88 89 73 74 70 71 59 61 27 53 55 102 20 21 22 23 25 24 26 29 30 28 98 0\n104 20 16 24 42 0 90 81 56 91 78 36 67 69 79 52 76 37 63 59 35 34 38 99 0\n105 16 24 42 0 90 81 56 91 78 44 67 69 80 54 77 45 65 104 9 16 43 42 46 100 0\n106 24 42 0 90 81 56 80 54 79 52 91 78 77 76 44 105 1 2 4 5 39 31 0\n107 42 0 90 91 79 80 76 77 52 54 63 26 65 106 10 11 15 17 24 29 30 27 25 28 98 0\n108 43 0 107 103 92 0\n109 -45 0 108 97 96 0\n110 -44 0 109 95 0\n111 -40 0 110 93 0\n112 -39 0 110 94 0\n113 -31 0 111 85 0\n114 -32 0 111 86 0\n115 -34 0 111 87 0\n116 -29 0 112 82 0\n117 -30 0 112 83 0\n118 -33 0 112 84 0\n119 -22 0 113 62 0\n120 -23 0 114 64 0\n121 -25 0 115 68 0\n122 -20 0 116 58 0\n123 -5 0 116 113 118 115 40 0\n124 -21 0 117 60 0\n125 -4 0 117 113 116 114 32 0\n126 -6 0 117 114 118 115 48 0\n127 -24 0 118 66 0\n128 18 16 19 0 115 118 114 121 127 120 124 126 117 44 57 55 45 42 46 100 0\n129 16 19 0 115 118 113 116 122 121 127 119 123 36 57 128 6 12 37 34 38 99 0\n130 19 0 127 121 117 114 113 116 36 129 1 3 4 5 51 33 0\n131 -17 0 130 7 0\n132 -18 0 130 8 0\n133 -26 0 130 13 0\n134 -27 0 130 14 0\n135 -1 0 131 132 119 124 122 120 24 0\n136 -10 0 131 119 122 29 0\n137 -11 0 131 132 119 124 122 120 30 0\n138 -7 0 131 119 132 120 26 0\n139 -8 0 131 122 132 124 27 0\n140 -9 0 132 120 124 28 0\n141 0 137 133 138 139 135 122 125 134 119 140 124 136 120 132 131 116 117 113 114 98 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record015.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record015.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record015.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record015.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record015 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record015.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record015.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record015.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record015.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record015 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record015_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record015_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record015_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record015_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record015_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record015_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record015_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record015 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record015_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record015_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record015_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00138.record015
