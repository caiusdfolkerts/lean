module
prelude
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow25Part00024Frames
public import GraphInputsRow25Part00024Leaves
public import GraphInputsRow25Part00024Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00024.record051
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1ac8f13c2f32aaa9aa96a3a4e8ba69a364d8b61d98e538ce8b92e2ba1e4789e0fb29aa5a9966394e4b9696354d4b51d58d534cd8b52d2b61d4749d0f723a8da394d332cc73c2e8b62e4b52ccb8ad2b2ad1b26c3b61d4731e2719e1745c9783c2f172328685a498a6158364388e1381e8c61916525294550d50d2344d0762348ca384c530ce0b42c8b12c1b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db6d26d249249a4924db49b492492692492492492492492492492492249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record051 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record051 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record051.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 50), (facetIndex 51), (facetIndex 52), (facetIndex 58), (facetIndex 65), (facetIndex 87), (facetIndex 109)]))
 (.leaf ([(facetIndex 45), (facetIndex 46), (facetIndex 62), (facetIndex 63), (facetIndex 64), (facetIndex 66), (facetIndex 67), (facetIndex 68)])))
 (.branch 3
 (.leaf ([(facetIndex 69), (facetIndex 70), (facetIndex 71), (facetIndex 72), (facetIndex 76), (facetIndex 77), (facetIndex 78)]))
 (.leaf ([(facetIndex 91), (facetIndex 92), (facetIndex 93), (facetIndex 94), (facetIndex 98), (facetIndex 99), (facetIndex 100)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 40), (facetIndex 41), (facetIndex 53), (facetIndex 54), (facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 59), (facetIndex 60), (facetIndex 61)]))
 (.leaf ([(facetIndex 79), (facetIndex 80), (facetIndex 81), (facetIndex 82), (facetIndex 83)])))
 (.branch 7
 (.leaf ([(facetIndex 101), (facetIndex 102), (facetIndex 103), (facetIndex 104), (facetIndex 105)]))
 (.branch 8
 (.leaf ([(facetIndex 73), (facetIndex 74), (facetIndex 86), (facetIndex 95), (facetIndex 96), (facetIndex 108)]))
 (.leaf ([(facetIndex 42), (facetIndex 43), (facetIndex 44), (facetIndex 47), (facetIndex 48), (facetIndex 49)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "700666663330773333000070055555222077222211101114440444440008881188844z28;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 1
 (.leaf ([(facetIndex 75), (facetIndex 84), (facetIndex 85), (facetIndex 88), (facetIndex 89), (facetIndex 90)]))
 (.branch 2
 (.leaf ([(facetIndex 97), (facetIndex 106), (facetIndex 107), (facetIndex 110), (facetIndex 111), (facetIndex 112)]))
 (.leaf ([(facetIndex 113), (facetIndex 114), (facetIndex 115), (facetIndex 116)]))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨2, sparse_nat% "2a950500004z30;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 3
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4, 5]
def grouped2_0003 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0004 : List Nat := [6]
def grouped2_0005 : List Nat := [6, 7, 8]
def grouped2_0006 : List Nat := [7]
def grouped2_0007 : List Nat := [7, 8]
def grouped2_0008 : List Nat := [8]
def grouped3_0009 : List Nat := [0]
def grouped3_0011 : List Nat := [1]
def grouped3_0012 : List Nat := [1, 2]
def grouped3_0013 : List Nat := [2]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record051 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record051_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00024.record051" "{\"atoms\":[{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0005\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":9,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00024.record051" 28

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00024.record051" "{\"ridges\":[[111,680],[112,808]],\"owners\":[[111,680,[89],[]],[112,808,[90],[]]],\"edges\":[],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00024.record051" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00024.record051\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-3,-1],[-3,-2],[-4,-1],[-4,-2],[-5,-1],[-5,-2],[-6,-3],[-6,-4],[-6,-5],[-7,-1],[-7,-2],[-7,-6],[-8,-1],[-8,-2],[-8,-6],[-9,-1],[-9,-2],[-9,-6],[-10,-3],[-10,-4],[-10,-5],[-10,-7],[-10,-8],[-10,-9],[-11,-3],[-11,-4],[-11,-5],[-11,-7],[-11,-8],[-11,-9],[-12,-1],[-12,-2],[-12,-6],[-12,-10],[-12,-11],[-13,-1],[-13,-2],[-13,-6],[-13,-10],[-13,-11],[-14,-1],[-14,-2],[-14,-6],[-14,-10],[-14,-11],[-15,-3],[-15,-4],[-15,-5],[-15,-7],[-15,-8],[-15,-9],[-15,-12],[-15,-13],[-15,-14],[-16,-1],[-16,-2],[-16,-6],[-16,-10],[-16,-11],[-16,-15],[-17,8],[-18,9],[-19,1,2,6,10,11,15],[-20,19],[-21,20],[-22,21],[-23,22],[23],[-24,3,4,5,7,8,9],[-8,24],[-9,24],[-25,12,13,14,16,17,18],[-26,25],[-27,24,26],[-24,-26,28],[27],[-28]],\"atoms\":[{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":75,\"b\":73},{\"tag\":\"incompatible\",\"a\":75,\"b\":74},{\"tag\":\"incompatible\",\"a\":84,\"b\":73},{\"tag\":\"incompatible\",\"a\":84,\"b\":74},{\"tag\":\"incompatible\",\"a\":85,\"b\":73},{\"tag\":\"incompatible\",\"a\":85,\"b\":74},{\"tag\":\"incompatible\",\"a\":86,\"b\":75},{\"tag\":\"incompatible\",\"a\":86,\"b\":84},{\"tag\":\"incompatible\",\"a\":86,\"b\":85},{\"tag\":\"incompatible\",\"a\":88,\"b\":73},{\"tag\":\"incompatible\",\"a\":88,\"b\":74},{\"tag\":\"incompatible\",\"a\":88,\"b\":86},{\"tag\":\"incompatible\",\"a\":89,\"b\":73},{\"tag\":\"incompatible\",\"a\":89,\"b\":74},{\"tag\":\"incompatible\",\"a\":89,\"b\":86},{\"tag\":\"incompatible\",\"a\":90,\"b\":73},{\"tag\":\"incompatible\",\"a\":90,\"b\":74},{\"tag\":\"incompatible\",\"a\":90,\"b\":86},{\"tag\":\"incompatible\",\"a\":95,\"b\":75},{\"tag\":\"incompatible\",\"a\":95,\"b\":84},{\"tag\":\"incompatible\",\"a\":95,\"b\":85},{\"tag\":\"incompatible\",\"a\":95,\"b\":88},{\"tag\":\"incompatible\",\"a\":95,\"b\":89},{\"tag\":\"incompatible\",\"a\":95,\"b\":90},{\"tag\":\"incompatible\",\"a\":96,\"b\":75},{\"tag\":\"incompatible\",\"a\":96,\"b\":84},{\"tag\":\"incompatible\",\"a\":96,\"b\":85},{\"tag\":\"incompatible\",\"a\":96,\"b\":88},{\"tag\":\"incompatible\",\"a\":96,\"b\":89},{\"tag\":\"incompatible\",\"a\":96,\"b\":90},{\"tag\":\"incompatible\",\"a\":97,\"b\":73},{\"tag\":\"incompatible\",\"a\":97,\"b\":74},{\"tag\":\"incompatible\",\"a\":97,\"b\":86},{\"tag\":\"incompatible\",\"a\":97,\"b\":95},{\"tag\":\"incompatible\",\"a\":97,\"b\":96},{\"tag\":\"incompatible\",\"a\":106,\"b\":73},{\"tag\":\"incompatible\",\"a\":106,\"b\":74},{\"tag\":\"incompatible\",\"a\":106,\"b\":86},{\"tag\":\"incompatible\",\"a\":106,\"b\":95},{\"tag\":\"incompatible\",\"a\":106,\"b\":96},{\"tag\":\"incompatible\",\"a\":107,\"b\":73},{\"tag\":\"incompatible\",\"a\":107,\"b\":74},{\"tag\":\"incompatible\",\"a\":107,\"b\":86},{\"tag\":\"incompatible\",\"a\":107,\"b\":95},{\"tag\":\"incompatible\",\"a\":107,\"b\":96},{\"tag\":\"incompatible\",\"a\":108,\"b\":75},{\"tag\":\"incompatible\",\"a\":108,\"b\":84},{\"tag\":\"incompatible\",\"a\":108,\"b\":85},{\"tag\":\"incompatible\",\"a\":108,\"b\":88},{\"tag\":\"incompatible\",\"a\":108,\"b\":89},{\"tag\":\"incompatible\",\"a\":108,\"b\":90},{\"tag\":\"incompatible\",\"a\":108,\"b\":97},{\"tag\":\"incompatible\",\"a\":108,\"b\":106},{\"tag\":\"incompatible\",\"a\":108,\"b\":107},{\"tag\":\"incompatible\",\"a\":110,\"b\":73},{\"tag\":\"incompatible\",\"a\":110,\"b\":74},{\"tag\":\"incompatible\",\"a\":110,\"b\":86},{\"tag\":\"incompatible\",\"a\":110,\"b\":95},{\"tag\":\"incompatible\",\"a\":110,\"b\":96},{\"tag\":\"incompatible\",\"a\":110,\"b\":108},{\"tag\":\"mate\",\"ridge\":680,\"a\":111,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":808,\"a\":112,\"owners\":[90]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[73,74,86,95,96,108],\"full_literals\":[-19,1,2,6,10,11,15]},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-20,19,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0004\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0005\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-21,false,20],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-22,false,21],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0003\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-23,false,22],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":9,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[75,84,85,88,89,90],\"full_literals\":[-24,3,4,5,7,8,9]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":89,\"full_literals\":[-8,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":90,\"full_literals\":[-9,24]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[97,106,107,110,111,112],\"full_literals\":[-25,12,13,14,16,17,18]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-26,25,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-27,24,26],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-24,-26,28],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true}]}"
  "p cnf 28 77\n-3 -1 0\n-3 -2 0\n-4 -1 0\n-4 -2 0\n-5 -1 0\n-5 -2 0\n-6 -3 0\n-6 -4 0\n-6 -5 0\n-7 -1 0\n-7 -2 0\n-7 -6 0\n-8 -1 0\n-8 -2 0\n-8 -6 0\n-9 -1 0\n-9 -2 0\n-9 -6 0\n-10 -3 0\n-10 -4 0\n-10 -5 0\n-10 -7 0\n-10 -8 0\n-10 -9 0\n-11 -3 0\n-11 -4 0\n-11 -5 0\n-11 -7 0\n-11 -8 0\n-11 -9 0\n-12 -1 0\n-12 -2 0\n-12 -6 0\n-12 -10 0\n-12 -11 0\n-13 -1 0\n-13 -2 0\n-13 -6 0\n-13 -10 0\n-13 -11 0\n-14 -1 0\n-14 -2 0\n-14 -6 0\n-14 -10 0\n-14 -11 0\n-15 -3 0\n-15 -4 0\n-15 -5 0\n-15 -7 0\n-15 -8 0\n-15 -9 0\n-15 -12 0\n-15 -13 0\n-15 -14 0\n-16 -1 0\n-16 -2 0\n-16 -6 0\n-16 -10 0\n-16 -11 0\n-16 -15 0\n-17 8 0\n-18 9 0\n-19 1 2 6 10 11 15 0\n-20 19 0\n-21 20 0\n-22 21 0\n-23 22 0\n23 0\n-24 3 4 5 7 8 9 0\n-8 24 0\n-9 24 0\n-25 12 13 14 16 17 18 0\n-26 25 0\n-27 24 26 0\n-24 -26 28 0\n27 0\n-28 0\n"
  "78 22 0 68 67 0\n79 21 0 78 66 0\n80 20 0 79 65 0\n81 19 0 80 64 0\n82 -12 1 2 15 0 81 33 34 35 63 0\n83 -6 12 -26 0 77 75 71 62 70 61 73 38 43 57 72 0\n84 -15 12 -26 0 77 75 71 62 70 61 73 53 54 60 72 0\n85 -12 0 31 32 52 82 0\n86 -13 -26 0 85 81 84 83 36 37 39 40 63 0\n87 -14 -26 0 85 81 84 83 41 42 44 45 63 0\n88 -26 0 77 85 81 73 75 70 71 61 62 83 84 86 87 72 55 56 58 59 63 0\n89 24 0 88 76 74 0\n90 -10 7 3 8 9 0 89 20 21 69 0\n91 -11 7 3 8 9 0 89 26 27 69 0\n92 -1 7 3 8 9 0 89 3 5 69 0\n93 -2 7 3 8 9 0 89 4 6 69 0\n94 -6 8 9 0 89 7 8 9 12 69 0\n95 7 3 15 8 9 0 81 94 90 91 92 93 63 0\n96 -7 15 6 0 81 10 11 22 28 63 0\n97 15 8 9 0 81 94 96 95 1 2 19 25 63 0\n98 8 9 0 89 97 46 47 48 49 69 0\n99 -8 0 81 13 14 15 23 29 50 63 0\n100 9 0 99 98 0\n101 -1 0 100 16 0\n102 -2 0 100 17 0\n103 -6 0 100 18 0\n104 -10 0 100 24 0\n105 -11 0 100 30 0\n106 -15 0 100 51 0\n107 0 102 101 81 104 105 103 106 63 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record051.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record051.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record051.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record051.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record051 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record051.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record051.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record051.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record051.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record051 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record051_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record051_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record051_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record051_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record051_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record051_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record051_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record051 Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record051_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record051_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record051_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00024.record051
