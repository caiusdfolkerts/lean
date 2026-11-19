module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow16Part00037Data
public import GraphInputsRow16Part00037Frames
public import GraphInputsRow16Part00037Leaves
public import GraphInputsRow16Part00037Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00037.record030
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record030
def vertexColumn : Fields := ⟨10, hexnat% "23c7295a36a3a598d68da2e2ba1e2783e72729564d98e565954d58d68d8b4ad8749d0f5c358d5334e3362d4b32e2b2ae1b46c9b16c3b51e2749ca719e1725c3783c8f0bc1f4a8c615a294a619316258545550cc348c5342c8b0ac1b21c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db69b6db69b4d24d34da49349249249249249a489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩, ⟨70, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [5197155069497180160, hexnat% "400100200228000000", 182395785176940544, 496979255754752, 7591690240, 9878428975104, 2199040032768]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record030_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record030_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record030_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record030_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record030_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record030_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record030_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record030_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record030_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00037.record030

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00037.record012
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "16c372729aa566392e1b89e17a719a56936565954d56354d3352d1b49d1772398e9394e331cd8b92e2b2ac6b26c5b61e4749c6785d1715c4f0bc1f4a8964388e986514a469254554348d1362348e1324d0b22c2b41c8705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6d269a49b49249249249a6924d34d2492249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record012 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record012 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record012.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 43), (facetIndex 55), (facetIndex 60)]))
 (.leaf ([(facetIndex 24), (facetIndex 33), (facetIndex 62), (facetIndex 65)])))
 (.branch 3
 (.leaf ([(facetIndex 25), (facetIndex 31), (facetIndex 40), (facetIndex 50), (facetIndex 64)]))
 (.leaf ([(facetIndex 29), (facetIndex 35), (facetIndex 44)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 36), (facetIndex 37), (facetIndex 38), (facetIndex 46)]))
 (.leaf ([(facetIndex 27), (facetIndex 28), (facetIndex 54)])))
 (.branch 7
 (.leaf ([(facetIndex 49), (facetIndex 58), (facetIndex 59)]))
 (.branch 8
 (.leaf ([(facetIndex 26), (facetIndex 47), (facetIndex 48), (facetIndex 51), (facetIndex 52), (facetIndex 53)]))
 (.leaf ([(facetIndex 42), (facetIndex 45)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "120100660005777267748308020444301020355721z18;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2, 3]
def grouped2_0006 : List Nat := [4, 5]
def grouped2_0007 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0008 : List Nat := [6]
def grouped2_0009 : List Nat := [6, 7, 8]
def grouped2_0010 : List Nat := [7]
def grouped2_0011 : List Nat := [7, 8]
def grouped2_0012 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record012 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record012_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00037.record012" "{\"atoms\":[{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00037.record012" 17

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00037.record012" "{\"ridges\":[[42,530],[43,530],[45,546],[55,592],[60,592],[66,582],[68,114]],\"owners\":[[42,530,[66],[8,29,43,44,68]],[43,530,[],[8,29,42,44,66,68]],[45,546,[],[10,38,42,46,67,68]],[55,592,[68],[18,43,60,66]],[60,592,[66],[18,43,55,68]],[66,582,[32],[]],[68,114,[41],[]]],\"edges\":[],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00037.record012" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00037.record012\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-3,-1],[-6,-2],[-7,-1],[-3,8],[-4],[-5],[-6,9],[-7,8],[-8,1],[-9,2],[-10,4,6,7],[-11,3,5],[-12,10],[-13,12],[-14,11],[-15,14],[-16,15],[-17,13,16],[17]],\"atoms\":[{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":42,\"b\":32},{\"tag\":\"incompatible\",\"a\":55,\"b\":41},{\"tag\":\"incompatible\",\"a\":60,\"b\":32},{\"tag\":\"mate\",\"ridge\":530,\"a\":42,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":530,\"a\":43,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":546,\"a\":45,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":592,\"a\":55,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":592,\"a\":60,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":582,\"a\":66,\"owners\":[32]},{\"tag\":\"mate\",\"ridge\":114,\"a\":68,\"owners\":[41]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[43,55,60],\"full_literals\":[-10,4,6,7]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[42,45],\"full_literals\":[-11,3,5]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-12,10,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-13,12,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-14,false,11],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-15,false,14],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-16,false,15],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-17,13,16],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true}]}"
  "p cnf 17 19\n-3 -1 0\n-6 -2 0\n-7 -1 0\n-3 8 0\n-4 0\n-5 0\n-6 9 0\n-7 8 0\n-8 1 0\n-9 2 0\n-10 4 6 7 0\n-11 3 5 0\n-12 10 0\n-13 12 0\n-14 11 0\n-15 14 0\n-16 15 0\n-17 13 16 0\n17 0\n"
  "20 -10 6 7 0 5 11 0\n21 -11 3 0 6 12 0\n22 -7 0 3 8 9 0\n23 -6 0 2 7 10 0\n24 -10 0 23 22 20 0\n25 -12 0 24 13 0\n26 -13 0 25 14 0\n27 16 0 26 19 18 0\n28 15 0 27 17 0\n29 14 0 28 16 0\n30 11 0 29 15 0\n31 3 0 30 21 0\n32 -1 0 31 1 0\n33 8 0 31 4 0\n34 0 33 32 9 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record012.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record012.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record012.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record012.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record012 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record012.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record012.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record012.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record012.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record012 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record012_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record012 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record012_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record012_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00037.record012

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00037.record013
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2749c96a36a6695a361d98e4b86e2785e9c5693672599695956351d58d9352d1b49d1766358e5334e331cd8b52ccb4ac6b26c5b61e4789ca719e1745c570dc4f0bc1f498964388e9865189525854954348d48c6324c5342c8b12d0721c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db6da4d34da49269a69a4934924924d2492492249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record013 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record013 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record013.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record013.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record013.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 49), (facetIndex 61)]))
 (.leaf ([(facetIndex 51), (facetIndex 62)])))
 (.branch 3
 (.leaf ([(facetIndex 64), (facetIndex 73)]))
 (.leaf ([(facetIndex 66), (facetIndex 74)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 34), (facetIndex 44), (facetIndex 55)]))
 (.leaf ([(facetIndex 69), (facetIndex 70), (facetIndex 71)])))
 (.branch 7
 (.leaf ([(facetIndex 72), (facetIndex 75), (facetIndex 76)]))
 (.leaf ([(facetIndex 53)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6cd6b680c20400008382000040000001z1a;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record013 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record013_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00037.record013" "{\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00037.record013" 49

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00037.record013" "{\"ridges\":[[5,73],[5,74],[17,548],[19,608],[26,73],[26,74],[33,548],[36,73],[36,74],[38,73],[38,74],[40,73],[40,74],[41,73],[41,74],[48,608],[49,92],[51,108],[53,588],[56,548],[59,608],[60,548],[61,216],[62,360],[63,608],[64,92],[66,108],[72,582],[73,216],[74,360],[75,562],[76,116]],\"owners\":[[5,73,[49,51,53,61,62],[26,36,38,40,41]],[26,73,[61,62],[5,36,38,40,41,49,51,53]],[36,73,[51,53,62],[5,26,38,40,41,49,61]],[38,73,[49,53,61],[5,26,36,40,41,51,62]],[40,73,[49,51,53,62],[5,26,36,38,41,61]],[41,73,[49,51,53,61],[5,26,36,38,40,62]],[5,74,[64,66,73,74],[26,36,38,40,41]],[26,74,[73,74],[5,36,38,40,41,64,66]],[36,74,[66,74],[5,26,38,40,41,64,73]],[38,74,[64,73],[5,26,36,40,41,66,74]],[40,74,[64,66,74],[5,26,36,38,41,73]],[41,74,[64,66,73],[5,26,36,38,40,74]],[17,548,[70,72,76],[33,56,59,60]],[33,548,[76],[17,56,59,60,70,72]],[56,548,[72],[17,33,59,60,70,76]],[60,548,[70,72,76],[17,33,56,59]],[19,608,[72,75,76],[48,59,63]],[48,608,[76],[19,59,63,72,75]],[59,608,[75],[19,48,63,72,76]],[63,608,[72],[19,48,59,75,76]],[72,582,[34,71],[]],[75,562,[44,70],[]],[49,92,[64],[]],[64,92,[49],[]],[51,108,[66],[]],[66,108,[51],[]],[53,588,[],[]],[76,116,[55,69],[]],[61,216,[73],[]],[73,216,[61],[]],[62,360,[74],[]],[74,360,[62],[]]],\"edges\":[[26,[5,26,36,38,40,41,49,51,53,61,62,64,66,73,74]],[38,[17,19,33,44,48,56,59,60,63,70,72,75,76]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00037.record013" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00037.record013\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,13,14,15,20,21],[-4,20,21],[-7,14,15,21],[-8,13,15,20],[-9,13,14,15,21],[-10,13,14,15,20],[-1,23,24,29,30],[-4,29,30],[-7,24,30],[-8,23,29],[-9,23,24,30],[-10,23,24,29],[-2,26,28,32],[-5,32],[-17,28],[-19,26,28,32],[-3,28,31,32],[-12,32],[-18,31],[-22,28],[-28,6,27],[-31,11,26],[-13,23],[-23,13],[-14,24],[-24,14],[-15],[-32,16,25],[-20,29],[-29,20],[-21,30],[-30,21],[-13,33],[-20,33],[-14,34],[-21,34],[-23,35],[-29,35],[-24,36],[-30,36],[-6,37],[-11,37],[-16,37],[-25,38],[-26,38],[-27,38],[-39,28,31,32],[-28,39],[-31,39],[-32,39],[-40,15],[-34,41],[-33,41],[-36,42],[-35,42],[-42,43],[-41,43],[-41,-42,44],[-38,45],[-37,45],[-46,39,40],[-39,46],[-45,47],[-45,-46,48],[-43,-48,49],[-44,-47,49],[-49],[1,4,7,8,9,10,13,14,15,20,21,23,24,29,30],[2,3,5,11,12,17,18,19,22,26,28,31,32]],\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":73,\"a\":5,\"owners\":[49,51,53,61,62]},{\"tag\":\"mate\",\"ridge\":73,\"a\":26,\"owners\":[61,62]},{\"tag\":\"mate\",\"ridge\":73,\"a\":36,\"owners\":[51,53,62]},{\"tag\":\"mate\",\"ridge\":73,\"a\":38,\"owners\":[49,53,61]},{\"tag\":\"mate\",\"ridge\":73,\"a\":40,\"owners\":[49,51,53,62]},{\"tag\":\"mate\",\"ridge\":73,\"a\":41,\"owners\":[49,51,53,61]},{\"tag\":\"mate\",\"ridge\":74,\"a\":5,\"owners\":[64,66,73,74]},{\"tag\":\"mate\",\"ridge\":74,\"a\":26,\"owners\":[73,74]},{\"tag\":\"mate\",\"ridge\":74,\"a\":36,\"owners\":[66,74]},{\"tag\":\"mate\",\"ridge\":74,\"a\":38,\"owners\":[64,73]},{\"tag\":\"mate\",\"ridge\":74,\"a\":40,\"owners\":[64,66,74]},{\"tag\":\"mate\",\"ridge\":74,\"a\":41,\"owners\":[64,66,73]},{\"tag\":\"mate\",\"ridge\":548,\"a\":17,\"owners\":[70,72,76]},{\"tag\":\"mate\",\"ridge\":548,\"a\":33,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":548,\"a\":56,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":548,\"a\":60,\"owners\":[70,72,76]},{\"tag\":\"mate\",\"ridge\":608,\"a\":19,\"owners\":[72,75,76]},{\"tag\":\"mate\",\"ridge\":608,\"a\":48,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":608,\"a\":59,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":608,\"a\":63,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":582,\"a\":72,\"owners\":[34,71]},{\"tag\":\"mate\",\"ridge\":562,\"a\":75,\"owners\":[44,70]},{\"tag\":\"mate\",\"ridge\":92,\"a\":49,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":92,\"a\":64,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":108,\"a\":51,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":108,\"a\":66,\"owners\":[51]},{\"tag\":\"mate\",\"ridge\":588,\"a\":53,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":116,\"a\":76,\"owners\":[55,69]},{\"tag\":\"mate\",\"ridge\":216,\"a\":61,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":216,\"a\":73,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":360,\"a\":62,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":360,\"a\":74,\"owners\":[62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":49,\"full_literals\":[-13,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":61,\"full_literals\":[-20,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":51,\"full_literals\":[-14,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":62,\"full_literals\":[-21,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":64,\"full_literals\":[-23,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":73,\"full_literals\":[-29,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":66,\"full_literals\":[-24,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":74,\"full_literals\":[-30,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":34,\"full_literals\":[-6,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":44,\"full_literals\":[-11,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":55,\"full_literals\":[-16,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":69,\"full_literals\":[-25,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":70,\"full_literals\":[-26,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":71,\"full_literals\":[-27,38]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[72,75,76],\"full_literals\":[-39,28,31,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":72,\"full_literals\":[-28,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":75,\"full_literals\":[-31,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":76,\"full_literals\":[-32,39]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[53],\"full_literals\":[-40,15]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-34,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-33,false,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-36,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-35,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-42,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-41,false,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-41,-42,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-38,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-37,false,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-46,39,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-39,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-45,false,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-45,-46,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-43,-48,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-44,-47,49],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":26,\"owners\":[5,26,36,38,40,41,49,51,53,61,62,64,66,73,74]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[17,19,33,44,48,56,59,60,63,70,72,75,76]}]}"
  "p cnf 49 69\n-1 13 14 15 20 21 0\n-4 20 21 0\n-7 14 15 21 0\n-8 13 15 20 0\n-9 13 14 15 21 0\n-10 13 14 15 20 0\n-1 23 24 29 30 0\n-4 29 30 0\n-7 24 30 0\n-8 23 29 0\n-9 23 24 30 0\n-10 23 24 29 0\n-2 26 28 32 0\n-5 32 0\n-17 28 0\n-19 26 28 32 0\n-3 28 31 32 0\n-12 32 0\n-18 31 0\n-22 28 0\n-28 6 27 0\n-31 11 26 0\n-13 23 0\n-23 13 0\n-14 24 0\n-24 14 0\n-15 0\n-32 16 25 0\n-20 29 0\n-29 20 0\n-21 30 0\n-30 21 0\n-13 33 0\n-20 33 0\n-14 34 0\n-21 34 0\n-23 35 0\n-29 35 0\n-24 36 0\n-30 36 0\n-6 37 0\n-11 37 0\n-16 37 0\n-25 38 0\n-26 38 0\n-27 38 0\n-39 28 31 32 0\n-28 39 0\n-31 39 0\n-32 39 0\n-40 15 0\n-34 41 0\n-33 41 0\n-36 42 0\n-35 42 0\n-42 43 0\n-41 43 0\n-41 -42 44 0\n-38 45 0\n-37 45 0\n-46 39 40 0\n-39 46 0\n-45 47 0\n-45 -46 48 0\n-43 -48 49 0\n-44 -47 49 0\n-49 0\n1 4 7 8 9 10 13 14 15 20 21 23 24 29 30 0\n2 3 5 11 12 17 18 19 22 26 28 31 32 0\n"
  "70 -40 0 27 51 0\n71 -46 39 0 70 61 0\n72 1 4 7 8 9 10 13 14 20 21 23 24 29 30 0 27 68 0\n73 43 0 56 57 54 55 52 53 39 40 37 38 35 36 33 34 9 7 10 11 12 8 72 0\n74 -48 0 73 67 65 0\n75 -46 0 74 71 64 59 60 44 45 46 41 42 43 22 21 28 47 0\n76 -39 0 75 62 0\n77 -28 0 76 48 0\n78 -31 0 76 49 0\n79 -32 0 76 50 0\n80 -17 0 77 15 0\n81 -3 0 77 78 79 17 0\n82 -22 0 77 20 0\n83 -18 0 78 19 0\n84 -5 0 79 14 0\n85 -12 0 79 18 0\n86 42 0 54 55 39 40 37 38 9 25 31 7 10 11 12 23 8 29 72 0\n87 41 0 27 52 53 35 36 33 34 3 26 32 1 4 5 6 24 2 30 72 0\n88 44 0 87 86 58 0\n89 -47 0 88 67 66 0\n90 -45 0 89 63 0\n91 -38 0 90 59 0\n92 -37 0 90 60 0\n93 -26 0 91 45 0\n94 -11 0 92 42 0\n95 -2 0 93 77 79 13 0\n96 -19 0 93 77 79 16 0\n97 0 96 93 95 84 94 85 83 80 82 81 77 78 79 69 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record013.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record013.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record013.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record013.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record013 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record013.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record013.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record013.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record013.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record013 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record013_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record013 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record013_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record013_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00037.record013
