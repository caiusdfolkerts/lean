module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00110Data
public import GraphInputsRow24Part00110Frames
public import GraphInputsRow24Part00110Leaves
public import GraphInputsRow24Part00110Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record020
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record020
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨65, by decide⟩, ⟨71, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 33688649728, 15010807620304896, 558446353793941504, (certNat% 4), 47485158424576]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record020_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record020_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record020_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record020_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record020_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record020_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record020_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record020_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record020_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record020

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record013
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "25c371aa369c6999963598e938ce8b92e2785e0fac96a659365c5c9665656553558d934cd4b61d2745d0f5c368e6364d8b92ccb8ad2b2ac5b0ed8791d4731e2719d1725c3783d0f23c4f8b0d2269261582e078d18a49991625494558342d0758330d2324c5322c2b06d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36d36d36d24936d349a4d349249349a492492492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record013 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record013 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record013.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record013.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record013.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 34), (facetIndex 38), (facetIndex 55), (facetIndex 59), (facetIndex 67)]))
 (.leaf ([(facetIndex 73), (facetIndex 76), (facetIndex 77)])))
 (.branch 3
 (.leaf ([(facetIndex 45), (facetIndex 48), (facetIndex 50), (facetIndex 51), (facetIndex 53), (facetIndex 54)]))
 (.leaf ([(facetIndex 58), (facetIndex 61), (facetIndex 64), (facetIndex 66)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 31), (facetIndex 35), (facetIndex 39), (facetIndex 42), (facetIndex 57), (facetIndex 63), (facetIndex 75), (facetIndex 81)]))
 (.leaf ([(facetIndex 30), (facetIndex 44), (facetIndex 56), (facetIndex 69), (facetIndex 74), (facetIndex 85)])))
 (.branch 7
 (.leaf ([(facetIndex 43), (facetIndex 46), (facetIndex 47)]))
 (.leaf ([(facetIndex 32), (facetIndex 33), (facetIndex 36), (facetIndex 37), (facetIndex 40), (facetIndex 41)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "280200099480280c38180e5090482d95d3f83f83f94z16;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record013 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record013_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record013" "{\"atoms\":[{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record013" 33

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record013" "{\"ridges\":[[19,580],[41,580],[49,586],[52,610],[61,580],[64,580],[66,580],[70,600],[72,712],[83,610]],\"owners\":[[19,580,[79,83,88],[41,61,64,66]],[41,580,[88],[19,61,64,66,79,83]],[61,580,[83],[19,41,64,66,79,88]],[64,580,[79,83],[19,41,61,66,88]],[66,580,[79,88],[19,41,61,64,83]],[49,586,[79],[]],[52,610,[83],[]],[83,610,[52],[]],[70,600,[88],[]],[72,712,[],[]]],\"edges\":[[41,[19,41,49,52,61,64,66,70,72,79,83,88]]],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record013" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record013\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-9,-6],[-17,-4],[-21,-2],[-21,-5],[-21,-10],[-21,-14],[-21,-18],[-22,-7],[-22,-19],[-22,-20],[-23,-21],[-24,-2],[-24,-5],[-24,-10],[-24,-14],[-24,-18],[-24,-23],[-1,21,22,24],[-3,24],[-11,22],[-12,21,22],[-13,21,24],[-8,21],[-9,22],[-22,9],[-15,24],[-16],[-25,17,19,20],[-26,2,5,10,14,18,23],[-27,4,6,7],[-28,25],[-29,28],[-30,26],[-31,27],[-32,30],[-32,31],[-33,29],[-33,32],[33],[1,3,8,9,11,12,13,15,16,21,22,24]],\"atoms\":[{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":52,\"b\":46},{\"tag\":\"incompatible\",\"a\":73,\"b\":43},{\"tag\":\"incompatible\",\"a\":79,\"b\":30},{\"tag\":\"incompatible\",\"a\":79,\"b\":44},{\"tag\":\"incompatible\",\"a\":79,\"b\":56},{\"tag\":\"incompatible\",\"a\":79,\"b\":69},{\"tag\":\"incompatible\",\"a\":79,\"b\":74},{\"tag\":\"incompatible\",\"a\":83,\"b\":47},{\"tag\":\"incompatible\",\"a\":83,\"b\":76},{\"tag\":\"incompatible\",\"a\":83,\"b\":77},{\"tag\":\"incompatible\",\"a\":85,\"b\":79},{\"tag\":\"incompatible\",\"a\":88,\"b\":30},{\"tag\":\"incompatible\",\"a\":88,\"b\":44},{\"tag\":\"incompatible\",\"a\":88,\"b\":56},{\"tag\":\"incompatible\",\"a\":88,\"b\":69},{\"tag\":\"incompatible\",\"a\":88,\"b\":74},{\"tag\":\"incompatible\",\"a\":88,\"b\":85},{\"tag\":\"mate\",\"ridge\":580,\"a\":19,\"owners\":[79,83,88]},{\"tag\":\"mate\",\"ridge\":580,\"a\":41,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":580,\"a\":61,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":580,\"a\":64,\"owners\":[79,83]},{\"tag\":\"mate\",\"ridge\":580,\"a\":66,\"owners\":[79,88]},{\"tag\":\"mate\",\"ridge\":586,\"a\":49,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":610,\"a\":52,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":610,\"a\":83,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":600,\"a\":70,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":712,\"a\":72,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[73,76,77],\"full_literals\":[-25,17,19,20]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[30,44,56,69,74,85],\"full_literals\":[-26,2,5,10,14,18,23]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[43,46,47],\"full_literals\":[-27,4,6,7]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-28,false,25],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-29,28,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-30,false,26],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-31,27,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-32,30,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-32,false,31],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-33,29,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-33,false,32],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"edge\",\"edge\":41,\"owners\":[19,41,49,52,61,64,66,70,72,79,83,88]}]}"
  "41 29 0 39 37 0\n42 32 0 39 38 0\n43 28 0 41 32 0\n44 30 0 42 35 0\n45 31 0 42 36 0\n46 25 0 43 31 0\n47 26 0 44 33 0\n48 27 0 45 34 0\n49 1 3 8 9 11 12 13 15 21 22 24 0 27 40 0\n50 -24 0 47 12 13 14 15 16 17 29 0\n51 -3 0 50 19 0\n52 -15 0 50 26 0\n53 21 22 0 50 52 51 24 20 23 18 22 21 49 0\n54 -21 0 47 3 4 5 6 7 11 29 0\n55 22 0 54 53 0\n56 -7 0 55 8 0\n57 -19 0 55 9 0\n58 -20 0 55 10 0\n59 9 0 55 25 0\n60 17 0 57 46 58 28 0\n61 -6 0 59 1 0\n62 -4 0 60 2 0\n63 0 61 62 48 56 30 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record013.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record013.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record013.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record013.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record013 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record013.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record013.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record013.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record013.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record013 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record013_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record013 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record013_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record013_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record013

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record014
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "372ca6aa5a369c6999963598e938ce8b92e2785e0fac96a659365c5995953558d934cd8b52d2745d0f6c370f2368e6364e53a2d8b92ccb4acab86c5b0ed8791d4731e2719d1725c3783d0f23c4f34a2a269261582e078d18a499494550b41d60e4330e2348c9314e0b22c2b06d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db4db4db4924db4db4db492492492492492492492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record014 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record014 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record014.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record014.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record014.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 65), (facetIndex 69)]))
 (.leaf ([(facetIndex 66), (facetIndex 73)])))
 (.branch 3
 (.leaf ([(facetIndex 81), (facetIndex 85)]))
 (.leaf ([(facetIndex 82), (facetIndex 89)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 64), (facetIndex 68), (facetIndex 70)]))
 (.leaf ([(facetIndex 72), (facetIndex 74), (facetIndex 80)])))
 (.branch 7
 (.leaf ([(facetIndex 84), (facetIndex 86), (facetIndex 91)]))
 (.leaf ([(facetIndex 88), (facetIndex 90)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "ddf1960d500014d104044z30;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record014 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record014_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record014" "{\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record014" 51

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record014" "{\"ridges\":[[14,577],[14,578],[15,386],[41,578],[42,386],[49,577],[49,578],[50,386],[52,577],[52,578],[53,386],[54,577],[54,578],[55,386],[57,386],[58,577],[58,578],[66,396],[68,404],[70,452],[72,600],[73,424],[74,712],[82,396],[84,404],[86,452],[88,600],[89,424],[90,712],[91,204]],\"owners\":[[14,577,[65,69,72,74],[41,49,52,54,58]],[49,577,[69],[14,41,52,54,58,65,72,74]],[52,577,[65,69,74],[14,41,49,54,58,72]],[54,577,[65,72,74],[14,41,49,52,58,69]],[58,577,[65,69,72],[14,41,49,52,54,74]],[14,578,[81,85,88,90],[41,49,52,54,58]],[41,578,[88,90],[14,49,52,54,58,81,85]],[49,578,[85],[14,41,52,54,58,81,88,90]],[52,578,[81,85,90],[14,41,49,54,58,88]],[54,578,[81,88,90],[14,41,49,52,58,85]],[58,578,[81,85,88],[14,41,49,52,54,90]],[15,386,[82,84,86,89],[42,50,53,55,57]],[42,386,[89],[15,50,53,55,57,82,84,86]],[50,386,[84,86],[15,42,53,55,57,82,89]],[53,386,[82,86,89],[15,42,50,55,57,84]],[55,386,[82,84,86],[15,42,50,53,57,89]],[57,386,[82,84,89],[15,42,50,53,55,86]],[91,204,[64,80],[]],[66,396,[82],[]],[82,396,[66],[]],[68,404,[84],[]],[84,404,[68],[]],[70,452,[86],[]],[86,452,[70],[]],[72,600,[88],[]],[88,600,[72],[]],[73,424,[89],[]],[89,424,[73],[]],[74,712,[90],[]],[90,712,[74],[]]],\"edges\":[[41,[14,41,49,52,54,58,65,69,72,74,81,85,88,90]],[42,[15,42,50,53,55,57,66,68,70,73,82,84,86,89]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record014" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record014\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,14,17,19,21],[-5,17],[-7,14,17,21],[-9,14,19,21],[-12,14,17,19],[-1,23,26,28,30],[-3,28,30],[-5,26],[-7,23,26,30],[-9,23,28,30],[-12,23,26,28],[-2,24,25,27,29],[-4,29],[-6,25,27],[-8,24,27,29],[-10,24,25,27],[-11,24,25,29],[-31,13,22],[-15,24],[-24,15],[-16,25],[-25,16],[-18,27],[-27,18],[-19,28],[-28,19],[-20,29],[-29,20],[-21,30],[-30,21],[-14,32],[-17,32],[-15,33],[-20,33],[-23,34],[-26,34],[-24,35],[-29,35],[-13,36],[-16,36],[-18,36],[-19,37],[-21,37],[-22,37],[-38,25,27,31],[-25,38],[-27,38],[-39,28,30],[-28,39],[-30,39],[-33,40],[-32,40],[-32,-33,41],[-35,42],[-34,42],[-34,-35,43],[-42,44],[-40,44],[-40,-43,45],[-41,-42,45],[-37,46],[-36,46],[-39,47],[-38,47],[-48,39],[-38,-39,48],[-46,-47,49],[-46,-48,50],[-50,51],[-44,-49,51],[-45,51],[-51],[1,3,5,7,9,12,14,17,19,21,23,26,28,30],[2,4,6,8,10,11,15,16,18,20,24,25,27,29]],\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":577,\"a\":14,\"owners\":[65,69,72,74]},{\"tag\":\"mate\",\"ridge\":577,\"a\":49,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":577,\"a\":52,\"owners\":[65,69,74]},{\"tag\":\"mate\",\"ridge\":577,\"a\":54,\"owners\":[65,72,74]},{\"tag\":\"mate\",\"ridge\":577,\"a\":58,\"owners\":[65,69,72]},{\"tag\":\"mate\",\"ridge\":578,\"a\":14,\"owners\":[81,85,88,90]},{\"tag\":\"mate\",\"ridge\":578,\"a\":41,\"owners\":[88,90]},{\"tag\":\"mate\",\"ridge\":578,\"a\":49,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":578,\"a\":52,\"owners\":[81,85,90]},{\"tag\":\"mate\",\"ridge\":578,\"a\":54,\"owners\":[81,88,90]},{\"tag\":\"mate\",\"ridge\":578,\"a\":58,\"owners\":[81,85,88]},{\"tag\":\"mate\",\"ridge\":386,\"a\":15,\"owners\":[82,84,86,89]},{\"tag\":\"mate\",\"ridge\":386,\"a\":42,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":386,\"a\":50,\"owners\":[84,86]},{\"tag\":\"mate\",\"ridge\":386,\"a\":53,\"owners\":[82,86,89]},{\"tag\":\"mate\",\"ridge\":386,\"a\":55,\"owners\":[82,84,86]},{\"tag\":\"mate\",\"ridge\":386,\"a\":57,\"owners\":[82,84,89]},{\"tag\":\"mate\",\"ridge\":204,\"a\":91,\"owners\":[64,80]},{\"tag\":\"mate\",\"ridge\":396,\"a\":66,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":396,\"a\":82,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":404,\"a\":68,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":404,\"a\":84,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":452,\"a\":70,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":452,\"a\":86,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":600,\"a\":72,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":600,\"a\":88,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":424,\"a\":73,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":424,\"a\":89,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":712,\"a\":74,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":712,\"a\":90,\"owners\":[74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":65,\"full_literals\":[-14,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":69,\"full_literals\":[-17,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":66,\"full_literals\":[-15,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":73,\"full_literals\":[-20,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":81,\"full_literals\":[-23,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":85,\"full_literals\":[-26,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":82,\"full_literals\":[-24,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":89,\"full_literals\":[-29,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":64,\"full_literals\":[-13,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":68,\"full_literals\":[-16,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":70,\"full_literals\":[-18,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":72,\"full_literals\":[-19,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":74,\"full_literals\":[-21,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":80,\"full_literals\":[-22,37]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[84,86,91],\"full_literals\":[-38,25,27,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":84,\"full_literals\":[-25,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":86,\"full_literals\":[-27,38]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[88,90],\"full_literals\":[-39,28,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":88,\"full_literals\":[-28,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":90,\"full_literals\":[-30,39]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-33,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-32,false,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-32,-33,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-35,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-34,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-34,-35,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-42,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-40,-43,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-41,-42,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-37,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-36,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-39,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-48,false,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-38,-39,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-46,-47,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-46,-48,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-50,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-44,-49,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-45,false,51],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":41,\"owners\":[14,41,49,52,54,58,65,69,72,74,81,85,88,90]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[15,42,50,53,55,57,66,68,70,73,82,84,86,89]}]}"
  "75 -50 0 72 69 0\n76 -45 0 72 71 0\n77 -48 0 75 65 68 61 42 43 26 30 48 0\n78 38 44 0 57 54 38 13 58 51 34 33 37 46 47 21 12 16 17 23 14 15 74 0\n79 44 0 77 57 58 55 52 35 36 31 32 8 78 66 49 50 25 6 10 11 29 7 9 73 0\n80 -49 0 79 72 70 0\n81 -38 0 80 64 67 61 62 44 39 40 41 18 22 24 45 0\n82 -25 0 81 46 0\n83 -27 0 81 47 0\n84 -16 0 82 21 0\n85 -18 0 83 23 0\n86 -6 0 83 82 14 0\n87 24 29 0 83 82 85 84 86 27 13 19 12 16 17 15 74 0\n88 -24 39 0 76 49 50 7 29 25 20 37 33 54 51 60 59 53 56 31 32 35 36 1 4 5 3 2 73 0\n89 39 0 76 49 50 25 29 7 88 87 28 38 34 54 51 60 59 53 56 31 32 35 36 1 4 5 3 2 73 0\n90 47 0 89 63 0\n91 -46 0 90 80 67 0\n92 -37 0 91 61 0\n93 -19 0 92 42 0\n94 -21 0 92 43 0\n95 -28 0 93 26 0\n96 -30 0 94 30 0\n97 0 95 96 89 48 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record014.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record014.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record014.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record014.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record014 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record014.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record014.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record014.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record014.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record014 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record014_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record014_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record014_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record014_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record014_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record014_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record014_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record014 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record014_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record014_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record014_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record014

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record018
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2e43d19c2f1d23ca6a1ea6639996358b61da2e4783eb85d13c5a99a599964b91e6c5a966539595954d52d475634ad8751d2743d70da398ce364d5334cb31ce4b8ad2b1ac5b0ed8791cc789ca719d1725c570de0f43e2c4682e07a61385913462946625294958342d0746344c5342c2b06c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db6db6db69249349b6d249a4da4926d24934d24936d2492491249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record018 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record018 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record018.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record018.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record018.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 42), (facetIndex 67), (facetIndex 69)]))
 (.leaf ([(facetIndex 57), (facetIndex 68), (facetIndex 72)])))
 (.branch 3
 (.leaf ([(facetIndex 85), (facetIndex 86)]))
 (.leaf ([(facetIndex 89), (facetIndex 90)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 34), (facetIndex 36), (facetIndex 44), (facetIndex 50), (facetIndex 51)]))
 (.leaf ([(facetIndex 35), (facetIndex 58), (facetIndex 61), (facetIndex 66), (facetIndex 81)])))
 (.branch 7
 (.leaf ([(facetIndex 80), (facetIndex 82), (facetIndex 83), (facetIndex 88)]))
 (.branch 8
 (.leaf ([(facetIndex 79), (facetIndex 84), (facetIndex 92)]))
 (.leaf ([(facetIndex 87), (facetIndex 91)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "78336822766567000000100010500005005100000440000040000000454z22;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record018 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record018_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record018" "{\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record018" 60

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record018" "{\"ridges\":[[6,82],[17,208],[19,224],[20,577],[20,608],[34,198],[35,582],[38,82],[43,98],[45,82],[45,208],[46,82],[48,224],[49,577],[49,608],[51,450],[60,208],[61,596],[63,224],[64,608],[66,708],[69,600],[71,577],[71,608],[73,224],[74,208],[75,224],[75,577],[75,608],[79,116],[80,178],[81,198],[82,390],[83,198],[84,582],[87,178],[88,450],[91,116],[92,708]],\"owners\":[[6,82,[79,81,85,87,88],[28,38,43,45,46]],[38,82,[79,81,87,88],[6,28,43,45,46,85]],[45,82,[79,85],[6,28,38,43,46,81,87,88]],[46,82,[79,81,85,87],[6,28,38,43,45,88]],[43,98,[83,84,86],[8,31,39,48,49,79,85,87]],[17,208,[81,87,88,91],[45,60,73,74]],[45,208,[91],[17,60,73,74,81,87,88]],[60,208,[87,88],[17,45,73,74,81,91]],[74,208,[81,87,91],[17,45,60,73,88]],[19,224,[83,87,91,92],[48,63,73,75]],[48,224,[91,92],[19,63,73,75,83,87]],[63,224,[87],[19,48,73,75,83,91,92]],[73,224,[83,92],[19,48,63,75,87,91]],[75,224,[83,87,91],[19,48,63,73,92]],[20,577,[35,42,61,66,69],[49,64,71,75]],[49,577,[61,66,69],[20,35,42,64,71,75]],[71,577,[35,61,66],[20,42,49,64,69,75]],[75,577,[35,42,61,69],[20,49,64,66,71]],[20,608,[84,86,92],[49,64,71,75]],[49,608,[92],[20,64,71,75,84,86]],[64,608,[86],[20,49,71,75,84,92]],[71,608,[84,92],[20,49,64,75,86]],[75,608,[84,86],[20,49,64,71,92]],[34,198,[81,83],[]],[81,198,[34,83],[]],[83,198,[34,81],[]],[35,582,[84],[]],[84,582,[35],[]],[82,390,[36],[]],[80,178,[44,87],[]],[87,178,[44,80],[]],[51,450,[88],[]],[88,450,[51],[]],[79,116,[58,91],[]],[91,116,[58,79],[]],[61,596,[],[]],[66,708,[92],[]],[92,708,[66],[]],[69,600,[],[]]],\"edges\":[[31,[6,17,28,38,43,45,46,58,60,61,67,69,73,74,79,81,85,87,88,91]],[39,[17,19,34,45,48,51,60,63,66,73,74,75,81,83,87,88,91,92]],[41,[20,35,42,49,61,64,66,69,71,75,84,86,92]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record018" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record018\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-11,-7],[-27,-23],[-35,-5],[-35,-18],[-35,-19],[-35,-30],[-35,-32],[-35,-34],[-40,-35],[-41,-5],[-41,-18],[-41,-19],[-41,-30],[-41,-32],[-41,-34],[-41,-35],[-41,-40],[-1,30,32,36,38,39],[-9,30,32,38,39],[-13,30,36],[-14,30,32,36,38],[-11,34,35,37],[-2,32,38,39,40],[-13,40],[-19,38,39],[-28,32,38,40],[-3,34,38,40,41],[-15,40,41],[-21,38],[-27,34,41],[-29,34,38,40],[-4,7,10,20,23,25],[-16,20,23,25],[-26,7,20,23],[-29,7,10,20,25],[-4,35,37,41],[-16,41],[-22,37],[-26,35,41],[-29,35,37],[-6,32,34],[-32,6,34],[-34,6,32],[-7,35],[-35,7],[-33,8],[-31,12,38],[-38,12,31],[-17,39],[-39,17],[-30,18,40],[-40,18,30],[-20],[-23,41],[-41,23],[-25],[-10,42],[-24,42],[-36,43],[-37,43],[-6,44],[-8,44],[-12,44],[-17,44],[-7,45],[-18,45],[-23,45],[-32,45],[-46,31,33,34,39],[-31,46],[-34,46],[-39,46],[-47,30,35,41],[-30,47],[-35,47],[-41,47],[-48,38,40],[-38,48],[-40,48],[-42,49],[-43,50],[-50,51],[-49,51],[-45,52],[-44,52],[-44,-45,53],[-54,47,48],[-48,54],[-47,54],[-47,-48,55],[-54,56],[-55,57],[-46,56],[-46,-54,57],[-57,58],[-52,-56,58],[-52,-57,59],[-53,58],[-59,60],[-51,-58,60],[-60],[1,2,5,9,11,13,14,18,19,20,24,25,27,28,30,32,36,38,39,40],[2,3,6,13,15,17,19,21,23,27,28,29,32,34,38,39,40,41],[4,7,10,16,20,22,23,25,26,29,35,37,41]],\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":43,\"b\":35},{\"tag\":\"incompatible\",\"a\":73,\"b\":66},{\"tag\":\"incompatible\",\"a\":84,\"b\":28},{\"tag\":\"incompatible\",\"a\":84,\"b\":58},{\"tag\":\"incompatible\",\"a\":84,\"b\":60},{\"tag\":\"incompatible\",\"a\":84,\"b\":79},{\"tag\":\"incompatible\",\"a\":84,\"b\":81},{\"tag\":\"incompatible\",\"a\":84,\"b\":83},{\"tag\":\"incompatible\",\"a\":91,\"b\":84},{\"tag\":\"incompatible\",\"a\":92,\"b\":28},{\"tag\":\"incompatible\",\"a\":92,\"b\":58},{\"tag\":\"incompatible\",\"a\":92,\"b\":60},{\"tag\":\"incompatible\",\"a\":92,\"b\":79},{\"tag\":\"incompatible\",\"a\":92,\"b\":81},{\"tag\":\"incompatible\",\"a\":92,\"b\":83},{\"tag\":\"incompatible\",\"a\":92,\"b\":84},{\"tag\":\"incompatible\",\"a\":92,\"b\":91},{\"tag\":\"mate\",\"ridge\":82,\"a\":6,\"owners\":[79,81,85,87,88]},{\"tag\":\"mate\",\"ridge\":82,\"a\":38,\"owners\":[79,81,87,88]},{\"tag\":\"mate\",\"ridge\":82,\"a\":45,\"owners\":[79,85]},{\"tag\":\"mate\",\"ridge\":82,\"a\":46,\"owners\":[79,81,85,87]},{\"tag\":\"mate\",\"ridge\":98,\"a\":43,\"owners\":[83,84,86]},{\"tag\":\"mate\",\"ridge\":208,\"a\":17,\"owners\":[81,87,88,91]},{\"tag\":\"mate\",\"ridge\":208,\"a\":45,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":208,\"a\":60,\"owners\":[87,88]},{\"tag\":\"mate\",\"ridge\":208,\"a\":74,\"owners\":[81,87,91]},{\"tag\":\"mate\",\"ridge\":224,\"a\":19,\"owners\":[83,87,91,92]},{\"tag\":\"mate\",\"ridge\":224,\"a\":48,\"owners\":[91,92]},{\"tag\":\"mate\",\"ridge\":224,\"a\":63,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":224,\"a\":73,\"owners\":[83,92]},{\"tag\":\"mate\",\"ridge\":224,\"a\":75,\"owners\":[83,87,91]},{\"tag\":\"mate\",\"ridge\":577,\"a\":20,\"owners\":[35,42,61,66,69]},{\"tag\":\"mate\",\"ridge\":577,\"a\":49,\"owners\":[61,66,69]},{\"tag\":\"mate\",\"ridge\":577,\"a\":71,\"owners\":[35,61,66]},{\"tag\":\"mate\",\"ridge\":577,\"a\":75,\"owners\":[35,42,61,69]},{\"tag\":\"mate\",\"ridge\":608,\"a\":20,\"owners\":[84,86,92]},{\"tag\":\"mate\",\"ridge\":608,\"a\":49,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":608,\"a\":64,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":608,\"a\":71,\"owners\":[84,92]},{\"tag\":\"mate\",\"ridge\":608,\"a\":75,\"owners\":[84,86]},{\"tag\":\"mate\",\"ridge\":198,\"a\":34,\"owners\":[81,83]},{\"tag\":\"mate\",\"ridge\":198,\"a\":81,\"owners\":[34,83]},{\"tag\":\"mate\",\"ridge\":198,\"a\":83,\"owners\":[34,81]},{\"tag\":\"mate\",\"ridge\":582,\"a\":35,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":582,\"a\":84,\"owners\":[35]},{\"tag\":\"mate\",\"ridge\":390,\"a\":82,\"owners\":[36]},{\"tag\":\"mate\",\"ridge\":178,\"a\":80,\"owners\":[44,87]},{\"tag\":\"mate\",\"ridge\":178,\"a\":87,\"owners\":[44,80]},{\"tag\":\"mate\",\"ridge\":450,\"a\":51,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":450,\"a\":88,\"owners\":[51]},{\"tag\":\"mate\",\"ridge\":116,\"a\":79,\"owners\":[58,91]},{\"tag\":\"mate\",\"ridge\":116,\"a\":91,\"owners\":[58,79]},{\"tag\":\"mate\",\"ridge\":596,\"a\":61,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":708,\"a\":66,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":708,\"a\":92,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":600,\"a\":69,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":42,\"full_literals\":[-10,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":67,\"full_literals\":[-24,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":85,\"full_literals\":[-36,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":86,\"full_literals\":[-37,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":34,\"full_literals\":[-6,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":36,\"full_literals\":[-8,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":44,\"full_literals\":[-12,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":51,\"full_literals\":[-17,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":35,\"full_literals\":[-7,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":58,\"full_literals\":[-18,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":66,\"full_literals\":[-23,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":81,\"full_literals\":[-32,45]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[80,82,83,88],\"full_literals\":[-46,31,33,34,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":80,\"full_literals\":[-31,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":83,\"full_literals\":[-34,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":88,\"full_literals\":[-39,46]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[79,84,92],\"full_literals\":[-47,30,35,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":79,\"full_literals\":[-30,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":84,\"full_literals\":[-35,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":92,\"full_literals\":[-41,47]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[87,91],\"full_literals\":[-48,38,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":87,\"full_literals\":[-38,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":91,\"full_literals\":[-40,48]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-43,false,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-50,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-49,false,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-45,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-44,-45,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-54,47,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-48,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-47,false,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-47,-48,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-54,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-55,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-46,-54,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-57,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-52,-56,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-52,-57,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-59,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-51,-58,60],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":31,\"owners\":[6,17,28,38,43,45,46,58,60,61,67,69,73,74,79,81,85,87,88,91]},{\"tag\":\"edge\",\"edge\":39,\"owners\":[17,19,34,45,48,51,60,63,66,73,74,75,81,83,87,88,91,92]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[20,35,42,49,61,64,66,69,71,75,84,86,92]}]}"
  "105 -59 0 101 99 0\n106 1 2 5 9 11 13 14 18 19 24 27 28 30 32 36 38 39 40 0 53 56 102 0\n107 4 7 10 16 22 23 26 29 35 37 41 0 53 56 104 0\n108 45 51 0 56 53 82 81 60 38 83 80 57 65 67 45 35 33 55 34 32 107 0\n109 35 41 51 0 54 37 82 81 60 38 83 80 57 44 40 39 36 107 0\n110 41 51 0 105 108 84 97 92 83 80 58 82 81 59 109 3 4 5 6 7 8 9 45 75 20 30 1 89 90 94 78 72 18 19 23 26 21 106 0\n111 51 0 105 82 83 81 80 59 60 58 108 84 97 92 110 10 11 12 13 14 15 16 17 55 76 20 22 2 89 90 94 78 72 18 19 23 26 21 106 0\n112 -58 0 111 101 100 0\n113 -57 0 112 95 0\n114 -53 0 112 98 0\n115 -55 0 113 92 0\n116 -41 0 112 55 76 67 89 84 91 96 0\n117 -23 0 116 54 0\n118 48 -54 35 0 112 116 91 96 84 66 79 87 51 73 0\n119 -54 35 0 113 112 115 91 94 96 70 84 85 66 63 48 118 77 90 52 74 0\n120 32 46 48 0 116 117 78 72 25 49 79 71 31 27 30 28 24 29 41 23 26 103 0\n121 -32 34 0 114 42 68 61 86 0\n122 46 48 0 71 120 121 0\n123 48 0 112 78 122 93 96 84 85 68 61 62 63 64 43 46 47 50 69 0\n124 54 0 123 88 0\n125 -47 0 123 115 90 0\n126 35 0 124 119 0\n127 0 126 125 75 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record018.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record018.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record018.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record018.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record018 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record018.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record018.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record018.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record018.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record018 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record018_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record018_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record018_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record018_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record018_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record018_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record018_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record018 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record018_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record018_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record018_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record018

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record029
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "23c749aa668da998e695a36338ae4785e0fae1745a9664d98e665396353362d2b61d4745d0f5c368e6338d9394d5334e3332d2b26c5b0ee4731e2729c6785d170dd0f23c4f9518a2a91a1582e07a51624a946645896151542d0758330ca344c5342c8b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36936d36924da4da69a4924934924d2492492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record029 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record029 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record029.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record029.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record029.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 46), (facetIndex 65)]))
 (.leaf ([(facetIndex 66), (facetIndex 69)])))
 (.branch 3
 (.leaf ([(facetIndex 80), (facetIndex 83)]))
 (.leaf ([(facetIndex 76), (facetIndex 84)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 61), (facetIndex 63)]))
 (.leaf ([(facetIndex 52), (facetIndex 70), (facetIndex 78)])))
 (.branch 7
 (.leaf ([(facetIndex 75)]))
 (.leaf ([(facetIndex 79)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "3402f43c00148040820000005z27;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record029 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record029_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record029" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record029" 47

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record029" "{\"ridges\":[[11,194],[17,545],[17,548],[38,545],[38,548],[39,194],[45,193],[45,194],[47,194],[51,194],[52,610],[54,194],[60,545],[60,548],[61,204],[62,548],[63,228],[64,545],[64,548],[66,216],[69,464],[70,736],[75,204],[78,228],[79,610],[80,216],[83,464]],\"owners\":[[45,193,[63,69,70],[11,39,47,51,54,61,66]],[11,194,[75,78,80,83],[39,45,47,51,54]],[39,194,[80,83],[11,45,47,51,54,75,78]],[45,194,[78,83],[11,39,47,51,54,75,80]],[47,194,[75,78],[11,39,45,51,54,80,83]],[51,194,[75,80,83],[11,39,45,47,54,78]],[54,194,[75,78,80],[11,39,45,47,51,83]],[17,545,[46,52,65,70],[38,60,62,64]],[38,545,[65,70],[17,46,52,60,62,64]],[60,545,[46,52,70],[17,38,62,64,65]],[64,545,[46,65],[17,38,52,60,62,70]],[17,548,[76,79,84],[38,60,62,64]],[38,548,[84],[17,60,62,64,76,79]],[60,548,[76,79],[17,38,62,64,84]],[62,548,[79],[17,38,60,64,76,84]],[64,548,[76,84],[17,38,60,62,79]],[52,610,[79],[]],[79,610,[52],[]],[61,204,[75],[]],[75,204,[61],[]],[63,228,[78],[]],[78,228,[63],[]],[66,216,[80],[]],[80,216,[66],[]],[69,464,[83],[]],[83,464,[69],[]],[70,736,[],[]]],\"edges\":[[38,[17,38,46,52,60,62,64,65,70,76,79,84]],[39,[11,39,45,47,51,54,61,63,66,69,70,75,78,80,83]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record029" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record029\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-23,-8],[-23,-14],[-23,-22],[-5,14,18,19],[-1,20,22,24,25],[-4,24,25],[-5,22,25],[-7,20,22],[-8,20,24,25],[-10,20,22,24],[-2,6,9,16,19],[-3,16,19],[-11,6,9,19],[-15,6,16],[-2,21,23,26],[-3,26],[-11,21,23],[-13,23],[-15,21,26],[-9,23],[-23,9],[-12,20],[-20,12],[-14,22],[-22,14],[-17,24],[-24,17],[-18,25],[-25,18],[-19],[-6,27],[-16,27],[-17,28],[-18,28],[-24,29],[-25,29],[-21,30],[-26,30],[-12,31],[-14,31],[-9,32],[-22,32],[-33,20],[-20,33],[-34,23],[-23,34],[-28,35],[-27,35],[-27,-28,36],[-30,37],[-29,37],[-29,-30,38],[-37,39],[-35,39],[-35,-38,40],[-36,-37,40],[-32,41],[-31,41],[-31,-32,42],[-34,43],[-33,43],[-44,34],[-33,-34,44],[-41,-43,45],[-41,-44,46],[-42,45],[-46,47],[-39,-45,47],[-40,47],[-47],[2,3,6,9,11,13,15,16,19,21,23,26],[1,4,5,7,8,10,12,14,17,18,19,20,22,24,25]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":79,\"b\":51},{\"tag\":\"incompatible\",\"a\":79,\"b\":63},{\"tag\":\"incompatible\",\"a\":79,\"b\":78},{\"tag\":\"mate\",\"ridge\":193,\"a\":45,\"owners\":[63,69,70]},{\"tag\":\"mate\",\"ridge\":194,\"a\":11,\"owners\":[75,78,80,83]},{\"tag\":\"mate\",\"ridge\":194,\"a\":39,\"owners\":[80,83]},{\"tag\":\"mate\",\"ridge\":194,\"a\":45,\"owners\":[78,83]},{\"tag\":\"mate\",\"ridge\":194,\"a\":47,\"owners\":[75,78]},{\"tag\":\"mate\",\"ridge\":194,\"a\":51,\"owners\":[75,80,83]},{\"tag\":\"mate\",\"ridge\":194,\"a\":54,\"owners\":[75,78,80]},{\"tag\":\"mate\",\"ridge\":545,\"a\":17,\"owners\":[46,52,65,70]},{\"tag\":\"mate\",\"ridge\":545,\"a\":38,\"owners\":[65,70]},{\"tag\":\"mate\",\"ridge\":545,\"a\":60,\"owners\":[46,52,70]},{\"tag\":\"mate\",\"ridge\":545,\"a\":64,\"owners\":[46,65]},{\"tag\":\"mate\",\"ridge\":548,\"a\":17,\"owners\":[76,79,84]},{\"tag\":\"mate\",\"ridge\":548,\"a\":38,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":548,\"a\":60,\"owners\":[76,79]},{\"tag\":\"mate\",\"ridge\":548,\"a\":62,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":548,\"a\":64,\"owners\":[76,84]},{\"tag\":\"mate\",\"ridge\":610,\"a\":52,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":610,\"a\":79,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":204,\"a\":61,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":204,\"a\":75,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":228,\"a\":63,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":228,\"a\":78,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":216,\"a\":66,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":216,\"a\":80,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":464,\"a\":69,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":464,\"a\":83,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":736,\"a\":70,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":46,\"full_literals\":[-6,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":65,\"full_literals\":[-16,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":66,\"full_literals\":[-17,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":69,\"full_literals\":[-18,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":80,\"full_literals\":[-24,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":83,\"full_literals\":[-25,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":76,\"full_literals\":[-21,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":84,\"full_literals\":[-26,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":61,\"full_literals\":[-12,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":63,\"full_literals\":[-14,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":52,\"full_literals\":[-9,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":78,\"full_literals\":[-22,32]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[75],\"full_literals\":[-33,20]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":75,\"full_literals\":[-20,33]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[79],\"full_literals\":[-34,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":79,\"full_literals\":[-23,34]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-28,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-27,false,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-27,-28,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-30,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-29,false,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-29,-30,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-37,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-35,false,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-35,-38,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-36,-37,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-32,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-31,false,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-31,-32,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-34,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-33,false,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-44,false,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-33,-34,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-41,-43,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-41,-44,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-46,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-39,-45,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,47],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":38,\"owners\":[17,38,46,52,60,62,64,65,70,76,79,84]},{\"tag\":\"edge\",\"edge\":39,\"owners\":[11,39,45,47,51,54,61,63,66,69,70,75,78,80,83]}]}"
  "73 -46 0 70 67 0\n74 -40 0 70 69 0\n75 2 3 6 9 11 13 15 16 21 23 26 0 30 71 0\n76 1 4 5 7 8 10 12 14 17 18 20 22 24 25 0 30 72 0\n77 -44 0 73 62 65 45 57 21 41 0\n78 -34 39 0 77 30 53 51 35 36 6 54 47 34 33 45 63 1 2 3 44 4 8 10 5 22 76 0\n79 39 0 53 54 50 48 37 38 31 32 16 19 78 46 18 20 17 15 75 0\n80 -45 0 79 70 68 0\n81 -42 0 80 66 0\n82 -33 0 80 43 61 23 64 39 58 0\n83 -20 0 82 44 0\n84 -12 0 83 22 0\n85 22 24 25 0 83 84 9 6 26 28 7 24 8 10 5 76 0\n86 -22 0 81 25 42 40 59 0\n87 -24 23 0 74 30 20 18 27 35 33 51 47 56 55 49 52 31 32 37 38 13 12 14 11 75 0\n88 23 0 86 74 30 18 20 87 85 29 36 34 51 47 56 55 49 52 31 32 37 38 13 12 14 11 75 0\n89 9 0 88 21 0\n90 34 0 88 46 0\n91 32 0 89 41 0\n92 43 0 90 60 0\n93 41 0 91 57 0\n94 0 93 92 80 64 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record029.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record029.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record029.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record029.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record029 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record029.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record029.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record029.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record029.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record029 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record029_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record029_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record029_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record029_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record029_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record029_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record029_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record029 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record029_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record029_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record029_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record029

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record040
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "370bc749aa668da2ea6695a2e4785e0fae1745a9364b9994e5954d52d4cd8b4ad4749d1743d70da398ce364e5354cd32cd8b32e2b4acab26c5b0ec6785d170de0f43c4f6611a91a261582e07991345892a51926645894550b41d90e2344c5342c2b06e0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db4da4924d249349b49249b4d249a692492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record040 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record040 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record040.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record040.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record040.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 32), (facetIndex 35), (facetIndex 36), (facetIndex 51), (facetIndex 65), (facetIndex 76)]))
 (.leaf ([(facetIndex 33), (facetIndex 42), (facetIndex 59), (facetIndex 74)])))
 (.branch 3
 (.leaf ([(facetIndex 30), (facetIndex 48), (facetIndex 63), (facetIndex 75)]))
 (.branch 4
 (.leaf ([(facetIndex 39), (facetIndex 40), (facetIndex 44), (facetIndex 46), (facetIndex 49), (facetIndex 79)]))
 (.leaf ([(facetIndex 41), (facetIndex 58), (facetIndex 68)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 47), (facetIndex 62), (facetIndex 69)]))
 (.leaf ([(facetIndex 37), (facetIndex 54), (facetIndex 66), (facetIndex 71)])))
 (.branch 8
 (.leaf ([(facetIndex 34), (facetIndex 38), (facetIndex 72), (facetIndex 73)]))
 (.branch 9
 (.leaf ([(facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 67)]))
 (.leaf ([(facetIndex 31)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "30002177605486002500148886000032530301433760071092z1e;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 50), (facetIndex 64), (facetIndex 70)]))
 (.leaf ([(facetIndex 60), (facetIndex 61)])))
 (.branch 3
 (.leaf ([(facetIndex 82), (facetIndex 83)]))
 (.branch 4
 (.leaf ([(facetIndex 43), (facetIndex 45), (facetIndex 52), (facetIndex 53)]))
 (.leaf ([(facetIndex 77), (facetIndex 78), (facetIndex 80), (facetIndex 81)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "4a412000000000000900001b0000186z20;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 5
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
def grouped2_0008 : List Nat := [5]
def grouped2_0009 : List Nat := [5, 6]
def grouped2_0010 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0011 : List Nat := [6]
def grouped2_0012 : List Nat := [7]
def grouped2_0013 : List Nat := [7, 8, 9]
def grouped2_0014 : List Nat := [8]
def grouped2_0015 : List Nat := [8, 9]
def grouped2_0016 : List Nat := [9]
def grouped3_0017 : List Nat := [0]
def grouped3_0018 : List Nat := [0, 1]
def grouped3_0020 : List Nat := [1]
def grouped3_0021 : List Nat := [2]
def grouped3_0022 : List Nat := [2, 3, 4]
def grouped3_0023 : List Nat := [3]
def grouped3_0024 : List Nat := [3, 4]
def grouped3_0025 : List Nat := [4]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record040 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record040_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record040" "{\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record040" 85

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record040" "{\"ridges\":[[12,25],[13,44],[17,152],[18,25],[19,41],[19,161],[19,168],[21,193],[21,208],[24,14],[29,392],[31,14],[31,265],[39,152],[40,161],[41,41],[46,193],[49,259],[49,385],[50,226],[52,418],[54,41],[55,25],[58,44],[58,161],[59,44],[60,204],[61,180],[64,228],[66,25],[66,161],[67,152],[67,193],[68,161],[69,193],[70,736],[72,14],[72,28],[74,14],[77,42],[77,178],[78,202],[79,266],[79,392],[79,400],[80,42],[80,418],[82,180],[83,204]],\"owners\":[[19,41,[6,13,37,41,42,54,59],[66,68]],[77,42,[6,24,41,42,74],[37,40,71,80]],[80,42,[6,24,37,42,71,74],[40,41,77]],[49,259,[7,31,41],[9,34,44,47,52,53]],[31,265,[18,20,68],[7,41,57]],[79,266,[7,31,41],[28,44,73,80]],[72,28,[12,54,56,57,82],[23,55,71,73,83]],[13,44,[24,71,74,82],[54,58,59]],[58,44,[24,71,74],[13,54,59,82]],[59,44,[24,71,82],[13,54,58,74]],[17,152,[29,77,78,79,82,83],[39,56,66,67]],[39,152,[29,82,83],[17,56,66,67,77,78,79]],[67,152,[29,77,79,82],[17,39,56,66,78,83]],[19,161,[45,50,52,61,64,70],[40,58,66,68]],[40,161,[61,64,70],[19,45,50,52,58,66,68]],[58,161,[45,50,52,70],[19,40,61,64,66,68]],[66,161,[50,52,64,70],[19,40,45,58,61,68]],[68,161,[45,50,61,64,70],[19,40,52,58,66]],[19,168,[77,80,82],[40,58,66,68]],[49,385,[20,68],[22,44,52,53,69]],[29,392,[20,44,68,80],[79]],[79,392,[20,68],[29,44,80]],[21,193,[43,50,53,60,64,70],[46,62,67,69]],[46,193,[60,64,70],[21,43,50,53,62,67,69]],[67,193,[50,53,64,70],[21,43,46,60,62,69]],[69,193,[43,50,60,64,70],[21,46,53,62,67]],[21,208,[78,81,83],[46,62,67,69]],[79,400,[22,69],[29,49,81]],[78,202,[43],[]],[77,178,[45],[]],[50,226,[],[]],[52,418,[80],[]],[80,418,[52],[]],[60,204,[83],[]],[83,204,[60],[]],[61,180,[82],[]],[82,180,[61],[]],[64,228,[],[]],[70,736,[],[]]],\"edges\":[[25,[6,13,19,24,37,40,41,42,54,58,59,66,68,71,74,77,80,82]],[27,[17,19,20,29,39,40,43,44,56,58,60,66,67,68,77,78,79,80,82,83]],[36,[19,40,45,50,52,58,61,64,66,68,70,77,80,82]],[39,[21,43,46,50,53,60,62,64,67,69,70,78,81,83]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record040" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record040\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-13,-1],[-14,-13],[-15,-2],[-15,-13],[-16,-13],[-17,-15],[-19,-13],[-19,-15],[-20,-13],[-21,-19],[-22,-8],[-22,-21],[-23,-15],[-23,-17],[-23,-22],[-25,-23],[-27,-17],[-27,-19],[-27,-21],[-27,-22],[-27,-25],[-28,-22],[-28,-27],[-29,-13],[-29,-17],[-29,-23],[-30,-29],[-31,-29],[-32,-13],[-32,-29],[-33,-15],[-33,-29],[-35,-33],[-36,-35],[-37,-33],[-37,-36],[-39,-8],[-39,-17],[-39,-22],[-39,-31],[-39,-33],[-40,-10],[-40,-25],[-40,-36],[-40,-39],[-41,-31],[-41,-35],[-41,-39],[-42,-36],[-42,-40],[-44,-13],[-44,-23],[-44,-39],[-45,-30],[-45,-40],[-46,-13],[-48,-29],[-48,-44],[-49,-27],[-50,-23],[-50,-27],[-51,-19],[-52,-27],[-54,-36],[-11,-13,-45],[-13,-45,-47],[-3,-6,-39],[-6,-30,-39],[-7,1,4,15,19,20,29,34],[-7,-19,-29],[-48,1,11,19,20,47],[-51,1,11,15,20,44,47],[-25,2,13,19],[-13,6,8,41],[-50,2,13,19],[-45,3,29,31,32,53],[-4,11,44,47,53],[-33,11,44,47],[-34,11,44,53],[-5,12,48,49,50,53,54],[-17,12,53,54],[-40,12,48,50,53],[-7,23,26,27,36,38,43],[-18,36,38,43],[-33,23,26,27,43],[-39,26,27,38,43],[-41,23,26,36,38,43],[-7,48,51,53],[-25,8,41],[-12,8,22,41,51],[-50,8,41],[-9,21,26,28,35,38,43],[-24,35,38,43],[-40,26,28,38,43],[-42,21,26,35,38,43],[-9,49,52,54],[-50,10,42],[-49,21],[-48,23],[-26],[-27,51],[-51,27],[-35,54],[-54,35],[-36,53],[-53,36],[-38],[-43],[-55,17,18,22,24,25,50],[-17,55],[-22,55],[-56,19,33,41],[-57,15,29,39,44],[-58,14,16,45,46],[-59,30,31,32,40],[-31,59],[-60,13],[-13,60],[-61,55,56],[-62,55],[-63,61],[-64,62],[-65,63],[-66,64],[-67,57],[-68,59,60],[-69,59],[-69,60],[-59,-60,69],[-70,58,69],[-71,58],[-70,68],[-71,69],[-72,67,71],[-73,67],[-72,70],[-73,71],[-74,65,73],[-74,66,72],[74],[-75,26,38,43],[-76,35,36],[-35,76],[-36,76],[-77,53,54],[-53,77],[-54,77],[-78,21,23,27,28],[-21,78],[-23,78],[-27,78],[-28,78],[-48,79],[-49,79],[-51,79],[-52,79],[-80,75,76],[-76,80],[-79,81],[-82,78],[-78,81],[-78,-79,82],[-83,77,82],[-82,83],[-77,-81,83],[-84,80,83],[-80,-83,85],[84],[-85],[1,4,7,11,15,18,19,20,29,33,34,39,41,44,47,48,51,53],[5,7,8,12,17,18,21,22,31,33,35,39,40,41,48,49,50,51,53,54],[7,18,23,26,27,33,36,38,39,41,43,48,51,53],[9,21,24,26,28,35,37,38,40,42,43,49,52,54]],\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":31,\"b\":6},{\"tag\":\"incompatible\",\"a\":34,\"b\":31},{\"tag\":\"incompatible\",\"a\":37,\"b\":7},{\"tag\":\"incompatible\",\"a\":37,\"b\":31},{\"tag\":\"incompatible\",\"a\":38,\"b\":31},{\"tag\":\"incompatible\",\"a\":39,\"b\":37},{\"tag\":\"incompatible\",\"a\":41,\"b\":31},{\"tag\":\"incompatible\",\"a\":41,\"b\":37},{\"tag\":\"incompatible\",\"a\":42,\"b\":31},{\"tag\":\"incompatible\",\"a\":43,\"b\":41},{\"tag\":\"incompatible\",\"a\":44,\"b\":20},{\"tag\":\"incompatible\",\"a\":44,\"b\":43},{\"tag\":\"incompatible\",\"a\":45,\"b\":37},{\"tag\":\"incompatible\",\"a\":45,\"b\":39},{\"tag\":\"incompatible\",\"a\":45,\"b\":44},{\"tag\":\"incompatible\",\"a\":49,\"b\":45},{\"tag\":\"incompatible\",\"a\":52,\"b\":39},{\"tag\":\"incompatible\",\"a\":52,\"b\":41},{\"tag\":\"incompatible\",\"a\":52,\"b\":43},{\"tag\":\"incompatible\",\"a\":52,\"b\":44},{\"tag\":\"incompatible\",\"a\":52,\"b\":49},{\"tag\":\"incompatible\",\"a\":53,\"b\":44},{\"tag\":\"incompatible\",\"a\":53,\"b\":52},{\"tag\":\"incompatible\",\"a\":54,\"b\":31},{\"tag\":\"incompatible\",\"a\":54,\"b\":39},{\"tag\":\"incompatible\",\"a\":54,\"b\":45},{\"tag\":\"incompatible\",\"a\":55,\"b\":54},{\"tag\":\"incompatible\",\"a\":56,\"b\":54},{\"tag\":\"incompatible\",\"a\":57,\"b\":31},{\"tag\":\"incompatible\",\"a\":57,\"b\":54},{\"tag\":\"incompatible\",\"a\":58,\"b\":37},{\"tag\":\"incompatible\",\"a\":58,\"b\":54},{\"tag\":\"incompatible\",\"a\":60,\"b\":58},{\"tag\":\"incompatible\",\"a\":61,\"b\":60},{\"tag\":\"incompatible\",\"a\":62,\"b\":58},{\"tag\":\"incompatible\",\"a\":62,\"b\":61},{\"tag\":\"incompatible\",\"a\":66,\"b\":20},{\"tag\":\"incompatible\",\"a\":66,\"b\":39},{\"tag\":\"incompatible\",\"a\":66,\"b\":44},{\"tag\":\"incompatible\",\"a\":66,\"b\":56},{\"tag\":\"incompatible\",\"a\":66,\"b\":58},{\"tag\":\"incompatible\",\"a\":67,\"b\":22},{\"tag\":\"incompatible\",\"a\":67,\"b\":49},{\"tag\":\"incompatible\",\"a\":67,\"b\":61},{\"tag\":\"incompatible\",\"a\":67,\"b\":66},{\"tag\":\"incompatible\",\"a\":68,\"b\":56},{\"tag\":\"incompatible\",\"a\":68,\"b\":60},{\"tag\":\"incompatible\",\"a\":68,\"b\":66},{\"tag\":\"incompatible\",\"a\":69,\"b\":61},{\"tag\":\"incompatible\",\"a\":69,\"b\":67},{\"tag\":\"incompatible\",\"a\":71,\"b\":31},{\"tag\":\"incompatible\",\"a\":71,\"b\":45},{\"tag\":\"incompatible\",\"a\":71,\"b\":66},{\"tag\":\"incompatible\",\"a\":72,\"b\":55},{\"tag\":\"incompatible\",\"a\":72,\"b\":67},{\"tag\":\"incompatible\",\"a\":73,\"b\":31},{\"tag\":\"incompatible\",\"a\":77,\"b\":54},{\"tag\":\"incompatible\",\"a\":77,\"b\":71},{\"tag\":\"incompatible\",\"a\":78,\"b\":52},{\"tag\":\"incompatible\",\"a\":79,\"b\":45},{\"tag\":\"incompatible\",\"a\":79,\"b\":52},{\"tag\":\"incompatible\",\"a\":80,\"b\":41},{\"tag\":\"incompatible\",\"a\":81,\"b\":52},{\"tag\":\"incompatible\",\"a\":83,\"b\":61},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[24,31,72]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[31,72,74]},{\"tag\":\"three\",\"ridge\":25,\"vertices\":[12,18,66]},{\"tag\":\"three\",\"ridge\":25,\"vertices\":[18,55,66]},{\"tag\":\"mate\",\"ridge\":41,\"a\":19,\"owners\":[6,13,37,41,42,54,59]},{\"tag\":\"three\",\"ridge\":41,\"vertices\":[19,41,54]},{\"tag\":\"mate\",\"ridge\":42,\"a\":77,\"owners\":[6,24,41,42,74]},{\"tag\":\"mate\",\"ridge\":42,\"a\":80,\"owners\":[6,24,37,42,71,74]},{\"tag\":\"mate\",\"ridge\":259,\"a\":49,\"owners\":[7,31,41]},{\"tag\":\"mate\",\"ridge\":265,\"a\":31,\"owners\":[18,20,68]},{\"tag\":\"mate\",\"ridge\":266,\"a\":79,\"owners\":[7,31,41]},{\"tag\":\"mate\",\"ridge\":28,\"a\":72,\"owners\":[12,54,56,57,82]},{\"tag\":\"mate\",\"ridge\":44,\"a\":13,\"owners\":[24,71,74,82]},{\"tag\":\"mate\",\"ridge\":44,\"a\":58,\"owners\":[24,71,74]},{\"tag\":\"mate\",\"ridge\":44,\"a\":59,\"owners\":[24,71,82]},{\"tag\":\"mate\",\"ridge\":152,\"a\":17,\"owners\":[29,77,78,79,82,83]},{\"tag\":\"mate\",\"ridge\":152,\"a\":39,\"owners\":[29,82,83]},{\"tag\":\"mate\",\"ridge\":152,\"a\":67,\"owners\":[29,77,79,82]},{\"tag\":\"mate\",\"ridge\":161,\"a\":19,\"owners\":[45,50,52,61,64,70]},{\"tag\":\"mate\",\"ridge\":161,\"a\":40,\"owners\":[61,64,70]},{\"tag\":\"mate\",\"ridge\":161,\"a\":58,\"owners\":[45,50,52,70]},{\"tag\":\"mate\",\"ridge\":161,\"a\":66,\"owners\":[50,52,64,70]},{\"tag\":\"mate\",\"ridge\":161,\"a\":68,\"owners\":[45,50,61,64,70]},{\"tag\":\"mate\",\"ridge\":168,\"a\":19,\"owners\":[77,80,82]},{\"tag\":\"mate\",\"ridge\":385,\"a\":49,\"owners\":[20,68]},{\"tag\":\"mate\",\"ridge\":392,\"a\":29,\"owners\":[20,44,68,80]},{\"tag\":\"mate\",\"ridge\":392,\"a\":79,\"owners\":[20,68]},{\"tag\":\"mate\",\"ridge\":193,\"a\":21,\"owners\":[43,50,53,60,64,70]},{\"tag\":\"mate\",\"ridge\":193,\"a\":46,\"owners\":[60,64,70]},{\"tag\":\"mate\",\"ridge\":193,\"a\":67,\"owners\":[50,53,64,70]},{\"tag\":\"mate\",\"ridge\":193,\"a\":69,\"owners\":[43,50,60,64,70]},{\"tag\":\"mate\",\"ridge\":208,\"a\":21,\"owners\":[78,81,83]},{\"tag\":\"mate\",\"ridge\":400,\"a\":79,\"owners\":[22,69]},{\"tag\":\"mate\",\"ridge\":202,\"a\":78,\"owners\":[43]},{\"tag\":\"mate\",\"ridge\":178,\"a\":77,\"owners\":[45]},{\"tag\":\"mate\",\"ridge\":226,\"a\":50,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":418,\"a\":52,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":418,\"a\":80,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":204,\"a\":60,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":204,\"a\":83,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":180,\"a\":61,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":180,\"a\":82,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":228,\"a\":64,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":736,\"a\":70,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[39,40,44,46,49,79],\"full_literals\":[-55,17,18,22,24,25,50]},{\"tag\":\"group_take\",\"kind\":2,\"index\":3,\"member\":39,\"full_literals\":[-17,55]},{\"tag\":\"group_take\",\"kind\":2,\"index\":3,\"member\":44,\"full_literals\":[-22,55]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[41,58,68],\"full_literals\":[-56,19,33,41]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[37,54,66,71],\"full_literals\":[-57,15,29,39,44]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[34,38,72,73],\"full_literals\":[-58,14,16,45,46]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[55,56,57,67],\"full_literals\":[-59,30,31,32,40]},{\"tag\":\"group_take\",\"kind\":2,\"index\":8,\"member\":56,\"full_literals\":[-31,59]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[31],\"full_literals\":[-60,13]},{\"tag\":\"group_take\",\"kind\":2,\"index\":9,\"member\":31,\"full_literals\":[-13,60]},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-61,55,56],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-62,55,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-63,false,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-64,false,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-65,false,63],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-66,false,64],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-67,false,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-68,59,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-69,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-69,false,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-59,-60,69],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-70,58,69],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-71,58,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-70,false,68],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-71,false,69],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-72,67,71],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-73,67,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-72,false,70],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-73,false,71],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-74,65,73],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-74,66,72],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[50,64,70],\"full_literals\":[-75,26,38,43]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[60,61],\"full_literals\":[-76,35,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":60,\"full_literals\":[-35,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":61,\"full_literals\":[-36,76]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[82,83],\"full_literals\":[-77,53,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":82,\"full_literals\":[-53,77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":83,\"full_literals\":[-54,77]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[43,45,52,53],\"full_literals\":[-78,21,23,27,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":43,\"full_literals\":[-21,78]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":45,\"full_literals\":[-23,78]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":52,\"full_literals\":[-27,78]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":53,\"full_literals\":[-28,78]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":77,\"full_literals\":[-48,79]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":78,\"full_literals\":[-49,79]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":80,\"full_literals\":[-51,79]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":81,\"full_literals\":[-52,79]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-80,75,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-76,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-79,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-82,78,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-78,false,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-78,-79,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-83,77,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-82,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-77,-81,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-84,80,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-80,-83,85],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":25,\"owners\":[6,13,19,24,37,40,41,42,54,58,59,66,68,71,74,77,80,82]},{\"tag\":\"edge\",\"edge\":27,\"owners\":[17,19,20,29,39,40,43,44,56,58,60,66,67,68,77,78,79,80,82,83]},{\"tag\":\"edge\",\"edge\":36,\"owners\":[19,40,45,50,52,58,61,64,66,68,70,77,80,82]},{\"tag\":\"edge\",\"edge\":39,\"owners\":[21,43,46,50,53,60,62,64,67,69,70,78,81,83]}]}"
  "174 -75 0 100 107 108 141 0\n175 -80 76 0 174 157 0\n176 7 18 23 27 33 36 39 41 48 51 53 0 100 107 108 172 0\n177 9 21 24 28 35 37 40 42 49 52 54 0 100 107 108 173 0\n178 -73 0 135 137 125 131 133 127 128 117 2 4 5 24 29 51 56 113 114 40 45 54 115 0\n179 65 0 178 140 138 0\n180 63 0 179 123 0\n181 61 0 180 121 0\n182 -71 36 0 107 108 106 84 131 133 127 128 117 1 2 4 5 7 9 24 29 51 56 114 54 55 66 65 115 77 72 71 78 79 40 46 69 170 0\n183 -69 -57 0 127 128 117 4 24 29 51 113 37 40 45 48 74 115 68 0\n184 -60 -58 -57 53 0 183 117 129 2 4 5 24 29 51 56 116 113 114 76 37 48 67 74 0\n185 -39 41 76 0 108 107 100 181 144 84 143 93 37 38 39 41 86 89 91 18 109 112 119 0\n186 -27 -55 50 25 76 0 107 108 144 84 143 93 17 20 109 0\n187 22 -55 8 41 76 0 107 108 89 91 186 102 144 106 84 143 104 93 109 90 81 0\n188 -55 8 41 -83 0 169 91 89 167 158 143 104 144 106 145 163 160 186 187 12 15 22 148 0\n189 33 -56 22 17 8 41 44 -57 76 0 107 108 91 185 144 106 84 143 104 112 8 10 62 113 98 90 28 57 70 80 82 171 0\n190 -33 39 44 -57 0 31 32 113 0\n191 8 41 44 -57 -83 0 169 181 167 158 185 190 188 110 111 119 189 0\n192 -19 39 41 44 -57 36 0 107 108 190 106 84 8 18 62 113 26 57 70 176 0\n193 -29 -55 22 -59 76 0 107 108 144 84 143 93 25 27 28 30 115 42 43 50 97 109 0\n194 41 44 -72 -83 0 107 108 169 181 136 132 167 158 144 106 182 134 125 183 130 184 126 118 84 143 93 185 190 191 11 192 112 119 193 113 3 6 73 75 109 0\n195 44 -72 -83 0 169 108 107 100 167 158 144 182 134 125 194 48 87 13 26 113 0\n196 33 -56 -44 36 0 108 107 100 52 87 58 53 106 84 112 18 62 83 176 0\n197 -33 23 35 0 108 107 100 104 93 35 85 19 23 59 63 95 94 92 177 0\n198 -27 -55 76 0 21 61 186 0\n199 -44 76 0 181 108 107 100 144 106 84 143 52 53 58 87 197 196 119 198 102 83 176 0\n200 23 -83 0 140 169 108 107 100 167 158 199 195 139 124 122 120 198 102 86 144 106 84 143 99 87 197 83 176 0\n201 -83 0 169 108 107 140 167 158 143 144 93 84 199 195 139 124 122 120 200 14 15 16 60 109 0\n202 -82 0 201 164 0\n203 80 0 201 168 166 0\n204 76 0 203 175 0\n205 36 27 0 100 108 107 204 201 102 86 84 106 142 33 47 103 147 165 159 161 153 150 88 176 0\n206 -36 0 108 107 201 34 36 44 49 64 105 93 146 165 159 161 154 156 149 152 96 177 0\n207 27 0 206 205 0\n208 51 0 207 101 0\n209 78 0 207 151 0\n210 79 0 208 155 0\n211 0 209 210 202 162 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record040.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record040.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record040.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record040.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record040 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record040.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record040.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record040.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record040.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record040 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record040_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record040_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record040_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record040_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record040_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record040_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record040_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record040 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record040_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record040_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record040_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00110.record040
