module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow28Part00002Frames
public import GraphInputsRow28Part00002Leaves
public import GraphInputsRow28Part00002Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow28Part00002.record011
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2f03e0f4730ec370f2aa8ea2ea96358b66394e338ae27ab19c4f15a4e91e555354753346d17723a8f13a4cb31cf0b52e2b4acab1ac3bc1d4785d1725c570dc8f13c2f07eb03c0e83514c332a2a4a322c8aa2590e23a311c5491a5451550d1370388e130cd0b0ad0705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "2492492492492492492492492492492492492492449249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record011 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record011 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record011.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record011.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record011.data.quota

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record011 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record011_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow28Part00002.record011" "{\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow28Part00002.record011" 5

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow28Part00002.record011" "{\"ridges\":[[8,769],[41,769],[48,769],[52,769],[54,769]],\"owners\":[[8,769,[],[41,48,52,54]],[41,769,[],[8,48,52,54]],[48,769,[],[8,41,52,54]],[52,769,[],[8,41,48,54]],[54,769,[],[8,41,48,52]]],\"edges\":[[44,[8,41,48,52,54]]],\"groupings\":[]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow28Part00002.record011" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow28Part00002.record011\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1],[-2],[-3],[-4],[-5],[1,2,3,4,5]],\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54}],\"rules\":[{\"tag\":\"mate\",\"ridge\":769,\"a\":8,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":769,\"a\":41,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":769,\"a\":48,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":769,\"a\":52,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":769,\"a\":54,\"owners\":[]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[8,41,48,52,54]}]}"
  "7 0 1 2 3 4 5 6 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record011.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record011.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record011.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record011.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record011 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record011.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record011.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record011.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record011.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record011 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record011_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record011 Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record011_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record011_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow28Part00002.record011
