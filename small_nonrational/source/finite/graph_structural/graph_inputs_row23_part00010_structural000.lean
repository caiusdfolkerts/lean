module
prelude
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow23Part00010Frames
public import GraphInputsRow23Part00010Leaves
public import GraphInputsRow23Part00010Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00010.record060
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2caaaa6a8e9c6659564d83eb26a99a63971595555350f783d0ec370ea398d9354e334cd8b52ccb2ac6b86d1b26c5ba1e4731e2749ca719c9715c8f13c2f07e8a92a2a0e986519160da89926290e585515150d68360e4350e2344c3382c8b12c2b06d0721c4709c17"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "92492492492492492492492492492492492491249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record060 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record060 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record060.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 41), (facetIndex 66), (facetIndex 67), (facetIndex 68), (facetIndex 69)]))
 (.leaf ([(facetIndex 49), (facetIndex 70), (facetIndex 71), (facetIndex 72), (facetIndex 73)])))
 (.branch 3
 (.leaf ([(facetIndex 75), (facetIndex 76), (facetIndex 77), (facetIndex 78)]))
 (.leaf ([(facetIndex 79), (facetIndex 80), (facetIndex 81), (facetIndex 82)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 33), (facetIndex 34), (facetIndex 55), (facetIndex 56), (facetIndex 65), (facetIndex 74)]))
 (.leaf ([(facetIndex 37), (facetIndex 38), (facetIndex 39), (facetIndex 40), (facetIndex 42), (facetIndex 43), (facetIndex 44), (facetIndex 45)])))
 (.branch 7
 (.leaf ([(facetIndex 48), (facetIndex 53), (facetIndex 54), (facetIndex 57), (facetIndex 58), (facetIndex 61)]))
 (.branch 8
 (.leaf ([(facetIndex 59), (facetIndex 60), (facetIndex 62), (facetIndex 63), (facetIndex 64)]))
 (.leaf ([(facetIndex 35), (facetIndex 36), (facetIndex 46), (facetIndex 47), (facetIndex 50), (facetIndex 51), (facetIndex 52)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "33332222411110000477767766446688816885555055558844z21;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record060 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record060_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00010.record060" "{\"atoms\":[]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00010.record060" 0

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00010.record060" "{\"ridges\":[],\"owners\":[],\"edges\":[],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00010.record060" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00010.record060\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[]],\"atoms\":[],\"rules\":[{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":10,\"grouped\":true}]}"
  "p cnf 0 1\n 0\n"
  "2 0 1 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record060.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record060.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record060.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record060.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record060 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record060.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record060.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record060.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record060.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record060 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record060_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record060_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record060_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record060_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record060_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record060_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record060_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record060 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record060_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record060_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record060_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00010.record060
