module

public import CompletedSeven.MixedCoveragePart04
public import DecodedCellBounds
public import FinitePolygonTemplates
public import KindedRootedFacetCoverage
public import OutsidePlacementSemantics
public import RootedSevenMixed030CanonicalS5T0Finite
public import RootedSevenMixed030CanonicalS5T0Placement
public import RootedSevenMixed030CanonicalS5T1Finite
public import RootedSevenMixed030CanonicalS5T1Placement
public import RootedSevenMixed030CanonicalT4Finite
public import RootedSevenMixed030CanonicalT4Placement
public import RootedSevenMixed030Outside
public import RootedSevenMixed031CanonicalS5T0Finite
public import RootedSevenMixed031CanonicalS5T0Placement
public import RootedSevenMixed031CanonicalS5T1Finite
public import RootedSevenMixed031CanonicalS5T1Placement
public import RootedSevenMixed031CanonicalT4Finite
public import RootedSevenMixed031CanonicalT4Placement
public import RootedSevenMixed031Outside
public import RootedSevenMixed032CanonicalS5T0Finite
public import RootedSevenMixed032CanonicalS5T0Placement
public import RootedSevenMixed032CanonicalS5T1Finite
public import RootedSevenMixed032CanonicalS5T1Placement
public import RootedSevenMixed032CanonicalT4Finite
public import RootedSevenMixed032CanonicalT4Placement
public import RootedSevenMixed032Outside
public import RootedSevenMixed033CanonicalS5T0Finite
public import RootedSevenMixed033CanonicalS5T0Placement
public import RootedSevenMixed033CanonicalS5T1Finite
public import RootedSevenMixed033CanonicalS5T1Placement
public import RootedSevenMixed033CanonicalT4Finite
public import RootedSevenMixed033CanonicalT4Placement
public import RootedSevenMixed033Outside
public import SevenFamilyActualEncoding
public import SymmetricRootedFacetCoverage

/-! Geometric placement coverage; the following proof bodies are unchanged. -/

/- Source module: RootedSevenMixed029Coverage -/
@[expose] public section

/-!
# Complete compatible-template coverage for RootedSevenMixed029

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSevenMixed029

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSevenMixed029

abbrev root : Fin FacetUniverses.RootedSevenMixed029.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 7 ↪ Fin 10 where
  toFun := ![0, 1, 2, 3, 4, 5, 6]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N7.templates 33)) =
      decodeCell (FacetUniverses.RootedSevenMixed029.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSevenMixed029.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [1]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed029.cells root 33 (fun a => a.size ≤ 5 ∨ a = .six 6) quota where
  rootEmbedding := rootEmbedding
  rootCell := root_exact
  rootKind := root_kind
  complete := by
    intro a hallowed hpos f h
    cases a with
    | tetrahedron =>
      change 0 < quota 1 at hpos
      rw [hzero 1 (by decide +kernel)] at hpos
      omega
    | bipyramid => exact S5T0.covers_exact f h
    | squarePyramid => exact S5T1.covers_exact f h
    | six i =>
      have hi : i = 6 := by
        rcases hallowed with hs | heq
        · change 6 ≤ 5 at hs
          omega
        · exact Kind.six.inj heq
      subst i
      exact T6.covers_exact f h

/-- The exact numerical family discharges every omitted-kind condition. -/
def rowCoverage :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed029.cells root 33
      (fun a => a.size ≤ 5 ∨ a = .six 6) (SevenFamilyActualEncoding.rowQuota 0 5 3 1) :=
  coverage _ (by
    intro k hk
    have hk' : k = 1 := by simpa [omittedTags] using hk
    rcases hk' with rfl <;> rfl)

end Papers.RationalityTen.RootedCoverage.RootedSevenMixed029

end
end


/- Source module: RootedSevenMixed030CanonicalS5T0 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed030.S5T0
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N5.templates 0)
theorem template_exact : decodeTemplate 5 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := rfl
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 5 (raw i) = true := by
  simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 5 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices :=
  DecodedCellBounds.decoded_edges_subset root (by decide +kernel)
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices :=
  DecodedCellBounds.decoded_ridges_subset root (by decide +kernel)
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed030.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed030.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed030.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed030.Outside.forward g) (FacetUniverses.RootedSevenMixed030.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed030.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed030.cells i) (FacetUniverses.RootedSevenMixed030.cells (FacetUniverses.RootedSevenMixed030.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed030.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed030.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed030.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed030.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed030.cells
    (FacetUniverses.RootedSevenMixed030.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed030.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed030.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed030.Outside.forward g) (FacetUniverses.RootedSevenMixed030.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed030.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed030.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed030.cells generators
    FacetUniverses.RootedSevenMixed030.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed030.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed030.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed030.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed030.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed030.S5T0

end
end


/- Source module: RootedSevenMixed030CanonicalS5T1 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed030.S5T1
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N5.templates 1)
theorem template_exact : decodeTemplate 5 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := rfl
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 5 (raw i) = true := by
  simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 5 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices :=
  DecodedCellBounds.decoded_edges_subset root (by decide +kernel)
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices :=
  DecodedCellBounds.decoded_ridges_subset root (by decide +kernel)
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed030.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed030.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed030.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed030.Outside.forward g) (FacetUniverses.RootedSevenMixed030.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed030.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed030.cells i) (FacetUniverses.RootedSevenMixed030.cells (FacetUniverses.RootedSevenMixed030.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed030.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed030.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed030.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed030.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed030.cells
    (FacetUniverses.RootedSevenMixed030.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed030.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed030.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed030.Outside.forward g) (FacetUniverses.RootedSevenMixed030.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed030.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed030.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed030.cells generators
    FacetUniverses.RootedSevenMixed030.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed030.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed030.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed030.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed030.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed030.S5T1

end
end


/- Source module: RootedSevenMixed030CanonicalT4 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed030.T4
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 4)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := rfl
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true := by
  simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices :=
  DecodedCellBounds.decoded_edges_subset root (by decide +kernel)
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices :=
  DecodedCellBounds.decoded_ridges_subset root (by decide +kernel)
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed030.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed030.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed030.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed030.Outside.forward g) (FacetUniverses.RootedSevenMixed030.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed030.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed030.cells i) (FacetUniverses.RootedSevenMixed030.cells (FacetUniverses.RootedSevenMixed030.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed030.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed030.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed030.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed030.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed030.cells
    (FacetUniverses.RootedSevenMixed030.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed030.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed030.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed030.Outside.forward g) (FacetUniverses.RootedSevenMixed030.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed030.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed030.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed030.cells generators
    FacetUniverses.RootedSevenMixed030.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed030.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed030.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed030.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed030.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed030.T4

end
end


/- Source module: RootedSevenMixed030Coverage -/
@[expose] public section

/-!
# Complete compatible-template coverage for RootedSevenMixed030

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSevenMixed030

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSevenMixed030

abbrev root : Fin FacetUniverses.RootedSevenMixed030.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 7 ↪ Fin 10 where
  toFun := ![0, 1, 2, 3, 4, 5, 6]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N7.templates 10)) =
      decodeCell (FacetUniverses.RootedSevenMixed030.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSevenMixed030.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [1]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed030.cells root 10 (fun a => a.size ≤ 5 ∨ a = .six 4) quota where
  rootEmbedding := rootEmbedding
  rootCell := root_exact
  rootKind := root_kind
  complete := by
    intro a hallowed hpos f h
    cases a with
    | tetrahedron =>
      change 0 < quota 1 at hpos
      rw [hzero 1 (by decide +kernel)] at hpos
      omega
    | bipyramid => exact S5T0.covers_exact f h
    | squarePyramid => exact S5T1.covers_exact f h
    | six i =>
      have hi : i = 4 := by
        rcases hallowed with hs | heq
        · change 6 ≤ 5 at hs
          omega
        · exact Kind.six.inj heq
      subst i
      exact T4.covers_exact f h

/-- The exact numerical family discharges every omitted-kind condition. -/
def rowCoverage :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed030.cells root 10
      (fun a => a.size ≤ 5 ∨ a = .six 4) (SevenFamilyActualEncoding.rowQuota 0 4 4 1) :=
  coverage _ (by
    intro k hk
    have hk' : k = 1 := by simpa [omittedTags] using hk
    rcases hk' with rfl <;> rfl)

end Papers.RationalityTen.RootedCoverage.RootedSevenMixed030

end
end


/- Source module: RootedSevenMixed031CanonicalS5T0 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed031.S5T0
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N5.templates 0)
theorem template_exact : decodeTemplate 5 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := rfl
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 5 (raw i) = true := by
  simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 5 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices :=
  DecodedCellBounds.decoded_edges_subset root (by decide +kernel)
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices :=
  DecodedCellBounds.decoded_ridges_subset root (by decide +kernel)
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed031.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed031.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed031.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed031.Outside.forward g) (FacetUniverses.RootedSevenMixed031.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed031.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed031.cells i) (FacetUniverses.RootedSevenMixed031.cells (FacetUniverses.RootedSevenMixed031.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed031.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed031.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed031.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed031.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed031.cells
    (FacetUniverses.RootedSevenMixed031.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed031.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed031.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed031.Outside.forward g) (FacetUniverses.RootedSevenMixed031.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed031.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed031.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed031.cells generators
    FacetUniverses.RootedSevenMixed031.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed031.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed031.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed031.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed031.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed031.S5T0

end
end


/- Source module: RootedSevenMixed031CanonicalS5T1 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed031.S5T1
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N5.templates 1)
theorem template_exact : decodeTemplate 5 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := rfl
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 5 (raw i) = true := by
  simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 5 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices :=
  DecodedCellBounds.decoded_edges_subset root (by decide +kernel)
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices :=
  DecodedCellBounds.decoded_ridges_subset root (by decide +kernel)
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed031.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed031.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed031.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed031.Outside.forward g) (FacetUniverses.RootedSevenMixed031.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed031.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed031.cells i) (FacetUniverses.RootedSevenMixed031.cells (FacetUniverses.RootedSevenMixed031.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed031.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed031.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed031.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed031.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed031.cells
    (FacetUniverses.RootedSevenMixed031.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed031.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed031.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed031.Outside.forward g) (FacetUniverses.RootedSevenMixed031.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed031.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed031.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed031.cells generators
    FacetUniverses.RootedSevenMixed031.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed031.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed031.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed031.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed031.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed031.S5T1

end
end


/- Source module: RootedSevenMixed031CanonicalT4 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed031.T4
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 4)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := rfl
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true := by
  simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices :=
  DecodedCellBounds.decoded_edges_subset root (by decide +kernel)
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices :=
  DecodedCellBounds.decoded_ridges_subset root (by decide +kernel)
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed031.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed031.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed031.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed031.Outside.forward g) (FacetUniverses.RootedSevenMixed031.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed031.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed031.cells i) (FacetUniverses.RootedSevenMixed031.cells (FacetUniverses.RootedSevenMixed031.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed031.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed031.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed031.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed031.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed031.cells
    (FacetUniverses.RootedSevenMixed031.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed031.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed031.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed031.Outside.forward g) (FacetUniverses.RootedSevenMixed031.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed031.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed031.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed031.cells generators
    FacetUniverses.RootedSevenMixed031.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed031.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed031.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed031.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed031.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed031.T4

end
end


/- Source module: RootedSevenMixed031Coverage -/
@[expose] public section

/-!
# Complete compatible-template coverage for RootedSevenMixed031

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSevenMixed031

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSevenMixed031

abbrev root : Fin FacetUniverses.RootedSevenMixed031.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 7 ↪ Fin 10 where
  toFun := ![0, 1, 2, 3, 4, 5, 6]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N7.templates 17)) =
      decodeCell (FacetUniverses.RootedSevenMixed031.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSevenMixed031.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [1]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed031.cells root 17 (fun a => a.size ≤ 5 ∨ a = .six 4) quota where
  rootEmbedding := rootEmbedding
  rootCell := root_exact
  rootKind := root_kind
  complete := by
    intro a hallowed hpos f h
    cases a with
    | tetrahedron =>
      change 0 < quota 1 at hpos
      rw [hzero 1 (by decide +kernel)] at hpos
      omega
    | bipyramid => exact S5T0.covers_exact f h
    | squarePyramid => exact S5T1.covers_exact f h
    | six i =>
      have hi : i = 4 := by
        rcases hallowed with hs | heq
        · change 6 ≤ 5 at hs
          omega
        · exact Kind.six.inj heq
      subst i
      exact T4.covers_exact f h

/-- The exact numerical family discharges every omitted-kind condition. -/
def rowCoverage :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed031.cells root 17
      (fun a => a.size ≤ 5 ∨ a = .six 4) (SevenFamilyActualEncoding.rowQuota 0 4 4 1) :=
  coverage _ (by
    intro k hk
    have hk' : k = 1 := by simpa [omittedTags] using hk
    rcases hk' with rfl <;> rfl)

end Papers.RationalityTen.RootedCoverage.RootedSevenMixed031

end
end


/- Source module: RootedSevenMixed032CanonicalS5T0 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed032.S5T0
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N5.templates 0)
theorem template_exact : decodeTemplate 5 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := rfl
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 5 (raw i) = true := by
  simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 5 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices :=
  DecodedCellBounds.decoded_edges_subset root (by decide +kernel)
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices :=
  DecodedCellBounds.decoded_ridges_subset root (by decide +kernel)
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed032.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed032.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed032.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed032.Outside.forward g) (FacetUniverses.RootedSevenMixed032.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed032.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed032.cells i) (FacetUniverses.RootedSevenMixed032.cells (FacetUniverses.RootedSevenMixed032.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed032.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed032.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed032.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed032.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed032.cells
    (FacetUniverses.RootedSevenMixed032.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed032.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed032.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed032.Outside.forward g) (FacetUniverses.RootedSevenMixed032.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed032.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed032.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed032.cells generators
    FacetUniverses.RootedSevenMixed032.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed032.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed032.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed032.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed032.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed032.S5T0

end
end


/- Source module: RootedSevenMixed032CanonicalS5T1 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed032.S5T1
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N5.templates 1)
theorem template_exact : decodeTemplate 5 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := rfl
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 5 (raw i) = true := by
  simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 5 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices :=
  DecodedCellBounds.decoded_edges_subset root (by decide +kernel)
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices :=
  DecodedCellBounds.decoded_ridges_subset root (by decide +kernel)
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed032.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed032.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed032.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed032.Outside.forward g) (FacetUniverses.RootedSevenMixed032.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed032.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed032.cells i) (FacetUniverses.RootedSevenMixed032.cells (FacetUniverses.RootedSevenMixed032.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed032.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed032.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed032.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed032.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed032.cells
    (FacetUniverses.RootedSevenMixed032.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed032.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed032.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed032.Outside.forward g) (FacetUniverses.RootedSevenMixed032.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed032.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed032.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed032.cells generators
    FacetUniverses.RootedSevenMixed032.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed032.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed032.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed032.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed032.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed032.S5T1

end
end


/- Source module: RootedSevenMixed032CanonicalT4 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed032.T4
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 4)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := rfl
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true := by
  simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices :=
  DecodedCellBounds.decoded_edges_subset root (by decide +kernel)
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices :=
  DecodedCellBounds.decoded_ridges_subset root (by decide +kernel)
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed032.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed032.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed032.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed032.Outside.forward g) (FacetUniverses.RootedSevenMixed032.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed032.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed032.cells i) (FacetUniverses.RootedSevenMixed032.cells (FacetUniverses.RootedSevenMixed032.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed032.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed032.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed032.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed032.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed032.cells
    (FacetUniverses.RootedSevenMixed032.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed032.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed032.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed032.Outside.forward g) (FacetUniverses.RootedSevenMixed032.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed032.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed032.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed032.cells generators
    FacetUniverses.RootedSevenMixed032.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed032.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed032.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed032.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed032.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed032.T4

end
end


/- Source module: RootedSevenMixed032Coverage -/
@[expose] public section

/-!
# Complete compatible-template coverage for RootedSevenMixed032

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSevenMixed032

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSevenMixed032

abbrev root : Fin FacetUniverses.RootedSevenMixed032.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 7 ↪ Fin 10 where
  toFun := ![0, 1, 2, 3, 4, 5, 6]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N7.templates 26)) =
      decodeCell (FacetUniverses.RootedSevenMixed032.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSevenMixed032.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [1]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed032.cells root 26 (fun a => a.size ≤ 5 ∨ a = .six 4) quota where
  rootEmbedding := rootEmbedding
  rootCell := root_exact
  rootKind := root_kind
  complete := by
    intro a hallowed hpos f h
    cases a with
    | tetrahedron =>
      change 0 < quota 1 at hpos
      rw [hzero 1 (by decide +kernel)] at hpos
      omega
    | bipyramid => exact S5T0.covers_exact f h
    | squarePyramid => exact S5T1.covers_exact f h
    | six i =>
      have hi : i = 4 := by
        rcases hallowed with hs | heq
        · change 6 ≤ 5 at hs
          omega
        · exact Kind.six.inj heq
      subst i
      exact T4.covers_exact f h

/-- The exact numerical family discharges every omitted-kind condition. -/
def rowCoverage :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed032.cells root 26
      (fun a => a.size ≤ 5 ∨ a = .six 4) (SevenFamilyActualEncoding.rowQuota 0 5 3 1) :=
  coverage _ (by
    intro k hk
    have hk' : k = 1 := by simpa [omittedTags] using hk
    rcases hk' with rfl <;> rfl)

end Papers.RationalityTen.RootedCoverage.RootedSevenMixed032

end
end


/- Source module: RootedSevenMixed033CanonicalS5T0 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed033.S5T0
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N5.templates 0)
theorem template_exact : decodeTemplate 5 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := rfl
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 5 (raw i) = true := by
  simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 5 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices :=
  DecodedCellBounds.decoded_edges_subset root (by decide +kernel)
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices :=
  DecodedCellBounds.decoded_ridges_subset root (by decide +kernel)
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed033.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed033.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed033.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed033.Outside.forward g) (FacetUniverses.RootedSevenMixed033.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed033.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed033.cells i) (FacetUniverses.RootedSevenMixed033.cells (FacetUniverses.RootedSevenMixed033.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed033.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed033.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed033.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed033.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed033.cells
    (FacetUniverses.RootedSevenMixed033.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed033.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed033.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed033.Outside.forward g) (FacetUniverses.RootedSevenMixed033.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed033.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed033.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed033.cells generators
    FacetUniverses.RootedSevenMixed033.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed033.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed033.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed033.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed033.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed033.S5T0

end
end


/- Source module: RootedSevenMixed033CanonicalS5T1 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed033.S5T1
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N5.templates 1)
theorem template_exact : decodeTemplate 5 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := rfl
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 5 (raw i) = true := by
  simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 5 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices :=
  DecodedCellBounds.decoded_edges_subset root (by decide +kernel)
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices :=
  DecodedCellBounds.decoded_ridges_subset root (by decide +kernel)
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed033.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed033.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed033.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed033.Outside.forward g) (FacetUniverses.RootedSevenMixed033.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed033.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed033.cells i) (FacetUniverses.RootedSevenMixed033.cells (FacetUniverses.RootedSevenMixed033.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed033.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed033.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed033.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed033.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed033.cells
    (FacetUniverses.RootedSevenMixed033.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed033.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed033.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed033.Outside.forward g) (FacetUniverses.RootedSevenMixed033.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed033.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed033.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed033.cells generators
    FacetUniverses.RootedSevenMixed033.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed033.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed033.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed033.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed033.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed033.S5T1

end
end


/- Source module: RootedSevenMixed033CanonicalT4 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed033.T4
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 4)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := rfl
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true := by
  simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices :=
  DecodedCellBounds.decoded_edges_subset root (by decide +kernel)
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices :=
  DecodedCellBounds.decoded_ridges_subset root (by decide +kernel)
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed033.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed033.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed033.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed033.Outside.forward g) (FacetUniverses.RootedSevenMixed033.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed033.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed033.cells i) (FacetUniverses.RootedSevenMixed033.cells (FacetUniverses.RootedSevenMixed033.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed033.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed033.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed033.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed033.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed033.cells
    (FacetUniverses.RootedSevenMixed033.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed033.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed033.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed033.Outside.forward g) (FacetUniverses.RootedSevenMixed033.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed033.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed033.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed033.cells generators
    FacetUniverses.RootedSevenMixed033.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed033.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed033.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed033.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed033.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed033.T4

end
end


/- Source module: RootedSevenMixed033Coverage -/
@[expose] public section

/-!
# Complete compatible-template coverage for RootedSevenMixed033

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSevenMixed033

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSevenMixed033

abbrev root : Fin FacetUniverses.RootedSevenMixed033.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 7 ↪ Fin 10 where
  toFun := ![0, 1, 2, 3, 4, 5, 6]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N7.templates 30)) =
      decodeCell (FacetUniverses.RootedSevenMixed033.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSevenMixed033.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [1]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed033.cells root 30 (fun a => a.size ≤ 5 ∨ a = .six 4) quota where
  rootEmbedding := rootEmbedding
  rootCell := root_exact
  rootKind := root_kind
  complete := by
    intro a hallowed hpos f h
    cases a with
    | tetrahedron =>
      change 0 < quota 1 at hpos
      rw [hzero 1 (by decide +kernel)] at hpos
      omega
    | bipyramid => exact S5T0.covers_exact f h
    | squarePyramid => exact S5T1.covers_exact f h
    | six i =>
      have hi : i = 4 := by
        rcases hallowed with hs | heq
        · change 6 ≤ 5 at hs
          omega
        · exact Kind.six.inj heq
      subst i
      exact T4.covers_exact f h

/-- The exact numerical family discharges every omitted-kind condition. -/
def rowCoverage :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed033.cells root 30
      (fun a => a.size ≤ 5 ∨ a = .six 4) (SevenFamilyActualEncoding.rowQuota 0 5 3 1) :=
  coverage _ (by
    intro k hk
    have hk' : k = 1 := by simpa [omittedTags] using hk
    rcases hk' with rfl <;> rfl)

end Papers.RationalityTen.RootedCoverage.RootedSevenMixed033

end
end

