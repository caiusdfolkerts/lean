module

public import DecodedCellBounds
public import FinitePolygonTemplates
public import KindedRootedFacetCoverage
public import OutsidePlacementSemantics
public import RootedSevenMixed006CanonicalS5T0Finite
public import RootedSevenMixed006CanonicalS5T0Placement
public import RootedSevenMixed006CanonicalS5T1Finite
public import RootedSevenMixed006CanonicalS5T1Placement
public import RootedSevenMixed006CanonicalT6Finite
public import RootedSevenMixed006CanonicalT6Placement
public import RootedSevenMixed006Outside
public import RootedSevenMixed007CanonicalS5T0Finite
public import RootedSevenMixed007CanonicalS5T0Placement
public import RootedSevenMixed007CanonicalS5T1Finite
public import RootedSevenMixed007CanonicalS5T1Placement
public import RootedSevenMixed007CanonicalT6Finite
public import RootedSevenMixed007CanonicalT6Placement
public import RootedSevenMixed007Outside
public import RootedSevenMixed008CanonicalS5T0Finite
public import RootedSevenMixed008CanonicalS5T0Placement
public import RootedSevenMixed008CanonicalS5T1Finite
public import RootedSevenMixed008CanonicalS5T1Placement
public import RootedSevenMixed008CanonicalT0Finite
public import RootedSevenMixed008CanonicalT0Placement
public import RootedSevenMixed008Outside
public import RootedSevenMixed009CanonicalS5T0Finite
public import RootedSevenMixed009CanonicalS5T0Placement
public import RootedSevenMixed009CanonicalS5T1Finite
public import RootedSevenMixed009CanonicalS5T1Placement
public import RootedSevenMixed009CanonicalT1Finite
public import RootedSevenMixed009CanonicalT1Placement
public import RootedSevenMixed009Outside
public import RootedSevenMixed010CanonicalS5T0Finite
public import RootedSevenMixed010CanonicalS5T0Placement
public import RootedSevenMixed010CanonicalS5T1Finite
public import RootedSevenMixed010CanonicalS5T1Placement
public import RootedSevenMixed010CanonicalT2Finite
public import RootedSevenMixed010CanonicalT2Placement
public import RootedSevenMixed010Outside
public import RootedSevenMixed011CanonicalS5T0Finite
public import RootedSevenMixed011CanonicalS5T0Placement
public import RootedSevenMixed011CanonicalS5T1Finite
public import RootedSevenMixed011CanonicalS5T1Placement
public import RootedSevenMixed011CanonicalT3Finite
public import RootedSevenMixed011CanonicalT3Placement
public import RootedSevenMixed011Outside
public import SevenFamilyActualEncoding
public import SymmetricRootedFacetCoverage

/-! Geometric placement coverage; the following proof bodies are unchanged. -/

/- Source module: RootedSevenMixed006CanonicalS5T0 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed006.S5T0
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed006.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed006.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed006.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed006.Outside.forward g) (FacetUniverses.RootedSevenMixed006.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed006.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed006.cells i) (FacetUniverses.RootedSevenMixed006.cells (FacetUniverses.RootedSevenMixed006.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed006.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed006.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed006.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed006.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed006.cells
    (FacetUniverses.RootedSevenMixed006.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed006.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed006.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed006.Outside.forward g) (FacetUniverses.RootedSevenMixed006.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed006.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed006.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed006.cells generators
    FacetUniverses.RootedSevenMixed006.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed006.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed006.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed006.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed006.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed006.S5T0

end
end


/- Source module: RootedSevenMixed006CanonicalS5T1 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed006.S5T1
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed006.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed006.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed006.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed006.Outside.forward g) (FacetUniverses.RootedSevenMixed006.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed006.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed006.cells i) (FacetUniverses.RootedSevenMixed006.cells (FacetUniverses.RootedSevenMixed006.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed006.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed006.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed006.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed006.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed006.cells
    (FacetUniverses.RootedSevenMixed006.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed006.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed006.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed006.Outside.forward g) (FacetUniverses.RootedSevenMixed006.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed006.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed006.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed006.cells generators
    FacetUniverses.RootedSevenMixed006.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed006.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed006.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed006.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed006.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed006.S5T1

end
end


/- Source module: RootedSevenMixed006CanonicalT6 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed006.T6
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 6)
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed006.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed006.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed006.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed006.Outside.forward g) (FacetUniverses.RootedSevenMixed006.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed006.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed006.cells i) (FacetUniverses.RootedSevenMixed006.cells (FacetUniverses.RootedSevenMixed006.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed006.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed006.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed006.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed006.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed006.cells
    (FacetUniverses.RootedSevenMixed006.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed006.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed006.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed006.Outside.forward g) (FacetUniverses.RootedSevenMixed006.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed006.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed006.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed006.cells generators
    FacetUniverses.RootedSevenMixed006.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed006.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed006.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed006.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed006.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed006.T6

end
end


/- Source module: RootedSevenMixed006Coverage -/
@[expose] public section

/-!
# Complete compatible-template coverage for RootedSevenMixed006

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSevenMixed006

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSevenMixed006

abbrev root : Fin FacetUniverses.RootedSevenMixed006.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 7 ↪ Fin 10 where
  toFun := ![0, 1, 2, 3, 4, 5, 6]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N7.templates 11)) =
      decodeCell (FacetUniverses.RootedSevenMixed006.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSevenMixed006.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [1]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed006.cells root 11 (fun a => a.size ≤ 5 ∨ a = .six 6) quota where
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
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed006.cells root 11
      (fun a => a.size ≤ 5 ∨ a = .six 6) (SevenFamilyActualEncoding.rowQuota 0 3 5 1) :=
  coverage _ (by
    intro k hk
    have hk' : k = 1 := by simpa [omittedTags] using hk
    rcases hk' with rfl <;> rfl)

end Papers.RationalityTen.RootedCoverage.RootedSevenMixed006

end
end


/- Source module: RootedSevenMixed007CanonicalS5T0 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed007.S5T0
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed007.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed007.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed007.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed007.Outside.forward g) (FacetUniverses.RootedSevenMixed007.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed007.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed007.cells i) (FacetUniverses.RootedSevenMixed007.cells (FacetUniverses.RootedSevenMixed007.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed007.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed007.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed007.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed007.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed007.cells
    (FacetUniverses.RootedSevenMixed007.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed007.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed007.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed007.Outside.forward g) (FacetUniverses.RootedSevenMixed007.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed007.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed007.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed007.cells generators
    FacetUniverses.RootedSevenMixed007.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed007.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed007.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed007.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed007.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed007.S5T0

end
end


/- Source module: RootedSevenMixed007CanonicalS5T1 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed007.S5T1
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed007.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed007.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed007.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed007.Outside.forward g) (FacetUniverses.RootedSevenMixed007.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed007.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed007.cells i) (FacetUniverses.RootedSevenMixed007.cells (FacetUniverses.RootedSevenMixed007.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed007.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed007.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed007.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed007.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed007.cells
    (FacetUniverses.RootedSevenMixed007.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed007.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed007.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed007.Outside.forward g) (FacetUniverses.RootedSevenMixed007.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed007.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed007.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed007.cells generators
    FacetUniverses.RootedSevenMixed007.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed007.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed007.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed007.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed007.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed007.S5T1

end
end


/- Source module: RootedSevenMixed007CanonicalT6 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed007.T6
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 6)
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed007.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed007.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed007.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed007.Outside.forward g) (FacetUniverses.RootedSevenMixed007.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed007.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed007.cells i) (FacetUniverses.RootedSevenMixed007.cells (FacetUniverses.RootedSevenMixed007.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed007.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed007.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed007.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed007.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed007.cells
    (FacetUniverses.RootedSevenMixed007.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed007.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed007.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed007.Outside.forward g) (FacetUniverses.RootedSevenMixed007.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed007.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed007.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed007.cells generators
    FacetUniverses.RootedSevenMixed007.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed007.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed007.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed007.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed007.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed007.T6

end
end


/- Source module: RootedSevenMixed007Coverage -/
@[expose] public section

/-!
# Complete compatible-template coverage for RootedSevenMixed007

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSevenMixed007

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSevenMixed007

abbrev root : Fin FacetUniverses.RootedSevenMixed007.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 7 ↪ Fin 10 where
  toFun := ![0, 1, 2, 3, 4, 5, 6]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N7.templates 12)) =
      decodeCell (FacetUniverses.RootedSevenMixed007.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSevenMixed007.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [1]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed007.cells root 12 (fun a => a.size ≤ 5 ∨ a = .six 6) quota where
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
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed007.cells root 12
      (fun a => a.size ≤ 5 ∨ a = .six 6) (SevenFamilyActualEncoding.rowQuota 0 3 5 1) :=
  coverage _ (by
    intro k hk
    have hk' : k = 1 := by simpa [omittedTags] using hk
    rcases hk' with rfl <;> rfl)

end Papers.RationalityTen.RootedCoverage.RootedSevenMixed007

end
end


/- Source module: RootedSevenMixed008CanonicalS5T0 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed008.S5T0
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed008.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed008.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed008.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed008.Outside.forward g) (FacetUniverses.RootedSevenMixed008.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed008.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed008.cells i) (FacetUniverses.RootedSevenMixed008.cells (FacetUniverses.RootedSevenMixed008.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed008.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed008.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed008.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed008.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed008.cells
    (FacetUniverses.RootedSevenMixed008.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed008.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed008.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed008.Outside.forward g) (FacetUniverses.RootedSevenMixed008.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed008.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed008.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed008.cells generators
    FacetUniverses.RootedSevenMixed008.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed008.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed008.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed008.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed008.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed008.S5T0

end
end


/- Source module: RootedSevenMixed008CanonicalS5T1 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed008.S5T1
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed008.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed008.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed008.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed008.Outside.forward g) (FacetUniverses.RootedSevenMixed008.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed008.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed008.cells i) (FacetUniverses.RootedSevenMixed008.cells (FacetUniverses.RootedSevenMixed008.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed008.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed008.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed008.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed008.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed008.cells
    (FacetUniverses.RootedSevenMixed008.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed008.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed008.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed008.Outside.forward g) (FacetUniverses.RootedSevenMixed008.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed008.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed008.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed008.cells generators
    FacetUniverses.RootedSevenMixed008.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed008.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed008.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed008.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed008.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed008.S5T1

end
end


/- Source module: RootedSevenMixed008CanonicalT0 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed008.T0
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 0)
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed008.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed008.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed008.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed008.Outside.forward g) (FacetUniverses.RootedSevenMixed008.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed008.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed008.cells i) (FacetUniverses.RootedSevenMixed008.cells (FacetUniverses.RootedSevenMixed008.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed008.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed008.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed008.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed008.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed008.cells
    (FacetUniverses.RootedSevenMixed008.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed008.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed008.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed008.Outside.forward g) (FacetUniverses.RootedSevenMixed008.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed008.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed008.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed008.cells generators
    FacetUniverses.RootedSevenMixed008.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed008.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed008.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed008.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed008.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed008.T0

end
end


/- Source module: RootedSevenMixed008Coverage -/
@[expose] public section

/-!
# Complete compatible-template coverage for RootedSevenMixed008

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSevenMixed008

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSevenMixed008

abbrev root : Fin FacetUniverses.RootedSevenMixed008.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 7 ↪ Fin 10 where
  toFun := ![0, 1, 2, 3, 4, 5, 6]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N7.templates 13)) =
      decodeCell (FacetUniverses.RootedSevenMixed008.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSevenMixed008.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [1]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed008.cells root 13 (fun a => a.size ≤ 5 ∨ a = .six 0) quota where
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
      have hi : i = 0 := by
        rcases hallowed with hs | heq
        · change 6 ≤ 5 at hs
          omega
        · exact Kind.six.inj heq
      subst i
      exact T0.covers_exact f h

/-- The exact numerical family discharges every omitted-kind condition. -/
def rowCoverage :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed008.cells root 13
      (fun a => a.size ≤ 5 ∨ a = .six 0) (SevenFamilyActualEncoding.rowQuota 0 1 7 1) :=
  coverage _ (by
    intro k hk
    have hk' : k = 1 := by simpa [omittedTags] using hk
    rcases hk' with rfl <;> rfl)

end Papers.RationalityTen.RootedCoverage.RootedSevenMixed008

end
end


/- Source module: RootedSevenMixed009CanonicalS5T0 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed009.S5T0
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed009.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed009.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed009.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed009.Outside.forward g) (FacetUniverses.RootedSevenMixed009.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed009.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed009.cells i) (FacetUniverses.RootedSevenMixed009.cells (FacetUniverses.RootedSevenMixed009.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed009.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed009.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed009.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed009.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed009.cells
    (FacetUniverses.RootedSevenMixed009.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed009.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed009.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed009.Outside.forward g) (FacetUniverses.RootedSevenMixed009.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed009.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed009.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed009.cells generators
    FacetUniverses.RootedSevenMixed009.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed009.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed009.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed009.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed009.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed009.S5T0

end
end


/- Source module: RootedSevenMixed009CanonicalS5T1 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed009.S5T1
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed009.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed009.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed009.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed009.Outside.forward g) (FacetUniverses.RootedSevenMixed009.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed009.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed009.cells i) (FacetUniverses.RootedSevenMixed009.cells (FacetUniverses.RootedSevenMixed009.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed009.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed009.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed009.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed009.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed009.cells
    (FacetUniverses.RootedSevenMixed009.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed009.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed009.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed009.Outside.forward g) (FacetUniverses.RootedSevenMixed009.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed009.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed009.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed009.cells generators
    FacetUniverses.RootedSevenMixed009.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed009.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed009.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed009.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed009.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed009.S5T1

end
end


/- Source module: RootedSevenMixed009CanonicalT1 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed009.T1
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 1)
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed009.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed009.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed009.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed009.Outside.forward g) (FacetUniverses.RootedSevenMixed009.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed009.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed009.cells i) (FacetUniverses.RootedSevenMixed009.cells (FacetUniverses.RootedSevenMixed009.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed009.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed009.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed009.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed009.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed009.cells
    (FacetUniverses.RootedSevenMixed009.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed009.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed009.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed009.Outside.forward g) (FacetUniverses.RootedSevenMixed009.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed009.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed009.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed009.cells generators
    FacetUniverses.RootedSevenMixed009.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed009.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed009.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed009.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed009.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed009.T1

end
end


/- Source module: RootedSevenMixed009Coverage -/
@[expose] public section

/-!
# Complete compatible-template coverage for RootedSevenMixed009

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSevenMixed009

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSevenMixed009

abbrev root : Fin FacetUniverses.RootedSevenMixed009.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 7 ↪ Fin 10 where
  toFun := ![0, 1, 2, 3, 4, 5, 6]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N7.templates 13)) =
      decodeCell (FacetUniverses.RootedSevenMixed009.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSevenMixed009.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [1]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed009.cells root 13 (fun a => a.size ≤ 5 ∨ a = .six 1) quota where
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
      have hi : i = 1 := by
        rcases hallowed with hs | heq
        · change 6 ≤ 5 at hs
          omega
        · exact Kind.six.inj heq
      subst i
      exact T1.covers_exact f h

/-- The exact numerical family discharges every omitted-kind condition. -/
def rowCoverage :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed009.cells root 13
      (fun a => a.size ≤ 5 ∨ a = .six 1) (SevenFamilyActualEncoding.rowQuota 0 2 6 1) :=
  coverage _ (by
    intro k hk
    have hk' : k = 1 := by simpa [omittedTags] using hk
    rcases hk' with rfl <;> rfl)

end Papers.RationalityTen.RootedCoverage.RootedSevenMixed009

end
end


/- Source module: RootedSevenMixed010CanonicalS5T0 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed010.S5T0
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed010.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed010.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed010.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed010.Outside.forward g) (FacetUniverses.RootedSevenMixed010.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed010.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed010.cells i) (FacetUniverses.RootedSevenMixed010.cells (FacetUniverses.RootedSevenMixed010.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed010.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed010.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed010.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed010.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed010.cells
    (FacetUniverses.RootedSevenMixed010.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed010.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed010.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed010.Outside.forward g) (FacetUniverses.RootedSevenMixed010.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed010.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed010.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed010.cells generators
    FacetUniverses.RootedSevenMixed010.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed010.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed010.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed010.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed010.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed010.S5T0

end
end


/- Source module: RootedSevenMixed010CanonicalS5T1 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed010.S5T1
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed010.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed010.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed010.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed010.Outside.forward g) (FacetUniverses.RootedSevenMixed010.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed010.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed010.cells i) (FacetUniverses.RootedSevenMixed010.cells (FacetUniverses.RootedSevenMixed010.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed010.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed010.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed010.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed010.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed010.cells
    (FacetUniverses.RootedSevenMixed010.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed010.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed010.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed010.Outside.forward g) (FacetUniverses.RootedSevenMixed010.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed010.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed010.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed010.cells generators
    FacetUniverses.RootedSevenMixed010.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed010.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed010.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed010.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed010.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed010.S5T1

end
end


/- Source module: RootedSevenMixed010CanonicalT2 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed010.T2
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 2)
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed010.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed010.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed010.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed010.Outside.forward g) (FacetUniverses.RootedSevenMixed010.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed010.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed010.cells i) (FacetUniverses.RootedSevenMixed010.cells (FacetUniverses.RootedSevenMixed010.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed010.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed010.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed010.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed010.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed010.cells
    (FacetUniverses.RootedSevenMixed010.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed010.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed010.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed010.Outside.forward g) (FacetUniverses.RootedSevenMixed010.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed010.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed010.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed010.cells generators
    FacetUniverses.RootedSevenMixed010.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed010.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed010.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed010.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed010.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed010.T2

end
end


/- Source module: RootedSevenMixed010Coverage -/
@[expose] public section

/-!
# Complete compatible-template coverage for RootedSevenMixed010

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSevenMixed010

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSevenMixed010

abbrev root : Fin FacetUniverses.RootedSevenMixed010.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 7 ↪ Fin 10 where
  toFun := ![0, 1, 2, 3, 4, 5, 6]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N7.templates 13)) =
      decodeCell (FacetUniverses.RootedSevenMixed010.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSevenMixed010.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [1]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed010.cells root 13 (fun a => a.size ≤ 5 ∨ a = .six 2) quota where
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
      have hi : i = 2 := by
        rcases hallowed with hs | heq
        · change 6 ≤ 5 at hs
          omega
        · exact Kind.six.inj heq
      subst i
      exact T2.covers_exact f h

/-- The exact numerical family discharges every omitted-kind condition. -/
def rowCoverage :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed010.cells root 13
      (fun a => a.size ≤ 5 ∨ a = .six 2) (SevenFamilyActualEncoding.rowQuota 0 1 7 1) :=
  coverage _ (by
    intro k hk
    have hk' : k = 1 := by simpa [omittedTags] using hk
    rcases hk' with rfl <;> rfl)

end Papers.RationalityTen.RootedCoverage.RootedSevenMixed010

end
end


/- Source module: RootedSevenMixed011CanonicalS5T0 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed011.S5T0
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed011.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed011.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed011.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed011.Outside.forward g) (FacetUniverses.RootedSevenMixed011.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed011.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed011.cells i) (FacetUniverses.RootedSevenMixed011.cells (FacetUniverses.RootedSevenMixed011.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed011.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed011.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed011.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed011.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed011.cells
    (FacetUniverses.RootedSevenMixed011.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed011.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed011.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed011.Outside.forward g) (FacetUniverses.RootedSevenMixed011.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed011.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed011.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed011.cells generators
    FacetUniverses.RootedSevenMixed011.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed011.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed011.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed011.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed011.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed011.S5T0

end
end


/- Source module: RootedSevenMixed011CanonicalS5T1 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed011.S5T1
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed011.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed011.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed011.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed011.Outside.forward g) (FacetUniverses.RootedSevenMixed011.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed011.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed011.cells i) (FacetUniverses.RootedSevenMixed011.cells (FacetUniverses.RootedSevenMixed011.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed011.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed011.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed011.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed011.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed011.cells
    (FacetUniverses.RootedSevenMixed011.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed011.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed011.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed011.Outside.forward g) (FacetUniverses.RootedSevenMixed011.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed011.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed011.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed011.cells generators
    FacetUniverses.RootedSevenMixed011.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed011.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed011.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed011.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed011.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed011.S5T1

end
end


/- Source module: RootedSevenMixed011CanonicalT3 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed011.T3
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 3)
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed011.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed011.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed011.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed011.Outside.forward g) (FacetUniverses.RootedSevenMixed011.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed011.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed011.cells i) (FacetUniverses.RootedSevenMixed011.cells (FacetUniverses.RootedSevenMixed011.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed011.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed011.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed011.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed011.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed011.cells
    (FacetUniverses.RootedSevenMixed011.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed011.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed011.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed011.Outside.forward g) (FacetUniverses.RootedSevenMixed011.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed011.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed011.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed011.cells generators
    FacetUniverses.RootedSevenMixed011.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed011.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed011.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed011.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed011.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed011.T3

end
end


/- Source module: RootedSevenMixed011Coverage -/
@[expose] public section

/-!
# Complete compatible-template coverage for RootedSevenMixed011

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSevenMixed011

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSevenMixed011

abbrev root : Fin FacetUniverses.RootedSevenMixed011.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 7 ↪ Fin 10 where
  toFun := ![0, 1, 2, 3, 4, 5, 6]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N7.templates 13)) =
      decodeCell (FacetUniverses.RootedSevenMixed011.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSevenMixed011.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [1]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed011.cells root 13 (fun a => a.size ≤ 5 ∨ a = .six 3) quota where
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
      have hi : i = 3 := by
        rcases hallowed with hs | heq
        · change 6 ≤ 5 at hs
          omega
        · exact Kind.six.inj heq
      subst i
      exact T3.covers_exact f h

/-- The exact numerical family discharges every omitted-kind condition. -/
def rowCoverage :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed011.cells root 13
      (fun a => a.size ≤ 5 ∨ a = .six 3) (SevenFamilyActualEncoding.rowQuota 0 2 6 1) :=
  coverage _ (by
    intro k hk
    have hk' : k = 1 := by simpa [omittedTags] using hk
    rcases hk' with rfl <;> rfl)

end Papers.RationalityTen.RootedCoverage.RootedSevenMixed011

end
end

