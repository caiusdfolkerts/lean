module

public import DecodedCellBounds
public import FinitePolygonTemplates
public import KindedRootedFacetCoverage
public import OutsidePlacementSemantics
public import RootedSevenMixed000CanonicalS5T0Finite
public import RootedSevenMixed000CanonicalS5T0Placement
public import RootedSevenMixed000CanonicalS5T1Finite
public import RootedSevenMixed000CanonicalS5T1Placement
public import RootedSevenMixed000CanonicalT6Finite
public import RootedSevenMixed000CanonicalT6Placement
public import RootedSevenMixed000Outside
public import RootedSevenMixed001CanonicalS5T0Finite
public import RootedSevenMixed001CanonicalS5T0Placement
public import RootedSevenMixed001CanonicalS5T1Finite
public import RootedSevenMixed001CanonicalS5T1Placement
public import RootedSevenMixed001CanonicalT6Finite
public import RootedSevenMixed001CanonicalT6Placement
public import RootedSevenMixed001Outside
public import RootedSevenMixed002CanonicalS5T0Finite
public import RootedSevenMixed002CanonicalS5T0Placement
public import RootedSevenMixed002CanonicalS5T1Finite
public import RootedSevenMixed002CanonicalS5T1Placement
public import RootedSevenMixed002CanonicalT6Finite
public import RootedSevenMixed002CanonicalT6Placement
public import RootedSevenMixed002Outside
public import RootedSevenMixed003CanonicalS5T0Finite
public import RootedSevenMixed003CanonicalS5T0Placement
public import RootedSevenMixed003CanonicalS5T1Finite
public import RootedSevenMixed003CanonicalS5T1Placement
public import RootedSevenMixed003CanonicalT6Finite
public import RootedSevenMixed003CanonicalT6Placement
public import RootedSevenMixed003Outside
public import RootedSevenMixed004CanonicalS5T0Finite
public import RootedSevenMixed004CanonicalS5T0Placement
public import RootedSevenMixed004CanonicalS5T1Finite
public import RootedSevenMixed004CanonicalS5T1Placement
public import RootedSevenMixed004CanonicalT6Finite
public import RootedSevenMixed004CanonicalT6Placement
public import RootedSevenMixed004Outside
public import RootedSevenMixed005CanonicalS5T0Finite
public import RootedSevenMixed005CanonicalS5T0Placement
public import RootedSevenMixed005CanonicalS5T1Finite
public import RootedSevenMixed005CanonicalS5T1Placement
public import RootedSevenMixed005CanonicalT6Finite
public import RootedSevenMixed005CanonicalT6Placement
public import RootedSevenMixed005Outside
public import SevenFamilyActualEncoding
public import SymmetricRootedFacetCoverage

/-! Geometric placement coverage; the following proof bodies are unchanged. -/

/- Source module: RootedSevenMixed000CanonicalS5T0 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed000.S5T0
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed000.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed000.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed000.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed000.Outside.forward g) (FacetUniverses.RootedSevenMixed000.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed000.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed000.cells i) (FacetUniverses.RootedSevenMixed000.cells (FacetUniverses.RootedSevenMixed000.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed000.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed000.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed000.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed000.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed000.cells
    (FacetUniverses.RootedSevenMixed000.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed000.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed000.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed000.Outside.forward g) (FacetUniverses.RootedSevenMixed000.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed000.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed000.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed000.cells generators
    FacetUniverses.RootedSevenMixed000.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed000.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed000.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed000.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed000.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed000.S5T0

end
end


/- Source module: RootedSevenMixed000CanonicalS5T1 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed000.S5T1
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed000.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed000.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed000.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed000.Outside.forward g) (FacetUniverses.RootedSevenMixed000.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed000.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed000.cells i) (FacetUniverses.RootedSevenMixed000.cells (FacetUniverses.RootedSevenMixed000.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed000.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed000.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed000.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed000.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed000.cells
    (FacetUniverses.RootedSevenMixed000.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed000.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed000.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed000.Outside.forward g) (FacetUniverses.RootedSevenMixed000.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed000.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed000.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed000.cells generators
    FacetUniverses.RootedSevenMixed000.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed000.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed000.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed000.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed000.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed000.S5T1

end
end


/- Source module: RootedSevenMixed000CanonicalT6 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed000.T6
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed000.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed000.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed000.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed000.Outside.forward g) (FacetUniverses.RootedSevenMixed000.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed000.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed000.cells i) (FacetUniverses.RootedSevenMixed000.cells (FacetUniverses.RootedSevenMixed000.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed000.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed000.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed000.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed000.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed000.cells
    (FacetUniverses.RootedSevenMixed000.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed000.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed000.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed000.Outside.forward g) (FacetUniverses.RootedSevenMixed000.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed000.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed000.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed000.cells generators
    FacetUniverses.RootedSevenMixed000.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed000.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed000.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed000.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed000.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed000.T6

end
end


/- Source module: RootedSevenMixed000Coverage -/
@[expose] public section

/-!
# Complete compatible-template coverage for RootedSevenMixed000

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSevenMixed000

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSevenMixed000

abbrev root : Fin FacetUniverses.RootedSevenMixed000.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 7 ↪ Fin 10 where
  toFun := ![0, 1, 2, 3, 4, 5, 6]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N7.templates 2)) =
      decodeCell (FacetUniverses.RootedSevenMixed000.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSevenMixed000.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [1]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed000.cells root 2 (fun a => a.size ≤ 5 ∨ a = .six 6) quota where
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
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed000.cells root 2
      (fun a => a.size ≤ 5 ∨ a = .six 6) (SevenFamilyActualEncoding.rowQuota 0 2 6 1) :=
  coverage _ (by
    intro k hk
    have hk' : k = 1 := by simpa [omittedTags] using hk
    rcases hk' with rfl <;> rfl)

end Papers.RationalityTen.RootedCoverage.RootedSevenMixed000

end
end


/- Source module: RootedSevenMixed001CanonicalS5T0 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed001.S5T0
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed001.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed001.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed001.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed001.Outside.forward g) (FacetUniverses.RootedSevenMixed001.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed001.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed001.cells i) (FacetUniverses.RootedSevenMixed001.cells (FacetUniverses.RootedSevenMixed001.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed001.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed001.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed001.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed001.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed001.cells
    (FacetUniverses.RootedSevenMixed001.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed001.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed001.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed001.Outside.forward g) (FacetUniverses.RootedSevenMixed001.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed001.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed001.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed001.cells generators
    FacetUniverses.RootedSevenMixed001.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed001.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed001.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed001.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed001.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed001.S5T0

end
end


/- Source module: RootedSevenMixed001CanonicalS5T1 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed001.S5T1
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed001.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed001.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed001.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed001.Outside.forward g) (FacetUniverses.RootedSevenMixed001.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed001.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed001.cells i) (FacetUniverses.RootedSevenMixed001.cells (FacetUniverses.RootedSevenMixed001.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed001.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed001.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed001.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed001.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed001.cells
    (FacetUniverses.RootedSevenMixed001.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed001.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed001.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed001.Outside.forward g) (FacetUniverses.RootedSevenMixed001.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed001.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed001.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed001.cells generators
    FacetUniverses.RootedSevenMixed001.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed001.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed001.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed001.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed001.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed001.S5T1

end
end


/- Source module: RootedSevenMixed001CanonicalT6 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed001.T6
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed001.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed001.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed001.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed001.Outside.forward g) (FacetUniverses.RootedSevenMixed001.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed001.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed001.cells i) (FacetUniverses.RootedSevenMixed001.cells (FacetUniverses.RootedSevenMixed001.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed001.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed001.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed001.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed001.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed001.cells
    (FacetUniverses.RootedSevenMixed001.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed001.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed001.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed001.Outside.forward g) (FacetUniverses.RootedSevenMixed001.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed001.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed001.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed001.cells generators
    FacetUniverses.RootedSevenMixed001.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed001.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed001.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed001.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed001.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed001.T6

end
end


/- Source module: RootedSevenMixed001Coverage -/
@[expose] public section

/-!
# Complete compatible-template coverage for RootedSevenMixed001

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSevenMixed001

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSevenMixed001

abbrev root : Fin FacetUniverses.RootedSevenMixed001.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 7 ↪ Fin 10 where
  toFun := ![0, 1, 2, 3, 4, 5, 6]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N7.templates 3)) =
      decodeCell (FacetUniverses.RootedSevenMixed001.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSevenMixed001.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [1]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed001.cells root 3 (fun a => a.size ≤ 5 ∨ a = .six 6) quota where
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
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed001.cells root 3
      (fun a => a.size ≤ 5 ∨ a = .six 6) (SevenFamilyActualEncoding.rowQuota 0 2 6 1) :=
  coverage _ (by
    intro k hk
    have hk' : k = 1 := by simpa [omittedTags] using hk
    rcases hk' with rfl <;> rfl)

end Papers.RationalityTen.RootedCoverage.RootedSevenMixed001

end
end


/- Source module: RootedSevenMixed002CanonicalS5T0 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed002.S5T0
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed002.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed002.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed002.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed002.Outside.forward g) (FacetUniverses.RootedSevenMixed002.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed002.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed002.cells i) (FacetUniverses.RootedSevenMixed002.cells (FacetUniverses.RootedSevenMixed002.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed002.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed002.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed002.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed002.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed002.cells
    (FacetUniverses.RootedSevenMixed002.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed002.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed002.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed002.Outside.forward g) (FacetUniverses.RootedSevenMixed002.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed002.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed002.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed002.cells generators
    FacetUniverses.RootedSevenMixed002.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed002.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed002.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed002.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed002.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed002.S5T0

end
end


/- Source module: RootedSevenMixed002CanonicalS5T1 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed002.S5T1
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed002.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed002.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed002.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed002.Outside.forward g) (FacetUniverses.RootedSevenMixed002.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed002.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed002.cells i) (FacetUniverses.RootedSevenMixed002.cells (FacetUniverses.RootedSevenMixed002.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed002.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed002.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed002.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed002.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed002.cells
    (FacetUniverses.RootedSevenMixed002.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed002.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed002.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed002.Outside.forward g) (FacetUniverses.RootedSevenMixed002.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed002.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed002.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed002.cells generators
    FacetUniverses.RootedSevenMixed002.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed002.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed002.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed002.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed002.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed002.S5T1

end
end


/- Source module: RootedSevenMixed002CanonicalT6 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed002.T6
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed002.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed002.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed002.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed002.Outside.forward g) (FacetUniverses.RootedSevenMixed002.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed002.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed002.cells i) (FacetUniverses.RootedSevenMixed002.cells (FacetUniverses.RootedSevenMixed002.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed002.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed002.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed002.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed002.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed002.cells
    (FacetUniverses.RootedSevenMixed002.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed002.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed002.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed002.Outside.forward g) (FacetUniverses.RootedSevenMixed002.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed002.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed002.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed002.cells generators
    FacetUniverses.RootedSevenMixed002.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed002.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed002.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed002.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed002.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed002.T6

end
end


/- Source module: RootedSevenMixed002Coverage -/
@[expose] public section

/-!
# Complete compatible-template coverage for RootedSevenMixed002

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSevenMixed002

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSevenMixed002

abbrev root : Fin FacetUniverses.RootedSevenMixed002.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 7 ↪ Fin 10 where
  toFun := ![0, 1, 2, 3, 4, 5, 6]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N7.templates 6)) =
      decodeCell (FacetUniverses.RootedSevenMixed002.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSevenMixed002.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [1]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed002.cells root 6 (fun a => a.size ≤ 5 ∨ a = .six 6) quota where
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
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed002.cells root 6
      (fun a => a.size ≤ 5 ∨ a = .six 6) (SevenFamilyActualEncoding.rowQuota 0 2 6 1) :=
  coverage _ (by
    intro k hk
    have hk' : k = 1 := by simpa [omittedTags] using hk
    rcases hk' with rfl <;> rfl)

end Papers.RationalityTen.RootedCoverage.RootedSevenMixed002

end
end


/- Source module: RootedSevenMixed003CanonicalS5T0 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed003.S5T0
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed003.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed003.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed003.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed003.Outside.forward g) (FacetUniverses.RootedSevenMixed003.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed003.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed003.cells i) (FacetUniverses.RootedSevenMixed003.cells (FacetUniverses.RootedSevenMixed003.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed003.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed003.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed003.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed003.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed003.cells
    (FacetUniverses.RootedSevenMixed003.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed003.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed003.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed003.Outside.forward g) (FacetUniverses.RootedSevenMixed003.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed003.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed003.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed003.cells generators
    FacetUniverses.RootedSevenMixed003.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed003.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed003.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed003.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed003.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed003.S5T0

end
end


/- Source module: RootedSevenMixed003CanonicalS5T1 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed003.S5T1
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed003.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed003.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed003.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed003.Outside.forward g) (FacetUniverses.RootedSevenMixed003.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed003.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed003.cells i) (FacetUniverses.RootedSevenMixed003.cells (FacetUniverses.RootedSevenMixed003.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed003.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed003.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed003.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed003.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed003.cells
    (FacetUniverses.RootedSevenMixed003.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed003.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed003.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed003.Outside.forward g) (FacetUniverses.RootedSevenMixed003.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed003.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed003.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed003.cells generators
    FacetUniverses.RootedSevenMixed003.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed003.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed003.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed003.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed003.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed003.S5T1

end
end


/- Source module: RootedSevenMixed003CanonicalT6 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed003.T6
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed003.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed003.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed003.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed003.Outside.forward g) (FacetUniverses.RootedSevenMixed003.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed003.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed003.cells i) (FacetUniverses.RootedSevenMixed003.cells (FacetUniverses.RootedSevenMixed003.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed003.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed003.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed003.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed003.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed003.cells
    (FacetUniverses.RootedSevenMixed003.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed003.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed003.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed003.Outside.forward g) (FacetUniverses.RootedSevenMixed003.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed003.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed003.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed003.cells generators
    FacetUniverses.RootedSevenMixed003.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed003.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed003.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed003.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed003.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed003.T6

end
end


/- Source module: RootedSevenMixed003Coverage -/
@[expose] public section

/-!
# Complete compatible-template coverage for RootedSevenMixed003

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSevenMixed003

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSevenMixed003

abbrev root : Fin FacetUniverses.RootedSevenMixed003.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 7 ↪ Fin 10 where
  toFun := ![0, 1, 2, 3, 4, 5, 6]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N7.templates 7)) =
      decodeCell (FacetUniverses.RootedSevenMixed003.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSevenMixed003.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [1]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed003.cells root 7 (fun a => a.size ≤ 5 ∨ a = .six 6) quota where
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
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed003.cells root 7
      (fun a => a.size ≤ 5 ∨ a = .six 6) (SevenFamilyActualEncoding.rowQuota 0 2 6 1) :=
  coverage _ (by
    intro k hk
    have hk' : k = 1 := by simpa [omittedTags] using hk
    rcases hk' with rfl <;> rfl)

end Papers.RationalityTen.RootedCoverage.RootedSevenMixed003

end
end


/- Source module: RootedSevenMixed004CanonicalS5T0 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed004.S5T0
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed004.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed004.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed004.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed004.Outside.forward g) (FacetUniverses.RootedSevenMixed004.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed004.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed004.cells i) (FacetUniverses.RootedSevenMixed004.cells (FacetUniverses.RootedSevenMixed004.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed004.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed004.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed004.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed004.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed004.cells
    (FacetUniverses.RootedSevenMixed004.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed004.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed004.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed004.Outside.forward g) (FacetUniverses.RootedSevenMixed004.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed004.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed004.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed004.cells generators
    FacetUniverses.RootedSevenMixed004.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed004.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed004.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed004.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed004.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed004.S5T0

end
end


/- Source module: RootedSevenMixed004CanonicalS5T1 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed004.S5T1
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed004.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed004.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed004.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed004.Outside.forward g) (FacetUniverses.RootedSevenMixed004.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed004.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed004.cells i) (FacetUniverses.RootedSevenMixed004.cells (FacetUniverses.RootedSevenMixed004.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed004.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed004.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed004.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed004.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed004.cells
    (FacetUniverses.RootedSevenMixed004.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed004.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed004.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed004.Outside.forward g) (FacetUniverses.RootedSevenMixed004.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed004.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed004.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed004.cells generators
    FacetUniverses.RootedSevenMixed004.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed004.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed004.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed004.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed004.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed004.S5T1

end
end


/- Source module: RootedSevenMixed004CanonicalT6 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed004.T6
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed004.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed004.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed004.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed004.Outside.forward g) (FacetUniverses.RootedSevenMixed004.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed004.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed004.cells i) (FacetUniverses.RootedSevenMixed004.cells (FacetUniverses.RootedSevenMixed004.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed004.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed004.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed004.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed004.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed004.cells
    (FacetUniverses.RootedSevenMixed004.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed004.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed004.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed004.Outside.forward g) (FacetUniverses.RootedSevenMixed004.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed004.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed004.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed004.cells generators
    FacetUniverses.RootedSevenMixed004.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed004.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed004.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed004.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed004.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed004.T6

end
end


/- Source module: RootedSevenMixed004Coverage -/
@[expose] public section

/-!
# Complete compatible-template coverage for RootedSevenMixed004

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSevenMixed004

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSevenMixed004

abbrev root : Fin FacetUniverses.RootedSevenMixed004.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 7 ↪ Fin 10 where
  toFun := ![0, 1, 2, 3, 4, 5, 6]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N7.templates 8)) =
      decodeCell (FacetUniverses.RootedSevenMixed004.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSevenMixed004.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [1]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed004.cells root 8 (fun a => a.size ≤ 5 ∨ a = .six 6) quota where
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
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed004.cells root 8
      (fun a => a.size ≤ 5 ∨ a = .six 6) (SevenFamilyActualEncoding.rowQuota 0 2 6 1) :=
  coverage _ (by
    intro k hk
    have hk' : k = 1 := by simpa [omittedTags] using hk
    rcases hk' with rfl <;> rfl)

end Papers.RationalityTen.RootedCoverage.RootedSevenMixed004

end
end


/- Source module: RootedSevenMixed005CanonicalS5T0 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed005.S5T0
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed005.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed005.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed005.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed005.Outside.forward g) (FacetUniverses.RootedSevenMixed005.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed005.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed005.cells i) (FacetUniverses.RootedSevenMixed005.cells (FacetUniverses.RootedSevenMixed005.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed005.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed005.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed005.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed005.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed005.cells
    (FacetUniverses.RootedSevenMixed005.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed005.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed005.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed005.Outside.forward g) (FacetUniverses.RootedSevenMixed005.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed005.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed005.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed005.cells generators
    FacetUniverses.RootedSevenMixed005.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed005.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed005.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed005.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed005.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed005.S5T0

end
end


/- Source module: RootedSevenMixed005CanonicalS5T1 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed005.S5T1
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed005.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed005.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed005.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed005.Outside.forward g) (FacetUniverses.RootedSevenMixed005.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed005.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed005.cells i) (FacetUniverses.RootedSevenMixed005.cells (FacetUniverses.RootedSevenMixed005.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed005.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed005.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed005.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed005.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed005.cells
    (FacetUniverses.RootedSevenMixed005.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed005.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed005.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed005.Outside.forward g) (FacetUniverses.RootedSevenMixed005.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed005.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed005.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed005.cells generators
    FacetUniverses.RootedSevenMixed005.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed005.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed005.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed005.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed005.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed005.S5T1

end
end


/- Source module: RootedSevenMixed005CanonicalT6 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed005.T6
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed005.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed005.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed005.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed005.Outside.forward g) (FacetUniverses.RootedSevenMixed005.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed005.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed005.cells i) (FacetUniverses.RootedSevenMixed005.cells (FacetUniverses.RootedSevenMixed005.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed005.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed005.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed005.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed005.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed005.cells
    (FacetUniverses.RootedSevenMixed005.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed005.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed005.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed005.Outside.forward g) (FacetUniverses.RootedSevenMixed005.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed005.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed005.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed005.cells generators
    FacetUniverses.RootedSevenMixed005.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed005.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed005.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed005.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed005.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed005.T6

end
end


/- Source module: RootedSevenMixed005Coverage -/
@[expose] public section

/-!
# Complete compatible-template coverage for RootedSevenMixed005

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSevenMixed005

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSevenMixed005

abbrev root : Fin FacetUniverses.RootedSevenMixed005.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 7 ↪ Fin 10 where
  toFun := ![0, 1, 2, 3, 4, 5, 6]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N7.templates 9)) =
      decodeCell (FacetUniverses.RootedSevenMixed005.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSevenMixed005.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [1]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed005.cells root 9 (fun a => a.size ≤ 5 ∨ a = .six 6) quota where
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
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed005.cells root 9
      (fun a => a.size ≤ 5 ∨ a = .six 6) (SevenFamilyActualEncoding.rowQuota 0 2 6 1) :=
  coverage _ (by
    intro k hk
    have hk' : k = 1 := by simpa [omittedTags] using hk
    rcases hk' with rfl <;> rfl)

end Papers.RationalityTen.RootedCoverage.RootedSevenMixed005

end
end

