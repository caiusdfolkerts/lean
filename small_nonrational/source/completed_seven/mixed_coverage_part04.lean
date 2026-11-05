module

public import CompletedSeven.MixedCoveragePart03
public import DecodedCellBounds
public import FinitePolygonTemplates
public import KindedRootedFacetCoverage
public import OutsidePlacementSemantics
public import RootedSevenMixed024CanonicalS5T0Finite
public import RootedSevenMixed024CanonicalS5T0Placement
public import RootedSevenMixed024CanonicalS5T1Finite
public import RootedSevenMixed024CanonicalS5T1Placement
public import RootedSevenMixed024CanonicalT6Finite
public import RootedSevenMixed024CanonicalT6Placement
public import RootedSevenMixed024Outside
public import RootedSevenMixed025CanonicalS5T0Finite
public import RootedSevenMixed025CanonicalS5T0Placement
public import RootedSevenMixed025CanonicalS5T1Finite
public import RootedSevenMixed025CanonicalS5T1Placement
public import RootedSevenMixed025CanonicalT6Finite
public import RootedSevenMixed025CanonicalT6Placement
public import RootedSevenMixed025Outside
public import RootedSevenMixed026CanonicalS5T0Finite
public import RootedSevenMixed026CanonicalS5T0Placement
public import RootedSevenMixed026CanonicalS5T1Finite
public import RootedSevenMixed026CanonicalS5T1Placement
public import RootedSevenMixed026CanonicalT6Finite
public import RootedSevenMixed026CanonicalT6Placement
public import RootedSevenMixed026Outside
public import RootedSevenMixed027CanonicalS5T0Finite
public import RootedSevenMixed027CanonicalS5T0Placement
public import RootedSevenMixed027CanonicalS5T1Finite
public import RootedSevenMixed027CanonicalS5T1Placement
public import RootedSevenMixed027CanonicalT6Finite
public import RootedSevenMixed027CanonicalT6Placement
public import RootedSevenMixed027Outside
public import RootedSevenMixed028CanonicalS5T0Finite
public import RootedSevenMixed028CanonicalS5T0Placement
public import RootedSevenMixed028CanonicalS5T1Finite
public import RootedSevenMixed028CanonicalS5T1Placement
public import RootedSevenMixed028CanonicalT6Finite
public import RootedSevenMixed028CanonicalT6Placement
public import RootedSevenMixed028Outside
public import RootedSevenMixed029CanonicalS5T0Finite
public import RootedSevenMixed029CanonicalS5T0Placement
public import RootedSevenMixed029CanonicalS5T1Finite
public import RootedSevenMixed029CanonicalS5T1Placement
public import RootedSevenMixed029CanonicalT6Finite
public import RootedSevenMixed029CanonicalT6Placement
public import RootedSevenMixed029Outside
public import SevenFamilyActualEncoding
public import SymmetricRootedFacetCoverage

/-! Geometric placement coverage; the following proof bodies are unchanged. -/

/- Source module: RootedSevenMixed023Coverage -/
@[expose] public section

/-!
# Complete compatible-template coverage for RootedSevenMixed023

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSevenMixed023

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSevenMixed023

abbrev root : Fin FacetUniverses.RootedSevenMixed023.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 7 ↪ Fin 10 where
  toFun := ![0, 1, 2, 3, 4, 5, 6]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N7.templates 24)) =
      decodeCell (FacetUniverses.RootedSevenMixed023.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSevenMixed023.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [1]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed023.cells root 24 (fun a => a.size ≤ 5 ∨ a = .six 6) quota where
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
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed023.cells root 24
      (fun a => a.size ≤ 5 ∨ a = .six 6) (SevenFamilyActualEncoding.rowQuota 0 3 5 1) :=
  coverage _ (by
    intro k hk
    have hk' : k = 1 := by simpa [omittedTags] using hk
    rcases hk' with rfl <;> rfl)

end Papers.RationalityTen.RootedCoverage.RootedSevenMixed023

end
end


/- Source module: RootedSevenMixed024CanonicalS5T0 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed024.S5T0
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed024.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed024.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed024.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed024.Outside.forward g) (FacetUniverses.RootedSevenMixed024.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed024.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed024.cells i) (FacetUniverses.RootedSevenMixed024.cells (FacetUniverses.RootedSevenMixed024.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed024.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed024.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed024.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed024.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed024.cells
    (FacetUniverses.RootedSevenMixed024.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed024.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed024.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed024.Outside.forward g) (FacetUniverses.RootedSevenMixed024.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed024.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed024.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed024.cells generators
    FacetUniverses.RootedSevenMixed024.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed024.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed024.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed024.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed024.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed024.S5T0

end
end


/- Source module: RootedSevenMixed024CanonicalS5T1 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed024.S5T1
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed024.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed024.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed024.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed024.Outside.forward g) (FacetUniverses.RootedSevenMixed024.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed024.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed024.cells i) (FacetUniverses.RootedSevenMixed024.cells (FacetUniverses.RootedSevenMixed024.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed024.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed024.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed024.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed024.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed024.cells
    (FacetUniverses.RootedSevenMixed024.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed024.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed024.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed024.Outside.forward g) (FacetUniverses.RootedSevenMixed024.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed024.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed024.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed024.cells generators
    FacetUniverses.RootedSevenMixed024.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed024.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed024.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed024.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed024.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed024.S5T1

end
end


/- Source module: RootedSevenMixed024CanonicalT6 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed024.T6
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed024.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed024.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed024.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed024.Outside.forward g) (FacetUniverses.RootedSevenMixed024.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed024.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed024.cells i) (FacetUniverses.RootedSevenMixed024.cells (FacetUniverses.RootedSevenMixed024.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed024.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed024.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed024.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed024.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed024.cells
    (FacetUniverses.RootedSevenMixed024.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed024.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed024.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed024.Outside.forward g) (FacetUniverses.RootedSevenMixed024.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed024.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed024.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed024.cells generators
    FacetUniverses.RootedSevenMixed024.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed024.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed024.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed024.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed024.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed024.T6

end
end


/- Source module: RootedSevenMixed024Coverage -/
@[expose] public section

/-!
# Complete compatible-template coverage for RootedSevenMixed024

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSevenMixed024

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSevenMixed024

abbrev root : Fin FacetUniverses.RootedSevenMixed024.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 7 ↪ Fin 10 where
  toFun := ![0, 1, 2, 3, 4, 5, 6]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N7.templates 25)) =
      decodeCell (FacetUniverses.RootedSevenMixed024.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSevenMixed024.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [1]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed024.cells root 25 (fun a => a.size ≤ 5 ∨ a = .six 6) quota where
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
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed024.cells root 25
      (fun a => a.size ≤ 5 ∨ a = .six 6) (SevenFamilyActualEncoding.rowQuota 0 4 4 1) :=
  coverage _ (by
    intro k hk
    have hk' : k = 1 := by simpa [omittedTags] using hk
    rcases hk' with rfl <;> rfl)

end Papers.RationalityTen.RootedCoverage.RootedSevenMixed024

end
end


/- Source module: RootedSevenMixed025CanonicalS5T0 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed025.S5T0
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed025.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed025.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed025.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed025.Outside.forward g) (FacetUniverses.RootedSevenMixed025.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed025.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed025.cells i) (FacetUniverses.RootedSevenMixed025.cells (FacetUniverses.RootedSevenMixed025.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed025.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed025.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed025.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed025.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed025.cells
    (FacetUniverses.RootedSevenMixed025.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed025.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed025.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed025.Outside.forward g) (FacetUniverses.RootedSevenMixed025.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed025.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed025.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed025.cells generators
    FacetUniverses.RootedSevenMixed025.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed025.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed025.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed025.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed025.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed025.S5T0

end
end


/- Source module: RootedSevenMixed025CanonicalS5T1 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed025.S5T1
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed025.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed025.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed025.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed025.Outside.forward g) (FacetUniverses.RootedSevenMixed025.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed025.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed025.cells i) (FacetUniverses.RootedSevenMixed025.cells (FacetUniverses.RootedSevenMixed025.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed025.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed025.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed025.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed025.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed025.cells
    (FacetUniverses.RootedSevenMixed025.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed025.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed025.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed025.Outside.forward g) (FacetUniverses.RootedSevenMixed025.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed025.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed025.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed025.cells generators
    FacetUniverses.RootedSevenMixed025.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed025.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed025.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed025.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed025.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed025.S5T1

end
end


/- Source module: RootedSevenMixed025CanonicalT6 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed025.T6
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed025.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed025.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed025.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed025.Outside.forward g) (FacetUniverses.RootedSevenMixed025.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed025.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed025.cells i) (FacetUniverses.RootedSevenMixed025.cells (FacetUniverses.RootedSevenMixed025.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed025.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed025.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed025.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed025.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed025.cells
    (FacetUniverses.RootedSevenMixed025.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed025.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed025.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed025.Outside.forward g) (FacetUniverses.RootedSevenMixed025.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed025.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed025.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed025.cells generators
    FacetUniverses.RootedSevenMixed025.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed025.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed025.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed025.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed025.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed025.T6

end
end


/- Source module: RootedSevenMixed025Coverage -/
@[expose] public section

/-!
# Complete compatible-template coverage for RootedSevenMixed025

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSevenMixed025

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSevenMixed025

abbrev root : Fin FacetUniverses.RootedSevenMixed025.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 7 ↪ Fin 10 where
  toFun := ![0, 1, 2, 3, 4, 5, 6]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N7.templates 27)) =
      decodeCell (FacetUniverses.RootedSevenMixed025.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSevenMixed025.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [1]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed025.cells root 27 (fun a => a.size ≤ 5 ∨ a = .six 6) quota where
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
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed025.cells root 27
      (fun a => a.size ≤ 5 ∨ a = .six 6) (SevenFamilyActualEncoding.rowQuota 0 4 4 1) :=
  coverage _ (by
    intro k hk
    have hk' : k = 1 := by simpa [omittedTags] using hk
    rcases hk' with rfl <;> rfl)

end Papers.RationalityTen.RootedCoverage.RootedSevenMixed025

end
end


/- Source module: RootedSevenMixed026CanonicalS5T0 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed026.S5T0
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed026.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed026.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed026.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed026.Outside.forward g) (FacetUniverses.RootedSevenMixed026.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed026.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed026.cells i) (FacetUniverses.RootedSevenMixed026.cells (FacetUniverses.RootedSevenMixed026.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed026.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed026.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed026.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed026.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed026.cells
    (FacetUniverses.RootedSevenMixed026.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed026.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed026.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed026.Outside.forward g) (FacetUniverses.RootedSevenMixed026.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed026.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed026.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed026.cells generators
    FacetUniverses.RootedSevenMixed026.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed026.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed026.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed026.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed026.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed026.S5T0

end
end


/- Source module: RootedSevenMixed026CanonicalS5T1 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed026.S5T1
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed026.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed026.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed026.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed026.Outside.forward g) (FacetUniverses.RootedSevenMixed026.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed026.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed026.cells i) (FacetUniverses.RootedSevenMixed026.cells (FacetUniverses.RootedSevenMixed026.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed026.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed026.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed026.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed026.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed026.cells
    (FacetUniverses.RootedSevenMixed026.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed026.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed026.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed026.Outside.forward g) (FacetUniverses.RootedSevenMixed026.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed026.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed026.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed026.cells generators
    FacetUniverses.RootedSevenMixed026.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed026.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed026.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed026.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed026.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed026.S5T1

end
end


/- Source module: RootedSevenMixed026CanonicalT6 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed026.T6
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed026.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed026.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed026.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed026.Outside.forward g) (FacetUniverses.RootedSevenMixed026.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed026.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed026.cells i) (FacetUniverses.RootedSevenMixed026.cells (FacetUniverses.RootedSevenMixed026.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed026.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed026.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed026.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed026.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed026.cells
    (FacetUniverses.RootedSevenMixed026.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed026.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed026.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed026.Outside.forward g) (FacetUniverses.RootedSevenMixed026.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed026.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed026.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed026.cells generators
    FacetUniverses.RootedSevenMixed026.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed026.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed026.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed026.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed026.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed026.T6

end
end


/- Source module: RootedSevenMixed026Coverage -/
@[expose] public section

/-!
# Complete compatible-template coverage for RootedSevenMixed026

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSevenMixed026

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSevenMixed026

abbrev root : Fin FacetUniverses.RootedSevenMixed026.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 7 ↪ Fin 10 where
  toFun := ![0, 1, 2, 3, 4, 5, 6]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N7.templates 28)) =
      decodeCell (FacetUniverses.RootedSevenMixed026.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSevenMixed026.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [1]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed026.cells root 28 (fun a => a.size ≤ 5 ∨ a = .six 6) quota where
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
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed026.cells root 28
      (fun a => a.size ≤ 5 ∨ a = .six 6) (SevenFamilyActualEncoding.rowQuota 0 3 5 1) :=
  coverage _ (by
    intro k hk
    have hk' : k = 1 := by simpa [omittedTags] using hk
    rcases hk' with rfl <;> rfl)

end Papers.RationalityTen.RootedCoverage.RootedSevenMixed026

end
end


/- Source module: RootedSevenMixed027CanonicalS5T0 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed027.S5T0
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed027.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed027.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed027.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed027.Outside.forward g) (FacetUniverses.RootedSevenMixed027.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed027.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed027.cells i) (FacetUniverses.RootedSevenMixed027.cells (FacetUniverses.RootedSevenMixed027.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed027.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed027.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed027.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed027.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed027.cells
    (FacetUniverses.RootedSevenMixed027.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed027.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed027.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed027.Outside.forward g) (FacetUniverses.RootedSevenMixed027.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed027.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed027.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed027.cells generators
    FacetUniverses.RootedSevenMixed027.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed027.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed027.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed027.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed027.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed027.S5T0

end
end


/- Source module: RootedSevenMixed027CanonicalS5T1 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed027.S5T1
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed027.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed027.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed027.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed027.Outside.forward g) (FacetUniverses.RootedSevenMixed027.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed027.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed027.cells i) (FacetUniverses.RootedSevenMixed027.cells (FacetUniverses.RootedSevenMixed027.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed027.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed027.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed027.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed027.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed027.cells
    (FacetUniverses.RootedSevenMixed027.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed027.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed027.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed027.Outside.forward g) (FacetUniverses.RootedSevenMixed027.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed027.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed027.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed027.cells generators
    FacetUniverses.RootedSevenMixed027.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed027.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed027.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed027.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed027.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed027.S5T1

end
end


/- Source module: RootedSevenMixed027CanonicalT6 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed027.T6
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed027.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed027.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed027.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed027.Outside.forward g) (FacetUniverses.RootedSevenMixed027.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed027.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed027.cells i) (FacetUniverses.RootedSevenMixed027.cells (FacetUniverses.RootedSevenMixed027.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed027.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed027.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed027.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed027.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed027.cells
    (FacetUniverses.RootedSevenMixed027.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed027.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed027.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed027.Outside.forward g) (FacetUniverses.RootedSevenMixed027.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed027.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed027.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed027.cells generators
    FacetUniverses.RootedSevenMixed027.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed027.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed027.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed027.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed027.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed027.T6

end
end


/- Source module: RootedSevenMixed027Coverage -/
@[expose] public section

/-!
# Complete compatible-template coverage for RootedSevenMixed027

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSevenMixed027

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSevenMixed027

abbrev root : Fin FacetUniverses.RootedSevenMixed027.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 7 ↪ Fin 10 where
  toFun := ![0, 1, 2, 3, 4, 5, 6]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N7.templates 29)) =
      decodeCell (FacetUniverses.RootedSevenMixed027.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSevenMixed027.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [1]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed027.cells root 29 (fun a => a.size ≤ 5 ∨ a = .six 6) quota where
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
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed027.cells root 29
      (fun a => a.size ≤ 5 ∨ a = .six 6) (SevenFamilyActualEncoding.rowQuota 0 4 4 1) :=
  coverage _ (by
    intro k hk
    have hk' : k = 1 := by simpa [omittedTags] using hk
    rcases hk' with rfl <;> rfl)

end Papers.RationalityTen.RootedCoverage.RootedSevenMixed027

end
end


/- Source module: RootedSevenMixed028CanonicalS5T0 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed028.S5T0
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed028.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed028.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed028.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed028.Outside.forward g) (FacetUniverses.RootedSevenMixed028.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed028.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed028.cells i) (FacetUniverses.RootedSevenMixed028.cells (FacetUniverses.RootedSevenMixed028.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed028.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed028.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed028.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed028.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed028.cells
    (FacetUniverses.RootedSevenMixed028.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed028.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed028.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed028.Outside.forward g) (FacetUniverses.RootedSevenMixed028.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed028.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed028.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed028.cells generators
    FacetUniverses.RootedSevenMixed028.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed028.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed028.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed028.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed028.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed028.S5T0

end
end


/- Source module: RootedSevenMixed028CanonicalS5T1 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed028.S5T1
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed028.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed028.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed028.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed028.Outside.forward g) (FacetUniverses.RootedSevenMixed028.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed028.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed028.cells i) (FacetUniverses.RootedSevenMixed028.cells (FacetUniverses.RootedSevenMixed028.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed028.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed028.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed028.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed028.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed028.cells
    (FacetUniverses.RootedSevenMixed028.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed028.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed028.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed028.Outside.forward g) (FacetUniverses.RootedSevenMixed028.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed028.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed028.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed028.cells generators
    FacetUniverses.RootedSevenMixed028.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed028.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed028.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed028.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed028.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed028.S5T1

end
end


/- Source module: RootedSevenMixed028CanonicalT6 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed028.T6
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed028.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed028.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed028.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed028.Outside.forward g) (FacetUniverses.RootedSevenMixed028.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed028.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed028.cells i) (FacetUniverses.RootedSevenMixed028.cells (FacetUniverses.RootedSevenMixed028.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed028.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed028.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed028.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed028.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed028.cells
    (FacetUniverses.RootedSevenMixed028.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed028.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed028.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed028.Outside.forward g) (FacetUniverses.RootedSevenMixed028.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed028.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed028.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed028.cells generators
    FacetUniverses.RootedSevenMixed028.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed028.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed028.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed028.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed028.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed028.T6

end
end


/- Source module: RootedSevenMixed028Coverage -/
@[expose] public section

/-!
# Complete compatible-template coverage for RootedSevenMixed028

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSevenMixed028

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSevenMixed028

abbrev root : Fin FacetUniverses.RootedSevenMixed028.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 7 ↪ Fin 10 where
  toFun := ![0, 1, 2, 3, 4, 5, 6]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N7.templates 31)) =
      decodeCell (FacetUniverses.RootedSevenMixed028.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSevenMixed028.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [1]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed028.cells root 31 (fun a => a.size ≤ 5 ∨ a = .six 6) quota where
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
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed028.cells root 31
      (fun a => a.size ≤ 5 ∨ a = .six 6) (SevenFamilyActualEncoding.rowQuota 0 4 4 1) :=
  coverage _ (by
    intro k hk
    have hk' : k = 1 := by simpa [omittedTags] using hk
    rcases hk' with rfl <;> rfl)

end Papers.RationalityTen.RootedCoverage.RootedSevenMixed028

end
end


/- Source module: RootedSevenMixed029CanonicalS5T0 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed029.S5T0
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed029.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed029.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed029.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed029.Outside.forward g) (FacetUniverses.RootedSevenMixed029.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed029.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed029.cells i) (FacetUniverses.RootedSevenMixed029.cells (FacetUniverses.RootedSevenMixed029.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed029.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed029.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed029.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed029.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed029.cells
    (FacetUniverses.RootedSevenMixed029.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed029.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed029.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed029.Outside.forward g) (FacetUniverses.RootedSevenMixed029.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed029.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed029.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed029.cells generators
    FacetUniverses.RootedSevenMixed029.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed029.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed029.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed029.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed029.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed029.S5T0

end
end


/- Source module: RootedSevenMixed029CanonicalS5T1 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed029.S5T1
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed029.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed029.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed029.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed029.Outside.forward g) (FacetUniverses.RootedSevenMixed029.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed029.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed029.cells i) (FacetUniverses.RootedSevenMixed029.cells (FacetUniverses.RootedSevenMixed029.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed029.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed029.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed029.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed029.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed029.cells
    (FacetUniverses.RootedSevenMixed029.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed029.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed029.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed029.Outside.forward g) (FacetUniverses.RootedSevenMixed029.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed029.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed029.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed029.cells generators
    FacetUniverses.RootedSevenMixed029.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed029.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed029.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed029.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed029.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed029.S5T1

end
end


/- Source module: RootedSevenMixed029CanonicalT6 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed029.T6
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed029.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed029.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed029.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed029.Outside.forward g) (FacetUniverses.RootedSevenMixed029.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed029.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed029.cells i) (FacetUniverses.RootedSevenMixed029.cells (FacetUniverses.RootedSevenMixed029.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed029.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed029.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed029.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed029.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed029.cells
    (FacetUniverses.RootedSevenMixed029.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed029.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed029.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed029.Outside.forward g) (FacetUniverses.RootedSevenMixed029.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed029.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed029.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed029.cells generators
    FacetUniverses.RootedSevenMixed029.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed029.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed029.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed029.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed029.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed029.T6

end
end

