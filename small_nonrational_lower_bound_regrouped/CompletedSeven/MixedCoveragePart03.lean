module

public import CompletedSeven.MixedCoveragePart02
public import DecodedCellBounds
public import FinitePolygonTemplates
public import KindedRootedFacetCoverage
public import OutsidePlacementSemantics
public import RootedSevenMixed018CanonicalS5T0Finite
public import RootedSevenMixed018CanonicalS5T0Placement
public import RootedSevenMixed018CanonicalS5T1Finite
public import RootedSevenMixed018CanonicalS5T1Placement
public import RootedSevenMixed018CanonicalT6Finite
public import RootedSevenMixed018CanonicalT6Placement
public import RootedSevenMixed018Outside
public import RootedSevenMixed019CanonicalS5T0Finite
public import RootedSevenMixed019CanonicalS5T0Placement
public import RootedSevenMixed019CanonicalS5T1Finite
public import RootedSevenMixed019CanonicalS5T1Placement
public import RootedSevenMixed019CanonicalT6Finite
public import RootedSevenMixed019CanonicalT6Placement
public import RootedSevenMixed019Outside
public import RootedSevenMixed020CanonicalS5T0Finite
public import RootedSevenMixed020CanonicalS5T0Placement
public import RootedSevenMixed020CanonicalS5T1Finite
public import RootedSevenMixed020CanonicalS5T1Placement
public import RootedSevenMixed020CanonicalT6Finite
public import RootedSevenMixed020CanonicalT6Placement
public import RootedSevenMixed020Outside
public import RootedSevenMixed021CanonicalS5T0Finite
public import RootedSevenMixed021CanonicalS5T0Placement
public import RootedSevenMixed021CanonicalS5T1Finite
public import RootedSevenMixed021CanonicalS5T1Placement
public import RootedSevenMixed021CanonicalT6Finite
public import RootedSevenMixed021CanonicalT6Placement
public import RootedSevenMixed021Outside
public import RootedSevenMixed022CanonicalS5T0Finite
public import RootedSevenMixed022CanonicalS5T0Placement
public import RootedSevenMixed022CanonicalS5T1Finite
public import RootedSevenMixed022CanonicalS5T1Placement
public import RootedSevenMixed022CanonicalT6Finite
public import RootedSevenMixed022CanonicalT6Placement
public import RootedSevenMixed022Outside
public import RootedSevenMixed023CanonicalS5T0Finite
public import RootedSevenMixed023CanonicalS5T0Placement
public import RootedSevenMixed023CanonicalS5T1Finite
public import RootedSevenMixed023CanonicalS5T1Placement
public import RootedSevenMixed023CanonicalT6Finite
public import RootedSevenMixed023CanonicalT6Placement
public import RootedSevenMixed023Outside
public import SevenFamilyActualEncoding
public import SymmetricRootedFacetCoverage

/-! Geometric placement coverage; the following proof bodies are unchanged. -/

/- Source module: RootedSevenMixed017Coverage -/
@[expose] public section

/-!
# Complete compatible-template coverage for RootedSevenMixed017

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSevenMixed017

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSevenMixed017

abbrev root : Fin FacetUniverses.RootedSevenMixed017.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 7 ↪ Fin 10 where
  toFun := ![0, 1, 2, 3, 4, 5, 6]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N7.templates 16)) =
      decodeCell (FacetUniverses.RootedSevenMixed017.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSevenMixed017.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [1]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed017.cells root 16 (fun a => a.size ≤ 5 ∨ a = .six 6) quota where
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
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed017.cells root 16
      (fun a => a.size ≤ 5 ∨ a = .six 6) (SevenFamilyActualEncoding.rowQuota 0 2 6 1) :=
  coverage _ (by
    intro k hk
    have hk' : k = 1 := by simpa [omittedTags] using hk
    rcases hk' with rfl <;> rfl)

end Papers.RationalityTen.RootedCoverage.RootedSevenMixed017

end
end


/- Source module: RootedSevenMixed018CanonicalS5T0 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed018.S5T0
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed018.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed018.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed018.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed018.Outside.forward g) (FacetUniverses.RootedSevenMixed018.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed018.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed018.cells i) (FacetUniverses.RootedSevenMixed018.cells (FacetUniverses.RootedSevenMixed018.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed018.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed018.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed018.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed018.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed018.cells
    (FacetUniverses.RootedSevenMixed018.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed018.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed018.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed018.Outside.forward g) (FacetUniverses.RootedSevenMixed018.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed018.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed018.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed018.cells generators
    FacetUniverses.RootedSevenMixed018.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed018.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed018.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed018.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed018.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed018.S5T0

end
end


/- Source module: RootedSevenMixed018CanonicalS5T1 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed018.S5T1
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed018.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed018.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed018.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed018.Outside.forward g) (FacetUniverses.RootedSevenMixed018.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed018.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed018.cells i) (FacetUniverses.RootedSevenMixed018.cells (FacetUniverses.RootedSevenMixed018.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed018.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed018.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed018.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed018.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed018.cells
    (FacetUniverses.RootedSevenMixed018.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed018.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed018.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed018.Outside.forward g) (FacetUniverses.RootedSevenMixed018.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed018.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed018.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed018.cells generators
    FacetUniverses.RootedSevenMixed018.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed018.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed018.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed018.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed018.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed018.S5T1

end
end


/- Source module: RootedSevenMixed018CanonicalT6 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed018.T6
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed018.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed018.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed018.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed018.Outside.forward g) (FacetUniverses.RootedSevenMixed018.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed018.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed018.cells i) (FacetUniverses.RootedSevenMixed018.cells (FacetUniverses.RootedSevenMixed018.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed018.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed018.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed018.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed018.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed018.cells
    (FacetUniverses.RootedSevenMixed018.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed018.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed018.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed018.Outside.forward g) (FacetUniverses.RootedSevenMixed018.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed018.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed018.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed018.cells generators
    FacetUniverses.RootedSevenMixed018.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed018.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed018.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed018.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed018.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed018.T6

end
end


/- Source module: RootedSevenMixed018Coverage -/
@[expose] public section

/-!
# Complete compatible-template coverage for RootedSevenMixed018

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSevenMixed018

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSevenMixed018

abbrev root : Fin FacetUniverses.RootedSevenMixed018.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 7 ↪ Fin 10 where
  toFun := ![0, 1, 2, 3, 4, 5, 6]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N7.templates 18)) =
      decodeCell (FacetUniverses.RootedSevenMixed018.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSevenMixed018.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [1]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed018.cells root 18 (fun a => a.size ≤ 5 ∨ a = .six 6) quota where
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
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed018.cells root 18
      (fun a => a.size ≤ 5 ∨ a = .six 6) (SevenFamilyActualEncoding.rowQuota 0 3 5 1) :=
  coverage _ (by
    intro k hk
    have hk' : k = 1 := by simpa [omittedTags] using hk
    rcases hk' with rfl <;> rfl)

end Papers.RationalityTen.RootedCoverage.RootedSevenMixed018

end
end


/- Source module: RootedSevenMixed019CanonicalS5T0 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed019.S5T0
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed019.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed019.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed019.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed019.Outside.forward g) (FacetUniverses.RootedSevenMixed019.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed019.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed019.cells i) (FacetUniverses.RootedSevenMixed019.cells (FacetUniverses.RootedSevenMixed019.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed019.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed019.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed019.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed019.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed019.cells
    (FacetUniverses.RootedSevenMixed019.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed019.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed019.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed019.Outside.forward g) (FacetUniverses.RootedSevenMixed019.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed019.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed019.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed019.cells generators
    FacetUniverses.RootedSevenMixed019.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed019.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed019.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed019.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed019.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed019.S5T0

end
end


/- Source module: RootedSevenMixed019CanonicalS5T1 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed019.S5T1
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed019.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed019.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed019.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed019.Outside.forward g) (FacetUniverses.RootedSevenMixed019.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed019.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed019.cells i) (FacetUniverses.RootedSevenMixed019.cells (FacetUniverses.RootedSevenMixed019.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed019.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed019.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed019.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed019.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed019.cells
    (FacetUniverses.RootedSevenMixed019.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed019.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed019.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed019.Outside.forward g) (FacetUniverses.RootedSevenMixed019.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed019.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed019.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed019.cells generators
    FacetUniverses.RootedSevenMixed019.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed019.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed019.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed019.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed019.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed019.S5T1

end
end


/- Source module: RootedSevenMixed019CanonicalT6 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed019.T6
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed019.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed019.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed019.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed019.Outside.forward g) (FacetUniverses.RootedSevenMixed019.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed019.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed019.cells i) (FacetUniverses.RootedSevenMixed019.cells (FacetUniverses.RootedSevenMixed019.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed019.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed019.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed019.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed019.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed019.cells
    (FacetUniverses.RootedSevenMixed019.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed019.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed019.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed019.Outside.forward g) (FacetUniverses.RootedSevenMixed019.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed019.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed019.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed019.cells generators
    FacetUniverses.RootedSevenMixed019.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed019.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed019.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed019.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed019.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed019.T6

end
end


/- Source module: RootedSevenMixed019Coverage -/
@[expose] public section

/-!
# Complete compatible-template coverage for RootedSevenMixed019

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSevenMixed019

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSevenMixed019

abbrev root : Fin FacetUniverses.RootedSevenMixed019.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 7 ↪ Fin 10 where
  toFun := ![0, 1, 2, 3, 4, 5, 6]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N7.templates 19)) =
      decodeCell (FacetUniverses.RootedSevenMixed019.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSevenMixed019.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [1]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed019.cells root 19 (fun a => a.size ≤ 5 ∨ a = .six 6) quota where
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
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed019.cells root 19
      (fun a => a.size ≤ 5 ∨ a = .six 6) (SevenFamilyActualEncoding.rowQuota 0 3 5 1) :=
  coverage _ (by
    intro k hk
    have hk' : k = 1 := by simpa [omittedTags] using hk
    rcases hk' with rfl <;> rfl)

end Papers.RationalityTen.RootedCoverage.RootedSevenMixed019

end
end


/- Source module: RootedSevenMixed020CanonicalS5T0 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed020.S5T0
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed020.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed020.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed020.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed020.Outside.forward g) (FacetUniverses.RootedSevenMixed020.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed020.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed020.cells i) (FacetUniverses.RootedSevenMixed020.cells (FacetUniverses.RootedSevenMixed020.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed020.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed020.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed020.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed020.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed020.cells
    (FacetUniverses.RootedSevenMixed020.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed020.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed020.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed020.Outside.forward g) (FacetUniverses.RootedSevenMixed020.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed020.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed020.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed020.cells generators
    FacetUniverses.RootedSevenMixed020.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed020.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed020.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed020.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed020.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed020.S5T0

end
end


/- Source module: RootedSevenMixed020CanonicalS5T1 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed020.S5T1
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed020.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed020.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed020.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed020.Outside.forward g) (FacetUniverses.RootedSevenMixed020.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed020.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed020.cells i) (FacetUniverses.RootedSevenMixed020.cells (FacetUniverses.RootedSevenMixed020.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed020.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed020.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed020.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed020.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed020.cells
    (FacetUniverses.RootedSevenMixed020.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed020.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed020.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed020.Outside.forward g) (FacetUniverses.RootedSevenMixed020.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed020.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed020.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed020.cells generators
    FacetUniverses.RootedSevenMixed020.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed020.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed020.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed020.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed020.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed020.S5T1

end
end


/- Source module: RootedSevenMixed020CanonicalT6 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed020.T6
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed020.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed020.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed020.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed020.Outside.forward g) (FacetUniverses.RootedSevenMixed020.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed020.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed020.cells i) (FacetUniverses.RootedSevenMixed020.cells (FacetUniverses.RootedSevenMixed020.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed020.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed020.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed020.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed020.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed020.cells
    (FacetUniverses.RootedSevenMixed020.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed020.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed020.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed020.Outside.forward g) (FacetUniverses.RootedSevenMixed020.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed020.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed020.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed020.cells generators
    FacetUniverses.RootedSevenMixed020.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed020.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed020.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed020.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed020.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed020.T6

end
end


/- Source module: RootedSevenMixed020Coverage -/
@[expose] public section

/-!
# Complete compatible-template coverage for RootedSevenMixed020

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSevenMixed020

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSevenMixed020

abbrev root : Fin FacetUniverses.RootedSevenMixed020.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 7 ↪ Fin 10 where
  toFun := ![0, 1, 2, 3, 4, 5, 6]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N7.templates 20)) =
      decodeCell (FacetUniverses.RootedSevenMixed020.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSevenMixed020.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [1]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed020.cells root 20 (fun a => a.size ≤ 5 ∨ a = .six 6) quota where
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
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed020.cells root 20
      (fun a => a.size ≤ 5 ∨ a = .six 6) (SevenFamilyActualEncoding.rowQuota 0 3 5 1) :=
  coverage _ (by
    intro k hk
    have hk' : k = 1 := by simpa [omittedTags] using hk
    rcases hk' with rfl <;> rfl)

end Papers.RationalityTen.RootedCoverage.RootedSevenMixed020

end
end


/- Source module: RootedSevenMixed021CanonicalS5T0 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed021.S5T0
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed021.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed021.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed021.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed021.Outside.forward g) (FacetUniverses.RootedSevenMixed021.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed021.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed021.cells i) (FacetUniverses.RootedSevenMixed021.cells (FacetUniverses.RootedSevenMixed021.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed021.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed021.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed021.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed021.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed021.cells
    (FacetUniverses.RootedSevenMixed021.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed021.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed021.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed021.Outside.forward g) (FacetUniverses.RootedSevenMixed021.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed021.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed021.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed021.cells generators
    FacetUniverses.RootedSevenMixed021.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed021.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed021.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed021.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed021.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed021.S5T0

end
end


/- Source module: RootedSevenMixed021CanonicalS5T1 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed021.S5T1
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed021.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed021.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed021.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed021.Outside.forward g) (FacetUniverses.RootedSevenMixed021.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed021.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed021.cells i) (FacetUniverses.RootedSevenMixed021.cells (FacetUniverses.RootedSevenMixed021.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed021.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed021.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed021.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed021.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed021.cells
    (FacetUniverses.RootedSevenMixed021.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed021.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed021.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed021.Outside.forward g) (FacetUniverses.RootedSevenMixed021.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed021.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed021.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed021.cells generators
    FacetUniverses.RootedSevenMixed021.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed021.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed021.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed021.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed021.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed021.S5T1

end
end


/- Source module: RootedSevenMixed021CanonicalT6 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed021.T6
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed021.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed021.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed021.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed021.Outside.forward g) (FacetUniverses.RootedSevenMixed021.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed021.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed021.cells i) (FacetUniverses.RootedSevenMixed021.cells (FacetUniverses.RootedSevenMixed021.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed021.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed021.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed021.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed021.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed021.cells
    (FacetUniverses.RootedSevenMixed021.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed021.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed021.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed021.Outside.forward g) (FacetUniverses.RootedSevenMixed021.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed021.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed021.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed021.cells generators
    FacetUniverses.RootedSevenMixed021.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed021.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed021.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed021.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed021.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed021.T6

end
end


/- Source module: RootedSevenMixed021Coverage -/
@[expose] public section

/-!
# Complete compatible-template coverage for RootedSevenMixed021

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSevenMixed021

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSevenMixed021

abbrev root : Fin FacetUniverses.RootedSevenMixed021.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 7 ↪ Fin 10 where
  toFun := ![0, 1, 2, 3, 4, 5, 6]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N7.templates 21)) =
      decodeCell (FacetUniverses.RootedSevenMixed021.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSevenMixed021.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [1]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed021.cells root 21 (fun a => a.size ≤ 5 ∨ a = .six 6) quota where
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
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed021.cells root 21
      (fun a => a.size ≤ 5 ∨ a = .six 6) (SevenFamilyActualEncoding.rowQuota 0 3 5 1) :=
  coverage _ (by
    intro k hk
    have hk' : k = 1 := by simpa [omittedTags] using hk
    rcases hk' with rfl <;> rfl)

end Papers.RationalityTen.RootedCoverage.RootedSevenMixed021

end
end


/- Source module: RootedSevenMixed022CanonicalS5T0 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed022.S5T0
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed022.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed022.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed022.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed022.Outside.forward g) (FacetUniverses.RootedSevenMixed022.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed022.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed022.cells i) (FacetUniverses.RootedSevenMixed022.cells (FacetUniverses.RootedSevenMixed022.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed022.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed022.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed022.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed022.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed022.cells
    (FacetUniverses.RootedSevenMixed022.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed022.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed022.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed022.Outside.forward g) (FacetUniverses.RootedSevenMixed022.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed022.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed022.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed022.cells generators
    FacetUniverses.RootedSevenMixed022.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed022.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed022.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed022.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed022.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed022.S5T0

end
end


/- Source module: RootedSevenMixed022CanonicalS5T1 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed022.S5T1
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed022.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed022.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed022.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed022.Outside.forward g) (FacetUniverses.RootedSevenMixed022.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed022.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed022.cells i) (FacetUniverses.RootedSevenMixed022.cells (FacetUniverses.RootedSevenMixed022.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed022.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed022.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed022.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed022.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed022.cells
    (FacetUniverses.RootedSevenMixed022.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed022.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed022.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed022.Outside.forward g) (FacetUniverses.RootedSevenMixed022.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed022.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed022.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed022.cells generators
    FacetUniverses.RootedSevenMixed022.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed022.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed022.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed022.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed022.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed022.S5T1

end
end


/- Source module: RootedSevenMixed022CanonicalT6 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed022.T6
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed022.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed022.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed022.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed022.Outside.forward g) (FacetUniverses.RootedSevenMixed022.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed022.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed022.cells i) (FacetUniverses.RootedSevenMixed022.cells (FacetUniverses.RootedSevenMixed022.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed022.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed022.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed022.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed022.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed022.cells
    (FacetUniverses.RootedSevenMixed022.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed022.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed022.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed022.Outside.forward g) (FacetUniverses.RootedSevenMixed022.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed022.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed022.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed022.cells generators
    FacetUniverses.RootedSevenMixed022.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed022.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed022.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed022.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed022.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed022.T6

end
end


/- Source module: RootedSevenMixed022Coverage -/
@[expose] public section

/-!
# Complete compatible-template coverage for RootedSevenMixed022

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSevenMixed022

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSevenMixed022

abbrev root : Fin FacetUniverses.RootedSevenMixed022.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 7 ↪ Fin 10 where
  toFun := ![0, 1, 2, 3, 4, 5, 6]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N7.templates 23)) =
      decodeCell (FacetUniverses.RootedSevenMixed022.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSevenMixed022.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [1]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed022.cells root 23 (fun a => a.size ≤ 5 ∨ a = .six 6) quota where
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
    SevenFamilyActualEncoding.Coverage FacetUniverses.RootedSevenMixed022.cells root 23
      (fun a => a.size ≤ 5 ∨ a = .six 6) (SevenFamilyActualEncoding.rowQuota 0 3 5 1) :=
  coverage _ (by
    intro k hk
    have hk' : k = 1 := by simpa [omittedTags] using hk
    rcases hk' with rfl <;> rfl)

end Papers.RationalityTen.RootedCoverage.RootedSevenMixed022

end
end


/- Source module: RootedSevenMixed023CanonicalS5T0 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed023.S5T0
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed023.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed023.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed023.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed023.Outside.forward g) (FacetUniverses.RootedSevenMixed023.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed023.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed023.cells i) (FacetUniverses.RootedSevenMixed023.cells (FacetUniverses.RootedSevenMixed023.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed023.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed023.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed023.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed023.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed023.cells
    (FacetUniverses.RootedSevenMixed023.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed023.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed023.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed023.Outside.forward g) (FacetUniverses.RootedSevenMixed023.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed023.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed023.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed023.cells generators
    FacetUniverses.RootedSevenMixed023.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed023.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed023.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed023.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed023.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed023.S5T0

end
end


/- Source module: RootedSevenMixed023CanonicalS5T1 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed023.S5T1
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed023.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed023.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed023.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed023.Outside.forward g) (FacetUniverses.RootedSevenMixed023.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed023.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed023.cells i) (FacetUniverses.RootedSevenMixed023.cells (FacetUniverses.RootedSevenMixed023.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed023.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed023.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed023.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed023.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed023.cells
    (FacetUniverses.RootedSevenMixed023.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed023.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed023.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed023.Outside.forward g) (FacetUniverses.RootedSevenMixed023.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed023.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed023.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed023.cells generators
    FacetUniverses.RootedSevenMixed023.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed023.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed023.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed023.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed023.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed023.S5T1

end
end


/- Source module: RootedSevenMixed023CanonicalT6 -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed023.T6
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
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed023.Outside.vertexCode root.vertices (raw i) = true := by
  simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
theorem generator_checks (g : Fin FacetUniverses.RootedSevenMixed023.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSevenMixed023.cellCount) :
    RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSevenMixed023.Outside.forward g) (FacetUniverses.RootedSevenMixed023.Outside.forward g) i = true ∧
    RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSevenMixed023.Outside.vertexCode g))
      (FacetUniverses.RootedSevenMixed023.cells i) (FacetUniverses.RootedSevenMixed023.cells (FacetUniverses.RootedSevenMixed023.Outside.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSevenMixed023.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSevenMixed023.Outside.cell_checked g i

noncomputable def generators (g : Fin FacetUniverses.RootedSevenMixed023.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed023.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSevenMixed023.cells
    (FacetUniverses.RootedSevenMixed023.Outside.vertexCode g) (FacetUniverses.RootedSevenMixed023.Outside.vertexCode g)
    (FacetUniverses.RootedSevenMixed023.Outside.vertex_checks g) (FacetUniverses.RootedSevenMixed023.Outside.forward g) (FacetUniverses.RootedSevenMixed023.Outside.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSevenMixed023.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSevenMixed023.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSevenMixed023.cells generators
    FacetUniverses.RootedSevenMixed023.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSevenMixed023.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSevenMixed023.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSevenMixed023.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSevenMixed023.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed023.T6

end
end

