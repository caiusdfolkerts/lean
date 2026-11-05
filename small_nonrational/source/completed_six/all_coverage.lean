module
public import RootedSixBase00Generators
public import RootedSixBase00OutsideData
public import BoundaryGeneratorFrames
public import RootedSixBase00CanonicalS4T0Placement
public import KindedRootedFacetCoverage
public import FinitePolygonTemplates
public import SymmetricRootedFacetCoverage
public import OutsidePlacementSemantics
public import RootedSixBase00CanonicalS5T0Placement
public import RootedSixBase00CanonicalS5T1Placement
public import RootedSixBase00CanonicalT0Placement
public import RootedSixBase00CanonicalT1Placement
public import RootedSixBase00CanonicalT2Placement
public import RootedSixBase00CanonicalT3Placement
public import RootedSixBase00CanonicalT5Placement
public import RootedSixBase00CanonicalT6Placement
public import Consolidated.SixActualAssembly
public import Mathlib.Tactic.FinCases
public import RootedSixBase01Generators
public import RootedSixBase01OutsideData
public import RootedSixBase01CanonicalS4T0Placement
public import RootedSixBase01CanonicalS5T0Placement
public import RootedSixBase01CanonicalS5T1Placement
public import RootedSixBase01CanonicalT1Placement
public import RootedSixBase01CanonicalT2Placement
public import RootedSixBase01CanonicalT3Placement
public import RootedSixBase01CanonicalT5Placement
public import RootedSixBase01CanonicalT6Placement
public import RootedSixBase02Generators
public import RootedSixBase02OutsideData
public import RootedSixBase02CanonicalS4T0Placement
public import RootedSixBase02CanonicalS5T0Placement
public import RootedSixBase02CanonicalS5T1Placement
public import RootedSixBase02CanonicalT2Placement
public import RootedSixBase02CanonicalT3Placement
public import RootedSixBase02CanonicalT5Placement
public import RootedSixBase02CanonicalT6Placement
public import RootedSixBase03Generators
public import RootedSixBase03OutsideData
public import RootedSixBase03CanonicalS4T0Placement
public import RootedSixBase03CanonicalS5T0Placement
public import RootedSixBase03CanonicalS5T1Placement
public import RootedSixBase03CanonicalT2Placement
public import RootedSixBase03CanonicalT3Placement
public import RootedSixBase03CanonicalT6Placement
public import RootedSixBase04Generators
public import RootedSixBase04OutsideData
public import RootedSixBase04CanonicalS4T0Placement
public import RootedSixBase04CanonicalS5T0Placement
public import RootedSixBase04CanonicalS5T1Placement
public import RootedSixBase04CanonicalT2Placement
public import RootedSixBase04CanonicalT6Placement
public import RootedSixExtra00Generators
public import RootedSixExtra00OutsideData
public import RootedSixExtra00CanonicalS4T0Placement
public import RootedSixExtra00CanonicalS5T0Placement
public import RootedSixExtra00CanonicalS5T1Placement
public import RootedSixExtra00CanonicalT4Placement
public import RootedSixExtra00CanonicalT5Placement
public import RootedSixExtra00CanonicalT6Placement
public import RootedSixExtra01Generators
public import RootedSixExtra01OutsideData
public import RootedSixExtra01CanonicalS4T0Placement
public import RootedSixExtra01CanonicalS5T0Placement
public import RootedSixExtra01CanonicalS5T1Placement
public import RootedSixExtra01CanonicalT4Placement
public import RootedSixExtra01CanonicalT6Placement
public import RootedSixExtra02Generators
public import RootedSixExtra02OutsideData
public import RootedSixExtra02CanonicalS4T0Placement
public import RootedSixExtra02CanonicalS5T0Placement
public import RootedSixExtra02CanonicalS5T1Placement
public import RootedSixExtra02CanonicalT2Placement
public import RootedSixExtra02CanonicalT4Placement
public import RootedSixExtra02CanonicalT5Placement
public import RootedSixExtra02CanonicalT6Placement
public import RootedSixExtra03Generators
public import RootedSixExtra03OutsideData
public import RootedSixExtra03CanonicalS4T0Placement
public import RootedSixExtra03CanonicalS5T0Placement
public import RootedSixExtra03CanonicalS5T1Placement
public import RootedSixExtra03CanonicalT4Placement
public import RootedSixExtra03CanonicalT6Placement
public import RootedSixExtra04Generators
public import RootedSixExtra04OutsideData
public import RootedSixExtra04CanonicalS4T0Placement
public import RootedSixExtra04CanonicalS5T0Placement
public import RootedSixExtra04CanonicalS5T1Placement
public import RootedSixExtra04CanonicalT4Placement
public import RootedSixExtra04CanonicalT6Placement
public import RootedSixExtra05Generators
public import RootedSixExtra05OutsideData
public import RootedSixExtra05CanonicalS4T0Placement
public import RootedSixExtra05CanonicalS5T0Placement
public import RootedSixExtra05CanonicalS5T1Placement
public import RootedSixExtra05CanonicalT4Placement
public import RootedSixExtra05CanonicalT6Placement
public import RootedSixExtra06Generators
public import RootedSixExtra06OutsideData
public import RootedSixExtra06CanonicalS4T0Placement
public import RootedSixExtra06CanonicalS5T0Placement
public import RootedSixExtra06CanonicalS5T1Placement
public import RootedSixExtra06CanonicalT4Placement

/-! Complete six-facet coverage. Source module identities are recorded below. -/

section SourcePart0
/- Original module: RootedSixBase00CoverageFrames. -/

@[expose] public section

/-! The outside generators are taken from the complete checked generator
family. Their vertex codes agree with the independently checked placement
normalizers. No packed cell-map equality is an assumption. -/

noncomputable section
namespace Papers.RationalityTen.RootedCoverageFrames.RootedSixBase00

def generator (g : Fin FacetUniverses.RootedSixBase00.Outside.generatorCount) :
    Fin FacetUniverses.RootedSixBase00.Generators.generatorCount :=
  ⟨g.val, Nat.lt_of_lt_of_le g.isLt (by decide +kernel)⟩

theorem vertex_code (g : Fin FacetUniverses.RootedSixBase00.Outside.generatorCount) :
    FacetUniverses.RootedSixBase00.Generators.vertexCode (generator g) = FacetUniverses.RootedSixBase00.Outside.vertexCode g := by
  have h : ∀ g : Fin FacetUniverses.RootedSixBase00.Outside.generatorCount,
      FacetUniverses.RootedSixBase00.Generators.vertexCode (generator g) = FacetUniverses.RootedSixBase00.Outside.vertexCode g := by
    decide +kernel
  exact h g

theorem generator_check (g : Fin FacetUniverses.RootedSixBase00.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSixBase00.cellCount) :
    (RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSixBase00.Generators.forward (generator g))
      (FacetUniverses.RootedSixBase00.Generators.inverse (generator g)) i &&
      RawGraphGrowthFrames.cellRelabelCheck
        (TenGraphEdges.vertexMap (FacetUniverses.RootedSixBase00.Generators.vertexCode (generator g)))
        (FacetUniverses.RootedSixBase00.cells i)
        (FacetUniverses.RootedSixBase00.cells (FacetUniverses.RootedSixBase00.Generators.forward (generator g) i))) = true := by
  simpa only [FacetUniverses.RootedSixBase00.Generators.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSixBase00.Generators.cell_checked (generator g) i

def frame (g : Fin FacetUniverses.RootedSixBase00.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase00.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSixBase00.cells
    (FacetUniverses.RootedSixBase00.Generators.vertexCode (generator g))
    (FacetUniverses.RootedSixBase00.Generators.vertexInverseCode (generator g))
    (FacetUniverses.RootedSixBase00.Generators.vertex_checks (generator g))
    (FacetUniverses.RootedSixBase00.Generators.forward (generator g))
    (FacetUniverses.RootedSixBase00.Generators.inverse (generator g))
    (fun i => (Bool.and_eq_true_iff.mp (generator_check g i)).1)
    (fun i => (Bool.and_eq_true_iff.mp (generator_check g i)).2)

theorem frame_vertices (g : Fin FacetUniverses.RootedSixBase00.Outside.generatorCount) (v : Fin 10) :
    (frame g).vertices v = TenGraphEdges.vertexMap (FacetUniverses.RootedSixBase00.Outside.vertexCode g) v := by
  change TenGraphEdges.vertexMap (FacetUniverses.RootedSixBase00.Generators.vertexCode (generator g)) v = _
  rw [vertex_code]

end Papers.RationalityTen.RootedCoverageFrames.RootedSixBase00

end
end
end SourcePart0

section SourcePart1
/- Original module: RootedSixBase00CanonicalS4T0. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase00.S4T0
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N4.templates 0)
theorem template_exact : decodeTemplate 4 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 4 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 4 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase00.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase00.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase00.cells :=
  RootedCoverageFrames.RootedSixBase00.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase00.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase00.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase00.cells generators
    FacetUniverses.RootedSixBase00.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase00.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 4 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase00.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase00.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase00.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 4 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase00.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase00.S4T0

end
end
end SourcePart1

section SourcePart2
/- Original module: RootedSixBase00CanonicalS5T0. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase00.S5T0
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N5.templates 0)
theorem template_exact : decodeTemplate 5 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 5 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 5 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase00.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase00.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase00.cells :=
  RootedCoverageFrames.RootedSixBase00.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase00.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase00.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase00.cells generators
    FacetUniverses.RootedSixBase00.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase00.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase00.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase00.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase00.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase00.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase00.S5T0

end
end
end SourcePart2

section SourcePart3
/- Original module: RootedSixBase00CanonicalS5T1. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase00.S5T1
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N5.templates 1)
theorem template_exact : decodeTemplate 5 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 5 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 5 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase00.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase00.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase00.cells :=
  RootedCoverageFrames.RootedSixBase00.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase00.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase00.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase00.cells generators
    FacetUniverses.RootedSixBase00.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase00.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase00.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase00.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase00.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase00.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase00.S5T1

end
end
end SourcePart3

section SourcePart4
/- Original module: RootedSixBase00CanonicalT0. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase00.T0
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 0)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase00.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase00.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase00.cells :=
  RootedCoverageFrames.RootedSixBase00.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase00.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase00.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase00.cells generators
    FacetUniverses.RootedSixBase00.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase00.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase00.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase00.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase00.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase00.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase00.T0

end
end
end SourcePart4

section SourcePart5
/- Original module: RootedSixBase00CanonicalT1. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase00.T1
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 1)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase00.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase00.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase00.cells :=
  RootedCoverageFrames.RootedSixBase00.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase00.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase00.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase00.cells generators
    FacetUniverses.RootedSixBase00.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase00.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase00.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase00.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase00.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase00.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase00.T1

end
end
end SourcePart5

section SourcePart6
/- Original module: RootedSixBase00CanonicalT2. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase00.T2
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 2)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase00.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase00.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase00.cells :=
  RootedCoverageFrames.RootedSixBase00.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase00.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase00.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase00.cells generators
    FacetUniverses.RootedSixBase00.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase00.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase00.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase00.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase00.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase00.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase00.T2

end
end
end SourcePart6

section SourcePart7
/- Original module: RootedSixBase00CanonicalT3. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase00.T3
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 3)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase00.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase00.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase00.cells :=
  RootedCoverageFrames.RootedSixBase00.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase00.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase00.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase00.cells generators
    FacetUniverses.RootedSixBase00.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase00.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase00.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase00.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase00.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase00.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase00.T3

end
end
end SourcePart7

section SourcePart8
/- Original module: RootedSixBase00CanonicalT5. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase00.T5
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 5)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase00.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase00.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase00.cells :=
  RootedCoverageFrames.RootedSixBase00.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase00.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase00.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase00.cells generators
    FacetUniverses.RootedSixBase00.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase00.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase00.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase00.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase00.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase00.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase00.T5

end
end
end SourcePart8

section SourcePart9
/- Original module: RootedSixBase00CanonicalT6. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase00.T6
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 6)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase00.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase00.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase00.cells :=
  RootedCoverageFrames.RootedSixBase00.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase00.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase00.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase00.cells generators
    FacetUniverses.RootedSixBase00.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase00.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase00.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase00.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase00.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase00.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase00.T6

end
end
end SourcePart9

section SourcePart10
/- Original module: RootedSixBase00Coverage. -/

@[expose] public section

/-!
# Complete template coverage for the first rooted six-facet universe

Every compatible embedding of every positive-quota local facet type is
covered. The only omitted positive tag is 10, the pentagonal pyramid;
its quota must be zero for a row to use this universe. The independent
placement theorems retain the complete local boundary and the exact kind.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSixBase00

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSixBase00

abbrev root : Fin FacetUniverses.RootedSixBase00.cellCount := 0

/-- Current local labels map to the producer's original root labels. -/
def rootEmbedding : Fin 6 ↪ Fin 10 where
  toFun := ![0, 1, 2, 3, 4, 5]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N6.templates (RawEncoding.oldToCurrent 0))) =
      decodeCell (FacetUniverses.RootedSixBase00.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSixBase00.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the positive tags omitted from this candidate universe. -/
def omittedTags : List Nat := [10]

/-- The zero-quota condition is discharged from the literal numerical row.
All remaining local embeddings are supplied by the complete placement proofs. -/
def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SixFamilyActualEncoding.Coverage FacetUniverses.RootedSixBase00.cells root 0 quota where
  rootEmbedding := rootEmbedding
  rootCell := root_exact
  rootKind := root_kind
  complete := by
    intro a hpos f h
    cases a with
    | tetrahedron => exact S4T0.covers_exact f h
    | bipyramid => exact S5T0.covers_exact f h
    | squarePyramid => exact S5T1.covers_exact f h
    | six i =>
      fin_cases i
      · exact T0.covers_exact f h
      · exact T1.covers_exact f h
      · exact T2.covers_exact f h
      · exact T3.covers_exact f h
      · change 0 < quota 10 at hpos
        rw [hzero 10 (by decide +kernel)] at hpos
        omega
      · exact T5.covers_exact f h
      · exact T6.covers_exact f h

end Papers.RationalityTen.RootedCoverage.RootedSixBase00

end
end
end SourcePart10

section SourcePart11
/- Original module: RootedSixBase01CoverageFrames. -/

@[expose] public section

/-! The outside generators are taken from the complete checked generator
family. Their vertex codes agree with the independently checked placement
normalizers. No packed cell-map equality is an assumption. -/

noncomputable section
namespace Papers.RationalityTen.RootedCoverageFrames.RootedSixBase01

def generator (g : Fin FacetUniverses.RootedSixBase01.Outside.generatorCount) :
    Fin FacetUniverses.RootedSixBase01.Generators.generatorCount :=
  ⟨g.val, Nat.lt_of_lt_of_le g.isLt (by decide +kernel)⟩

theorem vertex_code (g : Fin FacetUniverses.RootedSixBase01.Outside.generatorCount) :
    FacetUniverses.RootedSixBase01.Generators.vertexCode (generator g) = FacetUniverses.RootedSixBase01.Outside.vertexCode g := by
  have h : ∀ g : Fin FacetUniverses.RootedSixBase01.Outside.generatorCount,
      FacetUniverses.RootedSixBase01.Generators.vertexCode (generator g) = FacetUniverses.RootedSixBase01.Outside.vertexCode g := by
    decide +kernel
  exact h g

theorem generator_check (g : Fin FacetUniverses.RootedSixBase01.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSixBase01.cellCount) :
    (RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSixBase01.Generators.forward (generator g))
      (FacetUniverses.RootedSixBase01.Generators.inverse (generator g)) i &&
      RawGraphGrowthFrames.cellRelabelCheck
        (TenGraphEdges.vertexMap (FacetUniverses.RootedSixBase01.Generators.vertexCode (generator g)))
        (FacetUniverses.RootedSixBase01.cells i)
        (FacetUniverses.RootedSixBase01.cells (FacetUniverses.RootedSixBase01.Generators.forward (generator g) i))) = true := by
  simpa only [FacetUniverses.RootedSixBase01.Generators.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSixBase01.Generators.cell_checked (generator g) i

def frame (g : Fin FacetUniverses.RootedSixBase01.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase01.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSixBase01.cells
    (FacetUniverses.RootedSixBase01.Generators.vertexCode (generator g))
    (FacetUniverses.RootedSixBase01.Generators.vertexInverseCode (generator g))
    (FacetUniverses.RootedSixBase01.Generators.vertex_checks (generator g))
    (FacetUniverses.RootedSixBase01.Generators.forward (generator g))
    (FacetUniverses.RootedSixBase01.Generators.inverse (generator g))
    (fun i => (Bool.and_eq_true_iff.mp (generator_check g i)).1)
    (fun i => (Bool.and_eq_true_iff.mp (generator_check g i)).2)

theorem frame_vertices (g : Fin FacetUniverses.RootedSixBase01.Outside.generatorCount) (v : Fin 10) :
    (frame g).vertices v = TenGraphEdges.vertexMap (FacetUniverses.RootedSixBase01.Outside.vertexCode g) v := by
  change TenGraphEdges.vertexMap (FacetUniverses.RootedSixBase01.Generators.vertexCode (generator g)) v = _
  rw [vertex_code]

end Papers.RationalityTen.RootedCoverageFrames.RootedSixBase01

end
end
end SourcePart11

section SourcePart12
/- Original module: RootedSixBase01CanonicalS4T0. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase01.S4T0
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N4.templates 0)
theorem template_exact : decodeTemplate 4 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 4 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 4 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase01.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase01.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase01.cells :=
  RootedCoverageFrames.RootedSixBase01.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase01.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase01.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase01.cells generators
    FacetUniverses.RootedSixBase01.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase01.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 4 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase01.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase01.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase01.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 4 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase01.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase01.S4T0

end
end
end SourcePart12

section SourcePart13
/- Original module: RootedSixBase01CanonicalS5T0. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase01.S5T0
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N5.templates 0)
theorem template_exact : decodeTemplate 5 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 5 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 5 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase01.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase01.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase01.cells :=
  RootedCoverageFrames.RootedSixBase01.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase01.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase01.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase01.cells generators
    FacetUniverses.RootedSixBase01.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase01.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase01.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase01.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase01.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase01.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase01.S5T0

end
end
end SourcePart13

section SourcePart14
/- Original module: RootedSixBase01CanonicalS5T1. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase01.S5T1
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N5.templates 1)
theorem template_exact : decodeTemplate 5 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 5 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 5 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase01.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase01.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase01.cells :=
  RootedCoverageFrames.RootedSixBase01.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase01.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase01.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase01.cells generators
    FacetUniverses.RootedSixBase01.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase01.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase01.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase01.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase01.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase01.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase01.S5T1

end
end
end SourcePart14

section SourcePart15
/- Original module: RootedSixBase01CanonicalT1. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase01.T1
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 1)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase01.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase01.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase01.cells :=
  RootedCoverageFrames.RootedSixBase01.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase01.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase01.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase01.cells generators
    FacetUniverses.RootedSixBase01.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase01.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase01.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase01.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase01.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase01.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase01.T1

end
end
end SourcePart15

section SourcePart16
/- Original module: RootedSixBase01CanonicalT2. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase01.T2
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 2)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase01.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase01.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase01.cells :=
  RootedCoverageFrames.RootedSixBase01.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase01.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase01.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase01.cells generators
    FacetUniverses.RootedSixBase01.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase01.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase01.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase01.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase01.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase01.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase01.T2

end
end
end SourcePart16

section SourcePart17
/- Original module: RootedSixBase01CanonicalT3. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase01.T3
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 3)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase01.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase01.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase01.cells :=
  RootedCoverageFrames.RootedSixBase01.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase01.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase01.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase01.cells generators
    FacetUniverses.RootedSixBase01.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase01.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase01.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase01.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase01.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase01.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase01.T3

end
end
end SourcePart17

section SourcePart18
/- Original module: RootedSixBase01CanonicalT5. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase01.T5
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 5)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase01.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase01.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase01.cells :=
  RootedCoverageFrames.RootedSixBase01.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase01.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase01.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase01.cells generators
    FacetUniverses.RootedSixBase01.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase01.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase01.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase01.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase01.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase01.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase01.T5

end
end
end SourcePart18

section SourcePart19
/- Original module: RootedSixBase01CanonicalT6. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase01.T6
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 6)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase01.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase01.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase01.cells :=
  RootedCoverageFrames.RootedSixBase01.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase01.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase01.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase01.cells generators
    FacetUniverses.RootedSixBase01.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase01.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase01.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase01.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase01.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase01.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase01.T6

end
end
end SourcePart19

section SourcePart20
/- Original module: RootedSixBase01Coverage. -/

@[expose] public section

/-!
# Complete compatible-template coverage for RootedSixBase01

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSixBase01

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSixBase01

abbrev root : Fin FacetUniverses.RootedSixBase01.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 6 ↪ Fin 10 where
  toFun := ![5, 4, 2, 1, 3, 0]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N6.templates (RawEncoding.oldToCurrent 1))) =
      decodeCell (FacetUniverses.RootedSixBase01.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSixBase01.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [4, 10]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SixFamilyActualEncoding.Coverage FacetUniverses.RootedSixBase01.cells root 1 quota where
  rootEmbedding := rootEmbedding
  rootCell := root_exact
  rootKind := root_kind
  complete := by
    intro a hpos f h
    cases a with
    | tetrahedron => exact S4T0.covers_exact f h
    | bipyramid => exact S5T0.covers_exact f h
    | squarePyramid => exact S5T1.covers_exact f h
    | six i =>
      fin_cases i
      · change 0 < quota 4 at hpos
        rw [hzero 4 (by decide +kernel)] at hpos
        omega
      · exact T1.covers_exact f h
      · exact T2.covers_exact f h
      · exact T3.covers_exact f h
      · change 0 < quota 10 at hpos
        rw [hzero 10 (by decide +kernel)] at hpos
        omega
      · exact T5.covers_exact f h
      · exact T6.covers_exact f h

end Papers.RationalityTen.RootedCoverage.RootedSixBase01

end
end
end SourcePart20

section SourcePart21
/- Original module: RootedSixBase02CoverageFrames. -/

@[expose] public section

/-! The outside generators are taken from the complete checked generator
family. Their vertex codes agree with the independently checked placement
normalizers. No packed cell-map equality is an assumption. -/

noncomputable section
namespace Papers.RationalityTen.RootedCoverageFrames.RootedSixBase02

def generator (g : Fin FacetUniverses.RootedSixBase02.Outside.generatorCount) :
    Fin FacetUniverses.RootedSixBase02.Generators.generatorCount :=
  ⟨g.val, Nat.lt_of_lt_of_le g.isLt (by decide +kernel)⟩

theorem vertex_code (g : Fin FacetUniverses.RootedSixBase02.Outside.generatorCount) :
    FacetUniverses.RootedSixBase02.Generators.vertexCode (generator g) = FacetUniverses.RootedSixBase02.Outside.vertexCode g := by
  have h : ∀ g : Fin FacetUniverses.RootedSixBase02.Outside.generatorCount,
      FacetUniverses.RootedSixBase02.Generators.vertexCode (generator g) = FacetUniverses.RootedSixBase02.Outside.vertexCode g := by
    decide +kernel
  exact h g

theorem generator_check (g : Fin FacetUniverses.RootedSixBase02.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSixBase02.cellCount) :
    (RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSixBase02.Generators.forward (generator g))
      (FacetUniverses.RootedSixBase02.Generators.inverse (generator g)) i &&
      RawGraphGrowthFrames.cellRelabelCheck
        (TenGraphEdges.vertexMap (FacetUniverses.RootedSixBase02.Generators.vertexCode (generator g)))
        (FacetUniverses.RootedSixBase02.cells i)
        (FacetUniverses.RootedSixBase02.cells (FacetUniverses.RootedSixBase02.Generators.forward (generator g) i))) = true := by
  simpa only [FacetUniverses.RootedSixBase02.Generators.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSixBase02.Generators.cell_checked (generator g) i

def frame (g : Fin FacetUniverses.RootedSixBase02.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase02.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSixBase02.cells
    (FacetUniverses.RootedSixBase02.Generators.vertexCode (generator g))
    (FacetUniverses.RootedSixBase02.Generators.vertexInverseCode (generator g))
    (FacetUniverses.RootedSixBase02.Generators.vertex_checks (generator g))
    (FacetUniverses.RootedSixBase02.Generators.forward (generator g))
    (FacetUniverses.RootedSixBase02.Generators.inverse (generator g))
    (fun i => (Bool.and_eq_true_iff.mp (generator_check g i)).1)
    (fun i => (Bool.and_eq_true_iff.mp (generator_check g i)).2)

theorem frame_vertices (g : Fin FacetUniverses.RootedSixBase02.Outside.generatorCount) (v : Fin 10) :
    (frame g).vertices v = TenGraphEdges.vertexMap (FacetUniverses.RootedSixBase02.Outside.vertexCode g) v := by
  change TenGraphEdges.vertexMap (FacetUniverses.RootedSixBase02.Generators.vertexCode (generator g)) v = _
  rw [vertex_code]

end Papers.RationalityTen.RootedCoverageFrames.RootedSixBase02

end
end
end SourcePart21

section SourcePart22
/- Original module: RootedSixBase02CanonicalS4T0. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase02.S4T0
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N4.templates 0)
theorem template_exact : decodeTemplate 4 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 4 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 4 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase02.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase02.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase02.cells :=
  RootedCoverageFrames.RootedSixBase02.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase02.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase02.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase02.cells generators
    FacetUniverses.RootedSixBase02.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase02.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 4 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase02.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase02.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase02.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 4 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase02.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase02.S4T0

end
end
end SourcePart22

section SourcePart23
/- Original module: RootedSixBase02CanonicalS5T0. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase02.S5T0
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N5.templates 0)
theorem template_exact : decodeTemplate 5 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 5 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 5 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase02.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase02.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase02.cells :=
  RootedCoverageFrames.RootedSixBase02.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase02.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase02.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase02.cells generators
    FacetUniverses.RootedSixBase02.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase02.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase02.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase02.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase02.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase02.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase02.S5T0

end
end
end SourcePart23

section SourcePart24
/- Original module: RootedSixBase02CanonicalS5T1. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase02.S5T1
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N5.templates 1)
theorem template_exact : decodeTemplate 5 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 5 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 5 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase02.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase02.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase02.cells :=
  RootedCoverageFrames.RootedSixBase02.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase02.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase02.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase02.cells generators
    FacetUniverses.RootedSixBase02.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase02.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase02.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase02.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase02.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase02.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase02.S5T1

end
end
end SourcePart24

section SourcePart25
/- Original module: RootedSixBase02CanonicalT2. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase02.T2
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 2)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase02.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase02.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase02.cells :=
  RootedCoverageFrames.RootedSixBase02.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase02.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase02.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase02.cells generators
    FacetUniverses.RootedSixBase02.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase02.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase02.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase02.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase02.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase02.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase02.T2

end
end
end SourcePart25

section SourcePart26
/- Original module: RootedSixBase02CanonicalT3. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase02.T3
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 3)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase02.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase02.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase02.cells :=
  RootedCoverageFrames.RootedSixBase02.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase02.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase02.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase02.cells generators
    FacetUniverses.RootedSixBase02.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase02.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase02.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase02.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase02.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase02.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase02.T3

end
end
end SourcePart26

section SourcePart27
/- Original module: RootedSixBase02CanonicalT5. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase02.T5
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 5)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase02.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase02.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase02.cells :=
  RootedCoverageFrames.RootedSixBase02.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase02.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase02.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase02.cells generators
    FacetUniverses.RootedSixBase02.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase02.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase02.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase02.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase02.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase02.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase02.T5

end
end
end SourcePart27

section SourcePart28
/- Original module: RootedSixBase02CanonicalT6. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase02.T6
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 6)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase02.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase02.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase02.cells :=
  RootedCoverageFrames.RootedSixBase02.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase02.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase02.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase02.cells generators
    FacetUniverses.RootedSixBase02.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase02.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase02.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase02.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase02.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase02.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase02.T6

end
end
end SourcePart28

section SourcePart29
/- Original module: RootedSixBase02Coverage. -/

@[expose] public section

/-!
# Complete compatible-template coverage for RootedSixBase02

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSixBase02

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSixBase02

abbrev root : Fin FacetUniverses.RootedSixBase02.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 6 ↪ Fin 10 where
  toFun := ![0, 2, 1, 4, 3, 5]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N6.templates (RawEncoding.oldToCurrent 2))) =
      decodeCell (FacetUniverses.RootedSixBase02.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSixBase02.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [4, 5, 10]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SixFamilyActualEncoding.Coverage FacetUniverses.RootedSixBase02.cells root 2 quota where
  rootEmbedding := rootEmbedding
  rootCell := root_exact
  rootKind := root_kind
  complete := by
    intro a hpos f h
    cases a with
    | tetrahedron => exact S4T0.covers_exact f h
    | bipyramid => exact S5T0.covers_exact f h
    | squarePyramid => exact S5T1.covers_exact f h
    | six i =>
      fin_cases i
      · change 0 < quota 4 at hpos
        rw [hzero 4 (by decide +kernel)] at hpos
        omega
      · change 0 < quota 5 at hpos
        rw [hzero 5 (by decide +kernel)] at hpos
        omega
      · exact T2.covers_exact f h
      · exact T3.covers_exact f h
      · change 0 < quota 10 at hpos
        rw [hzero 10 (by decide +kernel)] at hpos
        omega
      · exact T5.covers_exact f h
      · exact T6.covers_exact f h

end Papers.RationalityTen.RootedCoverage.RootedSixBase02

end
end
end SourcePart29

section SourcePart30
/- Original module: RootedSixBase03CoverageFrames. -/

@[expose] public section

/-! The outside generators are taken from the complete checked generator
family. Their vertex codes agree with the independently checked placement
normalizers. No packed cell-map equality is an assumption. -/

noncomputable section
namespace Papers.RationalityTen.RootedCoverageFrames.RootedSixBase03

def generator (g : Fin FacetUniverses.RootedSixBase03.Outside.generatorCount) :
    Fin FacetUniverses.RootedSixBase03.Generators.generatorCount :=
  ⟨g.val, Nat.lt_of_lt_of_le g.isLt (by decide +kernel)⟩

theorem vertex_code (g : Fin FacetUniverses.RootedSixBase03.Outside.generatorCount) :
    FacetUniverses.RootedSixBase03.Generators.vertexCode (generator g) = FacetUniverses.RootedSixBase03.Outside.vertexCode g := by
  have h : ∀ g : Fin FacetUniverses.RootedSixBase03.Outside.generatorCount,
      FacetUniverses.RootedSixBase03.Generators.vertexCode (generator g) = FacetUniverses.RootedSixBase03.Outside.vertexCode g := by
    decide +kernel
  exact h g

theorem generator_check (g : Fin FacetUniverses.RootedSixBase03.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSixBase03.cellCount) :
    (RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSixBase03.Generators.forward (generator g))
      (FacetUniverses.RootedSixBase03.Generators.inverse (generator g)) i &&
      RawGraphGrowthFrames.cellRelabelCheck
        (TenGraphEdges.vertexMap (FacetUniverses.RootedSixBase03.Generators.vertexCode (generator g)))
        (FacetUniverses.RootedSixBase03.cells i)
        (FacetUniverses.RootedSixBase03.cells (FacetUniverses.RootedSixBase03.Generators.forward (generator g) i))) = true := by
  simpa only [FacetUniverses.RootedSixBase03.Generators.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSixBase03.Generators.cell_checked (generator g) i

def frame (g : Fin FacetUniverses.RootedSixBase03.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase03.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSixBase03.cells
    (FacetUniverses.RootedSixBase03.Generators.vertexCode (generator g))
    (FacetUniverses.RootedSixBase03.Generators.vertexInverseCode (generator g))
    (FacetUniverses.RootedSixBase03.Generators.vertex_checks (generator g))
    (FacetUniverses.RootedSixBase03.Generators.forward (generator g))
    (FacetUniverses.RootedSixBase03.Generators.inverse (generator g))
    (fun i => (Bool.and_eq_true_iff.mp (generator_check g i)).1)
    (fun i => (Bool.and_eq_true_iff.mp (generator_check g i)).2)

theorem frame_vertices (g : Fin FacetUniverses.RootedSixBase03.Outside.generatorCount) (v : Fin 10) :
    (frame g).vertices v = TenGraphEdges.vertexMap (FacetUniverses.RootedSixBase03.Outside.vertexCode g) v := by
  change TenGraphEdges.vertexMap (FacetUniverses.RootedSixBase03.Generators.vertexCode (generator g)) v = _
  rw [vertex_code]

end Papers.RationalityTen.RootedCoverageFrames.RootedSixBase03

end
end
end SourcePart30

section SourcePart31
/- Original module: RootedSixBase03CanonicalS4T0. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase03.S4T0
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N4.templates 0)
theorem template_exact : decodeTemplate 4 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 4 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 4 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase03.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase03.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase03.cells :=
  RootedCoverageFrames.RootedSixBase03.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase03.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase03.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase03.cells generators
    FacetUniverses.RootedSixBase03.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase03.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 4 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase03.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase03.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase03.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 4 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase03.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase03.S4T0

end
end
end SourcePart31

section SourcePart32
/- Original module: RootedSixBase03CanonicalS5T0. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase03.S5T0
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N5.templates 0)
theorem template_exact : decodeTemplate 5 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 5 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 5 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase03.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase03.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase03.cells :=
  RootedCoverageFrames.RootedSixBase03.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase03.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase03.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase03.cells generators
    FacetUniverses.RootedSixBase03.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase03.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase03.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase03.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase03.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase03.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase03.S5T0

end
end
end SourcePart32

section SourcePart33
/- Original module: RootedSixBase03CanonicalS5T1. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase03.S5T1
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N5.templates 1)
theorem template_exact : decodeTemplate 5 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 5 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 5 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase03.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase03.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase03.cells :=
  RootedCoverageFrames.RootedSixBase03.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase03.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase03.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase03.cells generators
    FacetUniverses.RootedSixBase03.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase03.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase03.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase03.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase03.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase03.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase03.S5T1

end
end
end SourcePart33

section SourcePart34
/- Original module: RootedSixBase03CanonicalT2. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase03.T2
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 2)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase03.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase03.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase03.cells :=
  RootedCoverageFrames.RootedSixBase03.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase03.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase03.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase03.cells generators
    FacetUniverses.RootedSixBase03.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase03.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase03.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase03.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase03.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase03.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase03.T2

end
end
end SourcePart34

section SourcePart35
/- Original module: RootedSixBase03CanonicalT3. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase03.T3
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 3)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase03.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase03.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase03.cells :=
  RootedCoverageFrames.RootedSixBase03.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase03.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase03.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase03.cells generators
    FacetUniverses.RootedSixBase03.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase03.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase03.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase03.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase03.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase03.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase03.T3

end
end
end SourcePart35

section SourcePart36
/- Original module: RootedSixBase03CanonicalT6. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase03.T6
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 6)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase03.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase03.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase03.cells :=
  RootedCoverageFrames.RootedSixBase03.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase03.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase03.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase03.cells generators
    FacetUniverses.RootedSixBase03.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase03.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase03.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase03.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase03.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase03.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase03.T6

end
end
end SourcePart36

section SourcePart37
/- Original module: RootedSixBase03Coverage. -/

@[expose] public section

/-!
# Complete compatible-template coverage for RootedSixBase03

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSixBase03

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSixBase03

abbrev root : Fin FacetUniverses.RootedSixBase03.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 6 ↪ Fin 10 where
  toFun := ![0, 2, 1, 4, 3, 5]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N6.templates (RawEncoding.oldToCurrent 3))) =
      decodeCell (FacetUniverses.RootedSixBase03.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSixBase03.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [4, 5, 6, 10]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SixFamilyActualEncoding.Coverage FacetUniverses.RootedSixBase03.cells root 3 quota where
  rootEmbedding := rootEmbedding
  rootCell := root_exact
  rootKind := root_kind
  complete := by
    intro a hpos f h
    cases a with
    | tetrahedron => exact S4T0.covers_exact f h
    | bipyramid => exact S5T0.covers_exact f h
    | squarePyramid => exact S5T1.covers_exact f h
    | six i =>
      fin_cases i
      · change 0 < quota 4 at hpos
        rw [hzero 4 (by decide +kernel)] at hpos
        omega
      · change 0 < quota 5 at hpos
        rw [hzero 5 (by decide +kernel)] at hpos
        omega
      · exact T2.covers_exact f h
      · exact T3.covers_exact f h
      · change 0 < quota 10 at hpos
        rw [hzero 10 (by decide +kernel)] at hpos
        omega
      · change 0 < quota 6 at hpos
        rw [hzero 6 (by decide +kernel)] at hpos
        omega
      · exact T6.covers_exact f h

end Papers.RationalityTen.RootedCoverage.RootedSixBase03

end
end
end SourcePart37

section SourcePart38
/- Original module: RootedSixBase04CoverageFrames. -/

@[expose] public section

/-! The outside generators are taken from the complete checked generator
family. Their vertex codes agree with the independently checked placement
normalizers. No packed cell-map equality is an assumption. -/

noncomputable section
namespace Papers.RationalityTen.RootedCoverageFrames.RootedSixBase04

def generator (g : Fin FacetUniverses.RootedSixBase04.Outside.generatorCount) :
    Fin FacetUniverses.RootedSixBase04.Generators.generatorCount :=
  ⟨g.val, Nat.lt_of_lt_of_le g.isLt (by decide +kernel)⟩

theorem vertex_code (g : Fin FacetUniverses.RootedSixBase04.Outside.generatorCount) :
    FacetUniverses.RootedSixBase04.Generators.vertexCode (generator g) = FacetUniverses.RootedSixBase04.Outside.vertexCode g := by
  have h : ∀ g : Fin FacetUniverses.RootedSixBase04.Outside.generatorCount,
      FacetUniverses.RootedSixBase04.Generators.vertexCode (generator g) = FacetUniverses.RootedSixBase04.Outside.vertexCode g := by
    decide +kernel
  exact h g

theorem generator_check (g : Fin FacetUniverses.RootedSixBase04.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSixBase04.cellCount) :
    (RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSixBase04.Generators.forward (generator g))
      (FacetUniverses.RootedSixBase04.Generators.inverse (generator g)) i &&
      RawGraphGrowthFrames.cellRelabelCheck
        (TenGraphEdges.vertexMap (FacetUniverses.RootedSixBase04.Generators.vertexCode (generator g)))
        (FacetUniverses.RootedSixBase04.cells i)
        (FacetUniverses.RootedSixBase04.cells (FacetUniverses.RootedSixBase04.Generators.forward (generator g) i))) = true := by
  simpa only [FacetUniverses.RootedSixBase04.Generators.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSixBase04.Generators.cell_checked (generator g) i

def frame (g : Fin FacetUniverses.RootedSixBase04.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase04.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSixBase04.cells
    (FacetUniverses.RootedSixBase04.Generators.vertexCode (generator g))
    (FacetUniverses.RootedSixBase04.Generators.vertexInverseCode (generator g))
    (FacetUniverses.RootedSixBase04.Generators.vertex_checks (generator g))
    (FacetUniverses.RootedSixBase04.Generators.forward (generator g))
    (FacetUniverses.RootedSixBase04.Generators.inverse (generator g))
    (fun i => (Bool.and_eq_true_iff.mp (generator_check g i)).1)
    (fun i => (Bool.and_eq_true_iff.mp (generator_check g i)).2)

theorem frame_vertices (g : Fin FacetUniverses.RootedSixBase04.Outside.generatorCount) (v : Fin 10) :
    (frame g).vertices v = TenGraphEdges.vertexMap (FacetUniverses.RootedSixBase04.Outside.vertexCode g) v := by
  change TenGraphEdges.vertexMap (FacetUniverses.RootedSixBase04.Generators.vertexCode (generator g)) v = _
  rw [vertex_code]

end Papers.RationalityTen.RootedCoverageFrames.RootedSixBase04

end
end
end SourcePart38

section SourcePart39
/- Original module: RootedSixBase04CanonicalS4T0. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase04.S4T0
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N4.templates 0)
theorem template_exact : decodeTemplate 4 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 4 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 4 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase04.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase04.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase04.cells :=
  RootedCoverageFrames.RootedSixBase04.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase04.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase04.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase04.cells generators
    FacetUniverses.RootedSixBase04.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase04.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 4 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase04.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase04.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase04.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 4 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase04.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase04.S4T0

end
end
end SourcePart39

section SourcePart40
/- Original module: RootedSixBase04CanonicalS5T0. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase04.S5T0
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N5.templates 0)
theorem template_exact : decodeTemplate 5 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 5 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 5 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase04.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase04.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase04.cells :=
  RootedCoverageFrames.RootedSixBase04.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase04.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase04.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase04.cells generators
    FacetUniverses.RootedSixBase04.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase04.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase04.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase04.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase04.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase04.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase04.S5T0

end
end
end SourcePart40

section SourcePart41
/- Original module: RootedSixBase04CanonicalS5T1. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase04.S5T1
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N5.templates 1)
theorem template_exact : decodeTemplate 5 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 5 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 5 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase04.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase04.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase04.cells :=
  RootedCoverageFrames.RootedSixBase04.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase04.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase04.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase04.cells generators
    FacetUniverses.RootedSixBase04.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase04.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase04.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase04.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase04.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase04.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase04.S5T1

end
end
end SourcePart41

section SourcePart42
/- Original module: RootedSixBase04CanonicalT2. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase04.T2
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 2)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase04.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase04.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase04.cells :=
  RootedCoverageFrames.RootedSixBase04.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase04.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase04.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase04.cells generators
    FacetUniverses.RootedSixBase04.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase04.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase04.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase04.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase04.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase04.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase04.T2

end
end
end SourcePart42

section SourcePart43
/- Original module: RootedSixBase04CanonicalT6. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase04.T6
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 6)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase04.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixBase04.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase04.cells :=
  RootedCoverageFrames.RootedSixBase04.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixBase04.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixBase04.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixBase04.cells generators
    FacetUniverses.RootedSixBase04.Outside.vertexCode
    RootedCoverageFrames.RootedSixBase04.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixBase04.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixBase04.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixBase04.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixBase04.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixBase04.T6

end
end
end SourcePart43

section SourcePart44
/- Original module: RootedSixBase04Coverage. -/

@[expose] public section

/-!
# Complete compatible-template coverage for RootedSixBase04

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSixBase04

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSixBase04

abbrev root : Fin FacetUniverses.RootedSixBase04.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 6 ↪ Fin 10 where
  toFun := ![0, 1, 2, 3, 4, 5]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N6.templates (RawEncoding.oldToCurrent 4))) =
      decodeCell (FacetUniverses.RootedSixBase04.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSixBase04.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [4, 5, 6, 7, 10]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SixFamilyActualEncoding.Coverage FacetUniverses.RootedSixBase04.cells root 4 quota where
  rootEmbedding := rootEmbedding
  rootCell := root_exact
  rootKind := root_kind
  complete := by
    intro a hpos f h
    cases a with
    | tetrahedron => exact S4T0.covers_exact f h
    | bipyramid => exact S5T0.covers_exact f h
    | squarePyramid => exact S5T1.covers_exact f h
    | six i =>
      fin_cases i
      · change 0 < quota 4 at hpos
        rw [hzero 4 (by decide +kernel)] at hpos
        omega
      · change 0 < quota 5 at hpos
        rw [hzero 5 (by decide +kernel)] at hpos
        omega
      · exact T2.covers_exact f h
      · change 0 < quota 7 at hpos
        rw [hzero 7 (by decide +kernel)] at hpos
        omega
      · change 0 < quota 10 at hpos
        rw [hzero 10 (by decide +kernel)] at hpos
        omega
      · change 0 < quota 6 at hpos
        rw [hzero 6 (by decide +kernel)] at hpos
        omega
      · exact T6.covers_exact f h

end Papers.RationalityTen.RootedCoverage.RootedSixBase04

end
end
end SourcePart44

section SourcePart45
/- Original module: RootedSixExtra00CoverageFrames. -/

@[expose] public section

/-! The outside generators are taken from the complete checked generator
family. Their vertex codes agree with the independently checked placement
normalizers. No packed cell-map equality is an assumption. -/

noncomputable section
namespace Papers.RationalityTen.RootedCoverageFrames.RootedSixExtra00

def generator (g : Fin FacetUniverses.RootedSixExtra00.Outside.generatorCount) :
    Fin FacetUniverses.RootedSixExtra00.Generators.generatorCount :=
  ⟨g.val, Nat.lt_of_lt_of_le g.isLt (by decide +kernel)⟩

theorem vertex_code (g : Fin FacetUniverses.RootedSixExtra00.Outside.generatorCount) :
    FacetUniverses.RootedSixExtra00.Generators.vertexCode (generator g) = FacetUniverses.RootedSixExtra00.Outside.vertexCode g := by
  have h : ∀ g : Fin FacetUniverses.RootedSixExtra00.Outside.generatorCount,
      FacetUniverses.RootedSixExtra00.Generators.vertexCode (generator g) = FacetUniverses.RootedSixExtra00.Outside.vertexCode g := by
    decide +kernel
  exact h g

theorem generator_check (g : Fin FacetUniverses.RootedSixExtra00.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSixExtra00.cellCount) :
    (RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSixExtra00.Generators.forward (generator g))
      (FacetUniverses.RootedSixExtra00.Generators.inverse (generator g)) i &&
      RawGraphGrowthFrames.cellRelabelCheck
        (TenGraphEdges.vertexMap (FacetUniverses.RootedSixExtra00.Generators.vertexCode (generator g)))
        (FacetUniverses.RootedSixExtra00.cells i)
        (FacetUniverses.RootedSixExtra00.cells (FacetUniverses.RootedSixExtra00.Generators.forward (generator g) i))) = true := by
  simpa only [FacetUniverses.RootedSixExtra00.Generators.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSixExtra00.Generators.cell_checked (generator g) i

def frame (g : Fin FacetUniverses.RootedSixExtra00.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra00.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSixExtra00.cells
    (FacetUniverses.RootedSixExtra00.Generators.vertexCode (generator g))
    (FacetUniverses.RootedSixExtra00.Generators.vertexInverseCode (generator g))
    (FacetUniverses.RootedSixExtra00.Generators.vertex_checks (generator g))
    (FacetUniverses.RootedSixExtra00.Generators.forward (generator g))
    (FacetUniverses.RootedSixExtra00.Generators.inverse (generator g))
    (fun i => (Bool.and_eq_true_iff.mp (generator_check g i)).1)
    (fun i => (Bool.and_eq_true_iff.mp (generator_check g i)).2)

theorem frame_vertices (g : Fin FacetUniverses.RootedSixExtra00.Outside.generatorCount) (v : Fin 10) :
    (frame g).vertices v = TenGraphEdges.vertexMap (FacetUniverses.RootedSixExtra00.Outside.vertexCode g) v := by
  change TenGraphEdges.vertexMap (FacetUniverses.RootedSixExtra00.Generators.vertexCode (generator g)) v = _
  rw [vertex_code]

end Papers.RationalityTen.RootedCoverageFrames.RootedSixExtra00

end
end
end SourcePart45

section SourcePart46
/- Original module: RootedSixExtra00CanonicalS4T0. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra00.S4T0
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N4.templates 0)
theorem template_exact : decodeTemplate 4 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 4 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 4 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra00.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra00.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra00.cells :=
  RootedCoverageFrames.RootedSixExtra00.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra00.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra00.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra00.cells generators
    FacetUniverses.RootedSixExtra00.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra00.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 4 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra00.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra00.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra00.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 4 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra00.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra00.S4T0

end
end
end SourcePart46

section SourcePart47
/- Original module: RootedSixExtra00CanonicalS5T0. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra00.S5T0
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N5.templates 0)
theorem template_exact : decodeTemplate 5 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 5 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 5 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra00.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra00.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra00.cells :=
  RootedCoverageFrames.RootedSixExtra00.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra00.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra00.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra00.cells generators
    FacetUniverses.RootedSixExtra00.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra00.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra00.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra00.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra00.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra00.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra00.S5T0

end
end
end SourcePart47

section SourcePart48
/- Original module: RootedSixExtra00CanonicalS5T1. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra00.S5T1
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N5.templates 1)
theorem template_exact : decodeTemplate 5 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 5 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 5 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra00.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra00.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra00.cells :=
  RootedCoverageFrames.RootedSixExtra00.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra00.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra00.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra00.cells generators
    FacetUniverses.RootedSixExtra00.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra00.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra00.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra00.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra00.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra00.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra00.S5T1

end
end
end SourcePart48

section SourcePart49
/- Original module: RootedSixExtra00CanonicalT4. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra00.T4
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 4)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra00.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra00.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra00.cells :=
  RootedCoverageFrames.RootedSixExtra00.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra00.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra00.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra00.cells generators
    FacetUniverses.RootedSixExtra00.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra00.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra00.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra00.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra00.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra00.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra00.T4

end
end
end SourcePart49

section SourcePart50
/- Original module: RootedSixExtra00CanonicalT5. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra00.T5
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 5)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra00.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra00.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra00.cells :=
  RootedCoverageFrames.RootedSixExtra00.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra00.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra00.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra00.cells generators
    FacetUniverses.RootedSixExtra00.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra00.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra00.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra00.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra00.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra00.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra00.T5

end
end
end SourcePart50

section SourcePart51
/- Original module: RootedSixExtra00CanonicalT6. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra00.T6
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 6)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra00.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra00.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra00.cells :=
  RootedCoverageFrames.RootedSixExtra00.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra00.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra00.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra00.cells generators
    FacetUniverses.RootedSixExtra00.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra00.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra00.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra00.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra00.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra00.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra00.T6

end
end
end SourcePart51

section SourcePart52
/- Original module: RootedSixExtra00Coverage. -/

@[expose] public section

/-!
# Complete compatible-template coverage for RootedSixExtra00

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSixExtra00

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSixExtra00

abbrev root : Fin FacetUniverses.RootedSixExtra00.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 6 ↪ Fin 10 where
  toFun := ![0, 1, 2, 3, 4, 5]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N6.templates (RawEncoding.oldToCurrent 0))) =
      decodeCell (FacetUniverses.RootedSixExtra00.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSixExtra00.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [4, 5, 7, 8]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SixFamilyActualEncoding.Coverage FacetUniverses.RootedSixExtra00.cells root 0 quota where
  rootEmbedding := rootEmbedding
  rootCell := root_exact
  rootKind := root_kind
  complete := by
    intro a hpos f h
    cases a with
    | tetrahedron => exact S4T0.covers_exact f h
    | bipyramid => exact S5T0.covers_exact f h
    | squarePyramid => exact S5T1.covers_exact f h
    | six i =>
      fin_cases i
      · change 0 < quota 4 at hpos
        rw [hzero 4 (by decide +kernel)] at hpos
        omega
      · change 0 < quota 5 at hpos
        rw [hzero 5 (by decide +kernel)] at hpos
        omega
      · change 0 < quota 8 at hpos
        rw [hzero 8 (by decide +kernel)] at hpos
        omega
      · change 0 < quota 7 at hpos
        rw [hzero 7 (by decide +kernel)] at hpos
        omega
      · exact T4.covers_exact f h
      · exact T5.covers_exact f h
      · exact T6.covers_exact f h

end Papers.RationalityTen.RootedCoverage.RootedSixExtra00

end
end
end SourcePart52

section SourcePart53
/- Original module: RootedSixExtra01CoverageFrames. -/

@[expose] public section

/-! The outside generators are taken from the complete checked generator
family. Their vertex codes agree with the independently checked placement
normalizers. No packed cell-map equality is an assumption. -/

noncomputable section
namespace Papers.RationalityTen.RootedCoverageFrames.RootedSixExtra01

def generator (g : Fin FacetUniverses.RootedSixExtra01.Outside.generatorCount) :
    Fin FacetUniverses.RootedSixExtra01.Generators.generatorCount :=
  ⟨g.val, Nat.lt_of_lt_of_le g.isLt (by decide +kernel)⟩

theorem vertex_code (g : Fin FacetUniverses.RootedSixExtra01.Outside.generatorCount) :
    FacetUniverses.RootedSixExtra01.Generators.vertexCode (generator g) = FacetUniverses.RootedSixExtra01.Outside.vertexCode g := by
  have h : ∀ g : Fin FacetUniverses.RootedSixExtra01.Outside.generatorCount,
      FacetUniverses.RootedSixExtra01.Generators.vertexCode (generator g) = FacetUniverses.RootedSixExtra01.Outside.vertexCode g := by
    decide +kernel
  exact h g

theorem generator_check (g : Fin FacetUniverses.RootedSixExtra01.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSixExtra01.cellCount) :
    (RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSixExtra01.Generators.forward (generator g))
      (FacetUniverses.RootedSixExtra01.Generators.inverse (generator g)) i &&
      RawGraphGrowthFrames.cellRelabelCheck
        (TenGraphEdges.vertexMap (FacetUniverses.RootedSixExtra01.Generators.vertexCode (generator g)))
        (FacetUniverses.RootedSixExtra01.cells i)
        (FacetUniverses.RootedSixExtra01.cells (FacetUniverses.RootedSixExtra01.Generators.forward (generator g) i))) = true := by
  simpa only [FacetUniverses.RootedSixExtra01.Generators.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSixExtra01.Generators.cell_checked (generator g) i

def frame (g : Fin FacetUniverses.RootedSixExtra01.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra01.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSixExtra01.cells
    (FacetUniverses.RootedSixExtra01.Generators.vertexCode (generator g))
    (FacetUniverses.RootedSixExtra01.Generators.vertexInverseCode (generator g))
    (FacetUniverses.RootedSixExtra01.Generators.vertex_checks (generator g))
    (FacetUniverses.RootedSixExtra01.Generators.forward (generator g))
    (FacetUniverses.RootedSixExtra01.Generators.inverse (generator g))
    (fun i => (Bool.and_eq_true_iff.mp (generator_check g i)).1)
    (fun i => (Bool.and_eq_true_iff.mp (generator_check g i)).2)

theorem frame_vertices (g : Fin FacetUniverses.RootedSixExtra01.Outside.generatorCount) (v : Fin 10) :
    (frame g).vertices v = TenGraphEdges.vertexMap (FacetUniverses.RootedSixExtra01.Outside.vertexCode g) v := by
  change TenGraphEdges.vertexMap (FacetUniverses.RootedSixExtra01.Generators.vertexCode (generator g)) v = _
  rw [vertex_code]

end Papers.RationalityTen.RootedCoverageFrames.RootedSixExtra01

end
end
end SourcePart53

section SourcePart54
/- Original module: RootedSixExtra01CanonicalS4T0. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra01.S4T0
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N4.templates 0)
theorem template_exact : decodeTemplate 4 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 4 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 4 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra01.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra01.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra01.cells :=
  RootedCoverageFrames.RootedSixExtra01.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra01.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra01.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra01.cells generators
    FacetUniverses.RootedSixExtra01.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra01.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 4 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra01.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra01.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra01.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 4 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra01.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra01.S4T0

end
end
end SourcePart54

section SourcePart55
/- Original module: RootedSixExtra01CanonicalS5T0. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra01.S5T0
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N5.templates 0)
theorem template_exact : decodeTemplate 5 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 5 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 5 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra01.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra01.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra01.cells :=
  RootedCoverageFrames.RootedSixExtra01.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra01.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra01.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra01.cells generators
    FacetUniverses.RootedSixExtra01.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra01.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra01.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra01.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra01.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra01.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra01.S5T0

end
end
end SourcePart55

section SourcePart56
/- Original module: RootedSixExtra01CanonicalS5T1. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra01.S5T1
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N5.templates 1)
theorem template_exact : decodeTemplate 5 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 5 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 5 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra01.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra01.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra01.cells :=
  RootedCoverageFrames.RootedSixExtra01.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra01.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra01.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra01.cells generators
    FacetUniverses.RootedSixExtra01.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra01.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra01.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra01.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra01.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra01.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra01.S5T1

end
end
end SourcePart56

section SourcePart57
/- Original module: RootedSixExtra01CanonicalT4. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra01.T4
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 4)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra01.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra01.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra01.cells :=
  RootedCoverageFrames.RootedSixExtra01.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra01.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra01.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra01.cells generators
    FacetUniverses.RootedSixExtra01.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra01.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra01.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra01.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra01.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra01.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra01.T4

end
end
end SourcePart57

section SourcePart58
/- Original module: RootedSixExtra01CanonicalT6. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra01.T6
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 6)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra01.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra01.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra01.cells :=
  RootedCoverageFrames.RootedSixExtra01.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra01.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra01.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra01.cells generators
    FacetUniverses.RootedSixExtra01.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra01.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra01.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra01.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra01.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra01.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra01.T6

end
end
end SourcePart58

section SourcePart59
/- Original module: RootedSixExtra01Coverage. -/

@[expose] public section

/-!
# Complete compatible-template coverage for RootedSixExtra01

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSixExtra01

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSixExtra01

abbrev root : Fin FacetUniverses.RootedSixExtra01.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 6 ↪ Fin 10 where
  toFun := ![5, 4, 2, 1, 3, 0]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N6.templates (RawEncoding.oldToCurrent 1))) =
      decodeCell (FacetUniverses.RootedSixExtra01.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSixExtra01.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [4, 5, 6, 7, 8]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SixFamilyActualEncoding.Coverage FacetUniverses.RootedSixExtra01.cells root 1 quota where
  rootEmbedding := rootEmbedding
  rootCell := root_exact
  rootKind := root_kind
  complete := by
    intro a hpos f h
    cases a with
    | tetrahedron => exact S4T0.covers_exact f h
    | bipyramid => exact S5T0.covers_exact f h
    | squarePyramid => exact S5T1.covers_exact f h
    | six i =>
      fin_cases i
      · change 0 < quota 4 at hpos
        rw [hzero 4 (by decide +kernel)] at hpos
        omega
      · change 0 < quota 5 at hpos
        rw [hzero 5 (by decide +kernel)] at hpos
        omega
      · change 0 < quota 8 at hpos
        rw [hzero 8 (by decide +kernel)] at hpos
        omega
      · change 0 < quota 7 at hpos
        rw [hzero 7 (by decide +kernel)] at hpos
        omega
      · exact T4.covers_exact f h
      · change 0 < quota 6 at hpos
        rw [hzero 6 (by decide +kernel)] at hpos
        omega
      · exact T6.covers_exact f h

end Papers.RationalityTen.RootedCoverage.RootedSixExtra01

end
end
end SourcePart59

section SourcePart60
/- Original module: RootedSixExtra02CoverageFrames. -/

@[expose] public section

/-! The outside generators are taken from the complete checked generator
family. Their vertex codes agree with the independently checked placement
normalizers. No packed cell-map equality is an assumption. -/

noncomputable section
namespace Papers.RationalityTen.RootedCoverageFrames.RootedSixExtra02

def generator (g : Fin FacetUniverses.RootedSixExtra02.Outside.generatorCount) :
    Fin FacetUniverses.RootedSixExtra02.Generators.generatorCount :=
  ⟨g.val, Nat.lt_of_lt_of_le g.isLt (by decide +kernel)⟩

theorem vertex_code (g : Fin FacetUniverses.RootedSixExtra02.Outside.generatorCount) :
    FacetUniverses.RootedSixExtra02.Generators.vertexCode (generator g) = FacetUniverses.RootedSixExtra02.Outside.vertexCode g := by
  have h : ∀ g : Fin FacetUniverses.RootedSixExtra02.Outside.generatorCount,
      FacetUniverses.RootedSixExtra02.Generators.vertexCode (generator g) = FacetUniverses.RootedSixExtra02.Outside.vertexCode g := by
    decide +kernel
  exact h g

theorem generator_check (g : Fin FacetUniverses.RootedSixExtra02.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSixExtra02.cellCount) :
    (RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSixExtra02.Generators.forward (generator g))
      (FacetUniverses.RootedSixExtra02.Generators.inverse (generator g)) i &&
      RawGraphGrowthFrames.cellRelabelCheck
        (TenGraphEdges.vertexMap (FacetUniverses.RootedSixExtra02.Generators.vertexCode (generator g)))
        (FacetUniverses.RootedSixExtra02.cells i)
        (FacetUniverses.RootedSixExtra02.cells (FacetUniverses.RootedSixExtra02.Generators.forward (generator g) i))) = true := by
  simpa only [FacetUniverses.RootedSixExtra02.Generators.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSixExtra02.Generators.cell_checked (generator g) i

def frame (g : Fin FacetUniverses.RootedSixExtra02.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra02.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSixExtra02.cells
    (FacetUniverses.RootedSixExtra02.Generators.vertexCode (generator g))
    (FacetUniverses.RootedSixExtra02.Generators.vertexInverseCode (generator g))
    (FacetUniverses.RootedSixExtra02.Generators.vertex_checks (generator g))
    (FacetUniverses.RootedSixExtra02.Generators.forward (generator g))
    (FacetUniverses.RootedSixExtra02.Generators.inverse (generator g))
    (fun i => (Bool.and_eq_true_iff.mp (generator_check g i)).1)
    (fun i => (Bool.and_eq_true_iff.mp (generator_check g i)).2)

theorem frame_vertices (g : Fin FacetUniverses.RootedSixExtra02.Outside.generatorCount) (v : Fin 10) :
    (frame g).vertices v = TenGraphEdges.vertexMap (FacetUniverses.RootedSixExtra02.Outside.vertexCode g) v := by
  change TenGraphEdges.vertexMap (FacetUniverses.RootedSixExtra02.Generators.vertexCode (generator g)) v = _
  rw [vertex_code]

end Papers.RationalityTen.RootedCoverageFrames.RootedSixExtra02

end
end
end SourcePart60

section SourcePart61
/- Original module: RootedSixExtra02CanonicalS4T0. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra02.S4T0
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N4.templates 0)
theorem template_exact : decodeTemplate 4 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 4 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 4 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra02.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra02.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra02.cells :=
  RootedCoverageFrames.RootedSixExtra02.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra02.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra02.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra02.cells generators
    FacetUniverses.RootedSixExtra02.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra02.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 4 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra02.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra02.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra02.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 4 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra02.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra02.S4T0

end
end
end SourcePart61

section SourcePart62
/- Original module: RootedSixExtra02CanonicalS5T0. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra02.S5T0
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N5.templates 0)
theorem template_exact : decodeTemplate 5 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 5 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 5 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra02.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra02.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra02.cells :=
  RootedCoverageFrames.RootedSixExtra02.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra02.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra02.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra02.cells generators
    FacetUniverses.RootedSixExtra02.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra02.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra02.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra02.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra02.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra02.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra02.S5T0

end
end
end SourcePart62

section SourcePart63
/- Original module: RootedSixExtra02CanonicalS5T1. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra02.S5T1
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N5.templates 1)
theorem template_exact : decodeTemplate 5 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 5 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 5 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra02.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra02.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra02.cells :=
  RootedCoverageFrames.RootedSixExtra02.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra02.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra02.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra02.cells generators
    FacetUniverses.RootedSixExtra02.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra02.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra02.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra02.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra02.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra02.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra02.S5T1

end
end
end SourcePart63

section SourcePart64
/- Original module: RootedSixExtra02CanonicalT2. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra02.T2
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 2)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra02.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra02.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra02.cells :=
  RootedCoverageFrames.RootedSixExtra02.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra02.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra02.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra02.cells generators
    FacetUniverses.RootedSixExtra02.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra02.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra02.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra02.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra02.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra02.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra02.T2

end
end
end SourcePart64

section SourcePart65
/- Original module: RootedSixExtra02CanonicalT4. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra02.T4
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 4)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra02.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra02.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra02.cells :=
  RootedCoverageFrames.RootedSixExtra02.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra02.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra02.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra02.cells generators
    FacetUniverses.RootedSixExtra02.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra02.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra02.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra02.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra02.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra02.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra02.T4

end
end
end SourcePart65

section SourcePart66
/- Original module: RootedSixExtra02CanonicalT5. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra02.T5
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 5)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra02.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra02.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra02.cells :=
  RootedCoverageFrames.RootedSixExtra02.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra02.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra02.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra02.cells generators
    FacetUniverses.RootedSixExtra02.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra02.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra02.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra02.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra02.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra02.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra02.T5

end
end
end SourcePart66

section SourcePart67
/- Original module: RootedSixExtra02CanonicalT6. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra02.T6
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 6)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra02.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra02.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra02.cells :=
  RootedCoverageFrames.RootedSixExtra02.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra02.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra02.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra02.cells generators
    FacetUniverses.RootedSixExtra02.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra02.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra02.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra02.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra02.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra02.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra02.T6

end
end
end SourcePart67

section SourcePart68
/- Original module: RootedSixExtra02Coverage. -/

@[expose] public section

/-!
# Complete compatible-template coverage for RootedSixExtra02

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSixExtra02

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSixExtra02

abbrev root : Fin FacetUniverses.RootedSixExtra02.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 6 ↪ Fin 10 where
  toFun := ![0, 2, 1, 4, 3, 5]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N6.templates (RawEncoding.oldToCurrent 2))) =
      decodeCell (FacetUniverses.RootedSixExtra02.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSixExtra02.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [4, 5, 7]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SixFamilyActualEncoding.Coverage FacetUniverses.RootedSixExtra02.cells root 2 quota where
  rootEmbedding := rootEmbedding
  rootCell := root_exact
  rootKind := root_kind
  complete := by
    intro a hpos f h
    cases a with
    | tetrahedron => exact S4T0.covers_exact f h
    | bipyramid => exact S5T0.covers_exact f h
    | squarePyramid => exact S5T1.covers_exact f h
    | six i =>
      fin_cases i
      · change 0 < quota 4 at hpos
        rw [hzero 4 (by decide +kernel)] at hpos
        omega
      · change 0 < quota 5 at hpos
        rw [hzero 5 (by decide +kernel)] at hpos
        omega
      · exact T2.covers_exact f h
      · change 0 < quota 7 at hpos
        rw [hzero 7 (by decide +kernel)] at hpos
        omega
      · exact T4.covers_exact f h
      · exact T5.covers_exact f h
      · exact T6.covers_exact f h

end Papers.RationalityTen.RootedCoverage.RootedSixExtra02

end
end
end SourcePart68

section SourcePart69
/- Original module: RootedSixExtra03CoverageFrames. -/

@[expose] public section

/-! The outside generators are taken from the complete checked generator
family. Their vertex codes agree with the independently checked placement
normalizers. No packed cell-map equality is an assumption. -/

noncomputable section
namespace Papers.RationalityTen.RootedCoverageFrames.RootedSixExtra03

def generator (g : Fin FacetUniverses.RootedSixExtra03.Outside.generatorCount) :
    Fin FacetUniverses.RootedSixExtra03.Generators.generatorCount :=
  ⟨g.val, Nat.lt_of_lt_of_le g.isLt (by decide +kernel)⟩

theorem vertex_code (g : Fin FacetUniverses.RootedSixExtra03.Outside.generatorCount) :
    FacetUniverses.RootedSixExtra03.Generators.vertexCode (generator g) = FacetUniverses.RootedSixExtra03.Outside.vertexCode g := by
  have h : ∀ g : Fin FacetUniverses.RootedSixExtra03.Outside.generatorCount,
      FacetUniverses.RootedSixExtra03.Generators.vertexCode (generator g) = FacetUniverses.RootedSixExtra03.Outside.vertexCode g := by
    decide +kernel
  exact h g

theorem generator_check (g : Fin FacetUniverses.RootedSixExtra03.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSixExtra03.cellCount) :
    (RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSixExtra03.Generators.forward (generator g))
      (FacetUniverses.RootedSixExtra03.Generators.inverse (generator g)) i &&
      RawGraphGrowthFrames.cellRelabelCheck
        (TenGraphEdges.vertexMap (FacetUniverses.RootedSixExtra03.Generators.vertexCode (generator g)))
        (FacetUniverses.RootedSixExtra03.cells i)
        (FacetUniverses.RootedSixExtra03.cells (FacetUniverses.RootedSixExtra03.Generators.forward (generator g) i))) = true := by
  simpa only [FacetUniverses.RootedSixExtra03.Generators.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSixExtra03.Generators.cell_checked (generator g) i

def frame (g : Fin FacetUniverses.RootedSixExtra03.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra03.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSixExtra03.cells
    (FacetUniverses.RootedSixExtra03.Generators.vertexCode (generator g))
    (FacetUniverses.RootedSixExtra03.Generators.vertexInverseCode (generator g))
    (FacetUniverses.RootedSixExtra03.Generators.vertex_checks (generator g))
    (FacetUniverses.RootedSixExtra03.Generators.forward (generator g))
    (FacetUniverses.RootedSixExtra03.Generators.inverse (generator g))
    (fun i => (Bool.and_eq_true_iff.mp (generator_check g i)).1)
    (fun i => (Bool.and_eq_true_iff.mp (generator_check g i)).2)

theorem frame_vertices (g : Fin FacetUniverses.RootedSixExtra03.Outside.generatorCount) (v : Fin 10) :
    (frame g).vertices v = TenGraphEdges.vertexMap (FacetUniverses.RootedSixExtra03.Outside.vertexCode g) v := by
  change TenGraphEdges.vertexMap (FacetUniverses.RootedSixExtra03.Generators.vertexCode (generator g)) v = _
  rw [vertex_code]

end Papers.RationalityTen.RootedCoverageFrames.RootedSixExtra03

end
end
end SourcePart69

section SourcePart70
/- Original module: RootedSixExtra03CanonicalS4T0. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra03.S4T0
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N4.templates 0)
theorem template_exact : decodeTemplate 4 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 4 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 4 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra03.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra03.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra03.cells :=
  RootedCoverageFrames.RootedSixExtra03.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra03.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra03.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra03.cells generators
    FacetUniverses.RootedSixExtra03.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra03.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 4 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra03.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra03.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra03.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 4 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra03.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra03.S4T0

end
end
end SourcePart70

section SourcePart71
/- Original module: RootedSixExtra03CanonicalS5T0. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra03.S5T0
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N5.templates 0)
theorem template_exact : decodeTemplate 5 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 5 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 5 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra03.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra03.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra03.cells :=
  RootedCoverageFrames.RootedSixExtra03.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra03.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra03.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra03.cells generators
    FacetUniverses.RootedSixExtra03.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra03.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra03.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra03.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra03.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra03.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra03.S5T0

end
end
end SourcePart71

section SourcePart72
/- Original module: RootedSixExtra03CanonicalS5T1. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra03.S5T1
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N5.templates 1)
theorem template_exact : decodeTemplate 5 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 5 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 5 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra03.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra03.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra03.cells :=
  RootedCoverageFrames.RootedSixExtra03.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra03.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra03.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra03.cells generators
    FacetUniverses.RootedSixExtra03.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra03.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra03.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra03.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra03.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra03.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra03.S5T1

end
end
end SourcePart72

section SourcePart73
/- Original module: RootedSixExtra03CanonicalT4. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra03.T4
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 4)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra03.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra03.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra03.cells :=
  RootedCoverageFrames.RootedSixExtra03.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra03.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra03.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra03.cells generators
    FacetUniverses.RootedSixExtra03.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra03.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra03.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra03.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra03.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra03.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra03.T4

end
end
end SourcePart73

section SourcePart74
/- Original module: RootedSixExtra03CanonicalT6. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra03.T6
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 6)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra03.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra03.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra03.cells :=
  RootedCoverageFrames.RootedSixExtra03.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra03.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra03.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra03.cells generators
    FacetUniverses.RootedSixExtra03.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra03.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra03.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra03.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra03.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra03.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra03.T6

end
end
end SourcePart74

section SourcePart75
/- Original module: RootedSixExtra03Coverage. -/

@[expose] public section

/-!
# Complete compatible-template coverage for RootedSixExtra03

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSixExtra03

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSixExtra03

abbrev root : Fin FacetUniverses.RootedSixExtra03.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 6 ↪ Fin 10 where
  toFun := ![0, 2, 1, 4, 3, 5]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N6.templates (RawEncoding.oldToCurrent 3))) =
      decodeCell (FacetUniverses.RootedSixExtra03.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSixExtra03.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [4, 5, 6, 7, 8]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SixFamilyActualEncoding.Coverage FacetUniverses.RootedSixExtra03.cells root 3 quota where
  rootEmbedding := rootEmbedding
  rootCell := root_exact
  rootKind := root_kind
  complete := by
    intro a hpos f h
    cases a with
    | tetrahedron => exact S4T0.covers_exact f h
    | bipyramid => exact S5T0.covers_exact f h
    | squarePyramid => exact S5T1.covers_exact f h
    | six i =>
      fin_cases i
      · change 0 < quota 4 at hpos
        rw [hzero 4 (by decide +kernel)] at hpos
        omega
      · change 0 < quota 5 at hpos
        rw [hzero 5 (by decide +kernel)] at hpos
        omega
      · change 0 < quota 8 at hpos
        rw [hzero 8 (by decide +kernel)] at hpos
        omega
      · change 0 < quota 7 at hpos
        rw [hzero 7 (by decide +kernel)] at hpos
        omega
      · exact T4.covers_exact f h
      · change 0 < quota 6 at hpos
        rw [hzero 6 (by decide +kernel)] at hpos
        omega
      · exact T6.covers_exact f h

end Papers.RationalityTen.RootedCoverage.RootedSixExtra03

end
end
end SourcePart75

section SourcePart76
/- Original module: RootedSixExtra04CoverageFrames. -/

@[expose] public section

/-! The outside generators are taken from the complete checked generator
family. Their vertex codes agree with the independently checked placement
normalizers. No packed cell-map equality is an assumption. -/

noncomputable section
namespace Papers.RationalityTen.RootedCoverageFrames.RootedSixExtra04

def generator (g : Fin FacetUniverses.RootedSixExtra04.Outside.generatorCount) :
    Fin FacetUniverses.RootedSixExtra04.Generators.generatorCount :=
  ⟨g.val, Nat.lt_of_lt_of_le g.isLt (by decide +kernel)⟩

theorem vertex_code (g : Fin FacetUniverses.RootedSixExtra04.Outside.generatorCount) :
    FacetUniverses.RootedSixExtra04.Generators.vertexCode (generator g) = FacetUniverses.RootedSixExtra04.Outside.vertexCode g := by
  have h : ∀ g : Fin FacetUniverses.RootedSixExtra04.Outside.generatorCount,
      FacetUniverses.RootedSixExtra04.Generators.vertexCode (generator g) = FacetUniverses.RootedSixExtra04.Outside.vertexCode g := by
    decide +kernel
  exact h g

theorem generator_check (g : Fin FacetUniverses.RootedSixExtra04.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSixExtra04.cellCount) :
    (RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSixExtra04.Generators.forward (generator g))
      (FacetUniverses.RootedSixExtra04.Generators.inverse (generator g)) i &&
      RawGraphGrowthFrames.cellRelabelCheck
        (TenGraphEdges.vertexMap (FacetUniverses.RootedSixExtra04.Generators.vertexCode (generator g)))
        (FacetUniverses.RootedSixExtra04.cells i)
        (FacetUniverses.RootedSixExtra04.cells (FacetUniverses.RootedSixExtra04.Generators.forward (generator g) i))) = true := by
  simpa only [FacetUniverses.RootedSixExtra04.Generators.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSixExtra04.Generators.cell_checked (generator g) i

def frame (g : Fin FacetUniverses.RootedSixExtra04.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra04.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSixExtra04.cells
    (FacetUniverses.RootedSixExtra04.Generators.vertexCode (generator g))
    (FacetUniverses.RootedSixExtra04.Generators.vertexInverseCode (generator g))
    (FacetUniverses.RootedSixExtra04.Generators.vertex_checks (generator g))
    (FacetUniverses.RootedSixExtra04.Generators.forward (generator g))
    (FacetUniverses.RootedSixExtra04.Generators.inverse (generator g))
    (fun i => (Bool.and_eq_true_iff.mp (generator_check g i)).1)
    (fun i => (Bool.and_eq_true_iff.mp (generator_check g i)).2)

theorem frame_vertices (g : Fin FacetUniverses.RootedSixExtra04.Outside.generatorCount) (v : Fin 10) :
    (frame g).vertices v = TenGraphEdges.vertexMap (FacetUniverses.RootedSixExtra04.Outside.vertexCode g) v := by
  change TenGraphEdges.vertexMap (FacetUniverses.RootedSixExtra04.Generators.vertexCode (generator g)) v = _
  rw [vertex_code]

end Papers.RationalityTen.RootedCoverageFrames.RootedSixExtra04

end
end
end SourcePart76

section SourcePart77
/- Original module: RootedSixExtra04CanonicalS4T0. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra04.S4T0
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N4.templates 0)
theorem template_exact : decodeTemplate 4 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 4 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 4 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra04.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra04.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra04.cells :=
  RootedCoverageFrames.RootedSixExtra04.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra04.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra04.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra04.cells generators
    FacetUniverses.RootedSixExtra04.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra04.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 4 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra04.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra04.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra04.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 4 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra04.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra04.S4T0

end
end
end SourcePart77

section SourcePart78
/- Original module: RootedSixExtra04CanonicalS5T0. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra04.S5T0
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N5.templates 0)
theorem template_exact : decodeTemplate 5 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 5 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 5 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra04.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra04.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra04.cells :=
  RootedCoverageFrames.RootedSixExtra04.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra04.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra04.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra04.cells generators
    FacetUniverses.RootedSixExtra04.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra04.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra04.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra04.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra04.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra04.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra04.S5T0

end
end
end SourcePart78

section SourcePart79
/- Original module: RootedSixExtra04CanonicalS5T1. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra04.S5T1
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N5.templates 1)
theorem template_exact : decodeTemplate 5 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 5 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 5 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra04.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra04.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra04.cells :=
  RootedCoverageFrames.RootedSixExtra04.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra04.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra04.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra04.cells generators
    FacetUniverses.RootedSixExtra04.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra04.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra04.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra04.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra04.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra04.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra04.S5T1

end
end
end SourcePart79

section SourcePart80
/- Original module: RootedSixExtra04CanonicalT4. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra04.T4
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 4)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra04.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra04.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra04.cells :=
  RootedCoverageFrames.RootedSixExtra04.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra04.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra04.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra04.cells generators
    FacetUniverses.RootedSixExtra04.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra04.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra04.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra04.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra04.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra04.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra04.T4

end
end
end SourcePart80

section SourcePart81
/- Original module: RootedSixExtra04CanonicalT6. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra04.T6
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 6)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra04.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra04.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra04.cells :=
  RootedCoverageFrames.RootedSixExtra04.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra04.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra04.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra04.cells generators
    FacetUniverses.RootedSixExtra04.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra04.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra04.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra04.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra04.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra04.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra04.T6

end
end
end SourcePart81

section SourcePart82
/- Original module: RootedSixExtra04Coverage. -/

@[expose] public section

/-!
# Complete compatible-template coverage for RootedSixExtra04

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSixExtra04

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSixExtra04

abbrev root : Fin FacetUniverses.RootedSixExtra04.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 6 ↪ Fin 10 where
  toFun := ![0, 1, 2, 3, 4, 5]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N6.templates (RawEncoding.oldToCurrent 4))) =
      decodeCell (FacetUniverses.RootedSixExtra04.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSixExtra04.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [4, 5, 6, 7, 8]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SixFamilyActualEncoding.Coverage FacetUniverses.RootedSixExtra04.cells root 4 quota where
  rootEmbedding := rootEmbedding
  rootCell := root_exact
  rootKind := root_kind
  complete := by
    intro a hpos f h
    cases a with
    | tetrahedron => exact S4T0.covers_exact f h
    | bipyramid => exact S5T0.covers_exact f h
    | squarePyramid => exact S5T1.covers_exact f h
    | six i =>
      fin_cases i
      · change 0 < quota 4 at hpos
        rw [hzero 4 (by decide +kernel)] at hpos
        omega
      · change 0 < quota 5 at hpos
        rw [hzero 5 (by decide +kernel)] at hpos
        omega
      · change 0 < quota 8 at hpos
        rw [hzero 8 (by decide +kernel)] at hpos
        omega
      · change 0 < quota 7 at hpos
        rw [hzero 7 (by decide +kernel)] at hpos
        omega
      · exact T4.covers_exact f h
      · change 0 < quota 6 at hpos
        rw [hzero 6 (by decide +kernel)] at hpos
        omega
      · exact T6.covers_exact f h

end Papers.RationalityTen.RootedCoverage.RootedSixExtra04

end
end
end SourcePart82

section SourcePart83
/- Original module: RootedSixExtra05CoverageFrames. -/

@[expose] public section

/-! The outside generators are taken from the complete checked generator
family. Their vertex codes agree with the independently checked placement
normalizers. No packed cell-map equality is an assumption. -/

noncomputable section
namespace Papers.RationalityTen.RootedCoverageFrames.RootedSixExtra05

def generator (g : Fin FacetUniverses.RootedSixExtra05.Outside.generatorCount) :
    Fin FacetUniverses.RootedSixExtra05.Generators.generatorCount :=
  ⟨g.val, Nat.lt_of_lt_of_le g.isLt (by decide +kernel)⟩

theorem vertex_code (g : Fin FacetUniverses.RootedSixExtra05.Outside.generatorCount) :
    FacetUniverses.RootedSixExtra05.Generators.vertexCode (generator g) = FacetUniverses.RootedSixExtra05.Outside.vertexCode g := by
  have h : ∀ g : Fin FacetUniverses.RootedSixExtra05.Outside.generatorCount,
      FacetUniverses.RootedSixExtra05.Generators.vertexCode (generator g) = FacetUniverses.RootedSixExtra05.Outside.vertexCode g := by
    decide +kernel
  exact h g

theorem generator_check (g : Fin FacetUniverses.RootedSixExtra05.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSixExtra05.cellCount) :
    (RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSixExtra05.Generators.forward (generator g))
      (FacetUniverses.RootedSixExtra05.Generators.inverse (generator g)) i &&
      RawGraphGrowthFrames.cellRelabelCheck
        (TenGraphEdges.vertexMap (FacetUniverses.RootedSixExtra05.Generators.vertexCode (generator g)))
        (FacetUniverses.RootedSixExtra05.cells i)
        (FacetUniverses.RootedSixExtra05.cells (FacetUniverses.RootedSixExtra05.Generators.forward (generator g) i))) = true := by
  simpa only [FacetUniverses.RootedSixExtra05.Generators.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSixExtra05.Generators.cell_checked (generator g) i

def frame (g : Fin FacetUniverses.RootedSixExtra05.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra05.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSixExtra05.cells
    (FacetUniverses.RootedSixExtra05.Generators.vertexCode (generator g))
    (FacetUniverses.RootedSixExtra05.Generators.vertexInverseCode (generator g))
    (FacetUniverses.RootedSixExtra05.Generators.vertex_checks (generator g))
    (FacetUniverses.RootedSixExtra05.Generators.forward (generator g))
    (FacetUniverses.RootedSixExtra05.Generators.inverse (generator g))
    (fun i => (Bool.and_eq_true_iff.mp (generator_check g i)).1)
    (fun i => (Bool.and_eq_true_iff.mp (generator_check g i)).2)

theorem frame_vertices (g : Fin FacetUniverses.RootedSixExtra05.Outside.generatorCount) (v : Fin 10) :
    (frame g).vertices v = TenGraphEdges.vertexMap (FacetUniverses.RootedSixExtra05.Outside.vertexCode g) v := by
  change TenGraphEdges.vertexMap (FacetUniverses.RootedSixExtra05.Generators.vertexCode (generator g)) v = _
  rw [vertex_code]

end Papers.RationalityTen.RootedCoverageFrames.RootedSixExtra05

end
end
end SourcePart83

section SourcePart84
/- Original module: RootedSixExtra05CanonicalS4T0. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S4T0
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N4.templates 0)
theorem template_exact : decodeTemplate 4 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 4 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 4 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra05.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra05.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra05.cells :=
  RootedCoverageFrames.RootedSixExtra05.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra05.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra05.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra05.cells generators
    FacetUniverses.RootedSixExtra05.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra05.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 4 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra05.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra05.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra05.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 4 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra05.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S4T0

end
end
end SourcePart84

section SourcePart85
/- Original module: RootedSixExtra05CanonicalS5T0. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S5T0
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N5.templates 0)
theorem template_exact : decodeTemplate 5 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 5 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 5 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra05.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra05.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra05.cells :=
  RootedCoverageFrames.RootedSixExtra05.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra05.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra05.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra05.cells generators
    FacetUniverses.RootedSixExtra05.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra05.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra05.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra05.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra05.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra05.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S5T0

end
end
end SourcePart85

section SourcePart86
/- Original module: RootedSixExtra05CanonicalS5T1. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S5T1
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N5.templates 1)
theorem template_exact : decodeTemplate 5 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 5 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 5 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra05.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra05.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra05.cells :=
  RootedCoverageFrames.RootedSixExtra05.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra05.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra05.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra05.cells generators
    FacetUniverses.RootedSixExtra05.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra05.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra05.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra05.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra05.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra05.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S5T1

end
end
end SourcePart86

section SourcePart87
/- Original module: RootedSixExtra05CanonicalT4. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra05.T4
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 4)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra05.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra05.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra05.cells :=
  RootedCoverageFrames.RootedSixExtra05.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra05.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra05.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra05.cells generators
    FacetUniverses.RootedSixExtra05.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra05.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra05.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra05.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra05.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra05.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra05.T4

end
end
end SourcePart87

section SourcePart88
/- Original module: RootedSixExtra05CanonicalT6. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra05.T6
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 6)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra05.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra05.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra05.cells :=
  RootedCoverageFrames.RootedSixExtra05.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra05.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra05.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra05.cells generators
    FacetUniverses.RootedSixExtra05.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra05.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra05.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra05.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra05.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra05.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra05.T6

end
end
end SourcePart88

section SourcePart89
/- Original module: RootedSixExtra05Coverage. -/

@[expose] public section

/-!
# Complete compatible-template coverage for RootedSixExtra05

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSixExtra05

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSixExtra05

abbrev root : Fin FacetUniverses.RootedSixExtra05.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 6 ↪ Fin 10 where
  toFun := ![0, 1, 2, 4, 3, 5]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N6.templates (RawEncoding.oldToCurrent 5))) =
      decodeCell (FacetUniverses.RootedSixExtra05.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSixExtra05.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [4, 5, 6, 7, 8]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SixFamilyActualEncoding.Coverage FacetUniverses.RootedSixExtra05.cells root 5 quota where
  rootEmbedding := rootEmbedding
  rootCell := root_exact
  rootKind := root_kind
  complete := by
    intro a hpos f h
    cases a with
    | tetrahedron => exact S4T0.covers_exact f h
    | bipyramid => exact S5T0.covers_exact f h
    | squarePyramid => exact S5T1.covers_exact f h
    | six i =>
      fin_cases i
      · change 0 < quota 4 at hpos
        rw [hzero 4 (by decide +kernel)] at hpos
        omega
      · change 0 < quota 5 at hpos
        rw [hzero 5 (by decide +kernel)] at hpos
        omega
      · change 0 < quota 8 at hpos
        rw [hzero 8 (by decide +kernel)] at hpos
        omega
      · change 0 < quota 7 at hpos
        rw [hzero 7 (by decide +kernel)] at hpos
        omega
      · exact T4.covers_exact f h
      · change 0 < quota 6 at hpos
        rw [hzero 6 (by decide +kernel)] at hpos
        omega
      · exact T6.covers_exact f h

end Papers.RationalityTen.RootedCoverage.RootedSixExtra05

end
end
end SourcePart89

section SourcePart90
/- Original module: RootedSixExtra06CoverageFrames. -/

@[expose] public section

/-! The outside generators are taken from the complete checked generator
family. Their vertex codes agree with the independently checked placement
normalizers. No packed cell-map equality is an assumption. -/

noncomputable section
namespace Papers.RationalityTen.RootedCoverageFrames.RootedSixExtra06

def generator (g : Fin FacetUniverses.RootedSixExtra06.Outside.generatorCount) :
    Fin FacetUniverses.RootedSixExtra06.Generators.generatorCount :=
  ⟨g.val, Nat.lt_of_lt_of_le g.isLt (by decide +kernel)⟩

theorem vertex_code (g : Fin FacetUniverses.RootedSixExtra06.Outside.generatorCount) :
    FacetUniverses.RootedSixExtra06.Generators.vertexCode (generator g) = FacetUniverses.RootedSixExtra06.Outside.vertexCode g := by
  have h : ∀ g : Fin FacetUniverses.RootedSixExtra06.Outside.generatorCount,
      FacetUniverses.RootedSixExtra06.Generators.vertexCode (generator g) = FacetUniverses.RootedSixExtra06.Outside.vertexCode g := by
    decide +kernel
  exact h g

theorem generator_check (g : Fin FacetUniverses.RootedSixExtra06.Outside.generatorCount)
    (i : Fin FacetUniverses.RootedSixExtra06.cellCount) :
    (RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.RootedSixExtra06.Generators.forward (generator g))
      (FacetUniverses.RootedSixExtra06.Generators.inverse (generator g)) i &&
      RawGraphGrowthFrames.cellRelabelCheck
        (TenGraphEdges.vertexMap (FacetUniverses.RootedSixExtra06.Generators.vertexCode (generator g)))
        (FacetUniverses.RootedSixExtra06.cells i)
        (FacetUniverses.RootedSixExtra06.cells (FacetUniverses.RootedSixExtra06.Generators.forward (generator g) i))) = true := by
  simpa only [FacetUniverses.RootedSixExtra06.Generators.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSixExtra06.Generators.cell_checked (generator g) i

def frame (g : Fin FacetUniverses.RootedSixExtra06.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra06.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.RootedSixExtra06.cells
    (FacetUniverses.RootedSixExtra06.Generators.vertexCode (generator g))
    (FacetUniverses.RootedSixExtra06.Generators.vertexInverseCode (generator g))
    (FacetUniverses.RootedSixExtra06.Generators.vertex_checks (generator g))
    (FacetUniverses.RootedSixExtra06.Generators.forward (generator g))
    (FacetUniverses.RootedSixExtra06.Generators.inverse (generator g))
    (fun i => (Bool.and_eq_true_iff.mp (generator_check g i)).1)
    (fun i => (Bool.and_eq_true_iff.mp (generator_check g i)).2)

theorem frame_vertices (g : Fin FacetUniverses.RootedSixExtra06.Outside.generatorCount) (v : Fin 10) :
    (frame g).vertices v = TenGraphEdges.vertexMap (FacetUniverses.RootedSixExtra06.Outside.vertexCode g) v := by
  change TenGraphEdges.vertexMap (FacetUniverses.RootedSixExtra06.Generators.vertexCode (generator g)) v = _
  rw [vertex_code]

end Papers.RationalityTen.RootedCoverageFrames.RootedSixExtra06

end
end
end SourcePart90

section SourcePart91
/- Original module: RootedSixExtra06CanonicalS4T0. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S4T0
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N4.templates 0)
theorem template_exact : decodeTemplate 4 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 4 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 4 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra06.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra06.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra06.cells :=
  RootedCoverageFrames.RootedSixExtra06.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra06.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra06.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra06.cells generators
    FacetUniverses.RootedSixExtra06.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra06.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 4 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra06.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra06.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra06.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 4 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra06.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S4T0

end
end
end SourcePart91

section SourcePart92
/- Original module: RootedSixExtra06CanonicalS5T0. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S5T0
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N5.templates 0)
theorem template_exact : decodeTemplate 5 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 5 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 5 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra06.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra06.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra06.cells :=
  RootedCoverageFrames.RootedSixExtra06.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra06.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra06.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra06.cells generators
    FacetUniverses.RootedSixExtra06.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra06.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra06.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra06.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra06.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra06.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S5T0

end
end
end SourcePart92

section SourcePart93
/- Original module: RootedSixExtra06CanonicalS5T1. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S5T1
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N5.templates 1)
theorem template_exact : decodeTemplate 5 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 5 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 5 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra06.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra06.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra06.cells :=
  RootedCoverageFrames.RootedSixExtra06.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra06.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra06.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra06.cells generators
    FacetUniverses.RootedSixExtra06.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra06.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra06.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra06.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra06.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra06.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S5T1

end
end
end SourcePart93

section SourcePart94
/- Original module: RootedSixExtra06CanonicalT4. -/

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra06.T4
open FaceNormalizerSemantics RawFacetEmbeddingSemantics
open LiteralMaskGeometry ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N6.templates 4)
theorem template_exact : decodeTemplate 6 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem local_vertices : localCell.vertices = Finset.univ := by decide +kernel
theorem root_wellFormed : WellFormed root := wellFormed_of_check _ metadata_root
theorem validity_complete : FiniteChecks.Interval validity 0 blockCount :=
  metadata_validity
theorem valid (i : Fin blockCount) : RawFaceNormalizers.blockValidCheck 6 (raw i) = true :=
  by simpa only [validity, Fin.ofNat_val_eq_self] using
    validity_complete i.val (Nat.zero_le _) i.isLt
noncomputable def blocks (i : Fin blockCount) : FacePlacementCodes.Block 6 :=
  checkedBlock (raw i) (valid i)
theorem normalizers_complete : FacePlacementGeometry.CompleteBlocks localCell (decodeCell root) blocks := by
  rw [← template_exact]
  exact completeCheck_sound template root raw valid faceWitness metadata_normalizers
theorem root_edges : ∀ e ∈ (decodeCell root).edges,
    e ⊆ (decodeCell root).vertices := by decide +kernel
theorem root_ridges : ∀ q ∈ (decodeCell root).ridges,
    q ⊆ (decodeCell root).vertices := by decide +kernel
theorem symmetry_complete : FiniteChecks.Interval symmetry 0 blockCount :=
  metadata_symmetry
theorem symmetry_checked (i : Fin blockCount) :
    RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra06.Outside.vertexCode root.vertices (raw i) = true :=
  by simpa only [symmetry, Fin.ofNat_val_eq_self] using
    symmetry_complete i.val (Nat.zero_le _) i.isLt
/-- The complete checked generator family supplies the outside swaps. -/
noncomputable def generators (g : Fin FacetUniverses.RootedSixExtra06.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra06.cells :=
  RootedCoverageFrames.RootedSixExtra06.frame g
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.RootedSixExtra06.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.RootedSixExtra06.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.RootedSixExtra06.cells generators
    FacetUniverses.RootedSixExtra06.Outside.vertexCode
    RootedCoverageFrames.RootedSixExtra06.frame_vertices root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 6 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.RootedSixExtra06.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.RootedSixExtra06.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.RootedSixExtra06.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 6 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.RootedSixExtra06.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.RootedSixExtra06.T4

end
end
end SourcePart94

section SourcePart95
/- Original module: RootedSixExtra06Coverage. -/

@[expose] public section

/-!
# Complete compatible-template coverage for RootedSixExtra06

The full canonical placement theorems retain vertices, edges, polygons
and the candidate kind. An omitted positive tag can be used only with
zero quota. Root labels are explicitly transported from the complete
local catalogue to the original finite universe.
-/

noncomputable section
namespace Papers.RationalityTen.RootedCoverage.RootedSixExtra06

open SixFacetProfileRefinement ActualFacetCatalogueTransport LiteralMaskGeometry
open RootedCanonical.RootedSixExtra06

abbrev root : Fin FacetUniverses.RootedSixExtra06.cellCount := 0

/-- Current local labels map to the original universe root labels. -/
def rootEmbedding : Fin 6 ↪ Fin 10 where
  toFun := ![0, 1, 2, 3, 4, 5]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding
      (cellOfBoundary (FiniteCycleCandidates.N6.templates (RawEncoding.oldToCurrent 6))) =
      decodeCell (FacetUniverses.RootedSixExtra06.cells root) := by
  apply cell_ext <;> decide +kernel

theorem root_kind : (FacetUniverses.RootedSixExtra06.cells root).kind = 0 := by
  decide +kernel

/-- Exactly the omitted tags among the permitted nonroot local kinds. -/
def omittedTags : List Nat := [4, 5, 6, 7, 8, 9]

def coverage (quota : Nat → Nat)
    (hzero : ∀ k, k ∈ omittedTags → quota k = 0) :
    SixFamilyActualEncoding.Coverage FacetUniverses.RootedSixExtra06.cells root 6 quota where
  rootEmbedding := rootEmbedding
  rootCell := root_exact
  rootKind := root_kind
  complete := by
    intro a hpos f h
    cases a with
    | tetrahedron => exact S4T0.covers_exact f h
    | bipyramid => exact S5T0.covers_exact f h
    | squarePyramid => exact S5T1.covers_exact f h
    | six i =>
      fin_cases i
      · change 0 < quota 4 at hpos
        rw [hzero 4 (by decide +kernel)] at hpos
        omega
      · change 0 < quota 5 at hpos
        rw [hzero 5 (by decide +kernel)] at hpos
        omega
      · change 0 < quota 8 at hpos
        rw [hzero 8 (by decide +kernel)] at hpos
        omega
      · change 0 < quota 7 at hpos
        rw [hzero 7 (by decide +kernel)] at hpos
        omega
      · exact T4.covers_exact f h
      · change 0 < quota 6 at hpos
        rw [hzero 6 (by decide +kernel)] at hpos
        omega
      · change 0 < quota 9 at hpos
        rw [hzero 9 (by decide +kernel)] at hpos
        omega

end Papers.RationalityTen.RootedCoverage.RootedSixExtra06

end
end
end SourcePart95
