module
public import SmallFacetUniverseCanonicalS5T1Placement
public import SmallFacetUniverseCanonicalS5T1Finite
public import KindedRootedFacetCoverage
public import FinitePolygonTemplates
public import SmallFacetUniverseOutside
public import SymmetricRootedFacetCoverage
public import OutsidePlacementSemantics


@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace Papers.RationalityTen.RootedCanonical.SmallFacetUniverse.S5T1
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
  FiniteChecks.fin_of_interval
    (fun j : Fin blockCount => RawFaceNormalizers.blockValidCheck 5 (raw j))
    validity_complete i
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
    RawOutsidePlacement.blockCheck FacetUniverses.Small.Outside.vertexCode root.vertices (raw i) = true :=
  FiniteChecks.fin_of_interval
    (fun j : Fin blockCount => RawOutsidePlacement.blockCheck
      FacetUniverses.Small.Outside.vertexCode root.vertices (raw j))
    symmetry_complete i
theorem generator_check (g : Fin FacetUniverses.Small.Outside.generatorCount)
    (i : Fin FacetUniverses.Small.cellCount) :
    (RawGraphGrowthFrames.inverseCheckAt (FacetUniverses.Small.Outside.forward g)
      (FacetUniverses.Small.Outside.forward g) i &&
      RawGraphGrowthFrames.cellRelabelCheck
        (TenGraphEdges.vertexMap (FacetUniverses.Small.Outside.vertexCode g))
        (FacetUniverses.Small.cells i)
        (FacetUniverses.Small.cells (FacetUniverses.Small.Outside.forward g i))) = true := by
  simpa only [FacetUniverses.Small.Outside.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.Small.Outside.cell_checked g i
noncomputable def generators (g : Fin FacetUniverses.Small.Outside.generatorCount) :
    BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.Small.cells :=
  BoundaryGeneratorFrames.checkedFrame FacetUniverses.Small.cells
    (FacetUniverses.Small.Outside.vertexCode g) (FacetUniverses.Small.Outside.vertexCode g)
    (FacetUniverses.Small.Outside.vertex_checks g)
    (FacetUniverses.Small.Outside.forward g) (FacetUniverses.Small.Outside.forward g)
    (fun i => (Bool.and_eq_true_iff.mp (generator_check g i)).1)
    (fun i => (Bool.and_eq_true_iff.mp (generator_check g i)).2)
theorem outside_avoids (i : Fin blockCount) (j : Fin (blocks i).outside) :
    OutsideBoundarySymmetry.outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices :=
  OutsidePlacementSemantics.outside_avoids_root FacetUniverses.Small.Outside.vertexCode root
    (blocks i) (raw i) (checkedBlock_representation _ _) (symmetry_checked i) j
theorem outside_generators (i : Fin blockCount) (j : Fin ((blocks i).outside - 1)) :
    ∃ F : BoundaryGeneratorFrames.BoundaryFrame FacetUniverses.Small.cells,
      F.vertices = (OutsideBoundarySymmetry.adjacentSwap (blocks i).outside j).viaEmbedding
        (OutsideBoundarySymmetry.outsideEmbedding (blocks i)) :=
  OutsidePlacementSemantics.adjacent_frame FacetUniverses.Small.cells generators
    FacetUniverses.Small.Outside.vertexCode (fun _ _ => rfl) root (blocks i) (raw i)
    (checkedBlock_representation _ _) (symmetry_checked i) j
theorem covers_exact : ∀ f : Fin 5 ↪ Fin 10,
    (mapCell f localCell).Compatible (decodeCell root) →
      ∃ i, (FacetUniverses.Small.cells i).kind = template.kind ∧
        decodeCell (FacetUniverses.Small.cells i) = mapCell f localCell :=
  SymmetricRootedFacetCoverage.covers_of_canonical_checks
    template root localCell template_exact local_vertices root_wellFormed root_edges root_ridges
    FacetUniverses.Small.cells blocks raw (fun i => checkedBlock_representation _ _)
    normalizers_complete outside_avoids outside_generators witness placement_checks
theorem covers (f : Fin 5 ↪ Fin 10)
    (h : (mapCell f localCell).Compatible (decodeCell root)) :
    ∃ i, decodeCell (FacetUniverses.Small.cells i) = mapCell f localCell := by
  obtain ⟨i, _, hi⟩ := covers_exact f h
  exact ⟨i, hi⟩
end Papers.RationalityTen.RootedCanonical.SmallFacetUniverse.S5T1
