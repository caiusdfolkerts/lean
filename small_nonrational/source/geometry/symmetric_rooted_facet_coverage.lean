module

public import OutsideBoundarySymmetry
public import KindedRootedFacetCoverage

@[expose] public section

/-!
# Complete rooted coverage from one outside placement

Only the inner common-face labels are enumerated in the geometric checks.
All outer injections are recovered using checked outside-swap frames and
the complete symmetric-group theorem. Every original injective placement
is still covered, with its exact prescribed kind.
-/

noncomputable section
namespace Papers.RationalityTen.SymmetricRootedFacetCoverage

open Finset
open MatroidChecked.FacetBoundaryEncoding ActualFacetCatalogueTransport
open LiteralMaskGeometry RawFacetEmbeddingSemantics
open FacePlacementCodes FacePlacementGeometry RootedFacetCoverage
open BoundaryGeneratorFrames OutsideBoundarySymmetry

theorem covers_of_canonical_checks {m b n : Nat} (template root : ConcreteGrowth.Cell)
    (C : Cell m) (htemplate : decodeTemplate m template = C)
    (hvertices : C.vertices = Finset.univ) (hroot : WellFormed root)
    (hedges : ∀ e ∈ (decodeCell root).edges, e ⊆ (decodeCell root).vertices)
    (hridges : ∀ q ∈ (decodeCell root).ridges, q ⊆ (decodeCell root).vertices)
    (cells : Fin n → ConcreteGrowth.Cell) (blocks : Fin b → Block m)
    (raw : Fin b → RawFacePlacement.Block)
    (H : ∀ i, Representation (blocks i) (raw i))
    (hblocks : CompleteBlocks C (decodeCell root) blocks)
    (houtside : ∀ i, ∀ j : Fin (blocks i).outside,
      outsideEmbedding (blocks i) j ∉ (decodeCell root).vertices)
    (hgenerators : ∀ i, ∀ j : Fin ((blocks i).outside - 1),
      ∃ F : BoundaryFrame cells,
        F.vertices = (adjacentSwap (blocks i).outside j).viaEmbedding
          (outsideEmbedding (blocks i)))
    (witness : Fin b → Nat → Fin n)
    (hchecks : ∀ i, FiniteChecks.Interval
      (fun inner => RawKindedFacePlacement.check m (raw i) template root cells
        inner 0 (witness i inner))
      0 (RawFacePlacement.count (raw i).shared (raw i).shared)) :
    ∀ f : Fin m ↪ Fin 10, (mapCell f C).Compatible (decodeCell root) →
      ∃ j, (cells j).kind = template.kind ∧ decodeCell (cells j) = mapCell f C := by
  intro f hf
  obtain ⟨i, inner, hi, outer, _, hdecode⟩ :=
    exists_block_and_codes C (decodeCell root) hvertices blocks hblocks f hf
  obtain ⟨σ, hfactor⟩ := decoded_factor (blocks i) inner outer
  obtain ⟨F, hF⟩ := frames_of_adjacent cells (outsideEmbedding (blocks i))
    (hgenerators i) σ
  have hrootFix : mapCell F.vertices.toEmbedding (decodeCell root) = decodeCell root := by
    rw [hF]
    apply mapCell_fixed (decodeCell root) (outsideEmbedding (blocks i)) _ hedges hridges σ
    intro v hv
    rintro ⟨j, rfl⟩
    exact houtside i j hv
  have hrootInverse : mapCell F.vertices.symm.toEmbedding (decodeCell root) = decodeCell root := by
    have h := congrArg (mapCell F.vertices.symm.toEmbedding) hrootFix
    rw [CellRelabelGeometry.mapCell_inverse] at h
    exact h.symm
  let g : Fin m ↪ Fin 10 := f.trans F.vertices.symm.toEmbedding
  have hgcell : mapCell g C = mapCell F.vertices.symm.toEmbedding (mapCell f C) := by
    apply cell_ext <;>
      simp only [mapCell, g, Finset.image_image, Function.comp_def,
        Function.Embedding.trans_apply, Equiv.toEmbedding_apply] <;> rfl
  have hgcompatible : (mapCell g C).Compatible (decodeCell root) := by
    have h := CellRelabelGeometry.compatible_mapCell F.vertices.symm _ _ hf
    rw [hrootInverse, ← hgcell] at h
    exact h
  have hcanonical (j : Fin m) : (blocks i).decoded inner 0 j = g j := by
    apply F.vertices.injective
    change F.vertices ((blocks i).decoded inner 0 j) =
      F.vertices (F.vertices.symm (f j))
    rw [F.vertices.apply_symm_apply, hF, hfactor]
    exact congrFun hdecode j
  have hlabel (j : Fin m) :
      RawFacePlacement.label m (raw i) inner 0 j.val = (g j).val := by
    rw [label_eq_decoded _ _ (H i), hcanonical]
  let placed := RawFacetEmbedding.mapCell m (RawFacePlacement.label m (raw i) inner 0) template
  have hplaced : decodeCell placed = mapCell g C := by
    rw [decode_mapCell _ g hlabel template, htemplate]
    rfl
  have hbound : Bounds placed := mapCell_bounds m _ (fun j hj => by
    rw [hlabel ⟨j, hj⟩]
    exact (g ⟨j, hj⟩).isLt) template
  have hc : RawFacePlacement.compatible placed root = true :=
    compatible_of_geometry placed root hbound (bounds_of_wellFormed root hroot)
      (hplaced.symm ▸ hgcompatible)
  have hi' : inner < RawFacePlacement.count (raw i).shared (raw i).shared := by
    simpa only [(H i).shared, count_eq] using hi
  have hcheck := hchecks i inner (Nat.zero_le _) hi'
  unfold RawKindedFacePlacement.check at hcheck
  change (!RawFacePlacement.compatible placed root || _) = true at hcheck
  rw [hc, Bool.not_true, Bool.false_or] at hcheck
  obtain ⟨hkind, hgeometry⟩ := Bool.and_eq_true_iff.mp hcheck
  refine ⟨F.cellMap.forward (witness i inner), ?_, ?_⟩
  · exact (F.kind_preserved _).trans (of_decide_eq_true hkind)
  · rw [F.cell_geometry, (sameGeometry_decoded hgeometry).trans hplaced, hgcell]
    simpa only [Equiv.symm_symm] using
      (CellRelabelGeometry.mapCell_inverse F.vertices.symm (mapCell f C))

end Papers.RationalityTen.SymmetricRootedFacetCoverage
