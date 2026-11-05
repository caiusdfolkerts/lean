module

public import RawKindedFacePlacement
public import FaceNormalizerSemantics

@[expose] public section

noncomputable section
namespace Papers.RationalityTen.KindedRootedFacetCoverage

open Finset
open MatroidChecked.FacetBoundaryEncoding ActualFacetCatalogueTransport
open LiteralMaskGeometry RawFacetEmbeddingSemantics
open FacePlacementCodes FacePlacementGeometry RootedFacetCoverage

/-- Complete compatible-template coverage with its exact prescribed kind.
No property of unused candidate records is assumed. -/
theorem covers_of_checks {m b n : Nat} (template root : ConcreteGrowth.Cell)
    (C : Cell m) (htemplate : decodeTemplate m template = C)
    (hvertices : C.vertices = Finset.univ) (hroot : WellFormed root)
    (cells : Fin n → ConcreteGrowth.Cell) (blocks : Fin b → Block m)
    (raw : Fin b → RawFacePlacement.Block)
    (H : ∀ i, Representation (blocks i) (raw i))
    (hblocks : CompleteBlocks C (decodeCell root) blocks)
    (witness : Fin b → Nat → Fin n)
    (hchecks : ∀ i, FiniteChecks.Interval
      (RawKindedFacePlacement.intervalCheck m (raw i) template root cells (witness i))
      0 (RawFacePlacement.count (raw i).shared (raw i).shared *
        RawFacePlacement.count (raw i).outside (m - (raw i).shared))) :
    ∀ f : Fin m ↪ Fin 10, (mapCell f C).Compatible (decodeCell root) →
      ∃ j, (cells j).kind = template.kind ∧ decodeCell (cells j) = mapCell f C := by
  intro f hf
  obtain ⟨i, inner, hi, outer, ho, hdecode⟩ :=
    exists_block_and_codes C (decodeCell root) hvertices blocks hblocks f hf
  have hfg (j : Fin m) : RawFacePlacement.label m (raw i) inner outer j.val = (f j).val := by
    rw [label_eq_decoded _ _ (H i), hdecode]
  let placed := RawFacetEmbedding.mapCell m (RawFacePlacement.label m (raw i) inner outer) template
  have hplaced : decodeCell placed = mapCell f C := by
    rw [decode_mapCell _ f hfg template, htemplate]
    rfl
  have hbound : Bounds placed := mapCell_bounds m _ (fun j hj => by
    rw [hfg ⟨j, hj⟩]
    exact (f ⟨j, hj⟩).isLt) template
  have hc : RawFacePlacement.compatible placed root = true :=
    compatible_of_geometry placed root hbound (bounds_of_wellFormed root hroot)
      (hplaced.symm ▸ hf)
  have hi' : inner < RawFacePlacement.count (raw i).shared (raw i).shared := by
    simpa only [(H i).shared, count_eq] using hi
  have ho' : outer < RawFacePlacement.count (raw i).outside (m - (raw i).shared) := by
    simpa only [(H i).shared, (H i).outside, count_eq] using ho
  have hcheck := RawKindedFacePlacement.check_of_interval (raw i) template root cells (witness i)
    (hchecks i) inner outer hi' ho'
  unfold RawKindedFacePlacement.check at hcheck
  change (!RawFacePlacement.compatible placed root || _) = true at hcheck
  rw [hc, Bool.not_true, Bool.false_or] at hcheck
  obtain ⟨hkind, hgeometry⟩ := Bool.and_eq_true_iff.mp hcheck
  exact ⟨_, of_decide_eq_true hkind, (sameGeometry_decoded hgeometry).trans hplaced⟩

end Papers.RationalityTen.KindedRootedFacetCoverage
