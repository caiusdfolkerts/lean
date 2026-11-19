module

public import Continuation.Geometry.OriginalLatticeAtlas

@[expose] public section

/-!
# Scheme-theoretic overlaps of the original-lattice charts

The square formed by the two original character inclusions is the actual
pullback of the two chart maps into the unchanged scheme.  The comparisons
also commute with the structural morphisms to the base field.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PaperVerification.ToricCharacters PaperVerification.ToricGeometry
open TauCeti.Toric
open scoped Classical

universe u v

namespace PaperVerification.OriginalLatticeCharts

variable {N : Type u} [AddCommGroup N]
    {V : Type v} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} (b : Module.Basis (Fin n) ℤ N)
    {ι : N →+ V} (hi : IsIntegralLattice ι)
    (k : Type u) [CommRing k]

private theorem coneChartFaceMap_eqToHom {r r' s : Finset (Lattice n)}
    (h : r = r') (hrs : r ⊆ s) :
    eqToHom (congrArg (coneChart k) h) ≫ coneChartFaceMap k (h ▸ hrs) =
      coneChartFaceMap k hrs := by
  subst r'
  simp

def intersectionChartIso (s t : Finset N) :
    affineChart hi k (s ∩ t) ≅
      coneChart k (s.image b.equivFun ∩ t.image b.equivFun) :=
  affineChartIso b hi k (s ∩ t) ≪≫
    eqToIso (congrArg (coneChart k) (Finset.image_inter s t b.equivFun.injective))

theorem intersectionChartIso_left (s t : Finset N) :
    (intersectionChartIso b hi k s t).hom ≫
        coneChartFaceMap k (Finset.inter_subset_left :
          s.image b.equivFun ∩ t.image b.equivFun ⊆ s.image b.equivFun) =
      affineFaceMap hi k (Finset.inter_subset_left : s ∩ t ⊆ s) ≫
        (affineChartIso b hi k s).hom := by
  rw [intersectionChartIso, Iso.trans_hom, Category.assoc]
  change (affineChartIso b hi k (s ∩ t)).hom ≫
      eqToHom (congrArg (coneChart k) (Finset.image_inter s t b.equivFun.injective)) ≫
      coneChartFaceMap k _ = _
  rw [coneChartFaceMap_eqToHom k (Finset.image_inter s t b.equivFun.injective)
    (Finset.image_subset_image (Finset.inter_subset_left : s ∩ t ⊆ s))]
  exact (affineChartIso_naturality b hi k Finset.inter_subset_left).symm

theorem intersectionChartIso_right (s t : Finset N) :
    (intersectionChartIso b hi k s t).hom ≫
        coneChartFaceMap k (Finset.inter_subset_right :
          s.image b.equivFun ∩ t.image b.equivFun ⊆ t.image b.equivFun) =
      affineFaceMap hi k (Finset.inter_subset_right : s ∩ t ⊆ t) ≫
        (affineChartIso b hi k t).hom := by
  rw [intersectionChartIso, Iso.trans_hom, Category.assoc]
  change (affineChartIso b hi k (s ∩ t)).hom ≫
      eqToHom (congrArg (coneChart k) (Finset.image_inter s t b.equivFun.injective)) ≫
      coneChartFaceMap k _ = _
  rw [coneChartFaceMap_eqToHom k (Finset.image_inter s t b.equivFun.injective)
    (Finset.image_subset_image (Finset.inter_subset_right : s ∩ t ⊆ t))]
  exact (affineChartIso_naturality b hi k Finset.inter_subset_right).symm

variable (F : SmoothCompleteFan n)

/-- The original common-face chart is the scheme-theoretic intersection
of the two open charts.  This is an actual categorical pullback. -/
theorem originalChart_overlap_isPullback (s t : OriginalConeIndex b F) :
    IsPullback
      (affineFaceMap hi k (Finset.inter_subset_right : s.val ∩ t.val ⊆ t.val))
      (affineFaceMap hi k (Finset.inter_subset_left : s.val ∩ t.val ⊆ s.val))
      (originalChartMap b hi k F t) (originalChartMap b hi k F s) := by
  apply (F.fanChart_inter_isPullback k
    (coordinateIndex b F s) (coordinateIndex b F t)).of_iso'
    (intersectionChartIso b hi k s.val t.val)
    (affineChartIso b hi k t.val) (affineChartIso b hi k s.val)
    (Iso.refl (F.fanScheme k))
  · exact intersectionChartIso_right b hi k s.val t.val
  · exact intersectionChartIso_left b hi k s.val t.val
  · simp only [Iso.refl_hom, Category.comp_id, originalChartMap]
  · simp only [Iso.refl_hom, Category.comp_id, originalChartMap]

instance affineChart_isOver (s : Finset N) :
    (affineChart hi k s).Over (Spec (CommRingCat.of k)) := by
  dsimp only [affineChart]
  infer_instance

instance affineChartIso_hom_isOver (s : Finset N) :
    (affineChartIso b hi k s).hom.IsOver (Spec (CommRingCat.of k)) := by
  constructor
  change Spec.map (CommRingCat.ofHom (coordinateRingEquiv b hi k s).symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k
        (monoidChartAlgebra k (dualConeMonoid (s.image b.equivFun))))) =
    Spec.map (CommRingCat.ofHom (algebraMap k (coordinateRing hi k s)))
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact (coordinateRingEquiv b hi k s).symm.commutes c

instance originalChartMap_isOver (s : OriginalConeIndex b F) :
    (originalChartMap b hi k F s).IsOver (Spec (CommRingCat.of k)) := by
  dsimp only [originalChartMap]
  infer_instance

end PaperVerification.OriginalLatticeCharts

#print axioms PaperVerification.OriginalLatticeCharts.originalChart_overlap_isPullback
#print axioms PaperVerification.OriginalLatticeCharts.originalChartMap_isOver
