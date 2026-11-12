module

public import ToricPower.CellularClosedSupportRestriction
public import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Detection maps on the genuine closed cohomological support

The original target can be replaced by extension of its restriction
through the actual quasi-isomorphic unit. The precise restriction and
extension adjunction then transports nonzero maps in both directions.
The source and target complexes may be wholly unbounded.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.Cellular

universe u w w'
variable (R : Type u) [Ring R] {B : Type u} [Preorder B]
  (P : B → Prop) (downward : Antitone P)
  [HasDerivedCategory.{w} (B ⥤ ModuleCat.{u} R)]
  [HasDerivedCategory.{w'} ({b : B // P b} ⥤ ModuleCat.{u} R)]
  (K : CochainComplex (B ⥤ ModuleCat.{u} R) ℤ)
  (vanishes : ∀ b : B, ¬ P b →
    ((((evaluation B (ModuleCat.{u} R)).obj b).mapHomologicalComplex (.up ℤ)).obj K).Acyclic)

def closedSupportModelIso :
    DerivedCategory.Q.obj K ≅
      (closedFaceExtensionFunctor R P downward).mapDerivedCategory.obj
        ((closedFaceRestriction R P).mapDerivedCategory.obj (DerivedCategory.Q.obj K)) :=
  closedFaceSupportedDerivedIso R P downward K vanishes ≪≫
    (((closedFaceRestriction R P ⋙ closedFaceExtensionFunctor R P downward).mapDerivedCategoryFactors).app K).symm ≪≫
    ((Functor.mapDerivedCategoryCompIso (closedFaceRestriction R P)
      (closedFaceExtensionFunctor R P downward)).app (DerivedCategory.Q.obj K)).symm

include downward vanishes in
theorem restrict_nonzero_into_closed_support
    (E : DerivedCategory (B ⥤ ModuleCat.{u} R))
    (f : E ⟶ DerivedCategory.Q.obj K) (nonzero : f ≠ 0) :
    ∃ g : (closedFaceRestriction R P).mapDerivedCategory.obj E ⟶
      (closedFaceRestriction R P).mapDerivedCategory.obj (DerivedCategory.Q.obj K), g ≠ 0 := by
  let e := closedSupportModelIso R P downward K vanishes
  let target := (closedFaceRestriction R P).mapDerivedCategory.obj (DerivedCategory.Q.obj K)
  let adj := closedFaceDerivedAdjunction R P downward
  refine ⟨(adj.homEquiv E target).symm (f ≫ e.hom),?_⟩
  intro zero
  have mapped := congrArg (adj.homEquiv E target) zero
  rw [Equiv.apply_symm_apply,adj.homAddEquiv_zero] at mapped
  apply nonzero
  rw [← cancel_mono e.hom,zero_comp]
  exact mapped

include downward vanishes in
theorem extend_nonzero_from_closed_support
    (E : DerivedCategory (B ⥤ ModuleCat.{u} R))
    (f : (closedFaceRestriction R P).mapDerivedCategory.obj E ⟶
      (closedFaceRestriction R P).mapDerivedCategory.obj (DerivedCategory.Q.obj K))
    (nonzero : f ≠ 0) : ∃ g : E ⟶ DerivedCategory.Q.obj K, g ≠ 0 := by
  let e := closedSupportModelIso R P downward K vanishes
  let target := (closedFaceRestriction R P).mapDerivedCategory.obj (DerivedCategory.Q.obj K)
  let adj := closedFaceDerivedAdjunction R P downward
  let a := adj.homEquiv E target f
  refine ⟨a ≫ e.inv,?_⟩
  intro zero
  have mapped : a = 0 := by
    rw [← cancel_mono e.inv,zero_comp]
    exact zero
  apply nonzero
  apply (adj.homEquiv E target).injective
  exact mapped.trans (adj.homAddEquiv_zero E target).symm

end ToricPower.Cellular

end
