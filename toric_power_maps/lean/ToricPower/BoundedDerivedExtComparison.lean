module

public import ToricPower.BoundedDerivedHomComparison
public import ToricPower.FunctorHomBijections
public import ToricPower.ExtComparisonEpiLifting

/-!
# Bounded derived full faithfulness from the actual Ext comparison

All-degree Ext bijectivity first gives the actual morphism comparison
between sheaves and positive shifts. Negative shifts vanish by the
canonical t-structure. Shifting both objects and applying finite
truncation induction then proves full faithfulness of the literal
bounded-source derived functor.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace ToricPower

universe w v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w} D]
  [HasExt.{w} C] [HasExt.{w} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (hExt : ∀ (X Y : C) (n : ℕ), Function.Bijective (F.mapExtAddHom X Y n))

include hExt in
/-- Ext bijectivity gives the genuine derived Hom comparison in every
nonnegative degree, with the actual single/shift comparison maps. -/
theorem derivedHom_map_bijective_of_Ext (X Y : C) (n : ℕ) :
    Function.Bijective (F.mapDerivedCategory.map :
      ((DerivedCategory.singleFunctor C 0).obj X ⟶
        ((DerivedCategory.singleFunctor C 0).obj Y)⟦(n : ℤ)⟧) → _) := by
  let eX := (F.mapDerivedCategorySingleFunctor 0).app X
  let eY := (F.mapDerivedCategory.commShiftIso (n : ℤ)).app
      ((DerivedCategory.singleFunctor C 0).obj Y) ≪≫
    (shiftFunctor (DerivedCategory D) (n : ℤ)).mapIso
      ((F.mapDerivedCategorySingleFunctor 0).app Y)
  let source : Ext.{w} X Y n ≃ _ := Ext.homEquiv
  let target := eX.homCongr eY
  have comparison : target ∘ F.mapDerivedCategory.map ∘ source =
      (Ext.homEquiv : Ext.{w} (F.obj X) (F.obj Y) n ≃ _) ∘ F.mapExtAddHom X Y n := by
    funext e
    simpa only [Function.comp_apply, target, source, Iso.homCongr_apply,
      eX, eY, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv,
      Functor.mapExtAddHom_apply, ShiftedHom.map, Category.assoc] using
      (Ext.mapExactFunctor_hom F e).symm
  have hb : Function.Bijective (target ∘ F.mapDerivedCategory.map ∘ source) := by
    rw [comparison]
    exact Ext.homEquiv.bijective.comp (hExt X Y n)
  have hm := (Function.Bijective.of_comp_iff' target.bijective
    (F.mapDerivedCategory.map ∘ source)).mp hb
  exact (Function.Bijective.of_comp_iff _ source.bijective).mp hm

/-- Negative shifted Hom between actual degree-zero sheaves is zero. -/
theorem negativeSingleHom_subsingleton (X Y : C) (p : ℤ) (hp : p < 0) :
    Subsingleton ((DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦p⟧) := by
  let t := DerivedCategory.TStructure.t (C := C)
  have hy : t.IsGE (((DerivedCategory.singleFunctor C 0).obj Y)⟦p⟧) (-p) :=
    t.isGE_shift _ 0 p (-p) (by omega)
  have hz (f : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦p⟧) : f = 0 :=
    t.zero_of_isLE_of_isGE f 0 (-p) (by omega) inferInstance hy
  exact ⟨fun f g => (hz f).trans (hz g).symm⟩

include hExt in
/-- The actual morphism comparison holds for every integer shift. -/
theorem derivedHom_map_bijective_all_shifts (X Y : C) (p : ℤ) :
    Function.Bijective (F.mapDerivedCategory.map :
      ((DerivedCategory.singleFunctor C 0).obj X ⟶
        ((DerivedCategory.singleFunctor C 0).obj Y)⟦p⟧) → _) := by
  by_cases hp : 0 ≤ p
  · lift p to ℕ using hp
    exact derivedHom_map_bijective_of_Ext F hExt X Y p
  · have hp' : p < 0 := lt_of_not_ge hp
    letI := negativeSingleHom_subsingleton X Y p hp'
    let eX := (F.mapDerivedCategorySingleFunctor 0).app X
    let eY := (F.mapDerivedCategory.commShiftIso p).app
        ((DerivedCategory.singleFunctor C 0).obj Y) ≪≫
      (shiftFunctor (DerivedCategory D) p).mapIso
        ((F.mapDerivedCategorySingleFunctor 0).app Y)
    letI : Subsingleton (F.mapDerivedCategory.obj ((DerivedCategory.singleFunctor C 0).obj X) ⟶
        F.mapDerivedCategory.obj (((DerivedCategory.singleFunctor C 0).obj Y)⟦p⟧)) := by
      constructor
      intro f g
      apply (eX.homCongr eY).injective
      exact @Subsingleton.elim _
        (negativeSingleHom_subsingleton (F.obj X) (F.obj Y) p hp') _ _
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun g => ⟨0, Subsingleton.elim _ _⟩⟩

include hExt in
/-- Transporting both single degrees retains the precise derived map. -/
theorem derivedHom_map_bijective_single_degrees (X Y : C) (a b : ℤ) :
    Function.Bijective (F.mapDerivedCategory.map :
      ((DerivedCategory.singleFunctor C a).obj X ⟶
        (DerivedCategory.singleFunctor C b).obj Y) → _) := by
  have h := (functorMap_bijective_iff_shift F.mapDerivedCategory
    ((DerivedCategory.singleFunctor C 0).obj X)
    (((DerivedCategory.singleFunctor C 0).obj Y)⟦a-b⟧) (-a)).mpr
      (derivedHom_map_bijective_all_shifts F hExt X Y (a-b))
  let eX := ((DerivedCategory.singleFunctors C).shiftIso (-a) a 0 (by omega)).app X
  let eY := ((shiftFunctorAdd' (DerivedCategory C) (a-b) (-a) (-b) (by omega)).symm.app
      ((DerivedCategory.singleFunctor C 0).obj Y)) ≪≫
    ((DerivedCategory.singleFunctors C).shiftIso (-b) b 0 (by omega)).app Y
  exact (functorMap_bijective_iff_of_iso F.mapDerivedCategory eX eY).mp h

/-- Full faithfulness from the proved all-degree Ext maps. -/
def boundedDerivedFullyFaithfulOfExt :
    (DerivedCategory.Bounded.ι (C := C) ⋙ F.mapDerivedCategory).FullyFaithful :=
  boundedDerivedFullyFaithfulOfSingles F.mapDerivedCategory
    (derivedHom_map_bijective_single_degrees F hExt)

/-- In particular, a fully faithful exact inclusion with actual coherent
epimorphism lifting has a fully faithful bounded derived inclusion. -/
def boundedDerivedFullyFaithfulOfEpimorphismLifts [F.Full] [F.Faithful]
    (lifting : HasEpimorphismLifts F) :
    (DerivedCategory.Bounded.ι (C := C) ⋙ F.mapDerivedCategory).FullyFaithful :=
  boundedDerivedFullyFaithfulOfExt F (mapExt_bijective_of_epimorphism_lifts F lifting)

end ToricPower

end
