module

public import ToricPower.ElementSumProductDerived

/-! # Nonzero tests pull back through the genuine covering adjunction -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower.ElementComparison

variable {C : Type} [SmallCategory C] (B : C ⥤ Type)
  (bijective : ∀ {c d : C} (f : c ⟶ d), Function.Bijective (B.map f))
  (R : Type) [CommRing R]
  [HasDerivedCategory (C ⥤ ModuleCat.{0} R)]
  [HasDerivedCategory (B.Elements ⥤ ModuleCat.{0} R)]

include bijective in
/-- Only the target homology has finite fiber support. The source and
the chosen cohomological degree are completely unrestricted. -/
theorem exists_nonzero_pullback_of_sum
    (K : CochainComplex (B.Elements ⥤ ModuleCat.{0} R) ℤ)
    (finite : ∀ (q : ℤ) (c : C),
      {r : B.obj c | ¬ IsZero ((K.homology q).obj (B.elementsMk c r))}.Finite)
    (E : DerivedCategory (C ⥤ ModuleCat.{0} R)) (q : ℤ)
    (f : E ⟶ ((ElementPushdown.functor B (D := ModuleCat.{0} R)).mapDerivedCategory.obj
      (DerivedCategory.Q.obj K))⟦q⟧) (nonzero : f ≠ 0) :
    ∃ g : (ElementPushdown.restriction B (D := ModuleCat.{0} R)).mapDerivedCategory.obj E ⟶
      (DerivedCategory.Q.obj K)⟦q⟧, g ≠ 0 := by
  let adj := ElementProduct.derivedAdjunction B bijective (D := ModuleCat.{0} R)
  let target := (shiftFunctor _ q).mapIso (derivedComparisonIso B bijective R K finite) ≪≫
    ((ElementProduct.functor B bijective (D := ModuleCat.{0} R)).mapDerivedCategory.commShiftIso q).symm.app
      (DerivedCategory.Q.obj K)
  let a := (adj.homEquiv E ((DerivedCategory.Q.obj K)⟦q⟧)).symm (f ≫ target.hom)
  refine ⟨a,?_⟩
  intro zero
  have mapped := congrArg (adj.homEquiv E ((DerivedCategory.Q.obj K)⟦q⟧)) zero
  rw [Equiv.apply_symm_apply,adj.homAddEquiv_zero] at mapped
  apply nonzero
  rw [← cancel_mono target.hom,zero_comp]
  exact mapped

end ToricPower.ElementComparison

end
