module

public import ToricPower.ElementSumProductComparison
public import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# The covering sum-to-product comparison after localization

The original inclusion of the whole direct sum into the whole product
becomes an isomorphism when the target has finite cohomological support
in every fiber. The resulting Hom comparison uses the genuine right
adjunction, and therefore applies to arbitrary unbounded source objects.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower.ElementComparison

variable {C : Type} [SmallCategory C] (B : C ⥤ Type)
  (bijective : ∀ {c d : C} (f : c ⟶ d), Function.Bijective (B.map f))
  (R : Type) [CommRing R]

set_option quotPrecheck false in
local notation "ModR" => ModuleCat.{0} R

variable [HasDerivedCategory (C ⥤ ModuleCat.{0} R)]
  [HasDerivedCategory (B.Elements ⥤ ModuleCat.{0} R)]

/-- This is the localization of the actual inclusion/projection matrix. -/
def derivedComparison :
    (ElementPushdown.functor B (D := ModR)).mapDerivedCategory ⟶
      (ElementProduct.functor B bijective (D := ModR)).mapDerivedCategory :=
  (comparison B bijective R).mapDerivedCategory

theorem derivedComparison_isIso
    (K : CochainComplex (B.Elements ⥤ ModR) ℤ)
    (finite : ∀ (q : ℤ) (c : C),
      {r : B.obj c | ¬ IsZero ((K.homology q).obj (B.elementsMk c r))}.Finite) :
    IsIso ((derivedComparison B bijective R).app (DerivedCategory.Q.obj K)) := by
  letI := comparison_complex_quasiIso B bijective R K finite
  unfold derivedComparison
  rw [NatTrans.mapDerivedCategory_app_Q_obj]
  infer_instance

/-- No termwise finite-support or degree-bound hypothesis is needed. -/
def derivedComparisonIso
    (K : CochainComplex (B.Elements ⥤ ModR) ℤ)
    (finite : ∀ (q : ℤ) (c : C),
      {r : B.obj c | ¬ IsZero ((K.homology q).obj (B.elementsMk c r))}.Finite) :
    (ElementPushdown.functor B (D := ModR)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj K) ≅
      (ElementProduct.functor B bijective (D := ModR)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj K) := by
  letI := derivedComparison_isIso B bijective R K finite
  exact asIso ((derivedComparison B bijective R).app (DerivedCategory.Q.obj K))

include bijective in
/-- A nonzero map from the entire pulled-back source produces a
nonzero map into the original sum direct image of the target. -/
theorem exists_nonzero_into_sum
    (K : CochainComplex (B.Elements ⥤ ModR) ℤ)
    (finite : ∀ (q : ℤ) (c : C),
      {r : B.obj c | ¬ IsZero ((K.homology q).obj (B.elementsMk c r))}.Finite)
    (E : DerivedCategory (C ⥤ ModR))
    (f : (ElementPushdown.restriction B (D := ModR)).mapDerivedCategory.obj E ⟶
      DerivedCategory.Q.obj K) (nonzero : f ≠ 0) :
    ∃ g : E ⟶ (ElementPushdown.functor B (D := ModR)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj K), g ≠ 0 := by
  let adj := ElementProduct.derivedAdjunction B bijective (D := ModR)
  let a := adj.homEquiv E (DerivedCategory.Q.obj K) f
  let e := derivedComparisonIso B bijective R K finite
  refine ⟨a ≫ e.inv, ?_⟩
  intro zero
  have ha : a = 0 := by
    rw [← cancel_mono e.inv, zero_comp]
    exact zero
  apply nonzero
  apply (adj.homEquiv E (DerivedCategory.Q.obj K)).injective
  exact ha.trans (adj.homAddEquiv_zero E (DerivedCategory.Q.obj K)).symm

end ToricPower.ElementComparison

end
