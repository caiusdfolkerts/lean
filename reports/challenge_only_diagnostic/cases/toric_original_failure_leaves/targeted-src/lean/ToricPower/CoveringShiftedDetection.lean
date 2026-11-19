module

public import ToricPower.CoveringDetectionTransfer
public import ToricPower.ShiftedHomComparison

/-!
# Shifted nonzero maps through the genuine covering adjunctions

Moving the shift to the unrestricted source allows the sum/product
comparison to use the original full target and its already proved
finite cohomological support. The conclusion restores the same target
shift after both actual covering adjunctions.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower

variable {C : Type} [SmallCategory C] (B P : C ⥤ Type)
  (bijective : ∀ {c d : C} (f : c ⟶ d), Function.Bijective (B.map f))
  (R : Type) [CommRing R]

local instance coveringShiftedDerivedBase : HasDerivedCategory.{1} (C ⥤ ModuleCat.{0} R) :=
  HasDerivedCategory.standard _
local instance coveringShiftedDerivedPower : HasDerivedCategory.{1} (P.Elements ⥤ ModuleCat.{0} R) :=
  HasDerivedCategory.standard _
local instance coveringShiftedDerivedUniversal : HasDerivedCategory.{1} (B.Elements ⥤ ModuleCat.{0} R) :=
  HasDerivedCategory.standard _
local instance coveringShiftedDerivedPulled :
    HasDerivedCategory.{1} ((Elements.π P ⋙ B).Elements ⥤ ModuleCat.{0} R) :=
  HasDerivedCategory.standard _

include bijective in
/-- The actual full direct images retain a nonzero shifted detection
map, with no boundedness or finite-dimensionality condition on `E`. -/
theorem coveringShiftedDetectionTransfer
    (K : CochainComplex (B.Elements ⥤ ModuleCat.{0} R) ℤ)
    (finite : ∀ (q : ℤ) (c : C),
      {r : B.obj c | ¬ IsZero ((K.homology q).obj (B.elementsMk c r))}.Finite)
    (E : DerivedCategory (P.Elements ⥤ ModuleCat.{0} R)) (q : ℤ)
    (f : (ElementPushdown.restriction (Elements.π P ⋙ B)
      (D := ModuleCat.{0} R)).mapDerivedCategory.obj E ⟶
        (DerivedCategory.Q.obj (pulledCoveringComplex B P R K))⟦q⟧)
    (nonzero : f ≠ 0) :
    ∃ g : (ElementPushdown.functor P (D := ModuleCat.{0} R)).mapDerivedCategory.obj E ⟶
      ((ElementPushdown.functor B (D := ModuleCat.{0} R)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj K))⟦q⟧, g ≠ 0 := by
  let pull := (ElementPushdown.restriction (Elements.π P ⋙ B)
    (D := ModuleCat.{0} R)).mapDerivedCategory
  let target := DerivedCategory.Q.obj (pulledCoveringComplex B P R K)
  let a := (shiftedHomAddEquiv (pull.obj E) target q).symm f
  have nonzeroA : a ≠ 0 := by
    intro zero
    apply nonzero
    have h := congrArg (shiftedHomAddEquiv (pull.obj E) target q) zero
    simp only [a,AddEquiv.apply_symm_apply,map_zero] at h
    exact h
  let frame := (pull.commShiftIso (-q)).app E
  have nonzeroPulled : frame.hom ≫ a ≠ 0 := by
    intro zero
    apply nonzeroA
    rw [← cancel_epi frame.hom,comp_zero]
    exact zero
  obtain ⟨b,hb⟩ := coveringDetectionTransfer B P bijective R K finite (E⟦-q⟧)
    (frame.hom ≫ a) nonzeroPulled
  let push := (ElementPushdown.functor P (D := ModuleCat.{0} R)).mapDerivedCategory
  let targetDown := (ElementPushdown.functor B (D := ModuleCat.{0} R)).mapDerivedCategory.obj
    (DerivedCategory.Q.obj K)
  let pushFrame := (push.commShiftIso (-q)).app E
  let g := shiftedHomAddEquiv (push.obj E) targetDown q (pushFrame.inv ≫ b)
  refine ⟨g,?_⟩
  intro zero
  have beforeShift : pushFrame.inv ≫ b = 0 :=
    (shiftedHomAddEquiv (push.obj E) targetDown q).injective
      (zero.trans (map_zero (shiftedHomAddEquiv (push.obj E) targetDown q)).symm)
  apply hb
  rw [← cancel_epi pushFrame.inv,comp_zero]
  exact beforeShift

end ToricPower

end
