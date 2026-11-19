module

public import ToricPower.EquivalenceComponentDetection
public import ToricPower.CoveringShiftedDetection

/-!
# Nonzero maps from one full component through both covering adjunctions

The component is selected inside an explicit equivalence with the entire
covering category. All other components remain in the target. The only
support condition is the proved finite homological support in each
universal fiber; the source is an arbitrary unbounded object.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower

variable {C W I : Type} [SmallCategory C] [SmallCategory W]
  (B P : C ⥤ Type) (k : Type) [Field k]

local instance componentCoverDerivedBase :
    HasDerivedCategory.{1} (C ⥤ ModuleCat.{0} k) := HasDerivedCategory.standard _
local instance componentCoverDerivedPower :
    HasDerivedCategory.{1} (P.Elements ⥤ ModuleCat.{0} k) := HasDerivedCategory.standard _
local instance componentCoverDerivedUniversal :
    HasDerivedCategory.{1} (B.Elements ⥤ ModuleCat.{0} k) := HasDerivedCategory.standard _
local instance componentCoverDerivedPulled :
    HasDerivedCategory.{1} ((Elements.π P ⋙ B).Elements ⥤ ModuleCat.{0} k) :=
  HasDerivedCategory.standard _
local instance componentCoverDerivedPresentation :
    HasDerivedCategory.{1} (W ⥤ ModuleCat.{0} k) := HasDerivedCategory.standard _

/-- Every functor and comparison in this transfer is specified. The
conclusion is a nonzero map between the two actual whole direct images. -/
theorem exists_nonzero_cover_from_component
    (bijective : ∀ {c d : C} (f : c ⟶ d), Function.Bijective (B.map f))
    (e : (Elements.π P ⋙ B).Elements ≌ Discrete I × W)
    (J : (Elements.π P ⋙ B).Elements ⥤ W)
    (projection : e.inverse ⋙ J ≅ CategoryTheory.Prod.snd (Discrete I) W)
    (K₀ : CochainComplex (B.Elements ⥤ ModuleCat.{0} k) ℤ)
    (K : CochainComplex (W ⥤ ModuleCat.{0} k) ℤ)
    (finite : ∀ (q : ℤ) (c : C),
      {r : B.obj c | ¬ IsZero ((K₀.homology q).obj (B.elementsMk c r))}.Finite)
    (targetFrame : (ElementPushdown.baseRestriction J (D := ModuleCat.{0} k)).mapDerivedCategory.obj (DerivedCategory.Q.obj K) ≅
        DerivedCategory.Q.obj (pulledCoveringComplex B P k K₀))
    (E : DerivedCategory (P.Elements ⥤ ModuleCat.{0} k)) (i : I) (q : ℤ)
    (f : (ComponentEquivalence.restriction k e i).mapDerivedCategory.obj
      ((ElementPushdown.restriction (Elements.π P ⋙ B) (D := ModuleCat.{0} k)).mapDerivedCategory.obj E) ⟶ (DerivedCategory.Q.obj K)⟦q⟧)
    (nonzero : f ≠ 0) :
    ∃ g : (ElementPushdown.functor P (D := ModuleCat.{0} k)).mapDerivedCategory.obj E ⟶
      ((ElementPushdown.functor B (D := ModuleCat.{0} k)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj K₀))⟦q⟧, g ≠ 0 := by
  let whole := (ElementPushdown.restriction (Elements.π P ⋙ B)
    (D := ModuleCat.{0} k)).mapDerivedCategory.obj E
  obtain ⟨a,ha⟩ := ComponentEquivalence.exists_nonzero_into_pullback k e J projection i
    whole ((DerivedCategory.Q.obj K)⟦q⟧) f nonzero
  let pull := (ElementPushdown.baseRestriction J (D := ModuleCat.{0} k)).mapDerivedCategory
  let t := (pull.commShiftIso q).app (DerivedCategory.Q.obj K) ≪≫
    (shiftFunctor _ q).mapIso targetFrame
  have nonzeroWhole : a ≫ t.hom ≠ 0 := by
    intro zero
    apply ha
    rw [← cancel_mono t.hom,zero_comp]
    exact zero
  exact coveringShiftedDetectionTransfer B P bijective k K₀ finite E q
    (a ≫ t.hom) nonzeroWhole

end ToricPower

end
