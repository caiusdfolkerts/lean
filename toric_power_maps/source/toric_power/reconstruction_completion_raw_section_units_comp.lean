module

public import ToricPower.ReconstructionCompletionRawSectionUnits

/-! # Composed section maps in the actual overlap comparison

The two consecutive section maps are combined before taking the
normalized adjunct. This retains their original composite and the
original unit-source map with the displayed association.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory MonoidalCategory

namespace ToricPower

universe u
variable (k : Type u) [Field k] {W Z : Scheme.{u}}
  [W.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
  (g : W ⟶ Z) [g.IsOver (Spec (.of k))]

/-- The two actual maps of sections have their literal normalized adjunct. -/
theorem reconstruction_mappedPushforwardSections_comp_unit
    (M M' : Z.Modules) (N : W.Modules) (a : M ⟶ M')
    (e : M' ⟶ (Scheme.Modules.pushforward g).obj N)
    (s : (FiniteCover.schemeBaseSections k Z ⊤).obj M) :
    (moduleUnitActualSectionsLinearEquiv k W N).symm
      ((pushforwardBaseSectionsLinearEquiv k g N ⊤)
        ((FiniteCover.schemeBaseSections k Z ⊤).map e
          ((FiniteCover.schemeBaseSections k Z ⊤).map a s))) =
      (Scheme.Modules.pullbackObjUnitIso g).inv ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm
          ((moduleUnitActualSectionsLinearEquiv k Z M).symm s ≫ a ≫ e) := by
  simpa only [Functor.map_comp, ModuleCat.comp_apply] using
    reconstruction_mappedPushforwardSections_unit k g M N (a ≫ e) s

end ToricPower

end
