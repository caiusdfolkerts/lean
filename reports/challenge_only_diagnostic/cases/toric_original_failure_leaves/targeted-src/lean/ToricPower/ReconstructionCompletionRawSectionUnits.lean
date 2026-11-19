module

public import ToricPower.ReconstructionCompletionRawTargets
public import ToricPower.SchemeExternalSections

/-! # Actual section coordinates of the two overlap targets -/

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

/-- The map of sections through an actual direct-image comparison is
precisely the normalized adjunct of the original mapped section. -/
theorem reconstruction_mappedPushforwardSections_unit
    (M : Z.Modules) (N : W.Modules) (e : M ⟶ (Scheme.Modules.pushforward g).obj N)
    (s : (FiniteCover.schemeBaseSections k Z ⊤).obj M) :
    (moduleUnitActualSectionsLinearEquiv k W N).symm
      ((pushforwardBaseSectionsLinearEquiv k g N ⊤)
        ((FiniteCover.schemeBaseSections k Z ⊤).map e s)) =
      (Scheme.Modules.pullbackObjUnitIso g).inv ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm
          ((moduleUnitActualSectionsLinearEquiv k Z M).symm s ≫ e) := by
  rw [reconstruction_pushforwardGlobalSections_unit,
    moduleUnitActualSectionsLinearEquiv_symm_naturality]

end ToricPower

end
