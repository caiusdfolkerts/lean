module

public import ToricPower.ReconstructionCompletionRawSectionUnitsComp

/-! # The entire section-target isomorphism on original sections

The actual target isomorphism is retained before its component is
evaluated. The section-to-unit comparison is proved on arbitrary schemes,
so the isomorphism's module presentation need not be expanded after
specialization to a toric chart.
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

/-- The complete target isomorphism has the original normalized adjunct. -/
theorem reconstruction_mappedPushforwardSections_target_unit
    (M M' : Z.Modules) (N : W.Modules) (a : M ⟶ M')
    (e : M' ≅ (Scheme.Modules.pushforward g).obj N)
    (s : (FiniteCover.schemeBaseSections k Z ⊤).obj M) :
    (moduleUnitActualSectionsLinearEquiv k W N).symm
      ((((FiniteCover.schemeBaseSections k Z ⊤).mapIso e ≪≫
        (pushforwardBaseSectionsLinearEquiv k g N ⊤).toModuleIso).hom)
        ((FiniteCover.schemeBaseSections k Z ⊤).map a s)) =
      (Scheme.Modules.pullbackObjUnitIso g).inv ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm
          ((moduleUnitActualSectionsLinearEquiv k Z M).symm s ≫ a ≫ e.hom) := by
  change (moduleUnitActualSectionsLinearEquiv k W N).symm
      ((pushforwardBaseSectionsLinearEquiv k g N ⊤)
        ((FiniteCover.schemeBaseSections k Z ⊤).map e.hom
          ((FiniteCover.schemeBaseSections k Z ⊤).map a s))) = _
  exact reconstruction_mappedPushforwardSections_comp_unit k g M M' N a e.hom s

end ToricPower

end
