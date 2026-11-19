module

public import ToricPower.QuasicoherentCategory
public import ToricPower.CoherentDerived

/-!
# The exact inclusion of coherent into quasi-coherent sheaves

This is the literal inclusion of full subcategories of module sheaves.
Its finite exactness follows from the already proved exact ambient
inclusions. No assertion about derived full faithfulness is included.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ToricPower

universe u

/-- The actual coherent sheaf, with its implied quasi-coherence predicate. -/
abbrev coherentToQuasicoherent (X : Scheme.{u}) : Coh X ⥤ QCoh X :=
  ObjectProperty.ιOfLE fun M hM => by
    letI : M.IsFinitePresentation := hM
    exact SheafOfModules.instIsQuasicoherentOfIsFinitePresentation M

@[simp]
theorem coherentToQuasicoherent_comp_inclusion (X : Scheme.{u}) :
    coherentToQuasicoherent X ⋙ quasicoherentInclusion X =
      (SheafOfModules.isFinitePresentation X.ringCatSheaf).ι := rfl

instance coherentToQuasicoherent_additive (X : Scheme.{u}) :
    (coherentToQuasicoherent X).Additive where
  map_add := by intros; rfl

instance coherentToQuasicoherent_preservesFiniteLimits (X : Scheme.{u})
    [IsLocallyNoetherian X] : PreservesFiniteLimits (coherentToQuasicoherent X) := by
  letI : PreservesFiniteLimits
      (coherentToQuasicoherent X ⋙ quasicoherentInclusion X) :=
    coherentInclusion_preservesFiniteLimits X
  exact preservesFiniteLimits_of_reflects_of_preserves
    (coherentToQuasicoherent X) (quasicoherentInclusion X)

instance coherentToQuasicoherent_preservesFiniteColimits (X : Scheme.{u})
    [IsLocallyNoetherian X] : PreservesFiniteColimits (coherentToQuasicoherent X) := by
  letI : PreservesFiniteColimits
      (coherentToQuasicoherent X ⋙ quasicoherentInclusion X) :=
    coherentInclusion_preservesFiniteColimits X
  exact preservesFiniteColimits_of_reflects_of_preserves
    (coherentToQuasicoherent X) (quasicoherentInclusion X)

end ToricPower

end
