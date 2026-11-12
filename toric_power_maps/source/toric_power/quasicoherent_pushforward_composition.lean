module

public import ToricPower.QuasicoherentOpenBaseChange

/-!
# Actual quasicoherent direct-image composition and open localization

The composition and equality comparisons are the original module-sheaf
comparisons, restricted to the actual quasicoherent categories. Open base
change then shows that localization at one affine open preserves the
essential image of direct image from every other affine open. These are
ordinary functor isomorphisms, before passing to complexes or derived
categories.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u

variable {U X Y : Scheme.{u}}

/-- Composition of actual affine direct images on quasicoherent sheaves. -/
def quasicoherentPushforwardCompIso (f : U ⟶ X) (g : X ⟶ Y)
    [IsAffineHom f] [IsAffineHom g] :
    quasicoherentAffinePushforward f ⋙ quasicoherentAffinePushforward g ≅
      quasicoherentAffinePushforward (f ≫ g) :=
  NatIso.ofComponents
    (fun M => ObjectProperty.isoMk _ ((Scheme.Modules.pushforwardComp f g).app M.obj))
    (fun h => ObjectProperty.hom_ext _
      ((Scheme.Modules.pushforwardComp f g).hom.naturality h.hom))

/-- Equal affine maps give the canonical ordinary direct-image comparison. -/
def quasicoherentPushforwardCongrIso {f g : U ⟶ X} (h : f = g)
    [IsAffineHom f] [IsAffineHom g] :
    quasicoherentAffinePushforward f ≅ quasicoherentAffinePushforward g :=
  NatIso.ofComponents
    (fun M => ObjectProperty.isoMk _ ((Scheme.Modules.pushforwardCongr h).app M.obj))
    (fun t => ObjectProperty.hom_ext _
      ((Scheme.Modules.pushforwardCongr h).hom.naturality t.hom))

/-- An affine open immersion remains affine after taking its inverse
image along an arbitrary scheme map. -/
instance affinePreimageOpenInclusion (f : U ⟶ X) (V : X.Opens)
    [IsAffineHom V.ι] : IsAffineHom (f ⁻¹ᵁ V).ι :=
  MorphismProperty.of_isPullback (isPullback_morphismRestrict f V)
    (inferInstanceAs (IsAffineHom V.ι))

/-- Applying an affine open localization to an actual affine-open direct
image again gives an actual direct image from the same open. The inner
functor is localization on the actual inverse-image open. -/
def quasicoherentOpenPushRestrictionIso (j : U ⟶ X)
    [IsOpenImmersion j] [IsAffineHom j] (V : X.Opens) [IsAffineHom V.ι] :
    quasicoherentAffinePushforward j ⋙ quasicoherentRestriction V.ι ⋙
        quasicoherentAffinePushforward V.ι ≅
      quasicoherentRestriction (j ⁻¹ᵁ V).ι ⋙
        quasicoherentAffinePushforward (j ⁻¹ᵁ V).ι ⋙
        quasicoherentAffinePushforward j :=
  Functor.isoWhiskerRight (quasicoherentRestrictPushforwardIso j V)
      (quasicoherentAffinePushforward V.ι) ≪≫
    Functor.isoWhiskerLeft (quasicoherentRestriction (j ⁻¹ᵁ V).ι)
      (quasicoherentPushforwardCompIso (j ∣_ V) V.ι ≪≫
        quasicoherentPushforwardCongrIso (morphismRestrict_ι j V) ≪≫
        (quasicoherentPushforwardCompIso (j ⁻¹ᵁ V).ι j).symm)

end ToricPower
