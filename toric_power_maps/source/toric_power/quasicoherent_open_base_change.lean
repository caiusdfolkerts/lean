module

public import ToricPower.QuasicoherentOpenAdjunction
public import ToricPower.ExactDerivedFunctorIso
public import TauCeti.AlgebraicGeometry.Modules.Pushforward

/-!
# Open base change in the actual quasicoherent derived category

The ordinary comparison is the module-sheaf base-change isomorphism,
restricted to quasicoherent sheaves. All participating functors are exact,
so the same comparison descends to arbitrary unbounded complexes.

The final vanishing statement is the step needed when successively
removing opens in a finite affine cover.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u

variable {U X Y : Scheme.{u}}

instance affineMorphismRestrict (f : U ⟶ X) [IsAffineHom f] (V : X.Opens) :
    IsAffineHom (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict (inferInstanceAs (IsAffineHom f)) V

instance openImmersionMorphismRestrict (j : U ⟶ X) [IsOpenImmersion j]
    (V : X.Opens) : IsOpenImmersion (j ∣_ V) :=
  IsZariskiLocalAtTarget.restrict (inferInstanceAs (IsOpenImmersion j)) V

/-- Ordinary open base change, with the original section maps. -/
def quasicoherentRestrictPushforwardIso (f : U ⟶ X) [IsAffineHom f]
    (V : X.Opens) :
    quasicoherentAffinePushforward f ⋙ quasicoherentRestriction V.ι ≅
      quasicoherentRestriction (f ⁻¹ᵁ V).ι ⋙
        quasicoherentAffinePushforward (f ∣_ V) :=
  NatIso.ofComponents
    (fun M => ObjectProperty.isoMk _
      ((TauCeti.AlgebraicGeometry.restrictPushforwardIso f V).app M.obj))
    (fun g => ObjectProperty.hom_ext _
      ((TauCeti.AlgebraicGeometry.restrictPushforwardIso f V).hom.naturality g.hom))

/-- Composition of actual restrictions to quasicoherent sheaves. -/
def quasicoherentRestrictionCompIso (f : U ⟶ X) (g : X ⟶ Y)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    quasicoherentRestriction (f ≫ g) ≅
      quasicoherentRestriction g ⋙ quasicoherentRestriction f :=
  NatIso.ofComponents
    (fun M => ObjectProperty.isoMk _ ((Scheme.Modules.restrictFunctorComp f g).app M.obj))
    (fun h => ObjectProperty.hom_ext _
      ((Scheme.Modules.restrictFunctorComp f g).hom.naturality h.hom))

/-- Equal open-immersion morphisms give the canonical restriction comparison. -/
def quasicoherentRestrictionCongrIso {f g : U ⟶ X} (h : f = g)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    quasicoherentRestriction f ≅ quasicoherentRestriction g :=
  NatIso.ofComponents
    (fun M => ObjectProperty.isoMk _ ((Scheme.Modules.restrictFunctorCongr h).app M.obj))
    (fun t => ObjectProperty.hom_ext _
      ((Scheme.Modules.restrictFunctorCongr h).hom.naturality t.hom))

local instance quasicoherentBaseChangeDerivedCategory (Z : Scheme.{u}) :
    HasDerivedCategory.{u+1} (QCoh Z) := HasDerivedCategory.standard _

/-- Open base change for the actual unbounded derived functors. -/
def quasicoherentDerivedRestrictPushforwardIso (f : U ⟶ X) [IsAffineHom f]
    (V : X.Opens) :
    (quasicoherentAffinePushforward f).mapDerivedCategory ⋙
        (quasicoherentRestriction V.ι).mapDerivedCategory ≅
      (quasicoherentRestriction (f ⁻¹ᵁ V).ι).mapDerivedCategory ⋙
        (quasicoherentAffinePushforward (f ∣_ V)).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    exactDerivedFunctorIso (quasicoherentRestrictPushforwardIso f V) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The composition comparison on arbitrary unbounded derived objects. -/
def quasicoherentDerivedRestrictionCompIso (f : U ⟶ X) (g : X ⟶ Y)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    (quasicoherentRestriction (f ≫ g)).mapDerivedCategory ≅
      (quasicoherentRestriction g).mapDerivedCategory ⋙
        (quasicoherentRestriction f).mapDerivedCategory :=
  exactDerivedFunctorIso (quasicoherentRestrictionCompIso f g) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- Restricting along equal scheme maps gives equal derived operations
up to the canonical natural isomorphism, rather than a definitional cast. -/
def quasicoherentDerivedRestrictionCongrIso {f g : U ⟶ X} (h : f = g)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    (quasicoherentRestriction f).mapDerivedCategory ≅
      (quasicoherentRestriction g).mapDerivedCategory :=
  exactDerivedFunctorIso (quasicoherentRestrictionCongrIso h)

/-- Restricting to an affine open and extending back cannot create support
on an open where the original derived object was already zero. The proof
uses the actual cartesian square of the two open immersions. -/
theorem quasicoherentOpenPushRestriction_isZero
    (j : U ⟶ X) [IsOpenImmersion j] [IsAffineHom j]
    (V : X.Opens) (E : DerivedQCoh X)
    (hE : IsZero ((quasicoherentRestriction V.ι).mapDerivedCategory.obj E)) :
    IsZero ((quasicoherentRestriction V.ι).mapDerivedCategory.obj
      ((quasicoherentAffinePushforward j).mapDerivedCategory.obj
        ((quasicoherentRestriction j).mapDerivedCategory.obj E))) := by
  let e :=
    (quasicoherentDerivedRestrictionCompIso (j ⁻¹ᵁ V).ι j).symm ≪≫
      quasicoherentDerivedRestrictionCongrIso (morphismRestrict_ι j V).symm ≪≫
      quasicoherentDerivedRestrictionCompIso (j ∣_ V) V.ι
  have hz : IsZero
      ((quasicoherentRestriction (j ⁻¹ᵁ V).ι).mapDerivedCategory.obj
        ((quasicoherentRestriction j).mapDerivedCategory.obj E)) :=
    (e.app E).isZero_iff.mpr
      ((quasicoherentRestriction (j ∣_ V)).mapDerivedCategory.map_isZero hE)
  exact ((quasicoherentDerivedRestrictPushforwardIso j V).app
    ((quasicoherentRestriction j).mapDerivedCategory.obj E)).isZero_iff.mpr
      ((quasicoherentAffinePushforward (j ∣_ V)).mapDerivedCategory.map_isZero hz)

end ToricPower

end
