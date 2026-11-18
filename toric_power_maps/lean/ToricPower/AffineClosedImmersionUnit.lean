module

public import ToricPower.AffineQuasicoherentDuality
public import ToricPower.SurjectiveScalarRestriction

/-!
# The canonical affine closed-immersion unit and counit

Surjective scalar restriction is transported through the actual affine
tilde equivalences. The statements concern the original scheme adjunction,
including its unit on every associated sheaf of a restricted module.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory

namespace ToricPower

universe u

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
  (surjective : Function.Surjective φ)

/-- The actual affine direct image is fully faithful for a quotient ring. -/
def affineQuasicoherentPushforwardFullyFaithfulOfSurjective :
    (quasicoherentAffinePushforward (Spec.map φ)).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful
    (((tildeEquiv (R := S)).fullyFaithfulInverse.comp
      (restrictScalarsFullyFaithfulOfSurjective φ.hom surjective)).ofIso
        (quasicoherentAffinePushforwardSectionsIso φ).symm)

/-- Restriction to quasicoherent sheaves keeps the literal unit. -/
theorem quasicoherentAdjunction_unit_underlying {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsAffineHom f] (M : QCoh Y) :
    (quasicoherentInclusion Y).map
        ((quasicoherentPullbackPushforwardAdjunction f).unit.app M) =
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M.obj := by
  simp only [quasicoherentPullbackPushforwardAdjunction,
    Adjunction.map_restrictFullyFaithful_unit_app, Iso.refl_hom,
    NatTrans.id_app, Functor.map_id, Category.comp_id]
  rfl

theorem quasicoherentAdjunction_counit_underlying {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsAffineHom f] (M : QCoh X) :
    (quasicoherentInclusion X).map
        ((quasicoherentPullbackPushforwardAdjunction f).counit.app M) =
      (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M.obj := by
  simp only [quasicoherentPullbackPushforwardAdjunction,
    Adjunction.map_restrictFullyFaithful_counit_app, Iso.refl_inv,
    NatTrans.id_app, Functor.map_id, Category.id_comp]
  change 𝟙 _ ≫ (Scheme.Modules.pullback f).map
      (𝟙 ((Scheme.Modules.pushforward f).obj M.obj)) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M.obj = _
  erw [(Scheme.Modules.pullback f).map_id]
  simp only [Category.id_comp]

include surjective

/-- The original sheaf counit is invertible on every quasicoherent sheaf. -/
theorem affineClosedImmersionCounit_isIso (M : QCoh (Spec S)) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).counit.app M.obj) := by
  let full := affineQuasicoherentPushforwardFullyFaithfulOfSurjective φ surjective
  letI := full.full
  letI := full.faithful
  haveI : IsIso ((quasicoherentPullbackPushforwardAdjunction (Spec.map φ)).counit.app M) :=
    inferInstance
  rw [← quasicoherentAdjunction_counit_underlying]
  infer_instance

/-- The original sheaf unit is invertible on each actual affine direct image. -/
theorem affineClosedImmersionUnit_onPushforward_isIso (M : QCoh (Spec S)) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app
      ((Scheme.Modules.pushforward (Spec.map φ)).obj M.obj)) := by
  let full := affineQuasicoherentPushforwardFullyFaithfulOfSurjective φ surjective
  letI := full.full
  letI := full.faithful
  let P := (quasicoherentAffinePushforward (Spec.map φ)).obj M
  haveI : IsIso ((quasicoherentPullbackPushforwardAdjunction (Spec.map φ)).unit.app P) :=
    inferInstance
  change IsIso ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app P.obj)
  rw [← quasicoherentAdjunction_unit_underlying]
  infer_instance

/-- The canonical unit on the associated sheaf of an arbitrary restricted module. -/
theorem affineClosedImmersionUnit_onTilde_isIso (M : ModuleCat.{u} S) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app
      (tilde ((ModuleCat.restrictScalars φ.hom).obj M))) := by
  rw [NatTrans.isIso_app_iff_of_iso
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit
    (affinePushforwardTildeIso φ M).symm]
  exact affineClosedImmersionUnit_onPushforward_isIso φ surjective
    ((tildeEquiv (R := S)).functor.obj M)

end ToricPower

end
