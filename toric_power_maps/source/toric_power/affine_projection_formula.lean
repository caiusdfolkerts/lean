module

public import ToricPower.AffineQuasicoherentDuality
public import ToricPower.ModuleColimitComparison
public import ToricPower.MonoidalProjectionComparison
public import ToricPower.QuasicoherentTensorColimits

/-!
# The actual affine projection formula for arbitrary quasicoherent coefficients

The canonical comparison is the ordinary unit/tensor morphism of sheaf
pullback and direct image. On a smooth affine power chart direct image
preserves colimits by the proved residue-trace adjunction. The affine
tilde equivalence and the unrestricted free-module presentation then
prove the comparison invertible for every quasicoherent coefficient.
No finite-generation, boundedness, or local-freeness assumption is made
on either coefficient sheaf.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace ToricPower

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]

/-- The genuine projection comparison on the quasicoherent coefficient category. -/
def quasicoherentProjectionComparison (N : QCoh X) :
    quasicoherentInclusion Y ⋙
        tensorRight ((Scheme.Modules.pushforward f).obj N.obj) ⟶
      quasicoherentPullback f ⋙ tensorRight N ⋙
        quasicoherentAffinePushforward f ⋙ quasicoherentInclusion Y where
  app M := (monoidalProjectionComparison
    (Scheme.Modules.pullbackPushforwardAdjunction f) N.obj).app M.obj
  naturality {M M'} g := by
    exact (monoidalProjectionComparison
      (Scheme.Modules.pullbackPushforwardAdjunction f) N.obj).naturality g.hom

/-- The canonical map remains natural in the source coefficient. -/
theorem quasicoherentProjectionComparison_naturality_right
    {N N' : QCoh X} (g : N ⟶ N') (M : QCoh Y) :
    M.obj ◁ (Scheme.Modules.pushforward f).map g.hom ≫
        (quasicoherentProjectionComparison f N').app M =
      (quasicoherentProjectionComparison f N).app M ≫
        (Scheme.Modules.pushforward f).map
          ((Scheme.Modules.pullback f).obj M.obj ◁ g.hom) :=
  monoidalProjectionComparison_naturality_right
    (Scheme.Modules.pullbackPushforwardAdjunction f) g.hom M.obj

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- A proved scalar adjunction suffices to establish the actual affine
projection formula for all quasicoherent sheaves. -/
theorem affineQuasicoherentProjectionComparison_isIso
    (scalarAdjunction : ModuleCat.restrictScalars.{u} φ.hom ⊣ ModuleCat.extendScalars φ.hom)
    (N : QCoh (Spec S)) (M : QCoh (Spec R)) :
    IsIso ((quasicoherentProjectionComparison (Spec.map φ) N).app M) := by
  letI := (quasicoherentPullbackPushforwardAdjunction (Spec.map φ)).isLeftAdjoint
  letI := (affineQuasicoherentPushforwardPullbackAdjunction φ scalarAdjunction).isLeftAdjoint
  let α := quasicoherentProjectionComparison (Spec.map φ) N
  let comparison := Functor.whiskerLeft (tildeEquiv (R := R)).functor α
  have unit : IsIso (comparison.app (ModuleCat.of R R)) := by
    change IsIso ((monoidalProjectionComparison
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)) N.obj).app
        (tilde (ModuleCat.of R R)))
    exact (NatTrans.isIso_app_iff_of_iso
      (monoidalProjectionComparison
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)) N.obj)
      (tildeSelf (R := R))).mpr
      (monoidalProjectionComparison_unit_isIso
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)) N.obj)
  have h : IsIso (α.app
      ((tildeEquiv (R := R)).functor.obj ((tildeEquiv (R := R)).inverse.obj M))) :=
    isIso_natTrans_app_of_free_unit R comparison unit _
  exact (NatTrans.isIso_app_iff_of_iso α ((tildeEquiv (R := R)).counitIso.app M)).mp h

/-- The full natural projection isomorphism, with the canonical map as its hom. -/
def affineQuasicoherentProjectionIso
    (scalarAdjunction : ModuleCat.restrictScalars.{u} φ.hom ⊣ ModuleCat.extendScalars φ.hom)
    (N : QCoh (Spec S)) :
    quasicoherentInclusion (Spec R) ⋙
        tensorRight ((Scheme.Modules.pushforward (Spec.map φ)).obj N.obj) ≅
      quasicoherentPullback (Spec.map φ) ⋙ tensorRight N ⋙
        quasicoherentAffinePushforward (Spec.map φ) ⋙ quasicoherentInclusion (Spec R) := by
  let α := quasicoherentProjectionComparison (Spec.map φ) N
  letI : IsIso α := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact affineQuasicoherentProjectionComparison_isIso φ scalarAdjunction N
  exact asIso α

end ToricPower

end
