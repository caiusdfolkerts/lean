module

public import ToricPower.QuasicoherentOpenAdjunction
public import ToricPower.AffineSplitting
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic
public import ToricPower.TransportedPowerTrace

/-!
# Actual affine quasicoherent duality from a proved scalar adjunction

The affine tilde equivalence identifies genuine pullback with extension
of scalars and genuine direct image with restriction of scalars. A proved
restriction--extension adjunction therefore gives a second adjunction
between these actual sheaf functors. The ordinary pullback--pushforward
adjunction is retained as well. Both descend to unbounded complexes.

In the power-map application the scalar adjunction is supplied by the
full complementary-residue pairing, not by an additional duality axiom.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u

/-- The actual pullback of quasicoherent module sheaves. -/
def quasicoherentPullback {X Y : Scheme.{u}} (f : X ⟶ Y) : QCoh Y ⥤ QCoh X :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).lift
    (quasicoherentInclusion Y ⋙ Scheme.Modules.pullback f)
    (fun M => Scheme.Modules.isQuasicoherent_pullback f M.obj)

instance quasicoherentPullback_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (quasicoherentPullback f).Additive where
  map_add := by
    intro M N g h
    apply ObjectProperty.hom_ext
    exact (Scheme.Modules.pullback f).map_add

/-- The ordinary adjunction restricted to the actual quasicoherent categories. -/
def quasicoherentPullbackPushforwardAdjunction {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsAffineHom f] :
    quasicoherentPullback f ⊣ quasicoherentAffinePushforward f :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).restrictFullyFaithful
    (L := quasicoherentPullback f) (R := quasicoherentAffinePushforward f)
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).fullyFaithfulι
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).fullyFaithfulι
    (Iso.refl _) (Iso.refl _)

instance quasicoherentPullback_preservesFiniteColimits {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsAffineHom f] : PreservesFiniteColimits (quasicoherentPullback f) := by
  letI := (quasicoherentPullbackPushforwardAdjunction f).isLeftAdjoint
  infer_instance

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- Actual affine direct image is restriction of scalars on global sections. -/
def quasicoherentAffinePushforwardSectionsIso :
    quasicoherentAffinePushforward (Spec.map φ) ⋙ (tildeEquiv (R := R)).inverse ≅
      (tildeEquiv (R := S)).inverse ⋙ ModuleCat.restrictScalars φ.hom :=
  NatIso.ofComponents
    (fun M => (affinePushforwardSectionsIso φ).app M.obj)
    (by
      intro M N f
      exact (affinePushforwardSectionsIso φ).hom.naturality f.hom)

/-- The affine base-change isomorphism, with its actual quasicoherent wrapper. -/
def quasicoherentTildePullbackIso :
    (tildeEquiv (R := R)).functor ⋙ quasicoherentPullback (Spec.map φ) ≅
      ModuleCat.extendScalars φ.hom ⋙ (tildeEquiv (R := S)).functor :=
  NatIso.ofComponents
    (fun M => ObjectProperty.isoMk _
      ((TauCeti.AlgebraicGeometry.tildeFunctorCompPullbackIso φ).app M))
    (by
      intro M N f
      apply ObjectProperty.hom_ext
      exact (TauCeti.AlgebraicGeometry.tildeFunctorCompPullbackIso φ).hom.naturality f)

/-- Actual pullback is extension of scalars on the affine section modules. -/
def quasicoherentAffinePullbackSectionsIso :
    quasicoherentPullback (Spec.map φ) ⋙ (tildeEquiv (R := S)).inverse ≅
      (tildeEquiv (R := R)).inverse ⋙ ModuleCat.extendScalars φ.hom :=
  Functor.isoWhiskerRight (tildeEquiv (R := R)).counitIso.symm
      (quasicoherentPullback (Spec.map φ) ⋙ (tildeEquiv (R := S)).inverse) ≪≫
    Functor.isoWhiskerLeft (tildeEquiv (R := R)).inverse
      (Functor.isoWhiskerRight (quasicoherentTildePullbackIso φ)
        (tildeEquiv (R := S)).inverse) ≪≫
    Functor.isoWhiskerLeft
      ((tildeEquiv (R := R)).inverse ⋙ ModuleCat.extendScalars φ.hom)
      (tildeEquiv (R := S)).unitIso.symm

/-- Transport a proved scalar adjunction through the literal affine equivalences. -/
def affineQuasicoherentPushforwardPullbackAdjunction
    (scalarAdjunction : ModuleCat.restrictScalars.{u} φ.hom ⊣ ModuleCat.extendScalars φ.hom) :
    quasicoherentAffinePushforward (Spec.map φ) ⊣ quasicoherentPullback (Spec.map φ) :=
  scalarAdjunction.restrictFullyFaithful
    (L := quasicoherentAffinePushforward (Spec.map φ))
    (R := quasicoherentPullback (Spec.map φ))
    (tildeEquiv (R := S)).fullyFaithfulInverse
    (tildeEquiv (R := R)).fullyFaithfulInverse
    (quasicoherentAffinePushforwardSectionsIso φ).symm
    (quasicoherentAffinePullbackSectionsIso φ).symm

/-- The second adjunction proves exactness of the genuine affine pullback. -/
theorem affineQuasicoherentPullback_preservesFiniteLimits
    (scalarAdjunction : ModuleCat.restrictScalars.{u} φ.hom ⊣ ModuleCat.extendScalars φ.hom) :
    PreservesFiniteLimits (quasicoherentPullback (Spec.map φ)) := by
  letI := (affineQuasicoherentPushforwardPullbackAdjunction φ scalarAdjunction).isRightAdjoint
  infer_instance

local instance affineDualityDerivedCategory (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} (QCoh X) := HasDerivedCategory.standard _

/-- Finite affine duality on the actual unbounded derived categories. -/
def affineQuasicoherentDerivedPushforwardPullbackAdjunction
    (scalarAdjunction : ModuleCat.restrictScalars.{u} φ.hom ⊣ ModuleCat.extendScalars φ.hom) :
    letI := affineQuasicoherentPullback_preservesFiniteLimits φ scalarAdjunction
    (quasicoherentAffinePushforward (Spec.map φ)).mapDerivedCategory ⊣
      (quasicoherentPullback (Spec.map φ)).mapDerivedCategory := by
  letI := affineQuasicoherentPullback_preservesFiniteLimits φ scalarAdjunction
  exact exactDerivedAdjunction
    (affineQuasicoherentPushforwardPullbackAdjunction φ scalarAdjunction)

end ToricPower

end
