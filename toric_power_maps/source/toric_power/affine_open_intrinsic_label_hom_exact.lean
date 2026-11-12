module

public import ToricPower.AffineOpenLabelHomExact
public import ToricPower.QuasicoherentBaseLinear

/-!
# Exactness for the intrinsic quasicoherent label Hom diagram

This version uses actual Hom objects inside `QCoh X`, exactly as in the
ordinary cellular realization--Hom adjunction on that category. Every
incidence map remains literal precomposition. Projectivity on the affine
open is the already proved projectivity of actual invertible sheaves.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace ToricPower

universe u

variable (R : Type u) [CommRing R] {U X : Scheme.{u}}
  [X.Over (Spec (.of R))] (j : U ⟶ X) [IsOpenImmersion j] [IsAffineHom j]
  {C : Type u} [Category.{u} C] (P : Cᵒᵖ ⥤ QCoh X)

/-- The actual direct image followed by the intrinsic quasicoherent
Hom diagram used by the ordinary cellular adjunction. -/
def quasicoherentOpenIntrinsicLabelHom : QCoh U ⥤ C ⥤ ModuleCat.{u} R :=
  quasicoherentAffinePushforward j ⋙ Cellular.homDiagram R P

instance quasicoherentOpenIntrinsicLabelHom_additive :
    (quasicoherentOpenIntrinsicLabelHom R j P).Additive := by
  unfold quasicoherentOpenIntrinsicLabelHom
  infer_instance

instance quasicoherentOpenIntrinsicLabelHom_preservesFiniteLimits :
    PreservesFiniteLimits (quasicoherentOpenIntrinsicLabelHom R j P) := by
  unfold quasicoherentOpenIntrinsicLabelHom
  infer_instance

variable [IsAffine U] [IsIntegral U]
  (invertible : ∀ c, TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible
    X (P.obj (op c)).obj)

include invertible

/-- Intrinsic Hom components preserve epimorphisms after affine direct
image, through the actual restriction--pushforward adjunction. -/
theorem quasicoherentOpenIntrinsicLabelHom_evaluation_epi
    {M N : QCoh U} (e : M ⟶ N) [Epi e] (c : C) :
    Epi (((quasicoherentOpenIntrinsicLabelHom R j P).map e).app c) := by
  letI := invertible c
  let label := P.obj (op c)
  letI : TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible U
      (((quasicoherentRestriction j).obj label).obj) :=
    InvertibleRestriction.invertible_restrict j label.obj
  letI : Projective ((quasicoherentRestriction j).obj label) :=
    quasicoherentAffineInvertible_projective U ((quasicoherentRestriction j).obj label)
  apply (ModuleCat.epi_iff_surjective _).mpr
  exact adjunction_postcomp_surjective_of_projective (quasicoherentOpenAdjunction j) label e

/-- The complete intrinsic quasicoherent label-Hom diagram is exact on
affine open direct images, for arbitrary invertible label functors. -/
theorem quasicoherentOpenIntrinsicLabelHom_exact :
    PreservesFiniteLimits (quasicoherentOpenIntrinsicLabelHom R j P) ∧
      PreservesFiniteColimits (quasicoherentOpenIntrinsicLabelHom R j P) := by
  constructor
  · infer_instance
  · apply preservesFiniteColimits_of_evaluation
    intro c
    let F := quasicoherentOpenIntrinsicLabelHom R j P ⋙ (evaluation C (ModuleCat R)).obj c
    apply (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi F).mpr
    intro S hS
    have left := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono F).mp
      inferInstance S hS
    letI := hS.epi_g
    exact ⟨left.1,
      quasicoherentOpenIntrinsicLabelHom_evaluation_epi R j P invertible S.g c⟩

end ToricPower
