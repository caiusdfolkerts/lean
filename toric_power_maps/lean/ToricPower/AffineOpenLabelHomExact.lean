module

public import ToricPower.QuasicoherentAffineProjective
public import ToricPower.QuasicoherentOpenAdjunction
public import ToricPower.CellularHomDiagram
public import ToricPower.ToricLineBundleFrames

/-!
# Exactness of the actual label Hom diagram on affine open direct images

Restriction of an invertible label to an integral affine open is
projective in the actual quasicoherent category. The actual open
restriction--pushforward adjunction therefore lifts each Hom component
against every quasicoherent epimorphism. Together with ordinary
representable limit preservation, this proves exactness of the entire
module-valued diagram, with its original incidence maps retained.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace ToricPower

universe u v₁ v₂ u₁ u₂

/-- A projective restricted object lifts actual maps through the right
adjoint of every epimorphism. -/
theorem adjunction_postcomp_surjective_of_projective
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R)
    (P : A) [Projective (L.obj P)] {M N : B} (e : M ⟶ N) [Epi e] :
    Function.Surjective (fun f : P ⟶ R.obj M => f ≫ R.map e) := by
  intro f
  let localMap := (adj.homEquiv P N).symm f
  let lift := Projective.factorThru localMap e
  refine ⟨adj.homEquiv P M lift, ?_⟩
  change adj.homEquiv P M lift ≫ R.map e = f
  rw [← adj.homEquiv_naturality_right, Projective.factorThru_comp,
    Equiv.apply_symm_apply]

variable (R : Type u) [CommRing R] {U X : Scheme.{u}}
  [X.Over (Spec (.of R))] (j : U ⟶ X) [IsOpenImmersion j] [IsAffineHom j]
  {C : Type u} [Category.{u} C] (P : Cᵒᵖ ⥤ X.Modules)

/-- Actual affine direct image followed by the actual scalar-linear
Hom diagram. No label map or coefficient map is replaced. -/
def quasicoherentOpenLabelHom : QCoh U ⥤ C ⥤ ModuleCat.{u} R :=
  quasicoherentAffinePushforward j ⋙ quasicoherentInclusion X ⋙ Cellular.homDiagram R P

instance quasicoherentOpenLabelHom_additive :
    (quasicoherentOpenLabelHom R j P).Additive := by
  unfold quasicoherentOpenLabelHom
  infer_instance

instance quasicoherentOpenLabelHom_preservesFiniteLimits :
    PreservesFiniteLimits (quasicoherentOpenLabelHom R j P) := by
  unfold quasicoherentOpenLabelHom
  infer_instance

variable [IsAffine U] [IsIntegral U]
  (invertible : ∀ c, TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X (P.obj (op c)))

include invertible

/-- Each actual Hom component takes an actual quasicoherent epi to a
surjective linear map. Projectivity of the restricted label is proved,
using invertibility and the actual integral affine source. -/
theorem quasicoherentOpenLabelHom_evaluation_epi
    {M N : QCoh U} (e : M ⟶ N) [Epi e] (c : C) :
    Epi (((quasicoherentOpenLabelHom R j P).map e).app c) := by
  letI := invertible c
  let label : QCoh X := ⟨P.obj (op c), inferInstance⟩
  letI : TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible U
      (((quasicoherentRestriction j).obj label).obj) :=
    InvertibleRestriction.invertible_restrict j (P.obj (op c))
  letI : Projective ((quasicoherentRestriction j).obj label) :=
    quasicoherentAffineInvertible_projective U ((quasicoherentRestriction j).obj label)
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro f
  obtain ⟨lift, same⟩ := adjunction_postcomp_surjective_of_projective
    (quasicoherentOpenAdjunction j) label e (ObjectProperty.homMk f)
  refine ⟨lift.hom, ?_⟩
  exact congrArg (fun mapping => mapping.hom) same

/-- The whole actual label Hom diagram is exact on quasicoherent
direct images from every integral affine open. This is the local input
for a finite affine coresolution of arbitrary unbounded complexes. -/
theorem quasicoherentOpenLabelHom_exact :
    PreservesFiniteLimits (quasicoherentOpenLabelHom R j P) ∧
      PreservesFiniteColimits (quasicoherentOpenLabelHom R j P) := by
  constructor
  · infer_instance
  · apply preservesFiniteColimits_of_evaluation
    intro c
    let F := quasicoherentOpenLabelHom R j P ⋙ (evaluation C (ModuleCat R)).obj c
    apply (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi F).mpr
    intro S hS
    have left := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono F).mp
      inferInstance S hS
    letI := hS.epi_g
    exact ⟨left.1, quasicoherentOpenLabelHom_evaluation_epi R j P invertible S.g c⟩

end ToricPower
