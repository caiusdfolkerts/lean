module

public import ToricPower.QuasicoherentCategory
public import ToricPower.ExactDerivedAdjunction
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Affine

/-!
# Actual quasicoherent restriction and affine pushforward

Restriction to an open subscheme is exact on quasicoherent sheaves.
Pushforward along an affine morphism is exact on this same category,
by actual affine-section exactness. For an affine open immersion they
form the genuine restriction--pushforward adjunction, and hence an
adjunction on the full unbounded derived categories.

These are the sheaf operations used in a finite affine Čech coresolution.
The existence and exactness of that coresolution are separate assertions.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u

variable {U X : Scheme.{u}}

/-- The actual restriction of a quasicoherent sheaf to an open subscheme. -/
def quasicoherentRestriction (j : U ⟶ X) [IsOpenImmersion j] : QCoh X ⥤ QCoh U :=
  (SheafOfModules.isQuasicoherent U.ringCatSheaf).lift
    (quasicoherentInclusion X ⋙ Scheme.Modules.restrictFunctor j)
    (fun M => Scheme.Modules.isQuasicoherent_restrictFunctor j M.obj)

/-- Actual ordinary pushforward, restricted to quasicoherent sheaves
along an affine morphism. -/
def quasicoherentAffinePushforward (f : U ⟶ X) [IsAffineHom f] : QCoh U ⥤ QCoh X :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).lift
    (quasicoherentInclusion U ⋙ Scheme.Modules.pushforward f)
    (fun M => TauCeti.AlgebraicGeometry.isQuasicoherent_pushforward_of_isAffineHom f M.obj)

instance quasicoherentRestriction_additive (j : U ⟶ X) [IsOpenImmersion j] :
    (quasicoherentRestriction j).Additive where
  map_add := by
    intro M N f g
    apply ObjectProperty.hom_ext
    exact (Scheme.Modules.restrictFunctor j).map_add

instance quasicoherentAffinePushforward_additive (f : U ⟶ X) [IsAffineHom f] :
    (quasicoherentAffinePushforward f).Additive where
  map_add := by
    intro M N g h
    apply ObjectProperty.hom_ext
    exact (Scheme.Modules.pushforward f).map_add

instance quasicoherentRestriction_preservesFiniteLimits
    (j : U ⟶ X) [IsOpenImmersion j] :
    PreservesFiniteLimits (quasicoherentRestriction j) := by
  letI : PreservesFiniteLimits
      (quasicoherentRestriction j ⋙ quasicoherentInclusion U) := by
    change PreservesFiniteLimits
      (quasicoherentInclusion X ⋙ Scheme.Modules.restrictFunctor j)
    exact @comp_preservesFiniteLimits _ _ _ _ _ _ _ _
      (quasicoherentInclusion_preservesFiniteLimits X)
      (inferInstanceAs (PreservesFiniteLimits (Scheme.Modules.restrictFunctor j)))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (quasicoherentInclusion U)

instance quasicoherentRestriction_preservesFiniteColimits
    (j : U ⟶ X) [IsOpenImmersion j] :
    PreservesFiniteColimits (quasicoherentRestriction j) := by
  letI : PreservesFiniteColimits
      (quasicoherentRestriction j ⋙ quasicoherentInclusion U) := by
    change PreservesFiniteColimits
      (quasicoherentInclusion X ⋙ Scheme.Modules.restrictFunctor j)
    exact @comp_preservesFiniteColimits _ _ _ _ _ _ _ _
      (inferInstanceAs (PreservesFiniteColimits (quasicoherentInclusion X)))
      (inferInstanceAs (PreservesFiniteColimits (Scheme.Modules.restrictFunctor j)))
  exact preservesFiniteColimits_of_reflects_of_preserves _ (quasicoherentInclusion U)

instance quasicoherentAffinePushforward_preservesFiniteLimits
    (f : U ⟶ X) [IsAffineHom f] :
    PreservesFiniteLimits (quasicoherentAffinePushforward f) := by
  letI : PreservesFiniteLimits
      (quasicoherentAffinePushforward f ⋙ quasicoherentInclusion X) := by
    change PreservesFiniteLimits
      (quasicoherentInclusion U ⋙ Scheme.Modules.pushforward f)
    exact @comp_preservesFiniteLimits _ _ _ _ _ _ _ _
      (quasicoherentInclusion_preservesFiniteLimits U)
      (inferInstanceAs (PreservesFiniteLimits (Scheme.Modules.pushforward f)))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (quasicoherentInclusion X)

instance quasicoherentAffinePushforward_preservesFiniteColimits
    (f : U ⟶ X) [IsAffineHom f] :
    PreservesFiniteColimits (quasicoherentAffinePushforward f) := by
  apply (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
    (quasicoherentAffinePushforward f)).2
  intro S hS
  have hleft := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (quasicoherentAffinePushforward f)).mp inferInstance S hS
  letI : Epi S.g := hS.epi_g
  letI : Epi S.g.hom :=
    inferInstanceAs (Epi ((quasicoherentInclusion U).map S.g))
  letI : Epi ((Scheme.Modules.pushforward f).map S.g.hom) :=
    affinePushforward_epi f S.g.hom
  refine ⟨hleft.1, ?_⟩
  apply (quasicoherentInclusion X).epi_of_epi_map
  exact inferInstanceAs (Epi ((Scheme.Modules.pushforward f).map S.g.hom))

/-- The literal module-sheaf adjunction restricts along the fully
faithful inclusions of the two quasicoherent categories. -/
def quasicoherentOpenAdjunction (j : U ⟶ X) [IsOpenImmersion j] [IsAffineHom j] :
    quasicoherentRestriction j ⊣ quasicoherentAffinePushforward j :=
  (Scheme.Modules.restrictAdjunction j).restrictFullyFaithful
    (L := quasicoherentRestriction j) (R := quasicoherentAffinePushforward j)
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).fullyFaithfulι
    (SheafOfModules.isQuasicoherent U.ringCatSheaf).fullyFaithfulι
    (Iso.refl _) (Iso.refl _)

instance quasicoherentOpenPushforward_full
    (j : U ⟶ X) [IsOpenImmersion j] [IsAffineHom j] :
    (quasicoherentAffinePushforward j).Full where
  map_surjective {M N} f := by
    obtain ⟨g, hg⟩ := (Scheme.Modules.pushforward j).map_surjective f.hom
    exact ⟨ObjectProperty.homMk g, ObjectProperty.hom_ext _ hg⟩

instance quasicoherentOpenPushforward_faithful
    (j : U ⟶ X) [IsOpenImmersion j] [IsAffineHom j] :
    (quasicoherentAffinePushforward j).Faithful where
  map_injective {M N} f g h := by
    apply ObjectProperty.hom_ext
    apply (Scheme.Modules.pushforward j).map_injective
    exact congrArg (fun t => t.hom) h

local instance openQuasicoherentDerivedCategory (Y : Scheme.{u}) :
    HasDerivedCategory.{u+1} (QCoh Y) := HasDerivedCategory.standard _

/-- Exact open restriction and affine direct image give the actual
adjunction on unbounded quasicoherent derived categories. -/
def quasicoherentOpenDerivedAdjunction
    (j : U ⟶ X) [IsOpenImmersion j] [IsAffineHom j] :
    (quasicoherentRestriction j).mapDerivedCategory ⊣
      (quasicoherentAffinePushforward j).mapDerivedCategory :=
  exactDerivedAdjunction (quasicoherentOpenAdjunction j)

/-- Affine open direct image is fully faithful on the full unbounded
derived category of quasicoherent sheaves. -/
def quasicoherentOpenDerivedPushforwardFullyFaithful
    (j : U ⟶ X) [IsOpenImmersion j] [IsAffineHom j] :
    (quasicoherentAffinePushforward j).mapDerivedCategory.FullyFaithful :=
  exactDerivedRightFullyFaithful (quasicoherentOpenAdjunction j)

end ToricPower

end
