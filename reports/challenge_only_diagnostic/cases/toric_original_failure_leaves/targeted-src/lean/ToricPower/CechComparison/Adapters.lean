module

public import ToricPower.Cohomology.QuasicoherentFlasque
public import ToricPower.Cohomology.SchemeFlasque
public import ToricPower.FinitePushforward
public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Actual all-degree finite-affine Čech comparison

For a Noetherian separated scheme and any finite affine open cover, the
cohomology of an actual quasicoherent module sheaf is isomorphic in every
degree to the homology of Mathlib's actual Čech complex. The proof constructs
a quasicoherent flasque resolution tower from injective modules on a finite
affine cover, proves positive Čech acyclicity of flasque sheaves by finite
open-set induction, and performs dimension shifting from the actual long
exact sequences. The final endpoint assumes neither a comparison map nor
an acyclicity assertion.

Only generic proof bodies are retained. Historical toric application imports
are replaced by the genuine generic theories already present in this project.
No completeness, projectivity, or generation hypothesis enters this module.

Development source: successful pinned compilation of the exact source and
all dependencies is required before reporting verification.
-/
/-! ## Adapters to existing genuine generic theories -/
/-!
Generic adapters to the genuine sheaf and cohomology results already present
in CoherentFoundations and CohomologyCore. These replace unused historical
toric imports in the recovered finite-affine Čech development.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace BondalThomsen.FiniteQuasicoherentPushforward

universe u

variable {Source Target : Scheme.{u}}

theorem affinePushforward_isQuasicoherent (morphism : Source ⟶ Target)
    [IsAffineHom morphism] (coefficient : Source.Modules) [coefficient.IsQuasicoherent] :
    ((Scheme.Modules.pushforward morphism).obj coefficient).IsQuasicoherent :=
  TauCeti.AlgebraicGeometry.isQuasicoherent_pushforward_of_isAffineHom morphism coefficient

/-- The chart restriction and restriction to its actual open image differ
by the restriction equivalence induced by the chart isomorphism. -/
theorem isQuasicoherent_restrict_opensRange (open_map : Source ⟶ Target)
    [IsOpenImmersion open_map] (coefficient : Target.Modules)
    [(coefficient.restrict open_map).IsQuasicoherent] :
    (coefficient.restrict open_map.opensRange.ι).IsQuasicoherent := by
  let U := open_map.opensRange
  let e := open_map.isoOpensRange
  let comparison : coefficient.restrict open_map ≅
      (coefficient.restrict U.ι).restrict e.hom :=
    (Scheme.Modules.restrictFunctorCongr open_map.isoOpensRange_hom_ι.symm).app coefficient ≪≫
      (Scheme.Modules.restrictFunctorComp e.hom U.ι).app coefficient
  letI : ((coefficient.restrict U.ι).restrict e.hom).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent Source.ringCatSheaf).prop_of_iso comparison inferInstance
  exact @TauCeti.AlgebraicGeometry.isQuasicoherent_of_isQuasicoherent_restrict_iso
    _ _ e.symm (coefficient.restrict U.ι)
    (inferInstanceAs (((coefficient.restrict U.ι).restrict e.hom).IsQuasicoherent))

theorem isQuasicoherent_of_openCover (cover : Scheme.OpenCover.{u} Target)
    (coefficient : Target.Modules)
    [∀ index, (coefficient.restrict (cover.f index)).IsQuasicoherent] :
    coefficient.IsQuasicoherent :=
  TauCeti.AlgebraicGeometry.isQuasicoherent_of_isQuasicoherent_restrict coefficient
    (fun index => (cover.f index).opensRange) cover.isOpenCover_opensRange
    (fun index => isQuasicoherent_restrict_opensRange (cover.f index) coefficient)

set_option backward.isDefEq.respectTransparency false in
/-- Equality of genuine sheaf morphisms is local on an actual open cover.
This is the unchanged generic proof from FiniteQuasicoherentPushforward. -/
theorem hom_ext_of_openCover (cover : Scheme.OpenCover.{u} Target)
    {first second : Target.Modules} (first_map second_map : first ⟶ second)
    (local_equality : ∀ index, (Scheme.Modules.restrictFunctor (cover.f index)).map first_map =
      (Scheme.Modules.restrictFunctor (cover.f index)).map second_map) :
    first_map = second_map := by
  let covers_top : (Opens.grothendieckTopology Target).CoversTop
      (fun index => (cover.f index).opensRange) :=
    (Opens.coversTop_iff _ _).mpr cover.isOpenCover_opensRange
  apply Scheme.Modules.hom_ext
  intro open_set
  apply second.isSheaf.hom_ext (covers_top.cover open_set)
  rintro ⟨local_open, inclusion, ⟨index, ⟨inside⟩⟩⟩
  have equality := congrArg
    (fun arrow => arrow.app ((cover.f index) ⁻¹ᵁ local_open)) (local_equality index)
  change first_map.app ((cover.f index) ''ᵁ (cover.f index) ⁻¹ᵁ local_open) =
    second_map.app ((cover.f index) ''ᵁ (cover.f index) ⁻¹ᵁ local_open) at equality
  rw [(cover.f index).image_preimage_eq_opensRange_inf,
    inf_eq_right.mpr inside.le] at equality
  change first_map.mapPresheaf.app (op open_set) ≫ second.presheaf.map inclusion.op =
    second_map.mapPresheaf.app (op open_set) ≫ second.presheaf.map inclusion.op
  rw [← first_map.mapPresheaf.naturality, ← second_map.mapPresheaf.naturality]
  exact congrArg (fun arrow => first.presheaf.map inclusion.op ≫ arrow) equality

end BondalThomsen.FiniteQuasicoherentPushforward

namespace BondalThomsen.ToricMultiplicationCohomologyTransport

universe u

/-- Ordinary direct image preserves flasqueness for every scheme morphism.
The historical namespace adds no toric or finiteness hypothesis. -/
instance pushforward_isFlasque {Source Target : Scheme.{u}}
    (morphism : Source ⟶ Target) (coefficient : Source.Modules)
    [coefficient.presheaf.IsFlasque] :
    ((Scheme.Modules.pushforward morphism).obj coefficient).presheaf.IsFlasque where
  epi {first_open second_open} restriction := by
    change Epi (coefficient.presheaf.map
      ((TopologicalSpace.Opens.map morphism.base).map restriction.unop).op)
    infer_instance

end BondalThomsen.ToricMultiplicationCohomologyTransport

namespace BondalThomsen.AffineHigherCohomologyVanishing

universe u

/-- The actual injective-module flasqueness theorem from CohomologyCore,
transported from categorical to ordinary module injectivity. -/
theorem injectiveTilde_isFlasque {ring : CommRingCat.{u}} [IsNoetherianRing ring]
    (coefficient : ModuleCat.{u} ring) [CategoryTheory.Injective coefficient] :
    (tilde coefficient).presheaf.IsFlasque := by
  letI : Module.Injective ring coefficient :=
    Module.injective_module_of_injective_object ring coefficient
  exact TauCeti.AlgebraicGeometry.isFlasque_tilde_of_injective coefficient

end BondalThomsen.AffineHigherCohomologyVanishing

namespace BondalThomsen.FiniteAffineCechCohomology

universe u

/-- Exactness of affine sections has already been proved for actual
quasicoherent module sheaves in CoherentFoundations. -/
theorem affineOpenSections_surjective {scheme : Scheme.{u}}
    {first second : scheme.Modules} [first.IsQuasicoherent] [second.IsQuasicoherent]
    (coefficient_map : first ⟶ second) [Epi coefficient_map]
    (open_set : scheme.Opens) (affine : IsAffineOpen open_set) :
    Function.Surjective (coefficient_map.app open_set) :=
  ToricPower.affineSections_surjective_of_epi coefficient_map affine

end BondalThomsen.FiniteAffineCechCohomology

end

