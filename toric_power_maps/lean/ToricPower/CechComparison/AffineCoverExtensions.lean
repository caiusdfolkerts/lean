module

public import ToricPower.CechComparison.FlasqueTowerConstruction

section CechComparisonSource02


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry Opposite
open BondalThomsen.QuasicoherentFlasqueTowerConstruction
open BondalThomsen.FiniteQuasicoherentCohomologyTower
open TauCeti.AlgebraicGeometry.Scheme.Modules


namespace BondalThomsen.FiniteAffineCoverQuasicoherentExtensions

universe u

noncomputable section

variable {scheme target : Scheme.{u}}

def affineOpenCoverOfAffineCover (cover : Scheme.OpenCover.{u} scheme)
    [∀ index, IsAffine (cover.X index)] : Scheme.AffineOpenCover.{u} scheme where
  I₀ := cover.I₀
  X index := Γ(cover.X index, ⊤)
  f index := (cover.X index).isoSpec.inv ≫ cover.f index
  idx := cover.idx
  covers point := by
    obtain ⟨local_point, local_image⟩ := cover.covers point
    refine ⟨(cover.X (cover.idx point)).isoSpec.hom local_point, ?_⟩
    change (cover.f (cover.idx point))
      (((cover.X (cover.idx point)).isoSpec.hom ≫
        (cover.X (cover.idx point)).isoSpec.inv) local_point) = point
    rw [Iso.hom_inv_id]
    exact local_image
  map_prop index := inferInstance

instance affineOpenCoverOfAffineCover_finite (cover : Scheme.OpenCover.{u} scheme)
    [∀ index, IsAffine (cover.X index)] [Finite cover.I₀] :
    Finite (affineOpenCoverOfAffineCover cover).I₀ := inferInstanceAs (Finite cover.I₀)

def finiteAffineOpenCover (scheme : Scheme.{u}) [CompactSpace scheme] :
    Scheme.AffineOpenCover.{u} scheme :=
  affineOpenCoverOfAffineCover scheme.affineCover.finiteSubcover

instance finiteAffineOpenCover_finite [CompactSpace scheme] :
    Finite (finiteAffineOpenCover scheme).I₀ := by
  dsimp [finiteAffineOpenCover]
  infer_instance

theorem affineChartRing_isNoetherian [IsLocallyNoetherian scheme]
    (cover : Scheme.AffineOpenCover.{u} scheme) (index : cover.I₀) :
    IsNoetherianRing (cover.X index) := by
  have : IsLocallyNoetherian (Spec (cover.X index)) :=
    isLocallyNoetherian_of_isOpenImmersion (cover.f index)
  exact isLocallyNoetherian_Spec.mp inferInstance

theorem tilde_map_mono {ring : CommRingCat.{u}} {first second : ModuleCat.{u} ring}
    (module_map : first ⟶ second) [Mono module_map] : Mono (tilde.map module_map) := by
  apply (SheafOfModules.forget (Spec ring).ringCatSheaf).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro open_set first_section second_section same_image
  apply Subtype.ext
  funext point
  apply LocalizedModule.map_injective point.val.asIdeal.primeCompl module_map.hom
    ((ModuleCat.mono_iff_injective module_map).mp inferInstance)
  exact congrArg (fun local_section => local_section.val point) same_image

def affineInjectiveFlasqueEmbedding {ring : CommRingCat.{u}} [IsNoetherianRing ring]
    (coefficient : (Spec ring).Modules) [coefficient.IsQuasicoherent] :
    AffineInjectiveFlasqueEmbedding ring coefficient := by
  letI : EnoughInjectives (ModuleCat.{u} ring) := ModuleCat.enoughInjectives ring
  let presentation : InjectivePresentation (moduleSpecΓFunctor.obj coefficient) :=
    Classical.choice (EnoughInjectives.presentation (moduleSpecΓFunctor.obj coefficient))
  letI := tilde_map_mono presentation.f
  exact
    { module := presentation.J
      injective := presentation.injective
      flasque := AffineHigherCohomologyVanishing.injectiveTilde_isFlasque presentation.J
      inclusion := (asIso coefficient.fromTildeΓ).inv ≫ tilde.map presentation.f
      mono := inferInstance }

def noetherianAffineChartEmbedding [IsLocallyNoetherian scheme]
    (cover : Scheme.AffineOpenCover.{u} scheme) (coefficient : scheme.Modules)
    [coefficient.IsQuasicoherent] (index : cover.I₀) :
    AffineInjectiveFlasqueEmbedding (cover.X index)
      (coefficient.restrict (cover.f index)) := by
  letI := affineChartRing_isNoetherian cover index
  exact affineInjectiveFlasqueEmbedding _

def noetherianLocalFlasqueEmbedding [IsLocallyNoetherian scheme]
    (cover : Scheme.AffineOpenCover.{u} scheme) (coefficient : scheme.Modules)
    [coefficient.IsQuasicoherent] : LocalFlasqueEmbedding cover.openCover coefficient :=
  localFlasqueEmbeddingOfAffineModules cover coefficient
    (noetherianAffineChartEmbedding cover coefficient)

def noetherianQuasicoherentFlasqueResolutionTower [IsLocallyNoetherian scheme]
    [scheme.IsSeparated] (cover : Scheme.AffineOpenCover.{u} scheme) [Finite cover.I₀]
    (coefficient : scheme.Modules) [coefficient.IsQuasicoherent] :
    QuasicoherentResolutionTower coefficient :=
  flasqueResolutionTowerOfAffineModules cover coefficient (fun current quasicoherent =>
    letI := quasicoherent
    noetherianAffineChartEmbedding cover current)

end

end BondalThomsen.FiniteAffineCoverQuasicoherentExtensions

-- Explicit source EOF scope closures.
end

end CechComparisonSource02
