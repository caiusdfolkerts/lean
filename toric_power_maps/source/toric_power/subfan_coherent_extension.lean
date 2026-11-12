module

public import ToricPower.SubfanAffineImmersion
public import ToricPower.CartierLocalCoherentImage
public import ToricPower.AffineLocalFiniteGenerators
public import ToricPower.ModuleRestrictionLocalIsomorphisms
public import ToricPower.ToricCoherentCartierCover

/-!
# Actual coherent extension across a divisorial toric boundary

The full-on-rays hypothesis makes the genuine subfan immersion affine.
Push forward the coherent sheaf, extend finitely many actual local
generators by Cartier sections, and take the coherent image. Local
isomorphism detection proves that its restriction is the original
sheaf. This constructs coherent extensions without assuming them and
does not require extension of arbitrary complexes.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open Scheme.Modules

namespace ToricPower

universe u

variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (fan extension : Fan i) (included : fan.cones ⊆ extension.cones)
  (nonempty : Nonempty fan.cones) (regular : extension.IsRegular)
  (rayFull : IsFullOnRays fan extension)

include nonempty regular rayFull in
/-- Every actual coherent sheaf on the original toric variety is the
restriction of an actual coherent sheaf on the extending variety. -/
theorem subfan_exists_coherent_extension (M : fan.algebraicRealization.Modules)
    [M.IsFinitePresentation] :
    letI := subfanSchemeMap_isOpenImmersion fan extension included
    ∃ (P : extension.algebraicRealization.Modules) (_ : P.IsFinitePresentation),
      Nonempty (P.restrict (subfanSchemeMap fan extension included) ≅ M) := by
  let j := subfanSchemeMap fan extension included
  letI := subfanSchemeMap_isOpenImmersion fan extension included
  letI := subfanSchemeMap_isAffineHom fan extension included regular rayFull
  let newNonempty : Nonempty extension.cones :=
    nonempty.map (subfanConeEmbedding fan extension included)
  letI := toricSchemeIntegral extension newNonempty
  letI := toricScheme_isNoetherian extension
  let E := (pushforward j).obj M
  letI : E.IsQuasicoherent :=
    TauCeti.AlgebraicGeometry.isQuasicoherent_pushforward_of_isAffineHom j M
  let chart (σ : fan.cones) :=
    extension.affineToricChartι (subfanConeEmbedding fan extension included σ)
  let opens (σ : fan.cones) := (chart σ).opensRange
  have localPresentation (σ : fan.cones) : (E.restrict (chart σ)).IsFinitePresentation := by
    let comparison := openPushforwardChartRestrictionIso j (fan.affineToricChartι σ)
      (chart σ) (subfanSchemeMap_chart fan extension included σ) M
    exact (SheafOfModules.isFinitePresentation (fan.affineToricChart σ).ringCatSheaf).prop_of_iso
      comparison.symm (finitePresentation_restrict (fan.affineToricChartι σ) M)
  letI := localPresentation
  choose G finiteG using fun σ : fan.cones =>
    exists_finite_generatingSections_of_affine_restriction (chart σ) E
  letI (σ : fan.cones) : (G σ).IsFiniteType := finiteG σ
  have sections : HasCartierSectionExtensions opens := by
    intro σ Q hQ s
    exact toricSection_exists_cartier_extension extension newNonempty regular
      (subfanConeEmbedding fan extension included σ) Q s
  obtain ⟨P,hP,f,mono,localIso⟩ := exists_coherent_image_iso_over opens sections E G
  letI := hP
  have restrictionIso : IsIso ((restrictFunctor j).map f) := by
    apply moduleSheaf_isIso_of_openImmersionCover fan.affineToricChart fan.affineToricChartι
      fan.exists_affineToricChartι_apply_eq
    intro σ
    let comparison : restrictFunctor j ⋙ restrictFunctor (fan.affineToricChartι σ) ≅
        restrictFunctor (chart σ) :=
      (restrictFunctorComp (fan.affineToricChartι σ) j).symm ≪≫
        restrictFunctorCongr (subfanSchemeMap_chart fan extension included σ)
    exact (NatIso.isIso_map_iff comparison f).mpr
      ((moduleRestriction_isIso_iff_over (chart σ) f).mpr (localIso σ))
  letI := restrictionIso
  exact ⟨P,hP,⟨asIso ((restrictFunctor j).map f) ≪≫ (restrictFunctorAdjCounitIso j).app M⟩⟩

end ToricPower

end
