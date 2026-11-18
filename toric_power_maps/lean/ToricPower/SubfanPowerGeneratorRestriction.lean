module

public import ToricPower.SubfanGeneratorRestriction
public import ToricPower.SubfanPowerRestriction
public import ToricPower.SubfanCartierRestriction
public import ToricPower.PrincipalStatements

/-!
# Restriction of the paper's actual power-map generators

The coherent extension theorem, ordinary power-map base change, and
the actual Cartier-line restriction isomorphism identify the restricted
generator with the paper's original object in literal bounded coherent
complexes. Boundary twists disappear under restriction.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TauCeti.Toric

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (fan extension : Fan i) (included : fan.cones ⊆ extension.cones)
  (hne : fan.cones.Nonempty) (regular : extension.IsRegular)
  (rayFull : IsFullOnRays fan extension)

include rayFull in
/-- Generation by an actual power pushforward descends through the
actual subfan immersion whenever the original Cartier lines agree. -/
theorem subfan_power_generates_of_restriction
    (D : toricCartierDivisor fan hne)
    (extended : toricCartierDivisor extension (hne.mono included))
    (comparison : letI := subfanSchemeMap_isOpenImmersion fan extension included
      (toricDivisorSheaf extension (hne.mono included) extended).restrict
        (subfanSchemeMap fan extension included) ≅ toricDivisorSheaf fan hne D)
    (ell : ℕ) (positive : 0 < ell)
    (generates : toricPowerGeneratesDbCoh extension regular (hne.mono included)
      extended ell positive) :
    toricPowerGeneratesDbCoh fan (subfan_isRegular fan extension included regular)
      hne D ell positive := by
  letI := toricScheme_isNoetherian fan
  letI := toricScheme_isNoetherian extension
  letI := subfanSchemeMap_isOpenImmersion fan extension included
  let j := subfanSchemeMap fan extension included
  let M : Coh extension.algebraicRealization :=
    ⟨toricPowerDivisorSheaf extension (hne.mono included) extended ell,
      toricPowerDivisorSheaf_isFinitePresentation extension regular (hne.mono included)
        extended ell positive⟩
  let P : Coh fan.algebraicRealization :=
    ⟨toricPowerDivisorSheaf fan hne D ell,
      toricPowerDivisorSheaf_isFinitePresentation fan
        (subfan_isRegular fan extension included regular) hne D ell positive⟩
  let localIso := subfanPowerPushforwardRestrictionIso fan extension included ell positive
      (toricDivisorSheaf extension (hne.mono included) extended) ≪≫
    (Scheme.Modules.pushforward (toricPowerMap fan ell)).mapIso comparison
  let coherentIso :
      (TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.restrictFunctor j).obj M ≅ P :=
    (SheafOfModules.isFinitePresentation fan.algebraicRealization.ringCatSheaf).isoMk localIso
  let derivedIso := coherentDerivedRestrictionSingleIso j M ≪≫ coherentSingleIso coherentIso
  have restricted := subfan_coherentDerivedRestriction_generates fan extension included
    hne.coe_sort regular rayFull (coherentSingle extension.algebraicRealization M) generates
  exact (classicalGenerator_iff_of_iso derivedIso).mp restricted

include rayFull in
/-- The actual generator for any boundary twist restricts to the
original power-map generator, at the identical exponent. -/
theorem subfan_boundary_power_generates (b : fan.Ray → ℤ) (a ell : ℕ) (positive : 0 < ell)
    (generates : letI := toricScheme_isIntegral extension (hne.mono included)
      toricPowerGeneratesDbCoh extension regular (hne.mono included)
        (invariantCartierDivisor extension (hne.mono included).coe_sort regular
          (subfanBoundaryTwist fan extension b a)) ell positive) :
    letI := toricScheme_isIntegral fan hne
    toricPowerGeneratesDbCoh fan (subfan_isRegular fan extension included regular) hne
      (invariantCartierDivisor fan hne.coe_sort
        (subfan_isRegular fan extension included regular) b) ell positive := by
  letI := toricScheme_isIntegral fan hne
  letI := toricScheme_isIntegral extension (hne.mono included)
  exact subfan_power_generates_of_restriction fan extension included hne regular rayFull _ _
    (subfanBoundaryCartierRestrictionIso fan extension included regular hne.coe_sort b a)
    ell positive generates

end ToricPower

end
