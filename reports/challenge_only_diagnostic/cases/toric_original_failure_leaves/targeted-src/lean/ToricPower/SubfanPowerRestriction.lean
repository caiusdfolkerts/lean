module

public import ToricPower.SubfanOpenImmersion
public import ToricPower.PowerSheafCore

/-!
# Power-map direct images commute with actual subfan restriction

The identity lattice map commutes with multiplication by every integer.
For positive exponents the inverse image of the subfan open is itself.
Ordinary open base change consequently identifies the actual direct
image sheaves. No derived base-change assertion is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TauCeti.Toric

namespace ToricPower

universe u

variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (fan extension : Fan i) (included : fan.cones ⊆ extension.cones)

/-- The genuine subfan morphism commutes with every power map. -/
theorem subfanSchemeMap_comp_power (ell : ℕ) :
    subfanSchemeMap fan extension included ≫ toricPowerMap extension ell =
      toricPowerMap fan ell ≫ subfanSchemeMap fan extension included := by
  change (subfanFanHom fan extension included).algebraicMap ≫
      (powerFanHom extension ell).algebraicMap =
    (powerFanHom fan ell).algebraicMap ≫
      (subfanFanHom fan extension included).algebraicMap
  rw [← FanHom.algebraicMap_comp,← FanHom.algebraicMap_comp]
  congr 1
  apply FanHom.ext
  ext x
  simp only [FanHom.comp_latticeMap,powerFanHom_latticeMap,subfanFanHom,
    AddMonoidHom.comp_apply,AddMonoidHom.id_apply]

/-- The inverse image of the actual subfan open is itself. -/
theorem toricPowerMap_preimage_subfan (ell : ℕ) (positive : 0 < ell) :
    letI := subfanSchemeMap_isOpenImmersion fan extension included
    toricPowerMap extension ell ⁻¹ᵁ (subfanSchemeMap fan extension included).opensRange =
      (subfanSchemeMap fan extension included).opensRange := by
  letI := subfanSchemeMap_isOpenImmersion fan extension included
  apply TopologicalSpace.Opens.ext
  change (toricPowerMap extension ell) ⁻¹' Set.range (subfanSchemeMap fan extension included) =
    Set.range (subfanSchemeMap fan extension included)
  rw [subfanSchemeMap_range,Set.preimage_iUnion]
  congr 1
  funext σ
  exact toricPowerMap_preimage_chart extension ell positive ⟨σ.val,included σ.property⟩

/-- Ordinary direct image and actual open restriction agree for all
module sheaves, with the same positive power on both toric varieties. -/
def subfanPowerPushforwardRestrictionIso (ell : ℕ) (positive : 0 < ell)
    (M : extension.algebraicRealization.Modules) :
    letI := subfanSchemeMap_isOpenImmersion fan extension included
    ((Scheme.Modules.pushforward (toricPowerMap extension ell)).obj M).restrict
        (subfanSchemeMap fan extension included) ≅
      (Scheme.Modules.pushforward (toricPowerMap fan ell)).obj
        (M.restrict (subfanSchemeMap fan extension included)) := by
  letI := subfanSchemeMap_isOpenImmersion fan extension included
  exact pushforwardRestrictionIso (toricPowerMap extension ell) (toricPowerMap fan ell)
    (subfanSchemeMap fan extension included) (subfanSchemeMap fan extension included)
    (subfanSchemeMap_comp_power fan extension included ell)
    (toricPowerMap_preimage_subfan fan extension included ell positive).le M

end ToricPower

end
