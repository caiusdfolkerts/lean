module

public import ToricPower.RestrictedInversePairingFrame
public import ToricPower.DivisorWeightGlobalFrames
public import ToricPower.ToricMonomialDualityFunctor
public import ToricPower.CechDivisorSections

/-!
# The actual character of the canonical inverse Cartier frame

The original chart frame has the negative local-equation character.
Its canonical inverse, defined by the actual evaluation pairing, has the
opposite character with coefficient exactly one. This calculation does
not assume that independently chosen Cartier equations are additive.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TauCeti.Toric TauCeti.AlgebraicGeometry.Scheme

namespace ToricPower

universe u v
variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  (b : fan.Ray → ℤ) (σ : fan.cones)

local notation "X" => fan.algebraicRealization
local notation "U" => fan.affineToricChart σ
local notation "j" => fan.affineToricChartι σ
local notation "D" => invariantCartierDivisor fan nonempty regular b

instance toricChart_imageTop_nonempty : Nonempty (j ''ᵁ (⊤ : (U).Opens)) := by
  rw [(j).image_top_eq_opensRange]
  exact chartOpen_nonempty fan σ

/-- The actual restricted frame retains the reciprocal character of
its original local Cartier equation, with every open transport retained. -/
theorem toricCartierAffineFrame_rationalValue :
    letI := toricSchemeIntegral fan nonempty
    rationalFunctionsEquiv (j ''ᵁ (⊤ : (U).Opens))
      (Scheme.Modules.Hom.app (D).sheafι (j ''ᵁ (⊤ : (U).Opens))
        (Scheme.Modules.Hom.app
          (toricCartierAffineFrame fan nonempty regular b σ).hom
          ⊤ (1 : Γ(U,⊤)))) =
      ((rationalCharacterUnit fan nonempty (coneDivisorCharacter fan regular b σ))⁻¹ :
        (X).functionField) := by
  letI := toricSchemeIntegral fan nonempty
  letI := chartOpen_nonempty fan σ
  have frame := toricCartierAffineFrame_top fan nonempty regular b σ 1
  simp only [map_one] at frame
  rw [frame]
  change rationalFunctionsEquiv (j ''ᵁ (⊤ : (U).Opens))
    (Scheme.Modules.Hom.app (D).sheafι (j ''ᵁ (⊤ : (U).Opens))
      ((D).sheaf.presheaf.map
        (homOfLE (le_of_eq (j).image_top_eq_opensRange)).op
        (toricCartierFrameSection fan nonempty regular b σ))) = _
  rw [cartierSheaf_rationalValue_restrict, toricCartierFrameSection_value,
    rationalCharacterUnit_neg, Units.val_inv_eq_inv_val]

/-- The specified inverse chart frame, before replacing the inverse
Cartier divisor by its equal negative coefficient divisor. -/
def toricCartierCanonicalInverseAffineFrame :
    letI := toricSchemeIntegral fan nonempty
    𝟙_ (U).Modules ≅ (-(D)).sheaf.restrict j := by
  letI := toricSchemeIntegral fan nonempty
  exact (restrictedCartierInverseFrame j D
    (toricCartierAffineFrame fan nonempty regular b σ)).symm

/-- The inverse frame is the actual positive local-equation monomial;
its scalar is exactly one, as forced by the literal evaluation pairing. -/
theorem toricCartierCanonicalInverseAffineFrame_rationalValue :
    letI := toricSchemeIntegral fan nonempty
    rationalFunctionsEquiv (j ''ᵁ (⊤ : (U).Opens))
      (Scheme.Modules.Hom.app (-(D)).sheafι (j ''ᵁ (⊤ : (U).Opens))
        (Scheme.Modules.Hom.app
          (toricCartierCanonicalInverseAffineFrame fan nonempty regular b σ).hom
          ⊤ (1 : Γ(U,⊤)))) =
      (rationalCharacterUnit fan nonempty (coneDivisorCharacter fan regular b σ) :
        (X).functionField) := by
  letI := toricSchemeIntegral fan nonempty
  exact restrictedCartierInverseFrame_value j D
    (toricCartierAffineFrame fan nonempty regular b σ)
    (rationalCharacterUnit fan nonempty (coneDivisorCharacter fan regular b σ))
    (toricCartierAffineFrame_rationalValue fan nonempty regular b σ)

end ToricPower

end
