module

public import ToricPower.ExternalCartierInternalDual
public import ToricPower.ToricCartierMonomialDuality
public import ToricPower.DiagonalGlobalComplex
public import ToricPower.InternalDualBiproduct
public import ToricPower.SchemeInternalDual

/-!
# Actual exterior labels and character maps of the dual diagonal

Each internal-dual term is identified with the finite sum of the actual
exterior inverse Cartier labels. A regular character pair `(a,-a)` is
transposed to that same pair on the inverse labels, with its source and
target reversed. These identities retain the original rational maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TauCeti.Toric TauCeti.AlgebraicGeometry.Scheme
open ToricPower.IntegralArrangement
open scoped Classical

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {latticeMap : N →+ V}
  (fan : Fan latticeMap) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "Y" => toricDiagonalProduct fan

/-- The actual same-character inverse map preserves rational evaluation. -/
theorem toricCartierMonomialMap_pairing (b c : fan.Ray → ℤ) (m : N →+ ℤ)
    (positive : ∀ ρ, 0 ≤ c ρ - b ρ + m (fanRayPrimitiveGenerator fan ρ)) :
    letI := toricSchemeIntegral fan nonempty
    (invariantCartierDivisor fan nonempty regular b).sheaf ◁
        toricCartierMonomialDualMap fan nonempty regular b c m positive ≫
      (cartierTensorNegIsoUnit (invariantCartierDivisor fan nonempty regular b)).hom =
    toricCartierMonomialMap fan nonempty regular b c m positive ▷
        (-(invariantCartierDivisor fan nonempty regular c)).sheaf ≫
      (cartierTensorNegIsoUnit (invariantCartierDivisor fan nonempty regular c)).hom := by
  letI := toricSchemeIntegral fan nonempty
  exact cartierPairing_of_rationalMultiplier _ _
    (rationalCharacterUnit fan nonempty m : fan.algebraicRealization.functionField)
    (toricCartierMonomialMap_value fan nonempty regular b c m positive)
    (toricCartierMonomialDualMap_value fan nonempty regular b c m positive)

/-- The actual inverse exterior label at a normalized cell. -/
def diagonalInverseProductSheaf {d : ℕ} (c : NormalizedCell A d) : (Y).Modules := by
  letI := toricSchemeIntegral fan nonempty
  exact externalCartierSheaf (toricDiagonalFirst fan) (toricDiagonalSecond fan)
    (-(invariantCartierDivisor fan nonempty regular
      (diagonalLeftCoefficients fan basis rays c)))
    (-(invariantCartierDivisor fan nonempty regular
      (diagonalRightCoefficients fan basis rays c)))

/-- The specified dual isomorphism comes from actual rational evaluation. -/
def diagonalProductInternalDualIso {d : ℕ} (c : NormalizedCell A d) :
    diagonalInverseProductSheaf fan nonempty regular basis rays c ≅
      (internalDual (Y).Modules).obj
        (op (diagonalProductSheaf fan nonempty regular basis rays c)) := by
  letI := toricSchemeIntegral fan nonempty
  exact externalCartierInternalDualIso (toricDiagonalFirst fan) (toricDiagonalSecond fan)
    (invariantCartierDivisor fan nonempty regular
      (diagonalLeftCoefficients fan basis rays c))
    (invariantCartierDivisor fan nonempty regular
      (diagonalRightCoefficients fan basis rays c))

/-- The literal reverse character pair on the actual inverse factors. -/
def diagonalInverseProductCharacterMap {e d : ℕ}
    (j : NormalizedCell A e) (i : NormalizedCell A d)
    (a : Fin n → ℤ) (positive : DiagonalEntryRegular fan basis rays j i a) :
    diagonalInverseProductSheaf fan nonempty regular basis rays i ⟶
      diagonalInverseProductSheaf fan nonempty regular basis rays j := by
  letI := toricSchemeIntegral fan nonempty
  exact externalCartierMap (toricDiagonalFirst fan) (toricDiagonalSecond fan)
    (toricCartierMonomialDualMap fan nonempty regular
      (diagonalLeftCoefficients fan basis rays j)
      (diagonalLeftCoefficients fan basis rays i) (basis.equivFun.symm a) positive.1)
    (toricCartierMonomialDualMap fan nonempty regular
      (diagonalRightCoefficients fan basis rays j)
      (diagonalRightCoefficients fan basis rays i) (-(basis.equivFun.symm a))
      (by intro ρ; simpa only [AddMonoidHom.neg_apply, sub_eq_add_neg] using positive.2 ρ))

/-- The actual internal dual of the original character map is exactly
the actual same-character map on inverse labels. -/
theorem diagonalProductInternalDualIso_character {e d : ℕ}
    (j : NormalizedCell A e) (i : NormalizedCell A d)
    (a : Fin n → ℤ) (positive : DiagonalEntryRegular fan basis rays j i a) :
    (diagonalProductInternalDualIso fan nonempty regular basis rays i).hom ≫
        (internalDual (Y).Modules).map
          (diagonalProductCharacterMap fan nonempty regular basis rays j i a positive).op =
      diagonalInverseProductCharacterMap fan nonempty regular basis rays j i a positive ≫
        (diagonalProductInternalDualIso fan nonempty regular basis rays j).hom := by
  letI := toricSchemeIntegral fan nonempty
  apply externalCartierInternalDualIso_naturality
  · exact toricCartierMonomialMap_pairing fan nonempty regular _ _ _ positive.1
  · exact toricCartierMonomialMap_pairing fan nonempty regular _ _ _
      (by intro ρ; simpa only [AddMonoidHom.neg_apply, sub_eq_add_neg] using positive.2 ρ)

local instance : HasFiniteBiproducts (Y).Modules := HasFiniteBiproducts.of_hasFiniteProducts
local instance (q : ℕ) : Fintype (NormalizedCell A q) := Fintype.ofFinite _

/-- The finite sum of actual exterior inverse labels in one degree. -/
def diagonalExteriorDualTerm (q : ℕ) : (Y).Modules :=
  ⨁ (fun c : NormalizedCell A q =>
    diagonalInverseProductSheaf fan nonempty regular basis rays c)

/-- The full term comparison uses the original inclusions and
projections of the finite biproduct. -/
def diagonalExteriorDualTermIso (q : ℕ) :
    diagonalExteriorDualTerm fan nonempty regular basis rays q ≅
      (internalDual (Y).Modules).obj
        (op (diagonalGlobalSheafTerm fan nonempty regular basis rays q)) :=
  biproduct.mapIso (diagonalProductInternalDualIso fan nonempty regular basis rays) ≪≫
    (internalDualBiproductIso
      (fun c : NormalizedCell A q => diagonalProductSheaf fan nonempty regular basis rays c)).symm

end ToricPower

end
