module

public import ToricPower.SchemeInternalDual
public import ToricPower.DiagonalGlobalRestriction
public import ToricPower.SchemeRestrictionTensor

/-!
# The actual internal dual of the global diagonal complex

Each original Cartier exterior product is dualizable. The finite sums
are dualizable by the actual finite biproduct pairing. This gives the
canonical pullback comparison for the whole internal-dual complex and
identifies it with the internal dual of the proved local free matrix.

The definition here is actual sheaf internal Hom into the structure
sheaf. Its exactness is a separate consequence of the explicit affine
dual calculation, not an exactness premise for the dual functor.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TauCeti.Toric ToricPower.IntegralArrangement
open scoped Classical

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {latticeMap : N →+ V}
  (fan : Fan latticeMap) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "Y" => toricDiagonalProduct fan
local notation "L" => diagonalProductSheaf fan nonempty regular basis rays
local notation "G" => diagonalGlobalSheafComplex fan nonempty regular basis rays

instance diagonalLeftSheaf_isInvertible {d : ℕ} (c : NormalizedCell A d) :
    TauCeti.SheafOfModules.IsInvertible
      (R := fan.algebraicRealization.ringCatSheaf)
      (diagonalLeftSheaf fan nonempty regular basis rays c) := by
  letI := toricSchemeIntegral fan nonempty
  exact (invariantCartierDivisor fan nonempty regular
    (diagonalLeftCoefficients fan basis rays c)).isInvertible_sheaf

instance diagonalRightSheaf_isInvertible {d : ℕ} (c : NormalizedCell A d) :
    TauCeti.SheafOfModules.IsInvertible
      (R := fan.algebraicRealization.ringCatSheaf)
      (diagonalRightSheaf fan nonempty regular basis rays c) := by
  letI := toricSchemeIntegral fan nonempty
  exact (invariantCartierDivisor fan nonempty regular
    (diagonalRightCoefficients fan basis rays c)).isInvertible_sheaf

instance diagonalLeftSheaf_hasLeftDual {d : ℕ} (c : NormalizedCell A d) :
    HasLeftDual (diagonalLeftSheaf fan nonempty regular basis rays c) :=
  schemeFiniteLocallyFreeHasLeftDual _

instance diagonalRightSheaf_hasLeftDual {d : ℕ} (c : NormalizedCell A d) :
    HasLeftDual (diagonalRightSheaf fan nonempty regular basis rays c) :=
  schemeFiniteLocallyFreeHasLeftDual _

instance diagonalProductSheaf_hasLeftDual {d : ℕ} (c : NormalizedCell A d) :
    HasLeftDual (L c) := by
  letI : HasLeftDual ((Scheme.Modules.pullback (toricDiagonalFirst fan)).obj
      (diagonalLeftSheaf fan nonempty regular basis rays c)) :=
    schemeFiniteLocallyFreeHasLeftDual _
  letI : HasLeftDual ((Scheme.Modules.pullback (toricDiagonalSecond fan)).obj
      (diagonalRightSheaf fan nonempty regular basis rays c)) :=
    schemeFiniteLocallyFreeHasLeftDual _
  change HasLeftDual
    (((Scheme.Modules.pullback (toricDiagonalFirst fan)).obj
      (diagonalLeftSheaf fan nonempty regular basis rays c)) ⊗
      ((Scheme.Modules.pullback (toricDiagonalSecond fan)).obj
        (diagonalRightSheaf fan nonempty regular basis rays c)))
  exact hasLeftDualTensor

local instance diagonalDualCellsFintype (q : ℕ) : Fintype (NormalizedCell A q) :=
  Fintype.ofFinite _

instance diagonalGlobalSheafTerm_hasLeftDual (q : ℕ) :
    HasLeftDual (diagonalGlobalSheafTerm fan nonempty regular basis rays q) := by
  letI : HasFiniteBiproducts (Y).Modules := HasFiniteBiproducts.of_hasFiniteProducts
  change HasLeftDual (⨁ (fun c : NormalizedCell A q => L c))
  exact
    { leftDual := ⨁ (fun c : NormalizedCell A q => ᘁ(L c))
      exact := inferInstance }

/-- The actual sheaf internal dual, including every original incidence
map, of the finite global diagonal complex. -/
def diagonalGlobalInternalDualComplex : CochainComplex (Y).Modules ℕ :=
  internalDualComplex (Y).Modules G

variable (σ τ : fan.cones)

local notation "R" => DiagonalChartRing ℂ A (fanConeRaySet fan rays σ) (fanConeRaySet fan rays τ)
local notation "U" => Spec (CommRingCat.of R)
local notation "P" => Scheme.Modules.pullback (diagonalProductChartι fan basis rays σ τ)

/-- Pulling back the genuine global internal dual gives exactly the
internal dual of the independently checked affine free complex. -/
def diagonalGlobalInternalDualChartIso :
    ((P).mapHomologicalComplex (.up ℕ)).obj
        (diagonalGlobalInternalDualComplex fan nonempty regular basis rays) ≅
      internalDualComplex (U).Modules
        (toricDiagonalFramedSheafComplex fan regular basis rays σ τ) := by
  letI (q : ℕ) : HasLeftDual ((G).X q) :=
    diagonalGlobalSheafTerm_hasLeftDual fan nonempty regular basis rays q
  letI : (P).Monoidal := Functor.Monoidal.ofOplaxMonoidal P
  exact internalDualComplexMapIso P G ≪≫
    internalDualComplexIso (U).Modules
      (diagonalGlobalComplexChartIso fan nonempty regular basis rays σ τ).symm

end ToricPower
