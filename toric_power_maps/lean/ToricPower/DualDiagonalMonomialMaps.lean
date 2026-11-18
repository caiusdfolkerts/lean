module

public import ToricPower.DualDiagonalWeightComparison
public import ToricPower.CellularTranslatedMaps
public import ToricPower.DualDiagonalCompactTranslation

/-!
# Actual monomial multiplication on dual-diagonal weights

The maps below are induced by natural transformations of the original
Cartier character coefficient diagrams. Their full universal-cover
coordinates are literal translation by the negative first character,
with unchanged coefficients. No cohomology map is imposed by definition.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (S T : Set (Fin s))
  (u : Fin n → ℤ) (a : rayCharacterMonoid A S) (b : rayCharacterMonoid A T)

local notation "v" => u + a.val + b.val
local notation "sourceAllowed" => dualDiagonalWeightAllowed A S T u
local notation "targetAllowed" => dualDiagonalWeightAllowed A S T v
local notation "sourceStable" => dualDiagonalWeightAllowed_map A S T u
local notation "targetStable" => dualDiagonalWeightAllowed_map A S T v

/-- The original character-basis map for the two actual dual factors. -/
theorem dualDiagonalWeightMonomial_permitted (c : IncidenceObject A) (w : Fin n → ℤ)
    (hw : sourceAllowed c w) : targetAllowed c (w + a.val) :=
  dualDiagonalMonomialAllowed_multiply A S T u a b c.2 w hw

def dualDiagonalWeightMonomialIndex (q : ℕ) :
    DualDiagonalWeightIndex A S T u q → DualDiagonalWeightIndex A S T v q :=
  translatedCellIndex A sourceAllowed targetAllowed a.val
    (dualDiagonalWeightMonomial_permitted A S T u a b) q

/-- The genuine translated cell map on the complete open strip. -/
def dualDiagonalStripCellMonomialMap (q : ℕ) :
    DualDiagonalStripCell A S T u q → DualDiagonalStripCell A S T v q :=
  openSupportCellTranslation A (-a.val)
    (dualDiagonalStrip_monomial_translation A S T u a b) q

/-- The sign in the literal Laurent character map agrees with the
actual translated universal-cover cell. -/
theorem dualDiagonalWeightMonomialIndex_cell (q : ℕ)
    (i : DualDiagonalWeightIndex A S T u q) :
    dualDiagonalWeightCellEquiv A S T v q (dualDiagonalWeightMonomialIndex A S T u a b q i) =
      dualDiagonalStripCellMonomialMap A S T u a b q
        (dualDiagonalWeightCellEquiv A S T u q i) := by
  apply Subtype.ext
  change translateCell A (-(i.2.val + a.val)) i.1.val =
    translateCell A (-a.val) (translateCell A (-i.2.val) i.1.val)
  rw [translateCell_add]
  congr 1
  abel

variable (k : Type) [Field k]

/-- Multiplication by the actual monomial pair, before taking homology. -/
def dualDiagonalWeightMonomialMap :
    dualDiagonalWeightComplex A S T u k ⟶ dualDiagonalWeightComplex A S T v k :=
  translatedCoefficientComplexMap A sourceAllowed targetAllowed sourceStable targetStable
    a.val (dualDiagonalWeightMonomial_permitted A S T u a b) k

/-- Every original generator has the exact translated generator as its
image, with coefficient unchanged. -/
theorem dualDiagonalWeightMonomialMap_generator (q : ℕ)
    (i : DualDiagonalWeightIndex A S T u q) (r : k) :
    dualDiagonalWeightCoordinates A S T v k q
        ((dualDiagonalWeightMonomialMap A S T u a b k).f q
          ((dualDiagonalWeightCoordinates A S T u k q).symm
            (Finsupp.single (dualDiagonalWeightCellEquiv A S T u q i) r))) =
      Finsupp.single (dualDiagonalStripCellMonomialMap A S T u a b q
        (dualDiagonalWeightCellEquiv A S T u q i)) r := by
  rw [dualDiagonalWeightCoordinates_symm_single]
  change Finsupp.mapDomain (dualDiagonalWeightCellEquiv A S T v q)
      (translatedWeightCellularCoordinates A targetAllowed targetStable k q
        ((translatedCoefficientComplexMap A sourceAllowed targetAllowed sourceStable targetStable
          a.val (dualDiagonalWeightMonomial_permitted A S T u a b) k).f q
          ((translatedWeightCellularCoordinates A sourceAllowed sourceStable k q).symm
            (Finsupp.single i r)))) = _
  rw [translatedCoefficientComplexMap_generator, Finsupp.mapDomain_single]
  exact congrArg (fun c => Finsupp.single c r)
    (dualDiagonalWeightMonomialIndex_cell A S T u a b q i)

/-- The complete actual monomial map in full Laurent coordinates. -/
theorem dualDiagonalWeightMonomialMap_coordinates (q : ℕ)
    (w : (dualDiagonalWeightComplex A S T u k).X q) :
    dualDiagonalWeightCoordinates A S T v k q
        ((dualDiagonalWeightMonomialMap A S T u a b k).f q w) =
      Finsupp.mapDomain (dualDiagonalStripCellMonomialMap A S T u a b q)
        (dualDiagonalWeightCoordinates A S T u k q w) := by
  let actual := (dualDiagonalWeightCoordinates A S T v k q).toLinearMap.comp
    (((dualDiagonalWeightMonomialMap A S T u a b k).f q).hom.comp
      (dualDiagonalWeightCoordinates A S T u k q).symm.toLinearMap)
  have equality : actual = Finsupp.lmapDomain k k
      (dualDiagonalStripCellMonomialMap A S T u a b q) := by
    apply Finsupp.lhom_ext
    intro i r
    obtain ⟨i', rfl⟩ := (dualDiagonalWeightCellEquiv A S T u q).surjective i
    exact (dualDiagonalWeightMonomialMap_generator A S T u a b k q i' r).trans
      Finsupp.mapDomain_single.symm
  have result := DFunLike.congr_fun equality (dualDiagonalWeightCoordinates A S T u k q w)
  simpa only [actual, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, Finsupp.lmapDomain_apply] using result

end ToricPower.IntegralArrangement
