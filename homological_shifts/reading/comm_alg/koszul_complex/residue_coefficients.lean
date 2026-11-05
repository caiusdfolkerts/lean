import CommAlg.KoszulComplex.FiniteVariables
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # The residue quotient is the coefficient field with its intended polynomial action -/

noncomputable section
namespace CommAlg.Koszul
open CategoryTheory MvPolynomial
universe u
variable {V k : Type u} [CommRing k]

/-- The coefficient ring, with polynomial action by evaluation at zero. -/
def residueCoefficientModule : ModuleCat.{u} (MvPolynomial V k) :=
  (ModuleCat.restrictScalars (constantCoeff : MvPolynomial V k →+* k)).obj (ModuleCat.of k k)

/-- The quotient by all variables agrees as a polynomial module with the coefficient ring. -/
def residueCoefficientEquiv :
    FiniteResidue V k ≃ₗ[MvPolynomial V k] residueCoefficientModule (V := V) (k := k) where
  toFun := (residueRingEquiv (V := V) (k := k))
  invFun := (residueRingEquiv (V := V) (k := k)).symm
  left_inv := (residueRingEquiv (V := V) (k := k)).left_inv
  right_inv := (residueRingEquiv (V := V) (k := k)).right_inv
  map_add' := (residueRingEquiv (V := V) (k := k)).map_add
  map_smul' f q := by
    change (residueRingEquiv (V := V) (k := k)) (f • q) = constantCoeff f * (residueRingEquiv (V := V) (k := k)) q
    refine Quotient.inductionOn' q ?_
    intro p
    change (residueRingEquiv (V := V) (k := k))
      (Ideal.Quotient.mk (idealOfVars V k) (f * p)) =
      constantCoeff f * (residueRingEquiv (V := V) (k := k))
        (Ideal.Quotient.mk (idealOfVars V k) p)
    simp only [residueRingEquiv_mk, map_mul]

/-- Canonical polynomial-module isomorphism to the actual coefficient ring. -/
def residueCoefficientIso :
    ModuleCat.of (MvPolynomial V k) (FiniteResidue V k) ≅
      residueCoefficientModule (V := V) (k := k) :=
  residueCoefficientEquiv.toModuleIso

variable [Fintype V] [LinearOrder V]

/-- The derived Tor groups used throughout are isomorphic to derived Tor with the coefficient ring
itself, carrying precisely its standard evaluation-at-zero polynomial action. -/
def finitePolynomialTorCoefficientIso (i : ℕ) (M : ModuleCat.{u} (MvPolynomial V k)) :
    finitePolynomialTor i M ≅
      ((Tor' (ModuleCat (MvPolynomial V k)) i).obj
        (residueCoefficientModule (V := V) (k := k))).obj M :=
  ((Functor.flip (Tor' (ModuleCat (MvPolynomial V k)) i)).obj M).mapIso residueCoefficientIso

end CommAlg.Koszul
