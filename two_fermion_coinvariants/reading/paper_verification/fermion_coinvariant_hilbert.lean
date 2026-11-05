module

public import PaperVerification.FermionCoinvariantBases
public import PaperVerification.FermionCoinvariantComplex
public import PaperVerification.FermionPairedExteriorPieces
public import PaperVerification.FermionStrictExteriorPieces
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Exterior Hilbert polynomials of the original invariant-theoretic quotients

The source degree space is defined from the original ambient exterior degree,
then mapped to the quotient by its independently defined positive-invariant
ideal. The proved equality with the moment ideal induces the identity on every
ambient representative, and hence an equivalence of these actual degree spaces.
The numerical formulas then follow from the verified moment bases. No degree
space is defined by transporting the desired answer.

-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.Fermion.Coinvariants

open Exterior

variable {R : Type*} [CommRing R] {n r a : ℕ}

local instance coinvariantHilbertOrder : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective

/-- Image of a fixed original ambient submodule under two literally equal
two-sided quotient ideals. Its map is induced by the identity on representatives. -/
def quotientImageEquivOfIdealEq {I J : TwoSidedIdeal (SuperRing R n)}
    (h : I=J) (U : Submodule R (SuperRing R n)) :
    U.map (I.ringCon.mkₐ R).toLinearMap ≃ₗ[R]
      U.map (J.ringCon.mkₐ R).toLinearMap :=
  (quotientEquivOfIdealEq h).toLinearEquiv.ofSubmodules
    (U.map (I.ringCon.mkₐ R).toLinearMap)
    (U.map (J.ringCon.mkₐ R).toLinearMap) (by
      rw [←Submodule.map_comp]
      congr 1)

/-- Total exterior degree in the genuine invariant-generated quotient. -/
def coinvariantExteriorPiece (a b j : ℕ) :
    Submodule R (CoinvariantAlgebra (R := R) (n := n) (r := r) a b) :=
  (BasisFiltered.homogeneousPiece (superMonomialBasis (K := R))
    (fun z ↦ z.2.card) j).map
      ((positiveInvariantIdeal (R := R) (n := n) (r := r) a b).ringCon.mkₐ R).toLinearMap

section Fields

variable {F : Type*} [Field F]

def oppositeExteriorPieceEquiv (hn : 0<n) (hr : 0<r) (ha : 0<a) (har : a<r)
    (hfac : IsUnit (n.factorial : F)) (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) r)
    (j : ℕ) :
    coinvariantExteriorPiece (R := F) (n := n) (r := r) a (r-a) j ≃ₗ[F]
      pairedExteriorPiece (oppositePowerData hn hr har.le hfac) j :=
  quotientImageEquivOfIdealEq (positiveInvariantIdeal_eq_paired hr ha har hfac ζ hζ)
    (BasisFiltered.homogeneousPiece (superMonomialBasis (K := F)) (fun z ↦ z.2.card) j)

def oppositeExteriorPieceBasis (hn : 0<n) (hr : 0<r) (ha : 0<a) (har : a<r)
    (hfac : IsUnit (n.factorial : F)) (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) r)
    (j : ℕ) :
    Module.Basis (PairedExteriorIndex (oppositePowerData hn hr har.le hfac) j) F
      (coinvariantExteriorPiece (R := F) (n := n) (r := r) a (r-a) j) :=
  (pairedExteriorPieceBasis (oppositePowerData hn hr har.le hfac) j).map
    (oppositeExteriorPieceEquiv hn hr ha har hfac ζ hζ j).symm

/-- Every coefficient of the printed total-exterior polynomial, in the
original wreath-product quotient and over its full stated field range. -/
theorem oppositeCoinvariant_exterior_hilbert_coefficient
    (hn : 0<n) (hr : 0<r) (ha : 0<a) (har : a<r)
    (hfac : IsUnit (n.factorial : F)) (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) r)
    (j : ℕ) :
    Module.finrank F (coinvariantExteriorPiece (R := F) (n := n) (r := r) a (r-a) j)=
      (Polynomial.C (r^n*n.factorial)*(1+Polynomial.X)^n : Polynomial ℕ).coeff j := by
  rw [(oppositeExteriorPieceEquiv hn hr ha har hfac ζ hζ j).finrank_eq,
    paired_exterior_hilbert_coefficient]
  simp only [oppositePowerData,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    Nat.one_ascFactorial]

def trivialColorExteriorPieceEquiv (hn : 0<n) (hr : 0<r)
    (hfac : IsUnit (n.factorial : F)) (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) r)
    (j : ℕ) :
    coinvariantExteriorPiece (R := F) (n := n) (r := r) 0 0 j ≃ₗ[F]
      strictExteriorPiece (trivialColorPowerData hn hr hfac) j :=
  quotientImageEquivOfIdealEq (positiveInvariantIdeal_eq_strict hr hfac ζ hζ)
    (BasisFiltered.homogeneousPiece (superMonomialBasis (K := F)) (fun z ↦ z.2.card) j)

theorem trivialColorCoinvariant_exterior_hilbert_coefficient
    (hn : 0<n) (hr : 0<r) (hfac : IsUnit (n.factorial : F))
    (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) r) (j : ℕ) :
    Module.finrank F (coinvariantExteriorPiece (R := F) (n := n) (r := r) 0 0 j)=
      (Polynomial.C (r^n*n.factorial)*(1+Polynomial.X)^(n-1) : Polynomial ℕ).coeff j := by
  rw [(trivialColorExteriorPieceEquiv hn hr hfac ζ hζ j).finrank_eq,
    strict_exterior_hilbert_coefficient]
  simp only [trivialColorPowerData,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

end Fields

/-- The type-A comparison retains every coefficient ring with n! invertible. -/
def typeAExteriorPieceEquiv (hn : 0<n) (hfac : IsUnit (n.factorial : R)) (j : ℕ) :
    coinvariantExteriorPiece (R := R) (n := n) (r := 1) 0 0 j ≃ₗ[R]
      strictExteriorPiece (trivialColorPowerData hn (by decide : 0<1) hfac) j :=
  quotientImageEquivOfIdealEq
    ((positiveInvariantIdeal_eq_blockIdeal_typeA hfac).trans
      (blockIdeal_eq_strictIdeal (by decide : 0<1)))
    (BasisFiltered.homogeneousPiece (superMonomialBasis (K := R)) (fun z ↦ z.2.card) j)

def typeAExteriorPieceBasis (hn : 0<n) (hfac : IsUnit (n.factorial : R)) (j : ℕ) :
    Module.Basis (StrictExteriorIndex (trivialColorPowerData hn (by decide : 0<1) hfac) j) R
      (coinvariantExteriorPiece (R := R) (n := n) (r := 1) 0 0 j) :=
  (strictExteriorPieceBasis (trivialColorPowerData hn (by decide : 0<1) hfac) j).map
    (typeAExteriorPieceEquiv hn hfac j).symm

theorem typeACoinvariant_exterior_basis_card
    (hn : 0<n) (hfac : IsUnit (n.factorial : R)) (j : ℕ) :
    Fintype.card (StrictExteriorIndex (trivialColorPowerData hn (by decide : 0<1) hfac) j)=
      (Polynomial.C n.factorial*(1+Polynomial.X)^(n-1) : Polynomial ℕ).coeff j := by
  rw [strict_exterior_basis_card]
  simp only [trivialColorPowerData,Finset.prod_const_one,one_mul]

theorem typeACoinvariant_exterior_hilbert_coefficient [Nontrivial R]
    (hn : 0<n) (hfac : IsUnit (n.factorial : R)) (j : ℕ) :
    Module.finrank R (coinvariantExteriorPiece (R := R) (n := n) (r := 1) 0 0 j)=
      (Polynomial.C n.factorial*(1+Polynomial.X)^(n-1) : Polynomial ℕ).coeff j := by
  rw [Module.finrank_eq_card_basis (typeAExteriorPieceBasis hn hfac j)]
  exact typeACoinvariant_exterior_basis_card hn hfac j

/-- The complex opposite-character formula with every group-action condition
discharged from the printed integer ranges. -/
theorem complex_opposite_exterior_hilbert_coefficient
    (hn : 0<n) (hr : 2≤r) (ha : 1≤a) (har : a≤r-1) (j : ℕ) :
    Module.finrank ℂ (coinvariantExteriorPiece (R := ℂ) (n := n) (r := r) a (r-a) j)=
      (Polynomial.C (r^n*n.factorial)*(1+Polynomial.X)^n : Polynomial ℕ).coeff j := by
  have hr' : 0<r := by omega
  obtain ⟨ζ,hζ⟩ := complex_primitive_unit hr'
  exact oppositeCoinvariant_exterior_hilbert_coefficient hn hr' (by omega) (by omega)
    (complex_factorial_unit n) ζ hζ j

theorem complex_trivialColor_exterior_hilbert_coefficient
    (hn : 0<n) (hr : 0<r) (j : ℕ) :
    Module.finrank ℂ (coinvariantExteriorPiece (R := ℂ) (n := n) (r := r) 0 0 j)=
      (Polynomial.C (r^n*n.factorial)*(1+Polynomial.X)^(n-1) : Polynomial ℕ).coeff j := by
  obtain ⟨ζ,hζ⟩ := complex_primitive_unit hr
  exact trivialColorCoinvariant_exterior_hilbert_coefficient hn hr
    (complex_factorial_unit n) ζ hζ j

end PaperVerification.Fermion.Coinvariants
