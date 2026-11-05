module

public import PaperVerification.FermionPairedWeightCorrespondence
public import PaperVerification.FermionPairedExteriorPieces

/-!
# Full source assembly of the paired Theorem 1.1

The basis uses the original paper index and literal ordered monomials. The
rank data are calculated from all admissible boxes; each exterior degree is
an independently defined homogeneous image of the actual quotient. The
associated-graded algebra is built from actual filtered products, and the
homogenized family has the stated two algebra fibers.

-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion

open Exterior

open MvPolynomial
open scoped BigOperators TensorProduct

variable {R : Type*} [CommRing R] {n : ℕ}

local instance FermionTheoremOneOne_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective

/-- All clauses of paired Theorem 1.1, with ranks expressed by the actual
finite bases so that even the zero coefficient ring is retained. Intrinsic
`finrank` formulas over a nonzero ring are recorded immediately below. -/
theorem theorem_1_1 (d : PairedData (K := R) (n := n)) :
    PairedBasisClaim d ∧
    Fintype.card (PairedIndex d)=2^n*(∏ i,d.r i)*d.s.ascFactorial n ∧
    (∀ j,Nonempty (Module.Basis (PairedExteriorIndex d j) R (pairedExteriorPiece d j)) ∧
      Fintype.card (PairedExteriorIndex d j)=
        (Polynomial.C ((∏ i,d.r i)*d.s.ascFactorial n)*(1+Polynomial.X)^n : Polynomial ℕ).coeff j) ∧
    (∃ e : PairedAssociatedGraded d ≃ₐ[R]
      PairedQuotient d.beta (fun i ↦ X i^d.r i) (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i),
      ∀ k,LinearMap.range (e.toLinearMap.comp
        (DirectSum.lof R ℕ (FilteredAlgebra.GradedPiece (pairedQuotientFiltration d)) k)) =
        pairedPowerWeightedPiece d k) ∧
    PairedBasisClaim (pairedHomogenizedData d) ∧
    (Module.Finite (Polynomial R) (PairedHomogenizedQuotient d) ∧
      Module.Free (Polynomial R) (PairedHomogenizedQuotient d)) ∧
    Module.Flat (Polynomial R) (PairedHomogenizedQuotient d) ∧
    (letI : Algebra (Polynomial R) R := (Polynomial.evalRingHom (0 : R)).toAlgebra;
      Nonempty (R ⊗[Polynomial R] PairedHomogenizedQuotient d ≃ₐ[R]
        PairedQuotient d.beta (fun i ↦ X i^d.r i) (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i))) ∧
    (letI : Algebra (Polynomial R) R := (Polynomial.evalRingHom (1 : R)).toAlgebra;
      Nonempty (R ⊗[Polynomial R] PairedHomogenizedQuotient d ≃ₐ[R]
        PairedQuotient d.beta d.phi d.a d.b)) := by
  refine ⟨paired_basis_claim d,card_pairedIndex d,?_,⟨pairedAssociatedGradedEquiv d,pairedAssociatedGradedEquiv_range d⟩,
    paired_basis_claim (pairedHomogenizedData d),pairedHomogenized_finite_free d,
    pairedHomogenized_flat d,⟨pairedHomogenized_fiber_zero d⟩,⟨pairedHomogenized_fiber_one d⟩⟩
  intro j
  exact ⟨⟨pairedExteriorPieceBasis d j⟩,paired_exterior_basis_card d j⟩

/-- The printed intrinsic rank and every coefficient of its exterior Hilbert
polynomial over an arbitrary nonzero coefficient ring. -/
theorem theorem_1_1_rank [Nontrivial R] (d : PairedData (K := R) (n := n)) :
    Module.finrank R (PairedQuotient d.beta d.phi d.a d.b)=
      2^n*(∏ i,d.r i)*d.s.ascFactorial n ∧
    ∀ j,Module.finrank R (pairedExteriorPiece d j)=
      (Polynomial.C ((∏ i,d.r i)*d.s.ascFactorial n)*(1+Polynomial.X)^n : Polynomial ℕ).coeff j :=
  ⟨paired_finrank d,paired_exterior_hilbert_coefficient d⟩

end PaperVerification.Fermion
