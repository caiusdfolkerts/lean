module

public import PaperVerification.FermionStrictAssociatedGraded
public import PaperVerification.FermionStrictExteriorPieces

/-!
# Full source assembly of strict Theorem 1.2

The basis retains the original integer arrival heights, exponent bounds,
and ordered theta/xi monomials over every original commutative ring. Exact
index enumeration gives the rank and actual exterior-degree bases. The
associated graded uses the independent zero-exterior-weight filtration and
the canonical highest-form algebra comparison, with explicit grading.

-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion

open Exterior

open MvPolynomial
open scoped BigOperators DirectSum

variable {R : Type*} [CommRing R] {n : ℕ}

local instance FermionTheoremOneTwo_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective

/-- All clauses of the strict theorem, using explicit finite basis
cardinalities so that the zero coefficient ring is also retained. -/
theorem theorem_1_2 (d : StrictData (K := R) (n := n)) :
    StrictBasisClaim d ∧
    Fintype.card (StrictIndex d)=2^(n-1)*(∏ i,d.r i)*n.factorial ∧
    (∀ j,Nonempty (Module.Basis (StrictExteriorIndex d j) R (strictExteriorPiece d j)) ∧
      Fintype.card (StrictExteriorIndex d j)=
        (Polynomial.C ((∏ i,d.r i)*n.factorial)*(1+Polynomial.X)^(n-1) : Polynomial ℕ).coeff j) ∧
    (∃ e : StrictAssociatedGraded d ≃ₐ[R] StrictQuotient d.beta (fun i ↦ X i^d.r i),
      ∀ k,LinearMap.range (e.toLinearMap.comp
        (DirectSum.lof R ℕ (FilteredAlgebra.GradedPiece (strictQuotientFiltration d)) k))=
          strictPowerWeightedPiece d k) := by
  refine ⟨strict_basis_claim d,card_strictIndex d,?_,
    ⟨strictAssociatedGradedEquiv d,strictAssociatedGradedEquiv_range d⟩⟩
  intro j
  exact ⟨⟨strictExteriorPieceBasis d j⟩,strict_exterior_basis_card d j⟩

/-- The literal intrinsic rank formulas over every nonzero coefficient
ring, with no field or reducedness hypothesis. -/
theorem theorem_1_2_rank [Nontrivial R] (d : StrictData (K := R) (n := n)) :
    Module.finrank R (StrictQuotient d.beta d.phi)=2^(n-1)*(∏ i,d.r i)*n.factorial ∧
    ∀ j,Module.finrank R (strictExteriorPiece d j)=
      (Polynomial.C ((∏ i,d.r i)*n.factorial)*(1+Polynomial.X)^(n-1) : Polynomial ℕ).coeff j :=
  ⟨strict_finrank d,strict_exterior_hilbert_coefficient d⟩

end PaperVerification.Fermion
