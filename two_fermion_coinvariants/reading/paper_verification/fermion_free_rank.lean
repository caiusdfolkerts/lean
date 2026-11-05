module

public import PaperVerification.FermionTheoremOneOne
public import PaperVerification.FermionTheoremOneTwo
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# The displayed free ranks over every coefficient ring

The paper first supplies an explicit finite free basis. Its displayed rank
therefore has an all-ring meaning: an isomorphism with a coordinate module of
the displayed finite size. This remains valid over the zero ring, where the
size of a free basis is not unique. Intrinsic `Module.finrank` formulas require
the nontrivial-ring hypothesis already separated in the principal files.

These equivalences reindex the original proved bases; they do not define or
replace any quotient, graded piece, or module action.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion

open scoped BigOperators

variable {R : Type*} [CommRing R] {n : ℕ}

/-- A finite free basis and a finite coordinate-module equivalence are
equivalent notions over every ring, including the zero ring. -/
theorem finite_basis_iff_coordinate_equiv {M : Type*} [AddCommGroup M]
    [Module R M] (N : ℕ) :
    Nonempty (Module.Basis (Fin N) R M) ↔
      Nonempty (M ≃ₗ[R] (Fin N → R)) := by
  constructor
  · rintro ⟨b⟩
    exact ⟨b.equivFun⟩
  · rintro ⟨e⟩
    exact ⟨Module.Basis.ofEquivFun e⟩

/-- The actual paired quotient is free of the displayed finite size over
every original coefficient ring. -/
def pairedFreeRankEquiv (d : PairedData (K := R) (n := n)) :
    PairedQuotient d.beta d.phi d.a d.b ≃ₗ[R]
      (Fin (2^n * (∏ i, d.r i) * d.s.ascFactorial n) → R) :=
  ((pairedPaperBasis d).reindex (Fintype.equivFinOfCardEq (card_pairedIndex d))).equivFun

/-- Every actual exterior-degree piece has the displayed finite free size. -/
def pairedExteriorFreeRankEquiv (d : PairedData (K := R) (n := n)) (j : ℕ) :
    pairedExteriorPiece d j ≃ₗ[R]
      (Fin ((Polynomial.C ((∏ i, d.r i) * d.s.ascFactorial n) *
        (1 + Polynomial.X)^n : Polynomial ℕ).coeff j) → R) :=
  ((pairedExteriorPieceBasis d j).reindex
    (Fintype.equivFinOfCardEq (paired_exterior_basis_card d j))).equivFun

/-- The paired rank and every exterior Hilbert coefficient in their precise
all-ring free-module meaning; no `Nontrivial R` hypothesis is imposed. -/
theorem theorem_1_1_free_rank (d : PairedData (K := R) (n := n)) :
    Nonempty (PairedQuotient d.beta d.phi d.a d.b ≃ₗ[R]
      (Fin (2^n * (∏ i, d.r i) * d.s.ascFactorial n) → R)) ∧
    ∀ j, Nonempty (pairedExteriorPiece d j ≃ₗ[R]
      (Fin ((Polynomial.C ((∏ i, d.r i) * d.s.ascFactorial n) *
        (1 + Polynomial.X)^n : Polynomial ℕ).coeff j) → R)) :=
  ⟨⟨pairedFreeRankEquiv d⟩, fun j ↦ ⟨pairedExteriorFreeRankEquiv d j⟩⟩

/-- The actual strict quotient is free of the displayed finite size over
every original coefficient ring. -/
def strictFreeRankEquiv (d : StrictData (K := R) (n := n)) :
    StrictQuotient d.beta d.phi ≃ₗ[R]
      (Fin (2^(n-1) * (∏ i, d.r i) * n.factorial) → R) :=
  ((strictPaperBasis d).reindex (Fintype.equivFinOfCardEq (card_strictIndex d))).equivFun

/-- Every actual strict exterior-degree piece has its stated free size. -/
def strictExteriorFreeRankEquiv (d : StrictData (K := R) (n := n)) (j : ℕ) :
    strictExteriorPiece d j ≃ₗ[R]
      (Fin ((Polynomial.C ((∏ i, d.r i) * n.factorial) *
        (1 + Polynomial.X)^(n-1) : Polynomial ℕ).coeff j) → R) :=
  ((strictExteriorPieceBasis d j).reindex
    (Fintype.equivFinOfCardEq (strict_exterior_basis_card d j))).equivFun

/-- The strict rank and every exterior Hilbert coefficient in their precise
all-ring free-module meaning. -/
theorem theorem_1_2_free_rank (d : StrictData (K := R) (n := n)) :
    Nonempty (StrictQuotient d.beta d.phi ≃ₗ[R]
      (Fin (2^(n-1) * (∏ i, d.r i) * n.factorial) → R)) ∧
    ∀ j, Nonempty (strictExteriorPiece d j ≃ₗ[R]
      (Fin ((Polynomial.C ((∏ i, d.r i) * n.factorial) *
        (1 + Polynomial.X)^(n-1) : Polynomial ℕ).coeff j) → R)) :=
  ⟨⟨strictFreeRankEquiv d⟩, fun j ↦ ⟨strictExteriorFreeRankEquiv d j⟩⟩

end PaperVerification.Fermion
