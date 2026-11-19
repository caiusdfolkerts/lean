module
public import graph_results.finer_ideal_rename

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.CanonicalFinerMonomialHomology -/
section

/-!
# The initial finer component is the literal monomial-ideal Tor component

The monomial coefficient equivalence preserves every weighted polynomial
and exterior degree. This identifies the initial model with the canonical
presentation of the actual monomial ideal, independently of the chosen
Gröbner presentation of the original ideal.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
noncomputable section

namespace FourPapers.Sublattice

open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial FilteredHomology
attribute [local instance] MvPolynomial.weightedGradedAlgebra

universe u v
variable {K V : Type u} [Field K] [Fintype V] [LinearOrder V]
  {Γ : Type v} [AddCommMonoid Γ]

theorem monomialIdeal_weighted_homogeneous (B : Family V) (ω : V → Γ) :
    (monomialIdeal K B).IsHomogeneous (weightedHomogeneousSubmodule K ω) := by
  apply Ideal.homogeneous_span
  rintro f ⟨a, ha, rfl⟩
  exact ⟨Finsupp.weight ω a, isWeightedHomogeneous_monomial ω a (1 : K) rfl⟩

variable (P : QuotientGroebnerData V K) (ω : V → Γ)

local notation "Q" => canonicalQuotientGroebnerData P.order (monomialIdeal K P.family)
local notation "hQ" => monomialIdeal_weighted_homogeneous (K := K) P.family ω

theorem initialFinerPiece_mem_canonical (γ : Γ) (p : ℕ)
    (x : Set.powersetCard V p →₀ P.ideal) :
    actualIdealMonomialEquiv P p x ∈ finerIdealPiece Q ω γ p ↔
      x ∈ finerIdealPiece P ω γ p := by
  rw [finerIdealPiece_eq_polynomial Q ω hQ]
  exact initialFinerPiece_mem_polynomial P ω γ p x

def initialFinerPieceEquivCanonical (γ : Γ) (p : ℕ) :
    finerIdealPiece P ω γ p ≃ₗ[K] finerIdealPiece Q ω γ p where
  toFun x := ⟨actualIdealMonomialEquiv P p x.val,
    (initialFinerPiece_mem_canonical P ω γ p x.val).mpr x.property⟩
  invFun y := ⟨(actualIdealMonomialEquiv P p).symm y.val, by
    apply (initialFinerPiece_mem_canonical P ω γ p _).mp
    rw [LinearEquiv.apply_symm_apply]
    exact y.property⟩
  left_inv x := Subtype.ext ((actualIdealMonomialEquiv P p).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((actualIdealMonomialEquiv P p).apply_symm_apply y.val)
  map_add' x y := Subtype.ext ((actualIdealMonomialEquiv P p).map_add x.val y.val)
  map_smul' r x := Subtype.ext ((actualIdealMonomialEquiv P p).map_smul r x.val)

lemma initialFinerPieceEquivCanonical_differential (γ : Γ) (p : ℕ)
    (x : finerIdealPiece P ω γ (p + 1)) :
    initialFinerPieceEquivCanonical P ω γ p (initialFinerIdealDifferential P ω γ p x) =
      finerIdealDifferential Q ω hQ γ p (initialFinerPieceEquivCanonical P ω γ (p + 1) x) := by
  apply Subtype.ext
  exact actualIdealMonomialEquiv_differential P p x.val

lemma initialFinerPieceEquivCanonical_previous (γ : Γ) (p : ℕ)
    (x : finerIdealPiece P ω γ p) :
    initialFinerPieceEquivCanonical P ω γ p.pred (initialFinerIdealPrevious P ω γ p x) =
      finerIdealPrevious Q ω hQ γ p (initialFinerPieceEquivCanonical P ω γ p x) := by
  cases p with
  | zero => exact (initialFinerPieceEquivCanonical P ω γ 0).map_zero
  | succ p => exact initialFinerPieceEquivCanonical_differential P ω γ p x

/-- This equivalence is induced by the monomial coefficient equivalence,
with the actual variable-action Koszul differentials on the target. -/
def initialFinerHomologyEquivCanonical (γ : Γ) (p : ℕ) :
    initialFinerIdealHomology P ω γ p ≃ₗ[K] finerIdealHomology Q ω hQ γ p :=
  threeTermHomologyEquiv (R := K)
    (X := finerIdealPiece P ω γ (p+1)) (Y := finerIdealPiece P ω γ p)
    (Z := finerIdealPiece P ω γ p.pred)
    (X' := finerIdealPiece Q ω γ (p+1)) (Y' := finerIdealPiece Q ω γ p)
    (Z' := finerIdealPiece Q ω γ p.pred)
    (initialFinerIdealDifferential P ω γ p) (initialFinerIdealPrevious P ω γ p)
    (initialFinerIdealDifferential_comp P ω γ p)
    (finerIdealDifferential Q ω hQ γ p) (finerIdealPrevious Q ω hQ γ p)
    (finerIdealDifferential_comp Q ω hQ γ p)
    (initialFinerPieceEquivCanonical P ω γ (p + 1))
    (initialFinerPieceEquivCanonical P ω γ p)
    (initialFinerPieceEquivCanonical P ω γ p.pred)
    (initialFinerPieceEquivCanonical_differential P ω γ p)
    (initialFinerPieceEquivCanonical_previous P ω γ p)

theorem initialFinerBettiNumber_eq_canonical (p : ℕ) (γ : Γ) :
    initialFinerBettiNumber P ω p γ = finerIdealBettiNumber Q ω hQ p γ := by
  rw [initialFinerBettiNumber, finerIdealBettiNumber,
    ← (initialFinerGradedTorEquiv P ω γ p).finrank_eq,
    ← (finerIdealGradedTorEquiv Q ω hQ γ p).finrank_eq]
  exact (initialFinerHomologyEquivCanonical P ω γ p).finrank_eq

end FourPapers.Sublattice

end
end
end


end
