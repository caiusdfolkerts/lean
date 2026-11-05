module
public import graph_foundation.part014
public import shared_results.part020_three_term_homology_equiv

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ActualIdealOrdinaryMonomialHomology -/
section

/-! # The actual ordinary monomial comparison for every homogeneous ideal -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open FourPapers.Universal FourPapers.FilteredHomology
attribute [local instance] ordinaryPieceAddCommGroup ordinaryPieceModule
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]
  (P : QuotientGroebnerData V k)

/-- The ordinary monomial model has the same actual vectors as the
transported initial complex, through the proved coefficient-basis map. -/
def actualIdealOrdinaryMonomialEquiv (q p : ℕ) :
    actualIdealOrdinaryPiece P q p ≃ₗ[k] ordinaryMonomialPiece (k := k) P.family q p where
  toFun x := ⟨actualIdealMonomialEquiv P p x.val,
    (actualIdealMonomialEquiv_piece_iff P p Finsupp.degree q x.val).mpr x.property⟩
  invFun x := ⟨(actualIdealMonomialEquiv P p).symm x.val, by
    apply (actualIdealMonomialEquiv_piece_iff P p Finsupp.degree q _).mp
    simpa only [ordinaryMonomialPiece, LinearEquiv.apply_symm_apply] using x.property⟩
  left_inv x := Subtype.ext (LinearEquiv.symm_apply_apply _ x.val)
  right_inv x := Subtype.ext (LinearEquiv.apply_symm_apply _ x.val)
  map_add' x y := Subtype.ext ((actualIdealMonomialEquiv P p).map_add x.val y.val)
  map_smul' r x := Subtype.ext ((actualIdealMonomialEquiv P p).map_smul r x.val)

lemma actualIdealOrdinaryMonomialEquiv_differential (q p : ℕ)
    (x : actualIdealOrdinaryPiece P q (p+1)) :
    actualIdealOrdinaryMonomialEquiv P q p (initialActualIdealOrdinaryDifferential P q p x) =
      ordinaryMonomialDifferential (k := k) P.family q p
        (actualIdealOrdinaryMonomialEquiv P q (p+1) x) :=
  Subtype.ext (actualIdealMonomialEquiv_differential P p x.val)

lemma actualIdealOrdinaryMonomialEquiv_previous (q p : ℕ)
    (x : actualIdealOrdinaryPiece P q p) :
    actualIdealOrdinaryMonomialEquiv P q p.pred (initialActualIdealOrdinaryPrevious P q p x) =
      ordinaryMonomialPrevious (k := k) P.family q p (actualIdealOrdinaryMonomialEquiv P q p x) := by
  cases p with
  | zero => simp only [initialActualIdealOrdinaryPrevious, ordinaryMonomialPrevious,
      LinearMap.zero_apply, map_zero]
  | succ p => exact actualIdealOrdinaryMonomialEquiv_differential P q p x

def initialActualIdealOrdinaryHomologyEquiv (q p : ℕ) :
    initialActualIdealOrdinaryHomology P q p ≃ₗ[k] ordinaryMonomialHomology (k := k) P.family q p :=
  threeTermHomologyEquiv (R := k)
    (X := actualIdealOrdinaryPiece P q (p+1))
    (Y := actualIdealOrdinaryPiece P q p)
    (Z := actualIdealOrdinaryPiece P q p.pred)
    (X' := ordinaryMonomialPiece (k := k) P.family q (p+1))
    (Y' := ordinaryMonomialPiece (k := k) P.family q p)
    (Z' := ordinaryMonomialPiece (k := k) P.family q p.pred)
    (initialActualIdealOrdinaryDifferential P q p) (initialActualIdealOrdinaryPrevious P q p)
    (initialActualIdealOrdinaryDifferential_comp P q p)
    (ordinaryMonomialDifferential (k := k) P.family q p) (ordinaryMonomialPrevious (k := k) P.family q p)
    (ordinaryMonomialDifferential_comp (k := k) P.family q p)
    (actualIdealOrdinaryMonomialEquiv P q (p+1)) (actualIdealOrdinaryMonomialEquiv P q p)
    (actualIdealOrdinaryMonomialEquiv P q p.pred)
    (actualIdealOrdinaryMonomialEquiv_differential P q p)
    (actualIdealOrdinaryMonomialEquiv_previous P q p)


end FourPapers.Sublattice

end
end
end


end
