module
public import graph_foundation.part014
public import shared_results.part020_ideal_coordinate_leading

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphIdealBettiComparison -/
section

/-! # Equality of the ordinary ideal Betti dimensions

Both dimensions are the sums of the dimensions of the same genuine
associated homology groups. On the monomial side, exact weight projections
supply the cycle lifts; on the original side, the previously constructed
actual lifts are used. Every ordinary and exterior degree is retained.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open FourPapers.Universal FourPapers.FilteredHomology
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance] ordinaryPieceAddCommGroup ordinaryPieceModule
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

variable (P : QuotientGroebnerData V k) (w : V → ℕ)

theorem initialActualIdealOrdinaryPrevious_preserves (q p : ℕ) :
    Preserves (actualIdealOrdinaryFiltration P w q p)
      (actualIdealOrdinaryFiltration P w q p.pred) (initialActualIdealOrdinaryPrevious P q p) :=
  basisHomogeneous_preserves _ _ _ _ _
    (initialActualIdealOrdinaryPrevious_basis_weight P w q p)

theorem initialActualIdealOrdinaryPrevious_lifts (q p : ℕ) :
    LiftsCycles (actualIdealOrdinaryFiltration P w q p)
      (actualIdealOrdinaryFiltration P w q p.pred) (initialActualIdealOrdinaryPrevious P q p) :=
  basisHomogeneous_liftsCycles _ _ _ _ _
    (initialActualIdealOrdinaryPrevious_basis_weight P w q p)

variable
  (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule k (fun _ : V => (1 : ℕ))))
  (htail : ∀ g ∈ P.generators, g ≠ 0 →
    ∀ a ∈ (monomial (P.order.degree g) 1-g).support,
      Finsupp.weight w a < Finsupp.weight w (P.order.degree g))
  (hstrict : ∀ p (a : ActualIdealIndex P p) (b : ActualIdealIndex P p.pred),
    Finsupp.weight w (actualIdealDegree a) ≤ Finsupp.weight w (actualIdealDegree b) →
    (actualIdealCoefficientBasis P p.pred).repr
      (actualIdealPreviousDifferential P.ideal p (actualIdealCoefficientBasis P p a) -
        initialActualIdealPrevious P p (actualIdealCoefficientBasis P p a)) b = 0)

include hstrict in
theorem actualIdealOrdinaryPrevious_gradeMap_eq (q p n : ℕ) :
    gradeMap _ _ (actualIdealOrdinaryPrevious P hJ q p)
      (actualIdealOrdinaryPrevious_preserves P hJ w htail q p) n =
    gradeMap (actualIdealOrdinaryFiltration P w q p)
      (actualIdealOrdinaryFiltration P w q p.pred)
      (initialActualIdealOrdinaryPrevious P q p)
      (initialActualIdealOrdinaryPrevious_preserves P w q p) n := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := (lowerInLevel (actualIdealOrdinaryFiltration P w q p) n).mkQ_surjective x
  rw [Submodule.mkQ_apply, gradeMap_mk, gradeMap_mk]
  apply (Submodule.Quotient.eq _).mpr
  exact basisStrictLower_level _ _ _ _ _
    (actualIdealOrdinaryPrevious_strictly_lowers P hJ w hstrict q p) n x.val x.property

include hstrict in
def actualInitialIdealGradedHomologyEquiv (q p n : ℕ) :
    actualIdealGradedHomology P hJ w htail q p n ≃ₗ[k]
      GradedHomology
        (actualIdealOrdinaryFiltration P w q (p+1))
        (actualIdealOrdinaryFiltration P w q p)
        (actualIdealOrdinaryFiltration P w q p.pred)
        (initialActualIdealOrdinaryDifferential P q p)
        (initialActualIdealOrdinaryPrevious P q p)
        (initialActualIdealOrdinaryPrevious_preserves P w q (p+1))
        (initialActualIdealOrdinaryPrevious_preserves P w q p)
        (initialActualIdealOrdinaryDifferential_comp P q p) n := by
  apply threeTermHomologyEquiv
    (actualIdealGradeDifferential P hJ w htail q p n)
    (actualIdealGradePrevious P hJ w htail q p n)
    (actualIdealGradeDifferential_comp P hJ w htail q p n)
    _ _ _ (LinearEquiv.refl k _) (LinearEquiv.refl k _) (LinearEquiv.refl k _)
  · intro x
    exact LinearMap.congr_fun (actualIdealOrdinaryPrevious_gradeMap_eq
      P w hJ htail hstrict q (p+1) n) x
  · intro x
    exact LinearMap.congr_fun (actualIdealOrdinaryPrevious_gradeMap_eq
      P w hJ htail hstrict q p n) x

end FourPapers.Sublattice

namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open FourPapers.Universal FourPapers.FilteredHomology
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance] ordinaryPieceAddCommGroup ordinaryPieceModule
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]
  (P : QuotientGroebnerData V k)
  (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule k (fun _ : V => (1 : ℕ))))
  (w : V → ℕ)
  (htail : ∀ g ∈ P.generators, g ≠ 0 →
    ∀ a ∈ (monomial (P.order.degree g) 1-g).support,
      Finsupp.weight w a < Finsupp.weight w (P.order.degree g))
  (hstrict : ∀ p (a : ActualIdealIndex P p) (b : ActualIdealIndex P p.pred),
    Finsupp.weight w (actualIdealDegree a) ≤ Finsupp.weight w (actualIdealDegree b) →
    (actualIdealCoefficientBasis P p.pred).repr
      (actualIdealPreviousDifferential P.ideal p (actualIdealCoefficientBasis P p a) -
        initialActualIdealPrevious P p (actualIdealCoefficientBasis P p a)) b = 0)

include htail hstrict in
/-- Equality of all ordinary graded homology dimensions with the genuine
monomial model, with no loss of homological degree zero. -/
theorem actualIdealOrdinaryHomology_finrank_eq_initial
    (M : ℕ) (hM : ∀ v, w v ≤ M)
    (hlift : ∀ p, LiftsCycles (actualIdealCoordinateFiltration P w p)
      (actualIdealCoordinateFiltration P w p.pred) (actualIdealPreviousDifferential P.ideal p))
    (q p : ℕ) :
    Module.finrank k (actualIdealOrdinaryHomology P hJ q p) =
      Module.finrank k (initialActualIdealOrdinaryHomology P q p) := by
  letI := actualIdealOrdinaryPiece_finite P q (p+1)
  letI := actualIdealOrdinaryPiece_finite P q p
  have hactual := finrank_homology_eq_sum_graded
    (actualIdealOrdinaryFiltration P w q (p+1)) (actualIdealOrdinaryFiltration P w q p)
    (actualIdealOrdinaryFiltration P w q p.pred)
    (actualIdealOrdinaryDifferential P hJ q p) (actualIdealOrdinaryPrevious P hJ q p)
    (actualIdealOrdinaryDifferential_preserves P hJ w htail q p)
    (actualIdealOrdinaryPrevious_preserves P hJ w htail q p)
    (actualIdealOrdinaryDifferential_comp P hJ q p)
    (M*q+1) (actualIdealOrdinaryFiltration_top P w M hM q p)
    (actualIdealOrdinaryPrevious_lifts P hJ w q (p+1) (hlift (p+1)))
    (actualIdealOrdinaryPrevious_lifts P hJ w q p (hlift p))
  have hinitial := finrank_homology_eq_sum_graded
    (actualIdealOrdinaryFiltration P w q (p+1)) (actualIdealOrdinaryFiltration P w q p)
    (actualIdealOrdinaryFiltration P w q p.pred)
    (initialActualIdealOrdinaryDifferential P q p) (initialActualIdealOrdinaryPrevious P q p)
    (initialActualIdealOrdinaryPrevious_preserves P w q (p+1))
    (initialActualIdealOrdinaryPrevious_preserves P w q p)
    (initialActualIdealOrdinaryDifferential_comp P q p)
    (M*q+1) (actualIdealOrdinaryFiltration_top P w M hM q p)
    (initialActualIdealOrdinaryPrevious_lifts P w q (p+1))
    (initialActualIdealOrdinaryPrevious_lifts P w q p)
  rw [hactual, hinitial]
  apply Finset.sum_congr rfl
  intro n hn
  exact (actualInitialIdealGradedHomologyEquiv P w hJ htail hstrict q p n).finrank_eq

end FourPapers.Sublattice

end
end
end


end
