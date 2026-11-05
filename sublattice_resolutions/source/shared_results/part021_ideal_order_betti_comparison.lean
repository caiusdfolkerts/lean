module
public import graph_foundation.part014
public import shared_results.part021_ideal_first_betti_lifting

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.IdealOrderBettiComparison -/
section

/-! # Ordinary graded Betti equality from original-order cycle lifting -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance] ordinaryPieceAddCommGroup ordinaryPieceModule

open Classical CommAlg MvPolynomial FilteredHomology

universe u
variable {K V : Type u} [Field K] [Fintype V] [LinearOrder V]
  (P : QuotientGroebnerData V K)
  (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule K (fun _ : V => (1 : ℕ))))

theorem actualIdealOrdinary_ordered_lifts_of_coordinate_lifts (q p : ℕ)
    (hlift : ActualIdealOrderedLifts P p) :
    BasisCycleLifting.LinearLifts (actualIdealOrdinaryBasis P q p)
      (actualIdealOrdinaryBasis P q p.pred)
      (fun a => P.order.toSyn (actualIdealDegree a.val))
      (fun b => P.order.toSyn (actualIdealDegree b.val))
      (actualIdealOrdinaryPrevious P hJ q p) := by
  intro n x hx hdx
  have hdx' : actualIdealPreviousDifferential P.ideal p x.val ∈
      BasisCycleLifting.lower (actualIdealCoefficientBasis P p.pred)
        (fun a => P.order.toSyn (actualIdealDegree a)) n := by
    have he := (actualIdealOrdinaryBasis_span_mem_iff P q p.pred
      {a | P.order.toSyn (actualIdealDegree a)<n}
      (actualIdealOrdinaryPrevious P hJ q p x)).mp hdx
    rwa [actualIdealOrdinaryPrevious_val] at he
  obtain ⟨y,hy,hdy,herr⟩ := hlift n x.val
    ((actualIdealOrdinaryBasis_span_mem_iff P q p
      {a | P.order.toSyn (actualIdealDegree a)≤n} x).mp hx) hdx'
  let z : actualIdealOrdinaryPiece P q p :=
    ⟨Grading.projection (actualIdealCoefficientBasis P p)
      (fun a => (actualIdealDegree a).degree) q y,Grading.projection_mem _ _ _ _⟩
  refine ⟨z,?_,?_,?_⟩
  · apply (actualIdealOrdinaryBasis_span_mem_iff P q p
      {a | P.order.toSyn (actualIdealDegree a)≤n} z).mpr
    exact projection_preserves_basisSpan_monoid (R := K)
      (X := Set.powersetCard V p →₀ P.ideal) (I := ActualIdealIndex P p) (A := ℕ)
      (actualIdealCoefficientBasis P p) (fun a => (actualIdealDegree a).degree) q
      {a | P.order.toSyn (actualIdealDegree a)≤n} y hy
  · apply Subtype.ext
    cases p with
    | zero => rfl
    | succ p =>
      have he := LinearMap.congr_fun (fineProjection_commutes (R := K)
        (X := Set.powersetCard V (p+1) →₀ P.ideal)
        (Y := Set.powersetCard V p →₀ P.ideal)
        (I := ActualIdealIndex P (p+1)) (J := ActualIdealIndex P p) (Γ := ℕ)
        (actualIdealCoefficientBasis P (p+1)) (actualIdealCoefficientBasis P p)
        (fun a => (actualIdealDegree a).degree) (fun a => (actualIdealDegree a).degree)
        (actualIdealCoordinateDifferential P.ideal p)
        (fun a => actualIdealCoordinateDifferential_ordinary P hJ _ p _
          (Grading.basis_mem_piece _ _ a)) q) y
      change actualIdealCoordinateDifferential P.ideal p y = 0 at hdy
      change actualIdealCoordinateDifferential P.ideal p
        (Grading.projection (actualIdealCoefficientBasis P (p+1))
          (fun a => (actualIdealDegree a).degree) q y) = 0
      simpa only [LinearMap.comp_apply, hdy, map_zero] using he
  · apply (actualIdealOrdinaryBasis_span_mem_iff P q p
      {a | P.order.toSyn (actualIdealDegree a)<n} (x-z)).mpr
    change x.val - Grading.projection (actualIdealCoefficientBasis P p)
      (fun a => (actualIdealDegree a).degree) q y ∈ _
    have he := projection_preserves_basisSpan_monoid (R := K)
      (X := Set.powersetCard V p →₀ P.ideal) (I := ActualIdealIndex P p) (A := ℕ)
      (actualIdealCoefficientBasis P p)
      (fun a => (actualIdealDegree a).degree) q {a | P.order.toSyn (actualIdealDegree a)<n}
      (x.val-y) herr
    rw [actualIdealCoordinate_sub_eq_add_neg_one_smul P p x.val y,
      map_add, map_smul, Grading.projection_eq_self x.property,
      ← actualIdealCoordinate_sub_eq_add_neg_one_smul P p x.val
        (Grading.projection (actualIdealCoefficientBasis P p)
          (fun a => (actualIdealDegree a).degree) q y)] at he
    exact he

theorem actualIdealOrdinary_kernel_eq_of_ordered_lifts (q p : ℕ)
    (hlift : ActualIdealOrderedLifts P p) :
    Module.finrank K (LinearMap.ker (actualIdealOrdinaryPrevious P hJ q p))=
      Module.finrank K (LinearMap.ker (initialActualIdealOrdinaryPrevious P q p)) := by
  letI : FiniteDimensional K (actualIdealOrdinaryPiece P q p) := actualIdealOrdinaryPiece_finite P q p
  letI : FiniteDimensional K (actualIdealOrdinaryPiece P q p.pred) :=
    actualIdealOrdinaryPiece_finite P q p.pred
  letI : Fintype (TermOrderDegreeIndex (V:=V) q) := Fintype.ofFinite _
  apply FiniteBasedComparison.kernel_finrank_eq_of_orderedLifts
    (actualIdealOrdinaryBasis P q p) (actualIdealOrdinaryBasis P q p.pred)
    (ordinaryFineAssignment P q p) (ordinaryFineAssignment P q p.pred)
    (fun a : TermOrderDegreeIndex (V:=V) q => P.order.toSyn a.val)
    (actualIdealOrdinaryPrevious P hJ q p) (initialActualIdealOrdinaryPrevious P q p)
  · intro a b hb
    have hb' : (actualIdealCoefficientBasis P p.pred).repr
        (initialActualIdealPrevious P p (actualIdealCoefficientBasis P p a.val)) b.val≠0 := by
      simpa only [actualIdealOrdinaryBasis_repr,
        initialActualIdealOrdinaryPrevious_val,actualIdealOrdinaryBasis_val] using hb
    exact (Grading.mem_piece _ _ _ _).mp
      (initialActualIdealPrevious_basis_regrade P P.order.toSyn p a.val) b.val hb'
  · intro a b hab
    have h0 := actualIdealPrevious_order_leading P p a.val b.val hab
    rw [actualIdealCoefficientBasis_repr_sub P p.pred] at h0
    have he := sub_eq_zero.mp h0
    simpa only [actualIdealOrdinaryBasis_repr,
      actualIdealOrdinaryPrevious_val,initialActualIdealOrdinaryPrevious_val,
      actualIdealOrdinaryBasis_val] using he
  · exact actualIdealOrdinary_ordered_lifts_of_coordinate_lifts P hJ q p hlift

theorem actualIdealOrdinaryHomology_finrank_eq_initial_of_ordered_lifts
    (hlift : ∀ p,ActualIdealOrderedLifts P p) (q p : ℕ) :
    Module.finrank K (actualIdealOrdinaryHomology P hJ q p)=
      Module.finrank K (initialActualIdealOrdinaryHomology P q p) := by
  letI : ∀ r,FiniteDimensional K (actualIdealOrdinaryPiece P q r) :=
    fun r => actualIdealOrdinaryPiece_finite P q r
  have hleft := finrank_homology_add_finrank_source
    (actualIdealOrdinaryDifferential P hJ q p) (actualIdealOrdinaryPrevious P hJ q p)
    (actualIdealOrdinaryDifferential_comp P hJ q p)
  have hright := finrank_homology_add_finrank_source
    (initialActualIdealOrdinaryDifferential P q p) (initialActualIdealOrdinaryPrevious P q p)
    (initialActualIdealOrdinaryDifferential_comp P q p)
  have hin := actualIdealOrdinary_kernel_eq_of_ordered_lifts P hJ q (p+1) (hlift (p+1))
  have hout := actualIdealOrdinary_kernel_eq_of_ordered_lifts P hJ q p (hlift p)
  change Module.finrank K (LinearMap.ker (actualIdealOrdinaryDifferential P hJ q p))=
    Module.finrank K (LinearMap.ker (initialActualIdealOrdinaryDifferential P q p)) at hin
  change Module.finrank K (actualIdealOrdinaryHomology P hJ q p) +
      Module.finrank K (actualIdealOrdinaryPiece P q (p+1)) =
    Module.finrank K (LinearMap.ker (actualIdealOrdinaryPrevious P hJ q p)) +
      Module.finrank K (LinearMap.ker (actualIdealOrdinaryDifferential P hJ q p)) at hleft
  change Module.finrank K (initialActualIdealOrdinaryHomology P q p) +
      Module.finrank K (actualIdealOrdinaryPiece P q (p+1)) =
    Module.finrank K (LinearMap.ker (initialActualIdealOrdinaryPrevious P q p)) +
      Module.finrank K (LinearMap.ker (initialActualIdealOrdinaryDifferential P q p)) at hright
  omega

theorem ordinaryIdealBettiNumber_eq_monomial_of_ordered_lifts
    (hlift : ∀ p,ActualIdealOrderedLifts P p) (p q : ℕ) :
    ordinaryIdealBettiNumber P hJ p q=ordinaryMonomialBettiNumber (k:=K) P.family q p := by
  rw [ordinaryIdealBettiNumber_eq_finrank,
    actualIdealOrdinaryHomology_finrank_eq_initial_of_ordered_lifts P hJ hlift q p,
    (initialActualIdealOrdinaryHomologyEquiv P q p).finrank_eq]
  rfl

end FourPapers.Sublattice

end
end
end


end
