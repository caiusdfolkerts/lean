module
public import graph_foundation.part014
public import shared_results.part021_finite_based_comparison

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.IdealFirstBettiLifting -/
section

/-! # First-power Betti equality forces original-order cycle lifting

The ordinary strands are finite. Equality of all their homology dimensions
recovers equality of each differential's kernel dimension, starting at
homological degree zero. The finitely many term-order weights in one
ordinary degree are then enumerated, without replacing the global term order.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance] ordinaryPieceAddCommGroup ordinaryPieceModule

open Classical CommAlg CommAlg.Polymatroid MvPolynomial FilteredHomology

universe u
variable {K V : Type u} [Field K] [Fintype V] [LinearOrder V]
  (P : QuotientGroebnerData V K)
  (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule K (fun _ : V => (1 : ℕ))))

abbrev TermOrderDegreeIndex (q : ℕ) := {a : Exponent V // a.degree=q}

instance termOrderDegreeIndex_finite (q : ℕ) : Finite (TermOrderDegreeIndex (V:=V) q) := by
  let B := {a : Exponent V // a.degree≤q}
  letI : Finite B := (Finsupp.finite_of_degree_le q).to_subtype
  exact Finite.of_injective
    (fun a : TermOrderDegreeIndex (V:=V) q => (⟨a.val,a.property.le⟩ : B))
    (fun a b h => Subtype.ext (congrArg (fun z : B => z.val) h))

def ordinaryFineAssignment (q p : ℕ)
    (a : {a : ActualIdealIndex P p // (actualIdealDegree a).degree=q}) :
    TermOrderDegreeIndex (V:=V) q := ⟨actualIdealDegree a.val,a.property⟩

/-- Restricting to an ordinary degree retains every support bound on the
literal monic ideal basis, including the original monomial-order levels. -/
theorem actualIdealOrdinaryBasis_span_mem_iff (q p : ℕ)
    (S : Set (ActualIdealIndex P p)) (x : actualIdealOrdinaryPiece P q p) :
    x ∈ Submodule.span K ((actualIdealOrdinaryBasis P q p) '' {a | a.val ∈ S}) ↔
      x.val ∈ Submodule.span K ((actualIdealCoefficientBasis P p) '' S) := by
  rw [(actualIdealOrdinaryBasis P q p).mem_span_image,
    (actualIdealCoefficientBasis P p).mem_span_image]
  refine finsupp_support_subset_iff_of_restrict
    ((actualIdealOrdinaryBasis P q p).repr x)
    ((actualIdealCoefficientBasis P p).repr x.val) Subtype.val
    (fun a => actualIdealOrdinaryBasis_repr P q p x a) ?_ S
  intro a ha
  have hd : (actualIdealDegree a).degree=q :=
    (Grading.mem_piece (actualIdealCoefficientBasis P p)
      (fun a => (actualIdealDegree a).degree) q x.val).mp x.property a
        (Finsupp.mem_support_iff.mp ha)
  exact ⟨⟨a, hd⟩, rfl⟩


theorem actualIdealOrdinary_kernel_finrank_eq
    (hβ : ∀ p q, Module.finrank K (actualIdealOrdinaryHomology P hJ q p)=
      Module.finrank K (initialActualIdealOrdinaryHomology P q p)) (q p : ℕ) :
    Module.finrank K (LinearMap.ker (actualIdealOrdinaryPrevious P hJ q p)) =
      Module.finrank K (LinearMap.ker (initialActualIdealOrdinaryPrevious P q p)) := by
  letI : ∀ r,FiniteDimensional K (actualIdealOrdinaryPiece P q r) :=
    fun r => actualIdealOrdinaryPiece_finite P q r
  exact FiniteComplexRanks.kernel_finrank_eq_of_homology_finrank_eq
    (fun r => actualIdealOrdinaryPiece P q r)
    (actualIdealOrdinaryDifferential P hJ q) (initialActualIdealOrdinaryDifferential P q)
    (fun r => actualIdealOrdinaryDifferential_comp P hJ q (r+1))
    (fun r => initialActualIdealOrdinaryDifferential_comp P q (r+1))
    (fun r => hβ r q) p

theorem actualIdealOrdinary_ordered_lifts
    (hβ : ∀ p q, Module.finrank K (actualIdealOrdinaryHomology P hJ q p)=
      Module.finrank K (initialActualIdealOrdinaryHomology P q p)) (q p : ℕ) :
    BasisCycleLifting.LinearLifts (actualIdealOrdinaryBasis P q p)
      (actualIdealOrdinaryBasis P q p.pred)
      (fun a => P.order.toSyn (actualIdealDegree a.val))
      (fun b => P.order.toSyn (actualIdealDegree b.val))
      (actualIdealOrdinaryPrevious P hJ q p) := by
  letI : FiniteDimensional K (actualIdealOrdinaryPiece P q p) := actualIdealOrdinaryPiece_finite P q p
  letI : FiniteDimensional K (actualIdealOrdinaryPiece P q p.pred) :=
    actualIdealOrdinaryPiece_finite P q p.pred
  letI : Fintype (TermOrderDegreeIndex (V:=V) q) := Fintype.ofFinite _
  apply FiniteBasedComparison.orderedLifts_of_equal_kernel
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
  · exact actualIdealOrdinary_kernel_finrank_eq P hJ hβ q p

def ActualIdealOrderedLifts (p : ℕ) : Prop :=
  BasisCycleLifting.LinearLifts (K := K)
    (X := Set.powersetCard V p →₀ P.ideal) (Y := Set.powersetCard V p.pred →₀ P.ideal)
    (I := ActualIdealIndex P p) (J := ActualIdealIndex P p.pred) (Γ := P.order.syn)
    (actualIdealCoefficientBasis P p) (actualIdealCoefficientBasis P p.pred)
    (fun a : ActualIdealIndex P p => P.order.toSyn (actualIdealDegree a))
    (fun b : ActualIdealIndex P p.pred => P.order.toSyn (actualIdealDegree b))
    (actualIdealPreviousDifferential P.ideal p)

/-- Every leading cycle in the full actual ideal complex lifts. The finite
ordinary-degree decomposition is applied to each input vector separately. -/
theorem actualIdeal_ordered_lifts_of_homology_eq
    (hβ : ∀ p q, Module.finrank K (actualIdealOrdinaryHomology P hJ q p)=
      Module.finrank K (initialActualIdealOrdinaryHomology P q p)) (p : ℕ) :
    ActualIdealOrderedLifts P p := by
  apply BasisCycleLifting.linearLifts_of_homogeneous_lifts (K := K)
    (X := Set.powersetCard V p →₀ P.ideal) (Y := Set.powersetCard V p.pred →₀ P.ideal)
    (I := ActualIdealIndex P p) (J := ActualIdealIndex P p.pred) (A := ℕ) (Γ := P.order.syn)
    (actualIdealCoefficientBasis P p) (actualIdealCoefficientBasis P p.pred)
    (fun a => P.order.toSyn (actualIdealDegree a))
    (fun b => P.order.toSyn (actualIdealDegree b)) (actualIdealPreviousDifferential P.ideal p)
    (fun a => (actualIdealDegree a).degree) (fun b => (actualIdealDegree b).degree)
  · intro a
    cases p with
    | zero => exact Submodule.zero_mem _
    | succ p =>
      exact actualIdealCoordinateDifferential_ordinary P hJ _ p _
        (Grading.basis_mem_piece _ _ a)
  · intro q n x hx hxF hdx
    let x' : actualIdealOrdinaryPiece P q p := ⟨x,hx⟩
    have hxF' : x'∈BasisCycleLifting.level (actualIdealOrdinaryBasis P q p)
        (fun a => P.order.toSyn (actualIdealDegree a.val)) n :=
      (actualIdealOrdinaryBasis_span_mem_iff P q p
        {a | P.order.toSyn (actualIdealDegree a)≤n} x').mpr hxF
    have hdx' : actualIdealOrdinaryPrevious P hJ q p x'∈
        BasisCycleLifting.lower (actualIdealOrdinaryBasis P q p.pred)
          (fun a => P.order.toSyn (actualIdealDegree a.val)) n := by
      apply (actualIdealOrdinaryBasis_span_mem_iff P q p.pred
        {a | P.order.toSyn (actualIdealDegree a)<n}
        (actualIdealOrdinaryPrevious P hJ q p x')).mpr
      rwa [actualIdealOrdinaryPrevious_val]
    obtain ⟨z,hz,hdz,herr⟩ := actualIdealOrdinary_ordered_lifts P hJ hβ q p n x' hxF' hdx'
    refine ⟨z.val,z.property,?_,?_,?_⟩
    · exact (actualIdealOrdinaryBasis_span_mem_iff P q p
        {a | P.order.toSyn (actualIdealDegree a)≤n} z).mp hz
    · have he := congrArg (fun t : actualIdealOrdinaryPiece P q p.pred => t.val) hdz
      simpa only [actualIdealOrdinaryPrevious_val, ZeroMemClass.coe_zero] using he
    · exact (actualIdealOrdinaryBasis_span_mem_iff P q p
        {a | P.order.toSyn (actualIdealDegree a)<n} (x'-z)).mp herr

/-- The hypothesis is equality of the full ordinary graded Betti numbers,
whose source is a genuine submodule of the derived Tor object. -/
theorem actualIdeal_ordered_lifts_of_betti_eq
    (hβ : ∀ p q, ordinaryIdealBettiNumber P hJ p q = ordinaryMonomialBettiNumber (k:=K) P.family q p)
    (p : ℕ) : ActualIdealOrderedLifts P p := by
  apply actualIdeal_ordered_lifts_of_homology_eq P hJ
  intro r q
  rw [← ordinaryIdealBettiNumber_eq_finrank P hJ r q,hβ r q,ordinaryMonomialBettiNumber,
    ← (initialActualIdealOrdinaryHomologyEquiv P q r).finrank_eq]

end FourPapers.Sublattice

end
end
end


end
