module
public import graph_foundation.part014
public import shared_results.part021_ideal_power_coordinate_transport

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.IdealCoordinateOrderLeading -/
section

/-! # Strictness for an arbitrary monomial order

No numeric weight vector is chosen. The full monomial order on the actual
polynomial-plus-exterior exponent is retained.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers

open Classical CommAlg

theorem basisMap_preserves_lower {K X Y I J Γ : Type*} [CommRing K]
    [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y] [LinearOrder Γ]
    (b : Module.Basis I K X) (c : Module.Basis J K Y) (w : I → Γ) (v : J → Γ)
    (f : X →ₗ[K] Y) (hf : ∀ i,f (b i)∈Grading.Piece c v (w i))
    (n : Γ) (x : X) (hx : x∈BasisCycleLifting.lower b w n) :
    f x∈BasisCycleLifting.lower c v n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,hi,rfl⟩ := hx
    rw [BasisCycleLifting.lower,Module.Basis.mem_span_image]
    intro j hj
    change v j < n
    rw [(Grading.mem_piece c v (w i) _).mp (hf i) j (Finsupp.mem_support_iff.mp hj)]
    exact hi
  | zero => simpa only [map_zero] using Submodule.zero_mem _
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul r x hx ih => simpa only [map_smul] using Submodule.smul_mem _ r ih

end FourPapers

namespace FourPapers.Sublattice

open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open FourPapers.Universal FourPapers.FilteredHomology

universe u
variable {K V : Type u} [CommRing K] [Nontrivial K] [Fintype V] [LinearOrder V]
  (P : QuotientGroebnerData V K)

theorem idealAmbient_basis_difference_repr (p : ℕ) (a : ActualIdealIndex P p)
    (b : QuotientIndex (∅ : Family V) p) :
    (quotientCoefficientBasis (k:=K) (∅ : Family V) p).repr
      (idealCoordinatesToAmbient P.ideal p (actualIdealCoefficientBasis P p a) -
        initialIdealAmbientMap P p (actualIdealCoefficientBasis P p a)) b =
      if a.1=b.1 then -(P.groebner.normalForm P.unitLeading
        (monomial a.2.val 1)).coeff b.2.val else 0 := by
  rw [idealAmbient_basis_difference,map_neg,Finsupp.neg_apply,
    quotientCoefficientBasis,Finsupp.basis_repr,Finsupp.single_apply]
  split_ifs
  · rw [emptyCoefficientPolynomialEquiv_repr,AlgEquiv.apply_symm_apply]
  · simp only [map_zero,Finsupp.zero_apply,neg_zero]

theorem idealAmbient_basis_difference_order_lower (p : ℕ) (a : ActualIdealIndex P p) :
    idealCoordinatesToAmbient P.ideal p (actualIdealCoefficientBasis P p a) -
      initialIdealAmbientMap P p (actualIdealCoefficientBasis P p a) ∈
      BasisCycleLifting.lower (quotientCoefficientBasis (k:=K) (∅ : Family V) p)
        (fun b => P.order.toSyn (quotientDegree b)) (P.order.toSyn (actualIdealDegree a)) := by
  rw [BasisCycleLifting.lower,Module.Basis.mem_span_image]
  intro b hb
  change P.order.toSyn (quotientDegree b) < P.order.toSyn (actualIdealDegree a)
  have hc := Finsupp.mem_support_iff.mp hb
  rw [idealAmbient_basis_difference_repr] at hc
  by_cases hF : a.1=b.1
  · rw [if_pos hF,neg_ne_zero] at hc
    have hnf := normalForm_support_lt_termOrder P.order P.ideal P.generators
      P.groebner P.unitLeading a.2 b.2.val (mem_support_iff.mpr hc)
    simpa only [actualIdealDegree,quotientDegree,map_add,hF,add_comm] using
      add_lt_add_right hnf (P.order.toSyn (faceExponent b.1.val))
  · rw [if_neg hF] at hc
    exact (hc rfl).elim

theorem actualIdealPrevious_order_leading (p : ℕ)
    (a : ActualIdealIndex P p) (b : ActualIdealIndex P p.pred)
    (hweight : P.order.toSyn (actualIdealDegree a) ≤ P.order.toSyn (actualIdealDegree b)) :
    (actualIdealCoefficientBasis P p.pred).repr
      (actualIdealPreviousDifferential P.ideal p (actualIdealCoefficientBasis P p a) -
        initialActualIdealPrevious P p (actualIdealCoefficientBasis P p a)) b=0 := by
  cases p with
  | zero =>
    change (actualIdealCoefficientBasis P 0).repr
      ((0 : Set.powersetCard V 0 →₀ P.ideal) - 0) b = 0
    rw [actualIdealCoefficientBasis_repr_sub]
    simp only [(actualIdealCoefficientBasis P 0).repr.map_zero, Finsupp.zero_apply, sub_self]
  | succ p =>
    have hd := basisMap_preserves_lower
      (quotientCoefficientBasis (k:=K) (∅ : Family V) (p+1))
      (quotientCoefficientBasis (k:=K) (∅ : Family V) p)
      (fun a => P.order.toSyn (quotientDegree a)) (fun a => P.order.toSyn (quotientDegree a))
      (quotientDifferential (k:=K) (∅ : Family V) p)
      (quotientDifferential_basis_regraded (∅ : Family V) P.order.toSyn p)
      (P.order.toSyn (actualIdealDegree a)) _ (idealAmbient_basis_difference_order_lower P (p+1) a)
    rw [map_sub,idealCoordinatesToAmbient_differential,← initialIdealAmbient_differential] at hd
    change (actualIdealCoefficientBasis P p).repr
      (actualIdealCoordinateDifferential P.ideal p (actualIdealCoefficientBasis P (p+1) a) -
        initialActualIdealDifferential P p (actualIdealCoefficientBasis P (p+1) a)) b = 0
    by_contra hne
    have hne' :
        (actualIdealCoefficientBasis P p).repr
          (actualIdealCoordinateDifferential P.ideal p
            (actualIdealCoefficientBasis P (p+1) a)) b -
        (actualIdealCoefficientBasis P p).repr
          (initialActualIdealDifferential P p
            (actualIdealCoefficientBasis P (p+1) a)) b ≠ 0 := by
      simpa only [actualIdealPreviousDifferential, initialActualIdealPrevious,
        actualIdealCoefficientBasis_repr_sub] using hne
    have hc : (quotientCoefficientBasis (k:=K) (∅ : Family V) p).repr
        (idealCoordinatesToAmbient P.ideal p
          (actualIdealCoordinateDifferential P.ideal p (actualIdealCoefficientBasis P (p+1) a)) -
          initialIdealAmbientMap P p
            (initialActualIdealDifferential P p (actualIdealCoefficientBasis P (p+1) a)))
        (actualIdealAmbientIndex P p b)≠0 := by
      rw [map_sub, Finsupp.sub_apply, initialIdealAmbient_repr P p]
      simpa only [idealCoordinatesToAmbient_repr, actualIdealAmbientIndex,
        ← actualIdealCoefficientBasis_repr] using hne'
    have hlt := ((quotientCoefficientBasis (k:=K) (∅ : Family V) p).mem_span_image).mp hd
      (Finsupp.mem_support_iff.mpr hc)
    exact (not_lt_of_ge hweight) hlt

end FourPapers.Sublattice

end
end
end


end
