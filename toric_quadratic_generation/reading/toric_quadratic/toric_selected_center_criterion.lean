module

public import PaperVerification.ToricSelectedSupportFormula
public import PaperVerification.ToricSimultaneousIntegralSupport
public import PaperVerification.ToricExtremalCriterion

@[expose] public section

/-!
# A scalar criterion for the genuine selected-fan centers

The selected fan is constructed from the old fan. Its integral strictly
convex support function is proved to exist. The nef conclusion follows
from the actual effective-cone extremal criterion and the three exhaustive
selected-ray cases.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable {ι : Type*} [Fintype ι] (R : ι → «Σ».PrimitiveRelation)
variable (hR : ∀ i, (R i).IsCombinatoriallyContractible)
variable (hne : ∀ i, (R i).negative.Nonempty)
variable (hdisj : «Σ».PairwiseDisjointFoci (fun i => (R i).negative))

include hR in
theorem selected_center_isNef_of_scalar_bounds
    (hpure : «Σ».IsPure) (P : LatticePolytope n) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) {bound : ℕ} (hbound : P.EdgesAtLeast bound)
    (c : ℝ) (hc : 0 ≤ c) (u : ι → ℝ)
    (ht : ∀ i, 0 ≤ u i - c * ((R i).negative.card - 1 : ℝ))
    (hrepair : ∀ i, 0 ≤
      (R i).degree (fun v => (P.integralSupport v : ℝ) - c) +
      ((R i).minimumCoefficient (hne i) : ℝ) *
        (u i - c * ((R i).negative.card - 1 : ℝ)))
    (hinactive : ∀ Q : «Σ».PrimitiveRelation, Q.IsCombinatoriallyContractible →
      (∀ i, «Σ».selectedRay R i ∉ Q.positive) →
      (∀ i, Q.positive ≠ (R i).positive) →
        0 ≤ Q.degree (fun v => (P.integralSupport v : ℝ) - c))
    (hone : ∀ i, 0 ≤ (bound : ℝ) -
      c * ((«Σ».selectedBaseDimension R i : ℝ) + 2) - u i)
    (htwo : ∀ i j, i ≠ j → 0 ≤ (bound : ℝ) - 2 * c +
      c * ((n : ℝ) - 1 - «Σ».selectedBaseDimension R i -
        «Σ».selectedBaseDimension R j) - u i - u j) :
    («Σ».selectedFan R hne hdisj).IsNef
      (fun v => «Σ».selectedPullback R (fun w => (P.integralSupport w : ℝ)) v - c -
        ∑ i, if v = «Σ».selectedRay R i then u i else 0) := by
  let Γ := «Σ».selectedFan R hne hdisj
  let a : Lattice n → ℝ := fun v => (P.integralSupport v : ℝ)
  let t : ι → ℝ := fun i => u i - c * ((R i).negative.card - 1 : ℝ)
  let F : Lattice n → ℝ := fun v => «Σ».selectedPullback R a v - c -
    ∑ i, if v = «Σ».selectedRay R i then u i else 0
  have hF : simultaneousSupport (fun i => (R i).negative) (fun v => a v - c) t = F :=
    «Σ».selected_center_coefficient_formula R hne hdisj a c u
  have hΓpure : Γ.IsPure := «Σ».isPure_simultaneousSubdivision
    («Σ».selectedStarFocus R) hpure (fun i => (R i).negative_cone)
    (fun i => hne i) («Σ».selectedStarFocus_disjoint R hdisj)
  obtain ⟨H, hH⟩ := «Σ».exists_integral_strictSupport_simultaneousSubdivision
    («Σ».selectedStarFocus R) (fun i => (R i).negative_cone)
    (fun i => hne i) («Σ».selectedStarFocus_disjoint R hdisj)
    (fun i => i.property) P.integralSupport
    (P.integralSupport_isStrictSupport «Σ» hfan)
  apply (Γ.isNef_iff_extremal_primitive_nonneg hΓpure H hH F).mpr
  intro S hSext
  have hS := S.combinatoriallyContractible_of_extremal hSext
  by_cases hex : ∃ i, «Σ».selectedRay R i ∈ S.positive
  · obtain ⟨i, hi⟩ := hex
    have hB := «Σ».selected_positive_pullback_degree_lower_bound R hne hdisj
      hpure P hP hfan hbound S hS ⟨i, hi⟩
    by_cases hexj : ∃ j, j ≠ i ∧ «Σ».selectedRay R j ∈ S.positive
    · obtain ⟨j, hji, hj⟩ := hexj
      have hij := hji.symm
      have hcard := («Σ».selected_two_positive_card_bound R hR hne hdisj
        hpure S hS i j hij hi hj).2
      have hcardR : (n : ℝ) ≤ (S.negative.card : ℝ) +
          «Σ».selectedBaseDimension R i + «Σ».selectedBaseDimension R j + 1 := by
        exact_mod_cast hcard
      have hnum : 0 ≤ (bound : ℝ) - 2 * c + c * (S.negative.card : ℝ) - u i - u j := by
        have hh := htwo i j hij
        nlinarith [mul_nonneg hc (sub_nonneg.mpr hcardR)]
      have hdeg := «Σ».selected_two_positive_degree_bound R hne hdisj S hS i j hij hi hj
        («Σ».selectedPullback R a) (bound : ℝ) c 0 hc hB ∅ (by simp) u
      have hdeg' : (bound : ℝ) - 2 * c + c * (S.negative.card : ℝ) - u i - u j ≤
          S.degree F := by
        simpa only [F, zero_mul, sub_zero, add_zero] using hdeg
      exact hnum.trans hdeg'
    · have hother : ∀ j, j ≠ i → «Σ».selectedRay R j ∉ S.positive := by
        intro j hji hj
        exact hexj ⟨j, hji, hj⟩
      have hdeg := «Σ».selected_one_positive_degree_bound R hR hne hdisj S hS i hi hother
        («Σ».selectedPullback R a) (bound : ℝ) c 0 hc le_rfl hB ∅ (by simp) u
      have hdeg' : (bound : ℝ) - c * ((«Σ».selectedBaseDimension R i : ℝ) + 2) - u i ≤
          S.degree F := by
        simpa only [F, zero_mul, sub_zero] using hdeg
      exact (hone i).trans hdeg'
  · have hnone : ∀ i, «Σ».selectedRay R i ∉ S.positive := by
      simpa only [not_exists] using hex
    rw [← hF]
    exact «Σ».selected_no_positive_degree_nonneg R hR hne hdisj
      (fun v => a v - c) t ht hrepair hinactive S hS hnone

end SmoothCompleteFan

end PaperVerification.ToricGeometry
