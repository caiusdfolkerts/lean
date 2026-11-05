module

public import PaperVerification.ToricSelectedWallCounts
public import PaperVerification.ToricSelectedCenterCriterion

@[expose] public section

/-!
# The full corrected nefness argument for original side-two boxes

The two-positive case uses both independent lower bounds. One comes from
the correction-height budget and the other from the actual negative-wall
count. No positive degree or box containment is included in the hypotheses.
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
/-- Proposition 5.2's corrected support is genuinely nef. The family is
the finite family of activated old contractible relations; the exact
ceiling construction supplies the displayed scalar repair and budgets. -/
theorem outside_side_two_corrected_isNef
    (hpure : «Σ».IsPure) (P : LatticePolytope n) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) (hbound : P.EdgesAtLeast n)
    (σ D : Finset (Lattice n)) (hσ : σ ∈ «Σ».cones) (hDσ : D ⊆ σ)
    (houtside : ∀ i, ¬ (R i).negative ⊆ σ)
    (τ : ι → ℝ) (hτ0 : ∀ i, 0 ≤ τ i)
    (hτfiber : ∀ i, τ i ≤ 2 * ((R i).fiberDimension : ℝ) - n)
    (hτbudget : ∀ i, τ i ≤ 2 * ((D ∩ (R i).positive).card : ℝ) -
      2 * (((R i).negative ∩ D).card : ℝ) - n)
    (hrepair : ∀ i, 0 ≤
      (R i).degree (fun v => (P.integralSupport v : ℝ) -
        2 * (if v ∈ D then 1 else 0)) +
      ((R i).minimumCoefficient (hne i) : ℝ) * τ i)
    (hinactive : ∀ Q : «Σ».PrimitiveRelation, Q.IsCombinatoriallyContractible →
      (∀ i, Q.positive ≠ (R i).positive) →
      0 ≤ Q.degree (fun v => (P.integralSupport v : ℝ) -
        2 * (if v ∈ D then 1 else 0))) :
    («Σ».selectedFan R hne hdisj).IsNef
      (simultaneousSupport (fun i => (R i).negative)
        (fun v => (P.integralSupport v : ℝ) - 2 * (if v ∈ D then 1 else 0)) τ) := by
  let Γ := «Σ».selectedFan R hne hdisj
  let a : Lattice n → ℝ := fun v => (P.integralSupport v : ℝ)
  let F := simultaneousSupport (fun i => (R i).negative)
    (fun v => a v - 2 * (if v ∈ D then 1 else 0)) τ
  let u := «Σ».selectedCorrectionWeight R 0 2 D τ
  have hD := «Σ».outside_cone_avoids_selected_rays R hσ hDσ houtside
  have hformula : F = fun v => «Σ».selectedPullback R a v -
      2 * (if v ∈ D then 1 else 0) -
      ∑ i, if v = «Σ».selectedRay R i then u i else 0 := by
    simpa only [F, sub_zero] using
      «Σ».selected_support_coefficient_formula R hne hdisj a 0 2 D hD τ
  have hu (i : ι) : u i = 2 * (((R i).negative ∩ D).card : ℝ) + τ i := by
    simp only [u, selectedCorrectionWeight, zero_mul, zero_add]
  have hk (i : ι) : (((R i).negative ∩ D).card : ℝ) + 1 ≤ (R i).negative.card := by
    exact_mod_cast «Σ».outside_focus_selection_card_bound R hDσ houtside i
  have hdim (i : ι) : (n : ℝ) = (R i).fiberDimension + (R i).negative.card +
      «Σ».selectedBaseDimension R i := by exact_mod_cast «Σ».selected_dimension_eq R hR i
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
      have hdeg := «Σ».selected_two_positive_degree_bound R hne hdisj S hS i j hij hi hj
        («Σ».selectedPullback R a) (n : ℝ) 0 2 le_rfl hB D hD u
      have hdeg' : (n : ℝ) + 2 * S.negativeWeightOn D - u i - u j ≤ S.degree F := by
        simpa only [hformula, sub_zero, mul_zero, zero_mul, add_zero] using hdeg
      rw [hu i, hu j] at hdeg'
      have hfirst : 2 * ((«Σ».selectedBaseDimension R i : ℝ) +
          «Σ».selectedBaseDimension R j) + 4 - n ≤ S.degree F := by
        have hns := S.negativeWeightOn_nonneg D
        have hki := hk i
        have hkj := hk j
        have hti := hτfiber i
        have htj := hτfiber j
        have hdi := hdim i
        have hdj := hdim j
        linarith
      have hweight := «Σ».selected_pair_negative_weight_bound R hR hne hdisj
        hpure S hS i j hij hi hj D ((Finset.card_le_card hDσ).trans («Σ».card_cone_le hσ))
      have hsecond : (n : ℝ) - 2 * ((«Σ».selectedBaseDimension R i : ℝ) +
          «Σ».selectedBaseDimension R j) - 2 ≤ S.degree F := by
        have hti := hτbudget i
        have htj := hτbudget j
        linarith
      exact zero_le_one.trans (outside_box_two_positive_bound n
        ((«Σ».selectedBaseDimension R i : ℝ) + «Σ».selectedBaseDimension R j)
        (S.degree F) hfirst hsecond)
    · have hother : ∀ j, j ≠ i → «Σ».selectedRay R j ∉ S.positive := by
        intro j hji hj
        exact hexj ⟨j, hji, hj⟩
      have hdeg := «Σ».selected_one_positive_degree_bound R hR hne hdisj S hS i hi hother
        («Σ».selectedPullback R a) (n : ℝ) 0 2 le_rfl (by norm_num) hB D hD u
      have hdeg' : (n : ℝ) - 2 * ((«Σ».selectedBaseDimension R i : ℝ) + 1) - u i ≤
          S.degree F := by
        simpa only [hformula, sub_zero, mul_zero, zero_mul] using hdeg
      rw [hu i] at hdeg'
      have hki := hk i
      have hti := hτfiber i
      have hdi := hdim i
      linarith
  · have hnone : ∀ i, «Σ».selectedRay R i ∉ S.positive := by
      simpa only [not_exists] using hex
    exact «Σ».selected_no_positive_degree_nonneg R hR hne hdisj
      (fun v => a v - 2 * (if v ∈ D then 1 else 0)) τ hτ0 hrepair
      (fun Q hQ hpos hother => hinactive Q hQ hother) S hS hnone

end SmoothCompleteFan

end PaperVerification.ToricGeometry
