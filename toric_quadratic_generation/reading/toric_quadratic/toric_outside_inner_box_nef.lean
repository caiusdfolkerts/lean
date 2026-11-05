module

public import PaperVerification.ToricOutsideBoxNef

@[expose] public section

/-!
# Corrected nefness for the inner unit boxes

This is the actual degree calculation in Section 7.2, including the
canonical coefficient, the old selected ray coefficients, and every
activated selected-divisor correction.
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
theorem outside_inner_unit_corrected_isNef
    (hpure : «Σ».IsPure) (P : LatticePolytope n) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) (hbound : P.EdgesAtLeast (n + 1))
    (σ D : Finset (Lattice n)) (hσ : σ ∈ «Σ».cones) (hDσ : D ⊆ σ)
    (houtside : ∀ i, ¬ (R i).negative ⊆ σ)
    (τ : ι → ℝ) (hτ0 : ∀ i, 0 ≤ τ i)
    (hτupper : ∀ i, τ i ≤ 2 * ((R i).fiberDimension : ℝ) - n - (R i).negative.card)
    (hrepair : ∀ i, 0 ≤
      (R i).degree (fun v => (P.integralSupport v : ℝ) - 1 -
        (if v ∈ D then 1 else 0)) +
      ((R i).minimumCoefficient (hne i) : ℝ) * τ i)
    (hinactive : ∀ Q : «Σ».PrimitiveRelation, Q.IsCombinatoriallyContractible →
      (∀ i, Q.positive ≠ (R i).positive) →
      0 ≤ Q.degree (fun v => (P.integralSupport v : ℝ) - 1 -
        (if v ∈ D then 1 else 0))) :
    («Σ».selectedFan R hne hdisj).IsNef
      (simultaneousSupport (fun i => (R i).negative)
        (fun v => (P.integralSupport v : ℝ) - 1 - (if v ∈ D then 1 else 0)) τ) := by
  let Γ := «Σ».selectedFan R hne hdisj
  let a : Lattice n → ℝ := fun v => (P.integralSupport v : ℝ)
  let F := simultaneousSupport (fun i => (R i).negative)
    (fun v => a v - 1 - (if v ∈ D then 1 else 0)) τ
  let u := «Σ».selectedCorrectionWeight R 1 1 D τ
  have hD := «Σ».outside_cone_avoids_selected_rays R hσ hDσ houtside
  have hformula : F = fun v => «Σ».selectedPullback R a v - 1 -
      (if v ∈ D then 1 else 0) -
      ∑ i, if v = «Σ».selectedRay R i then u i else 0 := by
    simpa only [F, one_mul] using
      «Σ».selected_support_coefficient_formula R hne hdisj a 1 1 D hD τ
  have hu (i : ι) : u i = ((R i).negative.card : ℝ) - 1 +
      (((R i).negative ∩ D).card : ℝ) + τ i := by
    simp only [u, selectedCorrectionWeight, one_mul]
  have hk (i : ι) : (((R i).negative ∩ D).card : ℝ) + 1 ≤ (R i).negative.card := by
    exact_mod_cast «Σ».outside_focus_selection_card_bound R hDσ houtside i
  have hdim (i : ι) : (n : ℝ) = (R i).fiberDimension + (R i).negative.card +
      «Σ».selectedBaseDimension R i := by exact_mod_cast «Σ».selected_dimension_eq R hR i
  have hr (i : ι) : ((R i).fiberDimension : ℝ) ≤ n := by
    have hh := (R i).contractible_dimension_bound (hR i)
    exact_mod_cast (show (R i).fiberDimension ≤ n by omega)
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
        («Σ».selectedPullback R a) ((n + 1 : ℕ) : ℝ) 1 1 zero_le_one hB D hD u
      have hdeg' : (n : ℝ) - 1 + S.negative.card + S.negativeWeightOn D -
          u i - u j ≤ S.degree F := by
        have hh : ((n + 1 : ℕ) : ℝ) - 2 + S.negative.card + S.negativeWeightOn D -
            u i - u j ≤ S.degree F := by
          simpa only [hformula, one_mul, mul_one] using hdeg
        norm_num only [Nat.cast_add, Nat.cast_one] at hh
        linarith
      rw [hu i, hu j] at hdeg'
      have hcard := («Σ».selected_two_positive_card_bound R hR hne hdisj
        hpure S hS i j hij hi hj).2
      have hcardR : (n : ℝ) ≤ (S.negative.card : ℝ) +
          «Σ».selectedBaseDimension R i + «Σ».selectedBaseDimension R j + 1 := by
        exact_mod_cast hcard
      have hns := S.negativeWeightOn_nonneg D
      have hki := hk i
      have hkj := hk j
      have hti := hτupper i
      have htj := hτupper j
      have hdi := hdim i
      have hdj := hdim j
      have hri := hr i
      have hrj := hr j
      linarith
    · have hother : ∀ j, j ≠ i → «Σ».selectedRay R j ∉ S.positive := by
        intro j hji hj
        exact hexj ⟨j, hji, hj⟩
      have hdeg := «Σ».selected_one_positive_degree_bound R hR hne hdisj S hS i hi hother
        («Σ».selectedPullback R a) ((n + 1 : ℕ) : ℝ) 1 1 zero_le_one zero_le_one hB D hD u
      have hdeg' : (n : ℝ) - 2 * «Σ».selectedBaseDimension R i - 2 - u i ≤ S.degree F := by
        have hh : ((n + 1 : ℕ) : ℝ) - ((«Σ».selectedBaseDimension R i : ℝ) + 2) -
            ((«Σ».selectedBaseDimension R i : ℝ) + 1) - u i =
            (n : ℝ) - 2 * «Σ».selectedBaseDimension R i - 2 - u i := by
          push_cast
          ring
        simpa only [hformula, one_mul, hh] using hdeg
      rw [hu i] at hdeg'
      have hki := hk i
      have hti := hτupper i
      have hdi := hdim i
      have hq : (0 : ℝ) ≤ (R i).negative.card := Nat.cast_nonneg _
      linarith
  · have hnone : ∀ i, «Σ».selectedRay R i ∉ S.positive := by
      simpa only [not_exists] using hex
    exact «Σ».selected_no_positive_degree_nonneg R hR hne hdisj
      (fun v => a v - 1 - (if v ∈ D then 1 else 0)) τ hτ0 hrepair
      (fun Q hQ hpos hother => hinactive Q hQ hother) S hS hnone

end SmoothCompleteFan

end PaperVerification.ToricGeometry
