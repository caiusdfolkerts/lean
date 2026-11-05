module

public import PaperVerification.ToricSelectedCenterCriterion

@[expose] public section

/-!
# Nefness of the parity and adjoint centers

All three center support functions have their literal coefficients on the
constructed selected fan. The input edge bounds concern actual lattice
edges of the original polytope. Inactive-class bounds and displacement
inequalities are the explicit scalar data supplied by the finite
obstruction selection and the integer ceiling construction.
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
/-- The real center divisor of Section 6.2 is nef on the actual common
subdivision. The selected family may be the union of both factors' full
obstruction families. -/
theorem parity_center_isNef
    (hpure : «Σ».IsPure) (P : LatticePolytope n) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) (hbound : P.EdgesAtLeast n)
    (t : ι → ℝ)
    (htlower : ∀ i, ((R i).negative.card : ℝ) - 1 ≤ t i)
    (htupper : ∀ i, t i ≤ (R i).fiberDimension + (R i).negative.card - 2)
    (hinactive : ∀ Q : «Σ».PrimitiveRelation, Q.IsCombinatoriallyContractible →
      (∀ i, Q.positive ≠ (R i).positive) →
      2 * (Q.fiberDimension : ℝ) ≤ Q.degree (fun v => (P.integralSupport v : ℝ))) :
    («Σ».selectedFan R hne hdisj).IsNef
      (fun v => «Σ».selectedPullback R (fun w => (P.integralSupport w : ℝ)) v - 1 -
        ∑ i, if v = «Σ».selectedRay R i then t i else 0) := by
  apply «Σ».selected_center_isNef_of_scalar_bounds R hR hne hdisj
    hpure P hP hfan hbound 1 zero_le_one t
  · intro i
    simpa only [one_mul] using sub_nonneg.mpr (htlower i)
  · intro i
    rw [(R i).degree_constant_subtraction]
    have hd := P.contractible_degree_lower_bound hP «Σ» hpure hfan hbound (R i) (hR i)
    have hdim := (R i).contractible_dimension_bound (hR i)
    have hq : 1 ≤ (R i).negative.card := Finset.card_pos.mpr (hne i)
    have hs : (R i).fiberDimension + 1 ≤ n := by omega
    have hsR : (R i).fiberDimension + (1 : ℝ) ≤ n := by exact_mod_cast hs
    have hC := (R i).negativeCoefficientSum_nonneg
    have ht := htlower i
    have hm : (0 : ℝ) ≤ (R i).minimumCoefficient (hne i) := Nat.cast_nonneg _
    simp only [one_mul]
    nlinarith [mul_nonneg hm (sub_nonneg.mpr ht)]
  · intro Q hQ hpos hother
    rw [Q.degree_constant_subtraction]
    have hd := hinactive Q hQ hother
    have hr : (1 : ℝ) ≤ Q.fiberDimension := by exact_mod_cast Q.fiberDimension_pos
    have hC := Q.negativeCoefficientSum_nonneg
    linarith
  · intro i
    have hdim : (n : ℝ) = (R i).fiberDimension + (R i).negative.card +
        «Σ».selectedBaseDimension R i := by exact_mod_cast «Σ».selected_dimension_eq R hR i
    have ht := htupper i
    linarith
  · intro i j hij
    have hdi : (n : ℝ) = (R i).fiberDimension + (R i).negative.card +
        «Σ».selectedBaseDimension R i := by exact_mod_cast «Σ».selected_dimension_eq R hR i
    have hdj : (n : ℝ) = (R j).fiberDimension + (R j).negative.card +
        «Σ».selectedBaseDimension R j := by exact_mod_cast «Σ».selected_dimension_eq R hR j
    have hti := htupper i
    have htj := htupper j
    linarith

include hR in
/-- The first unit-box center in Section 7.4. -/
theorem first_adjoint_center_isNef
    (hpure : «Σ».IsPure) (P : LatticePolytope n) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) (hbound : P.EdgesAtLeast (n + 1))
    (hlarge : ∀ i, n < 2 * (R i).fiberDimension) :
    («Σ».selectedFan R hne hdisj).IsNef
      (fun v => «Σ».selectedPullback R (fun w => (P.integralSupport w : ℝ)) v - 1 / 2 -
        ∑ i, if v = «Σ».selectedRay R i then ((R i).negative.card : ℝ) - 1 else 0) := by
  apply «Σ».selected_center_isNef_of_scalar_bounds R hR hne hdisj
    hpure P hP hfan hbound (1 / 2) (by norm_num)
    (fun i => ((R i).negative.card : ℝ) - 1)
  · intro i
    have hq : (1 : ℝ) ≤ (R i).negative.card := by
      exact_mod_cast Finset.card_pos.mpr (hne i)
    linarith
  · intro i
    rw [(R i).degree_constant_subtraction]
    have hd := P.contractible_degree_lower_bound hP «Σ» hpure hfan hbound (R i) (hR i)
    have hcard := ((«Σ».primitiveCollection_card_bounds (R i).primitive).2)
    rw [(R i).positive_card_eq_fiberDimension_add_one] at hcard
    have hr : (R i).fiberDimension ≤ n := by omega
    have hrR : ((R i).fiberDimension : ℝ) ≤ n := by exact_mod_cast hr
    have hq : (1 : ℝ) ≤ (R i).negative.card := by
      exact_mod_cast Finset.card_pos.mpr (hne i)
    have hC := (R i).negativeCoefficientSum_nonneg
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hm : (0 : ℝ) ≤ (R i).minimumCoefficient (hne i) := Nat.cast_nonneg _
    norm_num only [Nat.cast_add, Nat.cast_one] at hd
    nlinarith [mul_nonneg hm (sub_nonneg.mpr hq)]
  · intro Q hQ hpos hother
    rw [Q.degree_constant_subtraction]
    have hd := P.contractible_degree_lower_bound hP «Σ» hpure hfan hbound Q hQ
    have hcard := («Σ».primitiveCollection_card_bounds Q.primitive).2
    rw [Q.positive_card_eq_fiberDimension_add_one] at hcard
    have hr : Q.fiberDimension ≤ n := by omega
    have hrR : (Q.fiberDimension : ℝ) ≤ n := by exact_mod_cast hr
    have hC := Q.negativeCoefficientSum_nonneg
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    norm_num only [Nat.cast_add, Nat.cast_one] at hd
    linarith
  · intro i
    have hdim : (n : ℝ) = (R i).fiberDimension + (R i).negative.card +
        «Σ».selectedBaseDimension R i := by exact_mod_cast «Σ».selected_dimension_eq R hR i
    have hr : (0 : ℝ) ≤ (R i).fiberDimension := Nat.cast_nonneg _
    have hb : (0 : ℝ) ≤ «Σ».selectedBaseDimension R i := Nat.cast_nonneg _
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  · intro i j hij
    have hdi : (n : ℝ) = (R i).fiberDimension + (R i).negative.card +
        «Σ».selectedBaseDimension R i := by exact_mod_cast «Σ».selected_dimension_eq R hR i
    have hdj : (n : ℝ) = (R j).fiberDimension + (R j).negative.card +
        «Σ».selectedBaseDimension R j := by exact_mod_cast «Σ».selected_dimension_eq R hR j
    have hli : (n : ℝ) < 2 * (R i).fiberDimension := by exact_mod_cast hlarge i
    have hlj : (n : ℝ) < 2 * (R j).fiberDimension := by exact_mod_cast hlarge j
    have hbi : (0 : ℝ) ≤ «Σ».selectedBaseDimension R i := Nat.cast_nonneg _
    have hbj : (0 : ℝ) ≤ «Σ».selectedBaseDimension R j := Nat.cast_nonneg _
    have hqi : (0 : ℝ) ≤ (R i).negative.card := Nat.cast_nonneg _
    have hqj : (0 : ℝ) ≤ (R j).negative.card := Nat.cast_nonneg _
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith

include hR in
/-- The second, inner unit-box center in Section 7.4.  The repair is the
actual fiber inequality of the chosen displacement, with the minimum
coefficient taken from the genuine primitive relation. -/
theorem second_adjoint_center_isNef
    (hpure : «Σ».IsPure) (P : LatticePolytope n) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) (hbound : P.EdgesAtLeast (n + 1))
    (t : ι → ℝ)
    (htlower : ∀ i, 2 * (((R i).negative.card : ℝ) - 1) ≤ t i)
    (htupper : ∀ i, t i ≤ (n : ℝ) - 2 * «Σ».selectedBaseDimension R i - 2)
    (hfiber : ∀ i, 2 * ((R i).fiberDimension : ℝ) + 1 ≤
      (R i).degree (fun v => (P.integralSupport v : ℝ)) +
      (R i).negativeCoefficientSum + ((R i).minimumCoefficient (hne i) : ℝ) *
        (t i + 1 - (R i).negative.card))
    (hinactive : ∀ Q : «Σ».PrimitiveRelation, Q.IsCombinatoriallyContractible →
      (∀ i, Q.positive ≠ (R i).positive) →
      2 * (Q.fiberDimension : ℝ) + 1 ≤
        Q.degree (fun v => (P.integralSupport v : ℝ)) + Q.negativeCoefficientSum) :
    («Σ».selectedFan R hne hdisj).IsNef
      (fun v => «Σ».selectedPullback R (fun w => (P.integralSupport w : ℝ)) v - 3 / 2 -
        ∑ i, if v = «Σ».selectedRay R i then t i else 0) := by
  apply «Σ».selected_center_isNef_of_scalar_bounds R hR hne hdisj
    hpure P hP hfan hbound (3 / 2) (by norm_num) t
  · intro i
    have hq : (1 : ℝ) ≤ (R i).negative.card := by
      exact_mod_cast Finset.card_pos.mpr (hne i)
    have ht := htlower i
    linarith
  · intro i
    rw [(R i).degree_constant_subtraction]
    have hfix := hfiber i
    have hmcard := (R i).minimumCoefficient_mul_card_le_sum (hne i)
    have hr : (1 : ℝ) ≤ (R i).fiberDimension := by exact_mod_cast (R i).fiberDimension_pos
    have hm : (0 : ℝ) ≤ (R i).minimumCoefficient (hne i) := Nat.cast_nonneg _
    nlinarith
  · intro Q hQ hpos hother
    rw [Q.degree_constant_subtraction]
    have hd := hinactive Q hQ hother
    have hr : (1 : ℝ) ≤ Q.fiberDimension := by exact_mod_cast Q.fiberDimension_pos
    have hC := Q.negativeCoefficientSum_nonneg
    linarith
  · intro i
    have ht := htupper i
    have hb : (0 : ℝ) ≤ «Σ».selectedBaseDimension R i := Nat.cast_nonneg _
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  · intro i j hij
    have hti := htupper i
    have htj := htupper j
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hbi : (0 : ℝ) ≤ «Σ».selectedBaseDimension R i := Nat.cast_nonneg _
    have hbj : (0 : ℝ) ≤ «Σ».selectedBaseDimension R j := Nat.cast_nonneg _
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith

end SmoothCompleteFan

end PaperVerification.ToricGeometry
