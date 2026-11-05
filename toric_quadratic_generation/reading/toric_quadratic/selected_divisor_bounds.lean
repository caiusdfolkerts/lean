module

public import toric_quadratic.fan_basics

@[expose] public section

/-!
# The full selected-divisor bounds

These statements collect the cases of Lemma 5.1 into its two complete
conclusions. The first applies to every primitive relation meeting a
selected divisor. The second applies to every contractible primitive
relation meeting two selected divisors, and hence to the manuscript's
extremal relations. All rays, collections, and base dimensions are the
existing objects on the actual selected fan.
-/

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable {ι : Type*} [Fintype ι] (R : ι → «Σ».PrimitiveRelation)
variable (hR : ∀ i, (R i).IsCombinatoriallyContractible)
variable (hne : ∀ i, (R i).negative.Nonempty)
variable (hdisj : «Σ».PairwiseDisjointFoci (fun i => (R i).negative))

include hR in
/-- Lemma 5.1(i), including both one and two selected positive rays. -/
theorem selected_positive_card_bound
    (S : («Σ».selectedFan R hne hdisj).PrimitiveRelation)
    (i : ι) (hi : «Σ».selectedRay R i ∈ S.positive) :
    S.positive.card ≤ «Σ».selectedBaseDimension R i + 2 := by
  classical
  by_cases hex : ∃ j, j ≠ i ∧ «Σ».selectedRay R j ∈ S.positive
  · obtain ⟨j, hji, hj⟩ := hex
    have hpair := «Σ».primitive_selected_pair_eq R hne hdisj S.primitive i j hji.symm hi hj
    have hneRay : «Σ».selectedRay R i ≠ «Σ».selectedRay R j :=
      («Σ».selectedRay_injective R hdisj).ne hji.symm
    rw [hpair, Finset.card_pair hneRay]
    omega
  · exact «Σ».selected_one_positive_card_bound R hR hne hdisj S i hi
      (fun j hji hj => hex ⟨j, hji, hj⟩)

include hR in
/-- Lemma 5.1(ii): the entire positive collection is the selected pair,
and the negative-cardinality bound uses literal integer subtraction. -/
theorem selected_two_positive_full_bound
    (S : («Σ».selectedFan R hne hdisj).PrimitiveRelation)
    (hS : S.IsCombinatoriallyContractible)
    (i j : ι) (hij : i ≠ j)
    (hi : «Σ».selectedRay R i ∈ S.positive)
    (hj : «Σ».selectedRay R j ∈ S.positive) :
    S.positive = {«Σ».selectedRay R i, «Σ».selectedRay R j} ∧
      S.positive.card = 2 ∧
      (n : ℤ) - 1 - «Σ».selectedBaseDimension R i -
        «Σ».selectedBaseDimension R j ≤ (S.negative.card : ℤ) := by
  obtain ⟨hcard, hnegative⟩ := «Σ».selected_two_positive_card_bound R hR hne hdisj
    «Σ».isPure_of_complete S hS i j hij hi hj
  refine ⟨«Σ».primitive_selected_pair_eq R hne hdisj S.primitive i j hij hi hj,
    hcard, ?_⟩
  omega

end PaperVerification.ToricGeometry.SmoothCompleteFan
