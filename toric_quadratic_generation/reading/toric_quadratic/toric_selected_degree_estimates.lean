module

public import PaperVerification.ToricSelectedPositiveDegrees
public import PaperVerification.ToricCorrectionBounds

@[expose] public section

/-!
# Exact degree estimates for corrected support functions

The degree is evaluated on the actual primitive relation of the selected
fan.  Constants, old-ray selections, and selected-ray corrections are kept
separate.  In particular, the lower bounds below do not assume nefness or
the containment of any of the boxes they will be used to construct.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan.PrimitiveRelation

variable {n : ℕ} {Γ : SmoothCompleteFan n} (S : Γ.PrimitiveRelation)

def negativeCoefficientSum : ℝ := ∑ v ∈ S.negative, (S.coefficient v : ℝ)

def negativeWeightOn (D : Finset (Lattice n)) : ℝ :=
  ∑ v ∈ S.negative, if v ∈ D then (S.coefficient v : ℝ) else 0

theorem negativeCoefficientSum_nonneg : 0 ≤ S.negativeCoefficientSum :=
  Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

theorem card_negative_le_coefficientSum :
    (S.negative.card : ℝ) ≤ S.negativeCoefficientSum := by
  have hh : (∑ v ∈ S.negative, (1 : ℝ)) ≤
      ∑ v ∈ S.negative, (S.coefficient v : ℝ) := by
    apply Finset.sum_le_sum
    intro v hv
    exact_mod_cast S.coefficient_pos v hv
  simpa only [negativeCoefficientSum, Finset.sum_const, nsmul_eq_mul, mul_one] using hh

theorem minimumCoefficient_mul_card_le_sum (hne : S.negative.Nonempty) :
    (S.minimumCoefficient hne : ℝ) * S.negative.card ≤ S.negativeCoefficientSum := by
  have hh : (∑ v ∈ S.negative, (S.minimumCoefficient hne : ℝ)) ≤
      ∑ v ∈ S.negative, (S.coefficient v : ℝ) := by
    apply Finset.sum_le_sum
    intro v hv
    exact_mod_cast (S.minimumCoefficient_spec hne).2.2 v hv
  simpa only [negativeCoefficientSum, Finset.sum_const, nsmul_eq_mul, mul_comm] using hh

theorem negativeWeightOn_nonneg (D : Finset (Lattice n)) :
    0 ≤ S.negativeWeightOn D := by
  apply Finset.sum_nonneg
  intro v hv
  split_ifs <;> positivity

theorem card_negative_inter_le_weight (D : Finset (Lattice n)) :
    ((S.negative ∩ D).card : ℝ) ≤ S.negativeWeightOn D := by
  have hh : (∑ v ∈ S.negative, if v ∈ D then (1 : ℝ) else 0) ≤
      S.negativeWeightOn D := by
    apply Finset.sum_le_sum
    intro v hv
    split_ifs
    · exact_mod_cast S.coefficient_pos v hv
    · exact le_rfl
  simpa only [Finset.sum_boole, Finset.filter_mem_eq_inter] using hh

theorem degree_constant (c : ℝ) :
    S.degree (fun _ => c) = c * ((S.positive.card : ℝ) - S.negativeCoefficientSum) := by
  simp only [degree, negativeCoefficientSum, Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.sum_mul]
  ring

theorem positive_card_eq_fiberDimension_add_one :
    S.positive.card = S.fiberDimension + 1 := by
  have hh := (Γ.primitiveCollection_card_bounds S.primitive).1
  unfold fiberDimension
  omega

theorem degree_constant_subtraction (a : Lattice n → ℝ) (c : ℝ) :
    S.degree (fun v => a v - c) = S.degree a -
      c * ((S.fiberDimension : ℝ) + 1 - S.negativeCoefficientSum) := by
  change S.degree (a - (fun _ => c)) = _
  rw [S.degree_sub, S.degree_constant,
    S.positive_card_eq_fiberDimension_add_one, Nat.cast_add, Nat.cast_one]

theorem degree_indicator (D : Finset (Lattice n)) :
    S.degree (fun v => if v ∈ D then 1 else 0) =
      ((S.positive ∩ D).card : ℝ) - S.negativeWeightOn D := by
  simp only [degree, negativeWeightOn, mul_ite, mul_one, mul_zero,
    Finset.sum_boole, Finset.filter_mem_eq_inter]

/-- The full coefficient calculation used in all three correction
arguments, before discarding any helpful negative coefficient. -/
theorem degree_corrected_support {ι : Type*} [Fintype ι]
    (e : ι → Lattice n) (B : Lattice n → ℝ)
    (c side : ℝ) (D : Finset (Lattice n)) (u : ι → ℝ) :
    S.degree (fun v => B v - c - side * (if v ∈ D then 1 else 0) -
      ∑ i, if v = e i then u i else 0) =
      S.degree B - c * ((S.positive.card : ℝ) - S.negativeCoefficientSum) -
        side * (((S.positive ∩ D).card : ℝ) - S.negativeWeightOn D) -
        (∑ i, if e i ∈ S.positive then u i else 0) +
        ∑ i, if e i ∈ S.negative then (S.coefficient (e i) : ℝ) * u i else 0 := by
  rw [S.degree_sub_finite_ray_corrections]
  have hbase : S.degree (fun v => B v - c - side * (if v ∈ D then 1 else 0)) =
      S.degree B - c * ((S.positive.card : ℝ) - S.negativeCoefficientSum) -
        side * (((S.positive ∩ D).card : ℝ) - S.negativeWeightOn D) := by
    change S.degree ((B - (fun _ => c)) -
      side • (fun v => if v ∈ D then 1 else 0)) = _
    rw [S.degree_sub, S.degree_sub, S.degree_smul,
      S.degree_constant, S.degree_indicator]
  rw [hbase]

end SmoothCompleteFan.PrimitiveRelation

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable {ι : Type*} [Fintype ι] (R : ι → «Σ».PrimitiveRelation)
variable (hR : ∀ i, (R i).IsCombinatoriallyContractible)
variable (hne : ∀ i, (R i).negative.Nonempty)
variable (hdisj : «Σ».PairwiseDisjointFoci (fun i => (R i).negative))

/-- A contractible relation with a positive selected ray has no negative
selected ray.  This is forced by actual cone incidence, not by a sign
convention on the relation. -/
theorem selected_negative_empty_if_positive
    (S : («Σ».selectedFan R hne hdisj).PrimitiveRelation)
    (hS : S.IsCombinatoriallyContractible) (i : ι)
    (hi : «Σ».selectedRay R i ∈ S.positive) :
    ∀ j, «Σ».selectedRay R j ∉ S.negative := by
  have hex : ∃ x ∈ S.positive, x ≠ «Σ».selectedRay R i := by
    by_contra hn
    push_neg at hn
    have hsub : S.positive ⊆ {«Σ».selectedRay R i} := by
      intro x hx
      exact Finset.mem_singleton.mpr (hn x hx)
    have hcard := Finset.card_le_card hsub
    have htwo := ((«Σ».selectedFan R hne hdisj).primitiveCollection_card_bounds S.primitive).1
    simp only [Finset.card_singleton] at hcard
    omega
  obtain ⟨x, hx, hxi⟩ := hex
  have hcone := S.contractible_core_cone hS hx
  have hie : «Σ».selectedRay R i ∈ S.positive.erase x ∪ S.negative :=
    Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hxi.symm, hi⟩)
  intro j hj
  by_cases hji : j = i
  · subst j
    exact Finset.disjoint_left.mp S.disjoint hi hj
  · exact «Σ».selected_no_common_rays R hne hdisj i j (Ne.symm hji) hcone hie
      (Finset.mem_union_right _ hj)

theorem selected_correction_sum_one
    (S : («Σ».selectedFan R hne hdisj).PrimitiveRelation)
    (i : ι) (hi : «Σ».selectedRay R i ∈ S.positive)
    (hother : ∀ j, j ≠ i → «Σ».selectedRay R j ∉ S.positive) (u : ι → ℝ) :
    (∑ j, if «Σ».selectedRay R j ∈ S.positive then u j else 0) = u i := by
  rw [Finset.sum_eq_single i]
  · simp only [hi, if_true]
  · intro j hj hji
    simp only [hother j hji, if_false]
  · simp

theorem selected_correction_sum_two
    (S : («Σ».selectedFan R hne hdisj).PrimitiveRelation)
    (i j : ι) (hij : i ≠ j)
    (hi : «Σ».selectedRay R i ∈ S.positive)
    (hj : «Σ».selectedRay R j ∈ S.positive) (u : ι → ℝ) :
    (∑ k, if «Σ».selectedRay R k ∈ S.positive then u k else 0) = u i + u j := by
  have hP := «Σ».primitive_selected_pair_eq R hne hdisj S.primitive i j hij hi hj
  have hinj := «Σ».selectedRay_injective R hdisj
  have hterm (k : ι) :
      (if «Σ».selectedRay R k ∈ S.positive then u k else 0) =
        (if k = i then u i else 0) + (if k = j then u j else 0) := by
    by_cases hki : k = i
    · subst k
      simp only [hP, Finset.mem_insert, Finset.mem_singleton, hinj.eq_iff,
        true_or, if_true, hij, if_false, add_zero]
    · by_cases hkj : k = j
      · subst k
        simp only [hP, Finset.mem_insert, Finset.mem_singleton, hinj.eq_iff,
          or_true, if_true, hij.symm, if_false, zero_add]
      · simp only [hP, Finset.mem_insert, Finset.mem_singleton, hinj.eq_iff,
          hki, hkj, false_or, if_false, add_zero]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_add_distrib]
  simp

include hR in
/-- The one-positive-selected-ray lower bound, retaining an arbitrary
constant and an arbitrary nonnegative box side. -/
theorem selected_one_positive_degree_bound
    (S : («Σ».selectedFan R hne hdisj).PrimitiveRelation)
    (hS : S.IsCombinatoriallyContractible) (i : ι)
    (hi : «Σ».selectedRay R i ∈ S.positive)
    (hother : ∀ j, j ≠ i → «Σ».selectedRay R j ∉ S.positive)
    (B : Lattice n → ℝ) (bound c side : ℝ) (hc : 0 ≤ c) (hside : 0 ≤ side)
    (hB : bound ≤ S.degree B) (D : Finset (Lattice n))
    (hD : ∀ j, «Σ».selectedRay R j ∉ D) (u : ι → ℝ) :
    bound - c * ((«Σ».selectedBaseDimension R i : ℝ) + 2) -
      side * ((«Σ».selectedBaseDimension R i : ℝ) + 1) - u i ≤
    S.degree (fun v => B v - c - side * (if v ∈ D then 1 else 0) -
      ∑ j, if v = «Σ».selectedRay R j then u j else 0) := by
  have hneg := «Σ».selected_negative_empty_if_positive R hne hdisj S hS i hi
  rw [S.degree_corrected_support,
    «Σ».selected_correction_sum_one R hne hdisj S i hi hother u]
  simp only [hneg, if_false, Finset.sum_const_zero, add_zero]
  have hproper : S.positive ∩ D ⊂ S.positive := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, ?_⟩
    intro hh
    exact hD i (Finset.mem_inter.mp (hh.symm ▸ hi)).2
  have hcard := Finset.card_lt_card hproper
  have hcardR : ((S.positive ∩ D).card : ℝ) + 1 ≤ (S.positive.card : ℝ) := by
    have hh : (S.positive ∩ D).card + 1 ≤ S.positive.card := by omega
    exact_mod_cast hh
  have hs := «Σ».selected_one_positive_card_bound R hR hne hdisj S i hi hother
  have hsR : (S.positive.card : ℝ) ≤ («Σ».selectedBaseDimension R i : ℝ) + 2 := by
    exact_mod_cast hs
  have hC := S.negativeCoefficientSum_nonneg
  have hNS := S.negativeWeightOn_nonneg D
  nlinarith [mul_nonneg hc hC, mul_nonneg hside hNS,
    mul_nonneg hc (sub_nonneg.mpr hsR),
    mul_nonneg hside (sub_nonneg.mpr (le_trans hcardR hsR))]

/-- The two-positive estimate retains the weighted negative selection.
This term is essential in the second estimate of Proposition 5.2. -/
theorem selected_two_positive_degree_bound
    (S : («Σ».selectedFan R hne hdisj).PrimitiveRelation)
    (hS : S.IsCombinatoriallyContractible) (i j : ι) (hij : i ≠ j)
    (hi : «Σ».selectedRay R i ∈ S.positive)
    (hj : «Σ».selectedRay R j ∈ S.positive)
    (B : Lattice n → ℝ) (bound c side : ℝ) (hc : 0 ≤ c)
    (hB : bound ≤ S.degree B) (D : Finset (Lattice n))
    (hD : ∀ k, «Σ».selectedRay R k ∉ D) (u : ι → ℝ) :
    bound - 2 * c + c * (S.negative.card : ℝ) + side * S.negativeWeightOn D -
      u i - u j ≤
    S.degree (fun v => B v - c - side * (if v ∈ D then 1 else 0) -
      ∑ k, if v = «Σ».selectedRay R k then u k else 0) := by
  have hP := «Σ».primitive_selected_pair_eq R hne hdisj S.primitive i j hij hi hj
  have hef := («Σ».selectedRay_injective R hdisj).ne hij
  have hneg := «Σ».selected_negative_empty_if_positive R hne hdisj S hS i hi
  have hPD : S.positive ∩ D = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨hvP, hvD⟩ := Finset.mem_inter.mp hv
    rcases (by simpa only [hP, Finset.mem_insert, Finset.mem_singleton] using hvP :
      v = «Σ».selectedRay R i ∨ v = «Σ».selectedRay R j) with h | h
    · exact hD i (h ▸ hvD)
    · exact hD j (h ▸ hvD)
  rw [S.degree_corrected_support,
    «Σ».selected_correction_sum_two R hne hdisj S i j hij hi hj u, hPD]
  simp only [hneg, if_false, Finset.sum_const_zero, add_zero,
    Finset.card_empty, Nat.cast_zero, hP, Finset.card_pair hef, Nat.cast_ofNat,
    zero_sub, mul_neg, sub_neg_eq_add]
  have hC := S.card_negative_le_coefficientSum
  nlinarith [mul_nonneg hc (sub_nonneg.mpr hC)]

end SmoothCompleteFan

end PaperVerification.ToricGeometry
