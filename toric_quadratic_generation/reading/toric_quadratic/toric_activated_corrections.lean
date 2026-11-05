module

public import PaperVerification.ToricObstructionSelection
public import PaperVerification.ToricNefBoxGeometry

@[expose] public section

/-!
# The exhaustive activated family and its actual ceiling corrections

Activation is defined by negative degree of the integral old support
function, over every contractible primitive collection.  The repair is an
integer ceiling divided by the actual least positive focus coefficient.
The degree budgets are derived from the original edge lengths.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

abbrev ActivatedIndices (a : Lattice n → ℤ) :=
  «Σ».selectedPrimitiveCollections (fun Q => Q.degree (fun v => (a v : ℝ)) < 0)

def activatedRelation (a : Lattice n → ℤ) (i : «Σ».ActivatedIndices a) : «Σ».PrimitiveRelation :=
  «Σ».selectionRelation (fun Q => Q.degree (fun v => (a v : ℝ)) < 0) i

theorem activatedRelation_contractible (a : Lattice n → ℤ) (i : «Σ».ActivatedIndices a) :
    («Σ».activatedRelation a i).IsCombinatoriallyContractible :=
  «Σ».selectionRelation_contractible _ i

theorem activatedRelation_negative (a : Lattice n → ℤ) (i : «Σ».ActivatedIndices a) :
    («Σ».activatedRelation a i).degree (fun v => (a v : ℝ)) < 0 :=
  «Σ».selectionRelation_test _ i

theorem activatedRelation_exhaustive (a : Lattice n → ℤ) (Q : «Σ».PrimitiveRelation) :
    (∃ i : «Σ».ActivatedIndices a, Q.positive = («Σ».activatedRelation a i).positive) ↔
      Q.IsCombinatoriallyContractible ∧ Q.degree (fun v => (a v : ℝ)) < 0 := by
  apply «Σ».selectionRelation_exhaustive
  intro R S hpos
  rw [R.degree_unique S hpos]

theorem activatedRelation_unselected_nonneg (a : Lattice n → ℤ)
    (Q : «Σ».PrimitiveRelation) (hQ : Q.IsCombinatoriallyContractible)
    (hother : ∀ i : «Σ».ActivatedIndices a,
      Q.positive ≠ («Σ».activatedRelation a i).positive) :
    0 ≤ Q.degree (fun v => (a v : ℝ)) := by
  by_contra hh
  obtain ⟨i, hi⟩ := («Σ».activatedRelation_exhaustive a Q).mpr ⟨hQ, lt_of_not_ge hh⟩
  exact hother i hi

def activatedCorrection (a : Lattice n → ℤ)
    (hne : ∀ i : «Σ».ActivatedIndices a, («Σ».activatedRelation a i).negative.Nonempty)
    (i : «Σ».ActivatedIndices a) : ℤ :=
  Int.ceil (((-(«Σ».activatedRelation a i).integerDegree a : ℤ) : ℝ) /
    ((«Σ».activatedRelation a i).minimumCoefficient (hne i) : ℝ))

theorem activatedCorrection_bounds (a : Lattice n → ℤ)
    (hne : ∀ i : «Σ».ActivatedIndices a, («Σ».activatedRelation a i).negative.Nonempty)
    (i : «Σ».ActivatedIndices a) :
    1 ≤ «Σ».activatedCorrection a hne i ∧
      «Σ».activatedCorrection a hne i ≤ -(«Σ».activatedRelation a i).integerDegree a ∧
      0 ≤ («Σ».activatedRelation a i).integerDegree a +
        ((«Σ».activatedRelation a i).minimumCoefficient (hne i) : ℤ) *
          «Σ».activatedCorrection a hne i := by
  let Q := «Σ».activatedRelation a i
  have hneg := «Σ».activatedRelation_negative a i
  rw [← Q.integerDegree_cast] at hneg
  have hnegZ : Q.integerDegree a < 0 := by exact_mod_cast hneg
  have hδ : (0 : ℤ) < -Q.integerDegree a := by omega
  have hm : (1 : ℤ) ≤ Q.minimumCoefficient (hne i) := by
    exact_mod_cast (Q.minimumCoefficient_spec (hne i)).1
  obtain ⟨hpos, hupper, hrepair⟩ :=
    positive_ceil_correction (-Q.integerDegree a) (Q.minimumCoefficient (hne i)) hδ hm
  change 1 ≤ _ ∧ _ ≤ _ ∧ 0 ≤ _
  have hpos' : 1 ≤ «Σ».activatedCorrection a hne i := by
    simpa only [activatedCorrection, Int.cast_natCast] using hpos
  have hupper' : «Σ».activatedCorrection a hne i ≤ -Q.integerDegree a := by
    simpa only [activatedCorrection, Int.cast_natCast] using hupper
  have hrepair' : -Q.integerDegree a ≤
      (Q.minimumCoefficient (hne i) : ℤ) * «Σ».activatedCorrection a hne i := by
    simpa only [activatedCorrection, Int.cast_natCast] using hrepair
  dsimp only [Q] at hupper' hrepair'
  exact ⟨hpos', hupper', by omega⟩

theorem activatedCorrection_real_bounds (a : Lattice n → ℤ)
    (hne : ∀ i : «Σ».ActivatedIndices a, («Σ».activatedRelation a i).negative.Nonempty)
    (i : «Σ».ActivatedIndices a) :
    0 ≤ («Σ».activatedCorrection a hne i : ℝ) ∧
      («Σ».activatedCorrection a hne i : ℝ) ≤
        -(«Σ».activatedRelation a i).degree (fun v => (a v : ℝ)) ∧
      0 ≤ («Σ».activatedRelation a i).degree (fun v => (a v : ℝ)) +
        ((«Σ».activatedRelation a i).minimumCoefficient (hne i) : ℝ) *
          («Σ».activatedCorrection a hne i : ℝ) := by
  obtain ⟨hpos, hup, hrepair⟩ := «Σ».activatedCorrection_bounds a hne i
  have hposR : (1 : ℝ) ≤ «Σ».activatedCorrection a hne i := by exact_mod_cast hpos
  have hupR : («Σ».activatedCorrection a hne i : ℝ) ≤
      -((«Σ».activatedRelation a i).integerDegree a : ℝ) := by exact_mod_cast hup
  have hrepairR : (0 : ℝ) ≤ ((«Σ».activatedRelation a i).integerDegree a : ℝ) +
      ((«Σ».activatedRelation a i).minimumCoefficient (hne i) : ℝ) *
        («Σ».activatedCorrection a hne i : ℝ) := by exact_mod_cast hrepair
  rw [(«Σ».activatedRelation a i).integerDegree_cast] at hupR hrepairR
  exact ⟨zero_le_one.trans hposR, hupR, hrepairR⟩

def sideTwoOldSupport («_Σ» : SmoothCompleteFan n)
    (P : LatticePolytope n) (D : Finset (Lattice n)) : Lattice n → ℤ :=
  fun v => P.integralSupport v - if v ∈ D then 2 else 0

def innerUnitOldSupport («_Σ» : SmoothCompleteFan n)
    (P : LatticePolytope n) (D : Finset (Lattice n)) : Lattice n → ℤ :=
  fun v => P.integralSupport v - 1 - if v ∈ D then 1 else 0

theorem sideTwoOldSupport_cast (P : LatticePolytope n) (D : Finset (Lattice n)) :
    (fun v => («Σ».sideTwoOldSupport P D v : ℝ)) =
      fun v => (P.integralSupport v : ℝ) - 2 * (if v ∈ D then 1 else 0) := by
  funext v
  by_cases hv : v ∈ D <;> simp [sideTwoOldSupport, hv]

theorem innerUnitOldSupport_cast (P : LatticePolytope n) (D : Finset (Lattice n)) :
    (fun v => («Σ».innerUnitOldSupport P D v : ℝ)) =
      fun v => (P.integralSupport v : ℝ) - 1 - (if v ∈ D then 1 else 0) := by
  funext v
  by_cases hv : v ∈ D <;> simp [innerUnitOldSupport, hv]

theorem sideTwoOldSupport_degree (P : LatticePolytope n)
    (D : Finset (Lattice n)) (Q : «Σ».PrimitiveRelation) :
    Q.degree (fun v => («Σ».sideTwoOldSupport P D v : ℝ)) =
      Q.degree (fun v => (P.integralSupport v : ℝ)) -
        2 * (((D ∩ Q.positive).card : ℝ) - Q.negativeWeightOn D) := by
  rw [«Σ».sideTwoOldSupport_cast]
  have he : (fun v => (P.integralSupport v : ℝ) -
      2 * (if v ∈ D then 1 else 0)) =
      (fun v => (P.integralSupport v : ℝ)) -
        (2 : ℝ) • (fun v => if v ∈ D then 1 else 0) := by
    funext v
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [he]
  rw [Q.degree_sub, Q.degree_smul, Q.degree_indicator, Finset.inter_comm Q.positive D]

theorem innerUnitOldSupport_degree (P : LatticePolytope n)
    (D : Finset (Lattice n)) (Q : «Σ».PrimitiveRelation) :
    Q.degree (fun v => («Σ».innerUnitOldSupport P D v : ℝ)) =
      Q.degree (fun v => (P.integralSupport v : ℝ)) -
        ((Q.fiberDimension : ℝ) + 1 - Q.negativeCoefficientSum) -
        (((D ∩ Q.positive).card : ℝ) - Q.negativeWeightOn D) := by
  rw [«Σ».innerUnitOldSupport_cast]
  change Q.degree ((fun v => (P.integralSupport v : ℝ) - 1) -
    (fun v => if v ∈ D then 1 else 0)) = _
  rw [Q.degree_sub, Q.degree_constant_subtraction, Q.degree_indicator,
    Finset.inter_comm Q.positive D, one_mul]

theorem selection_positive_card_le_fiberDimension
    {σ D : Finset (Lattice n)} (hσ : σ ∈ «Σ».cones) (hD : D ⊆ σ)
    (Q : «Σ».PrimitiveRelation) : (D ∩ Q.positive).card ≤ Q.fiberDimension := by
  rw [Finset.inter_comm D Q.positive]
  exact (Finset.card_le_card (Finset.inter_subset_inter_left hD)).trans
    (Q.positive_rays_in_cone_bound hσ)

/-- Every side-two activated class is one of the paper's original
obstructions, and has large fiber dimension. -/
theorem side_two_activated_obstruction
    (hpure : «Σ».IsPure) (P : LatticePolytope n) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) (hbound : P.EdgesAtLeast n)
    {σ D : Finset (Lattice n)} (hσ : σ ∈ «Σ».cones) (hD : D ⊆ σ)
    (i : «Σ».ActivatedIndices («Σ».sideTwoOldSupport P D)) :
    («Σ».activatedRelation («Σ».sideTwoOldSupport P D) i).degree
        (fun v => (P.integralSupport v : ℝ)) <
      2 * ((«Σ».activatedRelation («Σ».sideTwoOldSupport P D) i).fiberDimension : ℝ) ∧
    n < 2 * («Σ».activatedRelation («Σ».sideTwoOldSupport P D) i).fiberDimension := by
  let Q := «Σ».activatedRelation («Σ».sideTwoOldSupport P D) i
  have hQ := «Σ».activatedRelation_contractible («Σ».sideTwoOldSupport P D) i
  have hneg := «Σ».activatedRelation_negative («Σ».sideTwoOldSupport P D) i
  rw [«Σ».sideTwoOldSupport_degree] at hneg
  have hA : ((D ∩ Q.positive).card : ℝ) ≤ Q.fiberDimension := by
    exact_mod_cast «Σ».selection_positive_card_le_fiberDimension hσ hD Q
  have hNS := Q.negativeWeightOn_nonneg D
  have hd := P.contractible_degree_lower_bound hP «Σ» hpure hfan hbound Q hQ
  have hobs : Q.degree (fun v => (P.integralSupport v : ℝ)) <
      2 * (Q.fiberDimension : ℝ) := by linarith
  refine ⟨hobs, ?_⟩
  exact_mod_cast hd.trans_lt hobs

theorem side_two_activated_deficit_budget
    (hpure : «Σ».IsPure) (P : LatticePolytope n) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) (hbound : P.EdgesAtLeast n)
    (D : Finset (Lattice n)) (Q : «Σ».PrimitiveRelation)
    (hQ : Q.IsCombinatoriallyContractible) :
    -Q.degree (fun v => («Σ».sideTwoOldSupport P D v : ℝ)) ≤
      2 * ((D ∩ Q.positive).card : ℝ) - 2 * ((Q.negative ∩ D).card : ℝ) - n := by
  rw [«Σ».sideTwoOldSupport_degree]
  have hd := P.contractible_degree_lower_bound hP «Σ» hpure hfan hbound Q hQ
  have hNS := Q.card_negative_inter_le_weight D
  linarith

/-- Every inner-unit activated class satisfies exactly the original
adjoint obstruction (12), and has large fiber dimension. -/
theorem inner_unit_activated_obstruction
    (hpure : «Σ».IsPure) (P : LatticePolytope n) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) (hbound : P.EdgesAtLeast (n + 1))
    {σ D : Finset (Lattice n)} (hσ : σ ∈ «Σ».cones) (hD : D ⊆ σ)
    (i : «Σ».ActivatedIndices («Σ».innerUnitOldSupport P D)) :
    0 < 2 * ((«Σ».activatedRelation («Σ».innerUnitOldSupport P D) i).fiberDimension : ℝ) + 1 -
      («Σ».activatedRelation («Σ».innerUnitOldSupport P D) i).degree
        (fun v => (P.integralSupport v : ℝ)) -
      («Σ».activatedRelation («Σ».innerUnitOldSupport P D) i).negativeCoefficientSum ∧
    n < 2 * («Σ».activatedRelation («Σ».innerUnitOldSupport P D) i).fiberDimension := by
  let Q := «Σ».activatedRelation («Σ».innerUnitOldSupport P D) i
  have hQ := «Σ».activatedRelation_contractible («Σ».innerUnitOldSupport P D) i
  have hneg := «Σ».activatedRelation_negative («Σ».innerUnitOldSupport P D) i
  rw [«Σ».innerUnitOldSupport_degree] at hneg
  have hA : ((D ∩ Q.positive).card : ℝ) ≤ Q.fiberDimension := by
    exact_mod_cast «Σ».selection_positive_card_le_fiberDimension hσ hD Q
  have hNS := Q.negativeWeightOn_nonneg D
  have hC := Q.negativeCoefficientSum_nonneg
  have hd := P.contractible_degree_lower_bound hP «Σ» hpure hfan hbound Q hQ
  norm_num only [Nat.cast_add, Nat.cast_one] at hd
  have hobs : 0 < 2 * (Q.fiberDimension : ℝ) + 1 -
      Q.degree (fun v => (P.integralSupport v : ℝ)) - Q.negativeCoefficientSum := by linarith
  refine ⟨hobs, ?_⟩
  have hh : (n : ℝ) < 2 * (Q.fiberDimension : ℝ) := by linarith
  exact_mod_cast hh

theorem inner_unit_activated_deficit_budget
    (hpure : «Σ».IsPure) (P : LatticePolytope n) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) (hbound : P.EdgesAtLeast (n + 1))
    {σ D : Finset (Lattice n)} (hσ : σ ∈ «Σ».cones) (hD : D ⊆ σ)
    (Q : «Σ».PrimitiveRelation) (hQ : Q.IsCombinatoriallyContractible) :
    -Q.degree (fun v => («Σ».innerUnitOldSupport P D v : ℝ)) ≤
      2 * (Q.fiberDimension : ℝ) - n - Q.negative.card := by
  rw [«Σ».innerUnitOldSupport_degree]
  have hd := P.contractible_degree_lower_bound hP «Σ» hpure hfan hbound Q hQ
  have hA : ((D ∩ Q.positive).card : ℝ) ≤ Q.fiberDimension := by
    exact_mod_cast «Σ».selection_positive_card_le_fiberDimension hσ hD Q
  have hC := Q.card_negative_le_coefficientSum
  have hNS := Q.negativeWeightOn_nonneg D
  norm_num only [Nat.cast_add, Nat.cast_one] at hd
  linarith

end SmoothCompleteFan

end PaperVerification.ToricGeometry
