module

public import PaperVerification.ToricActivatedCorrections

@[expose] public section

/-!
# Canonical corrected supports at an outside cone

All activated classes and all correction coefficients are constructed from
the actual integral support. The conclusions contain no supplied
contractible-class degree bounds, correction family, or nefness premise.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem exists_outside_side_two_correction
    (hpure : «Σ».IsPure) (P : LatticePolytope n) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) (hbound : P.EdgesAtLeast n)
    (σ D : Finset (Lattice n)) (hσ : σ ∈ «Σ».cones) (hDσ : D ⊆ σ)
    (houtside : ∀ Q : «Σ».PrimitiveRelation, Q.IsCombinatoriallyContractible →
      Q.degree (fun v => (P.integralSupport v : ℝ)) < 2 * (Q.fiberDimension : ℝ) →
      ¬ Q.negative ⊆ σ) :
    ∃ (Γ : SmoothCompleteFan n) (F : Lattice n → ℝ),
      Γ.IsNef F ∧ «Σ».rays ⊆ Γ.rays ∧ σ ∈ Γ.cones ∧
      (∀ v ∈ σ, F v = (P.integralSupport v : ℝ) - 2 * (if v ∈ D then 1 else 0)) ∧
      (∀ v ∈ «Σ».rays, F v ≤ (P.integralSupport v : ℝ) - 2 * (if v ∈ D then 1 else 0)) := by
  let a := «Σ».sideTwoOldSupport P D
  let R := «Σ».activatedRelation a
  have hR (i : «Σ».ActivatedIndices a) : (R i).IsCombinatoriallyContractible :=
    «Σ».activatedRelation_contractible a i
  have hobs (i : «Σ».ActivatedIndices a) :
      (R i).degree (fun v => (P.integralSupport v : ℝ)) < 2 * ((R i).fiberDimension : ℝ) :=
    («Σ».side_two_activated_obstruction hpure P hP hfan hbound hσ hDσ i).1
  have hlarge (i : «Σ».ActivatedIndices a) : n < 2 * (R i).fiberDimension :=
    («Σ».side_two_activated_obstruction hpure P hP hfan hbound hσ hDσ i).2
  have hdisj : «Σ».PairwiseDisjointFoci (fun i => (R i).negative) :=
    «Σ».selectionRelation_disjoint_of_large hpure _ hlarge
  have hout (i : «Σ».ActivatedIndices a) : ¬ (R i).negative ⊆ σ :=
    houtside (R i) (hR i) (hobs i)
  have hne (i : «Σ».ActivatedIndices a) : (R i).negative.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hh
    apply hout i
    rw [hh]
    exact Finset.empty_subset _
  let τ : «Σ».ActivatedIndices a → ℝ := fun i => («Σ».activatedCorrection a hne i : ℝ)
  let Γ := «Σ».selectedFan R hne hdisj
  let aR : Lattice n → ℝ := fun v => (a v : ℝ)
  have haR : aR = fun v => (P.integralSupport v : ℝ) - 2 * (if v ∈ D then 1 else 0) :=
    «Σ».sideTwoOldSupport_cast P D
  let F := simultaneousSupport (fun i => (R i).negative) aR τ
  have hτ0 (i : «Σ».ActivatedIndices a) : 0 ≤ τ i :=
    («Σ».activatedCorrection_real_bounds a hne i).1
  have hbudget (i : «Σ».ActivatedIndices a) : τ i ≤
      2 * ((D ∩ (R i).positive).card : ℝ) -
        2 * (((R i).negative ∩ D).card : ℝ) - n :=
    («Σ».activatedCorrection_real_bounds a hne i).2.1.trans
      («Σ».side_two_activated_deficit_budget hpure P hP hfan hbound D (R i) (hR i))
  have hfiber (i : «Σ».ActivatedIndices a) : τ i ≤ 2 * ((R i).fiberDimension : ℝ) - n := by
    have hh := hbudget i
    have hA : ((D ∩ (R i).positive).card : ℝ) ≤ (R i).fiberDimension := by
      exact_mod_cast «Σ».selection_positive_card_le_fiberDimension hσ hDσ (R i)
    have hk : (0 : ℝ) ≤ ((R i).negative ∩ D).card := Nat.cast_nonneg _
    linarith
  have hrepair (i : «Σ».ActivatedIndices a) : 0 ≤
      (R i).degree (fun v => (P.integralSupport v : ℝ) - 2 * (if v ∈ D then 1 else 0)) +
        ((R i).minimumCoefficient (hne i) : ℝ) * τ i := by
    have hh := («Σ».activatedCorrection_real_bounds a hne i).2.2
    change 0 ≤ (R i).degree aR + _ at hh
    rw [haR] at hh
    exact hh
  have hinactive (Q : «Σ».PrimitiveRelation) (hQ : Q.IsCombinatoriallyContractible)
      (hother : ∀ i : «Σ».ActivatedIndices a, Q.positive ≠ (R i).positive) :
      0 ≤ Q.degree (fun v => (P.integralSupport v : ℝ) - 2 * (if v ∈ D then 1 else 0)) := by
    have hh := «Σ».activatedRelation_unselected_nonneg a Q hQ hother
    change 0 ≤ Q.degree aR at hh
    rw [haR] at hh
    exact hh
  have hF : Γ.IsNef F := by
    change Γ.IsNef (simultaneousSupport (fun i => (R i).negative) aR τ)
    rw [haR]
    exact «Σ».outside_side_two_corrected_isNef R hR hne hdisj
      hpure P hP hfan hbound σ D hσ hDσ hout τ hτ0 hfiber hbudget hrepair hinactive
  refine ⟨Γ, F, hF, «Σ».old_rays_subset_selected R hne hdisj,
    «Σ».outside_cone_mem_selected R hne hdisj hσ hout, ?_, ?_⟩
  · intro v hv
    change simultaneousSupport (fun i => (R i).negative) aR τ v = _
    rw [«Σ».selected_support_eq_old_on_outside_cone R aR τ hσ hout hv]
    exact congrFun haR v
  · intro v hv
    have hh := «Σ».selected_support_le_old_on_rays R hne hdisj aR τ hτ0 hv
    rw [congrFun haR v] at hh
    exact hh

theorem exists_outside_inner_unit_correction
    (hpure : «Σ».IsPure) (P : LatticePolytope n) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) (hbound : P.EdgesAtLeast (n + 1))
    (σ D : Finset (Lattice n)) (hσ : σ ∈ «Σ».cones) (hDσ : D ⊆ σ)
    (houtside : ∀ Q : «Σ».PrimitiveRelation, Q.IsCombinatoriallyContractible →
      0 < 2 * (Q.fiberDimension : ℝ) + 1 -
        Q.degree (fun v => (P.integralSupport v : ℝ)) - Q.negativeCoefficientSum →
      ¬ Q.negative ⊆ σ) :
    ∃ (Γ : SmoothCompleteFan n) (F : Lattice n → ℝ),
      Γ.IsNef F ∧ «Σ».rays ⊆ Γ.rays ∧ σ ∈ Γ.cones ∧
      (∀ v ∈ σ, F v = (P.integralSupport v : ℝ) - 1 - (if v ∈ D then 1 else 0)) ∧
      (∀ v ∈ «Σ».rays, F v ≤ (P.integralSupport v : ℝ) - 1 - (if v ∈ D then 1 else 0)) := by
  let a := «Σ».innerUnitOldSupport P D
  let R := «Σ».activatedRelation a
  have hR (i : «Σ».ActivatedIndices a) : (R i).IsCombinatoriallyContractible :=
    «Σ».activatedRelation_contractible a i
  have hobs (i : «Σ».ActivatedIndices a) : 0 < 2 * ((R i).fiberDimension : ℝ) + 1 -
      (R i).degree (fun v => (P.integralSupport v : ℝ)) - (R i).negativeCoefficientSum :=
    («Σ».inner_unit_activated_obstruction hpure P hP hfan hbound hσ hDσ i).1
  have hlarge (i : «Σ».ActivatedIndices a) : n < 2 * (R i).fiberDimension :=
    («Σ».inner_unit_activated_obstruction hpure P hP hfan hbound hσ hDσ i).2
  have hdisj : «Σ».PairwiseDisjointFoci (fun i => (R i).negative) :=
    «Σ».selectionRelation_disjoint_of_large hpure _ hlarge
  have hout (i : «Σ».ActivatedIndices a) : ¬ (R i).negative ⊆ σ :=
    houtside (R i) (hR i) (hobs i)
  have hne (i : «Σ».ActivatedIndices a) : (R i).negative.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hh
    apply hout i
    rw [hh]
    exact Finset.empty_subset _
  let τ : «Σ».ActivatedIndices a → ℝ := fun i => («Σ».activatedCorrection a hne i : ℝ)
  let Γ := «Σ».selectedFan R hne hdisj
  let aR : Lattice n → ℝ := fun v => (a v : ℝ)
  have haR : aR = fun v => (P.integralSupport v : ℝ) - 1 - (if v ∈ D then 1 else 0) :=
    «Σ».innerUnitOldSupport_cast P D
  let F := simultaneousSupport (fun i => (R i).negative) aR τ
  have hτ0 (i : «Σ».ActivatedIndices a) : 0 ≤ τ i :=
    («Σ».activatedCorrection_real_bounds a hne i).1
  have hupper (i : «Σ».ActivatedIndices a) : τ i ≤
      2 * ((R i).fiberDimension : ℝ) - n - (R i).negative.card :=
    («Σ».activatedCorrection_real_bounds a hne i).2.1.trans
      («Σ».inner_unit_activated_deficit_budget hpure P hP hfan hbound hσ hDσ (R i) (hR i))
  have hrepair (i : «Σ».ActivatedIndices a) : 0 ≤
      (R i).degree (fun v => (P.integralSupport v : ℝ) - 1 - (if v ∈ D then 1 else 0)) +
        ((R i).minimumCoefficient (hne i) : ℝ) * τ i := by
    have hh := («Σ».activatedCorrection_real_bounds a hne i).2.2
    change 0 ≤ (R i).degree aR + _ at hh
    rw [haR] at hh
    exact hh
  have hinactive (Q : «Σ».PrimitiveRelation) (hQ : Q.IsCombinatoriallyContractible)
      (hother : ∀ i : «Σ».ActivatedIndices a, Q.positive ≠ (R i).positive) :
      0 ≤ Q.degree (fun v => (P.integralSupport v : ℝ) - 1 - (if v ∈ D then 1 else 0)) := by
    have hh := «Σ».activatedRelation_unselected_nonneg a Q hQ hother
    change 0 ≤ Q.degree aR at hh
    rw [haR] at hh
    exact hh
  have hF : Γ.IsNef F := by
    change Γ.IsNef (simultaneousSupport (fun i => (R i).negative) aR τ)
    rw [haR]
    exact «Σ».outside_inner_unit_corrected_isNef R hR hne hdisj
      hpure P hP hfan hbound σ D hσ hDσ hout τ hτ0 hupper hrepair hinactive
  refine ⟨Γ, F, hF, «Σ».old_rays_subset_selected R hne hdisj,
    «Σ».outside_cone_mem_selected R hne hdisj hσ hout, ?_, ?_⟩
  · intro v hv
    change simultaneousSupport (fun i => (R i).negative) aR τ v = _
    rw [«Σ».selected_support_eq_old_on_outside_cone R aR τ hσ hout hv]
    exact congrFun haR v
  · intro v hv
    have hh := «Σ».selected_support_le_old_on_rays R hne hdisj aR τ hτ0 hv
    rw [congrFun haR v] at hh
    exact hh

end SmoothCompleteFan

end PaperVerification.ToricGeometry
