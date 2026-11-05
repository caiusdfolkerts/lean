module

public import PaperVerification.ToricSelectedLift
public import PaperVerification.ToricMinimumCoefficient

@[expose] public section

/-!
# Complete no-positive-selected-ray repair

Inactive old contractible classes remain nonnegative, while an activated
class is identified by its actual positive collection and the proved unique
minimum-coefficient lift formula. Exceptional fiber relations have exactly
their prescribed nonnegative correction degree.
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

theorem selected_exceptional_degree
    (i : «Σ».BlowupIndices R)
    (S : («Σ».selectedFan R hne hdisj).PrimitiveRelation)
    (hSP : S.positive = (R i).negative)
    (a : Lattice n → ℝ) (t : ι → ℝ) :
    S.degree (simultaneousSupport (fun j => (R j).negative) a t) = t i := by
  let E := «Σ».simultaneousExceptionalRelation («Σ».selectedStarFocus R)
    (fun j => (R j).negative_cone) (fun j => hne j)
    («Σ».selectedStarFocus_disjoint R hdisj) (fun j => j.property) i
  rw [S.degree_unique E hSP]
  let F := simultaneousSupport (fun j => (R j).negative) a t
  have hsum : (∑ v ∈ (R i).negative, F v) = ∑ v ∈ (R i).negative, a v := by
    apply Finset.sum_congr rfl
    intro v hv
    exact «Σ».selectedSupport_on_blowup_focus R hdisj i i.property a t hv
  change E.degree F = _
  simp only [PrimitiveRelation.degree, E, simultaneousExceptionalRelation,
    selectedStarFocus, Nat.cast_one, Finset.sum_singleton, one_mul]
  rw [hsum]
  have he : F (∑ v ∈ (R i).negative, v) =
      (∑ v ∈ (R i).negative, a v) - t i :=
    «Σ».selectedSupport_at_selected_ray R hdisj a t i
  rw [he]
  ring

include hR in
/-- The complete corrected-degree conclusion in the case that no selected
ray occurs positively. The hypotheses are exactly old-class inactivity and
the scalar repairs, all on actual primitive relations. -/
theorem selected_no_positive_degree_nonneg
    (a : Lattice n → ℝ) (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i)
    (hrepair : ∀ i, 0 ≤ (R i).degree a +
      ((R i).minimumCoefficient (hne i) : ℝ) * t i)
    (hinactive : ∀ Q : «Σ».PrimitiveRelation, Q.IsCombinatoriallyContractible →
      (∀ i, «Σ».selectedRay R i ∉ Q.positive) →
      (∀ i, Q.positive ≠ (R i).positive) → 0 ≤ Q.degree a)
    (S : («Σ».selectedFan R hne hdisj).PrimitiveRelation)
    (hS : S.IsCombinatoriallyContractible)
    (hpos : ∀ i, «Σ».selectedRay R i ∉ S.positive) :
    0 ≤ S.degree (simultaneousSupport (fun j => (R j).negative) a t) := by
  by_cases hex : ∃ i : «Σ».BlowupIndices R, S.positive = (R i).negative
  · obtain ⟨i, hi⟩ := hex
    rw [«Σ».selected_exceptional_degree R hne hdisj i S hi a t]
    exact ht i
  · have hneT : ∀ i : «Σ».BlowupIndices R, S.positive ≠ «Σ».selectedStarFocus R i := by
      intro i hi
      exact hex ⟨i, hi⟩
    obtain ⟨Q, hQP, hQ, hdeg⟩ := «Σ».simultaneous_contractible_pushdown («Σ».selectedStarFocus R)
      (fun j => (R j).negative_cone) (fun j => hne j)
      («Σ».selectedStarFocus_disjoint R hdisj) (fun j => j.property)
      S hS (fun j => hpos j) hneT
    by_cases hselected : ∃ i, Q.positive = (R i).positive
    · obtain ⟨i, hi⟩ := hselected
      have hSP : S.positive = (R i).positive := hQP.symm.trans hi
      obtain ⟨hm, hmem, hmin⟩ := (R i).minimumCoefficient_spec (hne i)
      rw [«Σ».selected_lift_degree_of_minimum R hR hne hdisj i
        ((R i).minimumCoefficient (hne i)) hmem hmin S hSP a t]
      exact hrepair i
    · have hQpos : ∀ i, «Σ».selectedRay R i ∉ Q.positive := by
        intro i hh
        exact hpos i (hQP ▸ hh)
      have hQother : ∀ i, Q.positive ≠ (R i).positive := by
        intro i hi
        exact hselected ⟨i, hi⟩
      have hnonneg := hinactive Q hQ hQpos hQother
      have hpullback : S.degree («Σ».selectedPullback R a) = Q.degree a := by
        rcases hdeg with hz | ⟨i, hi, hh⟩
        · exact hz a 0
        · have hh0 := hh a (0 : «Σ».BlowupIndices R → ℝ)
          rw [Pi.zero_apply, mul_zero, add_zero] at hh0
          exact hh0
      have hle := «Σ».selected_support_degree_ge_pullback R hne hdisj S a t ht hpos
      rw [hpullback] at hle
      exact hnonneg.trans hle

end SmoothCompleteFan

end PaperVerification.ToricGeometry
