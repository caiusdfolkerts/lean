module

public import PaperVerification.ToricSimultaneousPushdown
public import PaperVerification.ToricStarLift

@[expose] public section

/-!
# Exact activated lift degrees for simultaneous corrections

The single-star minimum-coefficient relation lives on the simultaneous fan
because its entire negative focus lies in that exceptional star. Uniqueness
of actual primitive relations then identifies every lift of the selected
positive collection, with all other correction coefficients disappearing.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable {ι : Type*} [Fintype ι] (T : ι → Finset (Lattice n))
variable (hT : ∀ i, T i ∈ «Σ».cones) (hne : ∀ i, (T i).Nonempty)
variable (hdisj : «Σ».PairwiseDisjointFoci T) (hcard : ∀ i, 2 ≤ (T i).card)

include hcard

theorem simultaneous_minimum_lift_degree_universal
    (i : ι) (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible)
    (hfocus : R.negative = T i) :
    ∃ m : ℕ, 0 < m ∧ (∃ p ∈ T i, R.coefficient p = m) ∧
      (∀ v ∈ T i, m ≤ R.coefficient v) ∧
      ∀ S : («Σ».simultaneousSubdivision T hT hne hdisj).PrimitiveRelation,
        S.positive = R.positive → ∀ a : Lattice n → ℝ,
          S.degree a = R.degree a + (m : ℝ) *
            ((∑ v ∈ T i, a v) - a (∑ v ∈ T i, v)) := by
  have hsub : T i ⊆ R.negative := hfocus.symm ▸ Finset.Subset.refl (T i)
  obtain ⟨m, hm, hmem, hmin, Si, hSiP, hSideg⟩ :=
    «Σ».exists_minimum_coefficient_lift (T i) (hT i) (hne i) (hcard i) R hsub
  let e := ∑ v ∈ T i, v
  have heold : e ∉ «Σ».rays := «Σ».sum_rays_not_mem_rays (hT i) (hcard i)
  have heRpos : e ∉ R.positive := fun hh => heold (R.primitive.1 hh)
  have heRneg : e ∉ R.negative := fun hh => heold («Σ».ray_mem_of_mem_cone R.negative_cone hh)
  have heSpos : e ∉ Si.positive := by simpa only [hSiP] using heRpos
  have heSneg : e ∈ Si.negative := by
    by_contra hnot
    let f : Lattice n → ℝ := fun v => if v = e then 1 else 0
    have hRzero : R.degree f = 0 := by
      unfold PrimitiveRelation.degree
      have hp : ∀ v ∈ R.positive, f v = 0 := by
        intro v hv
        change (if v = e then (1 : ℝ) else 0) = 0
        exact if_neg (fun hh : v = e => heRpos (hh ▸ hv))
      have hn : ∀ v ∈ R.negative, f v = 0 := by
        intro v hv
        change (if v = e then (1 : ℝ) else 0) = 0
        exact if_neg (fun hh : v = e => heRneg (hh ▸ hv))
      have hp0 : (∑ v ∈ R.positive, f v) = 0 := Finset.sum_eq_zero hp
      have hn0 : (∑ v ∈ R.negative, (R.coefficient v : ℝ) * f v) = 0 := by
        apply Finset.sum_eq_zero
        intro v hv
        rw [hn v hv, mul_zero]
      exact sub_eq_zero.mpr (hp0.trans hn0.symm)
    have hSzero : Si.degree f = 0 := by
      unfold PrimitiveRelation.degree
      have hp : ∀ v ∈ Si.positive, f v = 0 := by
        intro v hv
        change (if v = e then (1 : ℝ) else 0) = 0
        exact if_neg (fun hh : v = e => heSpos (hh ▸ hv))
      have hn : ∀ v ∈ Si.negative, f v = 0 := by
        intro v hv
        change (if v = e then (1 : ℝ) else 0) = 0
        exact if_neg (fun hh : v = e => hnot (hh ▸ hv))
      have hp0 : (∑ v ∈ Si.positive, f v) = 0 := Finset.sum_eq_zero hp
      have hn0 : (∑ v ∈ Si.negative, (Si.coefficient v : ℝ) * f v) = 0 := by
        apply Finset.sum_eq_zero
        intro v hv
        rw [hn v hv, mul_zero]
      exact sub_eq_zero.mpr (hp0.trans hn0.symm)
    have hTzero : (∑ v ∈ T i, f v) = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      change (if v = e then (1 : ℝ) else 0) = 0
      exact if_neg (fun hh : v = e => heold (hh ▸ «Σ».ray_mem_of_mem_cone (hT i) hv))
    have h := hSideg f
    rw [hSzero, hRzero, hTzero] at h
    have hfe : f e = 1 := by simp [f]
    rw [hfe] at h
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    nlinarith
  have hnot (j : ι) : ¬ T j ⊆ R.positive := by
    by_cases hji : j = i
    · subst j
      intro hh
      obtain ⟨p, hp⟩ := hne i
      exact Finset.disjoint_left.mp R.disjoint (hh hp) (hsub hp)
    · apply «Σ».focus_not_subset_positive_of_disjoint (T j) (hT j) R hR
      intro hh
      apply hdisj j i hji
      simpa only [hfocus] using hh
  have hPnew := «Σ».primitive_survives_simultaneous T hT hne hdisj hcard R.primitive hnot
  have hPiNew : («Σ».simultaneousSubdivision T hT hne hdisj).IsPrimitiveCollection Si.positive := by
    simpa only [hSiP] using hPnew
  have hNiNew := («Σ».simultaneous_cone_over_sum_iff T hT hne hdisj hcard i heSneg).mpr Si.negative_cone
  let S₀ := Si.copyToFan («Σ».simultaneousSubdivision T hT hne hdisj) hPiNew hNiNew
  refine ⟨m, hm, hmem, hmin, ?_⟩
  intro S hSP a
  have hsame : S.positive = S₀.positive := hSP.trans hSiP.symm
  rw [S.degree_unique S₀ hsame]
  exact hSideg a

theorem simultaneous_minimum_lift_degree
    (i : ι) (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible)
    (hfocus : R.negative = T i) :
    ∃ m : ℕ, 0 < m ∧ (∃ p ∈ T i, R.coefficient p = m) ∧
      (∀ v ∈ T i, m ≤ R.coefficient v) ∧
      ∀ S : («Σ».simultaneousSubdivision T hT hne hdisj).PrimitiveRelation,
        S.positive = R.positive → ∀ (a : Lattice n → ℝ) (t : ι → ℝ),
          S.degree (simultaneousSupport T a t) = R.degree a + (m : ℝ) * t i := by
  obtain ⟨m, hm, hmem, hmin, hdegree⟩ :=
    «Σ».simultaneous_minimum_lift_degree_universal T hT hne hdisj hcard i R hR hfocus
  refine ⟨m, hm, hmem, hmin, ?_⟩
  intro S hSP a t
  rw [hdegree S hSP]
  have hRdegree : R.degree (simultaneousSupport T a t) = R.degree a := by
    apply R.degree_congr_on_rays
    · intro v hv
      exact «Σ».simultaneousSupport_old T hT hcard a t v (R.primitive.1 hv)
    · intro v hv
      exact «Σ».simultaneousSupport_old T hT hcard a t v
        («Σ».ray_mem_of_mem_cone R.negative_cone hv)
  have hsum : (∑ v ∈ T i, simultaneousSupport T a t v) = ∑ v ∈ T i, a v := by
    apply Finset.sum_congr rfl
    intro v hv
    exact «Σ».simultaneousSupport_old T hT hcard a t v («Σ».ray_mem_of_mem_cone (hT i) hv)
  rw [hRdegree, hsum,
    simultaneousSupport_at_sum T («Σ».simultaneous_sum_rays_injective T hT hdisj)]
  ring

end SmoothCompleteFan

end PaperVerification.ToricGeometry
