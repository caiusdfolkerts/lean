module

public import PaperVerification.ToricSelectedSupport

@[expose] public section

/-!
# Exact lift degrees for every selected class

Both a subdivided focus and an unblown divisor give the same repair formula
`old degree + minimum coefficient * correction`. All other selected
corrections disappear because their actual ray incidences are disjoint.
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
theorem selected_minimum_lift_degree (i : ι) :
    ∃ m : ℕ, 0 < m ∧ (∃ p ∈ (R i).negative, (R i).coefficient p = m) ∧
      (∀ v ∈ (R i).negative, m ≤ (R i).coefficient v) ∧
      ∀ S : («Σ».selectedFan R hne hdisj).PrimitiveRelation,
        S.positive = (R i).positive → ∀ (a : Lattice n → ℝ) (t : ι → ℝ),
          S.degree (simultaneousSupport (fun j => (R j).negative) a t) =
            (R i).degree a + (m : ℝ) * t i := by
  by_cases hi : 2 ≤ (R i).negative.card
  · let i' : «Σ».BlowupIndices R := ⟨i, hi⟩
    obtain ⟨m, hm, hmem, hmin, hdeg⟩ :=
      «Σ».simultaneous_minimum_lift_degree_universal («Σ».selectedStarFocus R)
        (fun j => (R j).negative_cone) (fun j => hne j)
        («Σ».selectedStarFocus_disjoint R hdisj) (fun j => j.property)
        i' (R i) (hR i) rfl
    refine ⟨m, hm, hmem, hmin, ?_⟩
    intro S hSP a t
    let F := simultaneousSupport (fun j => (R j).negative) a t
    have havoidP (j : ι) : «Σ».selectedRay R j ∉ (R i).positive := by
      by_cases hji : j = i
      · subst j
        exact fun hh => «Σ».sum_rays_not_mem_rays (R i).negative_cone hi ((R i).primitive.1 hh)
      · exact «Σ».selected_ray_not_positive_of_ne R hR hne hdisj j i hji
    have havoidN (j : ι) : «Σ».selectedRay R j ∉ (R i).negative := by
      by_cases hji : j = i
      · subst j
        exact fun hh => «Σ».sum_rays_not_mem_rays (R i).negative_cone hi
          («Σ».ray_mem_of_mem_cone (R i).negative_cone hh)
      · exact «Σ».selected_ray_not_negative_of_ne R hdisj j i hji
    have hFpos (v : Lattice n) (hv : v ∈ (R i).positive) : F v = a v :=
      simultaneousSupport_of_not_sum _ a t v (fun j hh => by
        have hh' : v = «Σ».selectedRay R j := hh
        exact havoidP j (hh' ▸ hv))
    have hFneg (v : Lattice n) (hv : v ∈ (R i).negative) : F v = a v :=
      simultaneousSupport_of_not_sum _ a t v (fun j hh => by
        have hh' : v = «Σ».selectedRay R j := hh
        exact havoidN j (hh' ▸ hv))
    have hRdeg : (R i).degree F = (R i).degree a :=
      (R i).degree_congr_on_rays F a hFpos hFneg
    have hsum : (∑ v ∈ (R i).negative, F v) = ∑ v ∈ (R i).negative, a v :=
      Finset.sum_congr rfl hFneg
    change S.degree F = (R i).degree a + (m : ℝ) * t i
    have hdegree := hdeg S hSP F
    change S.degree F = (R i).degree F +
      (m : ℝ) * ((∑ v ∈ (R i).negative, F v) - F («Σ».selectedRay R i)) at hdegree
    have hFselected : F («Σ».selectedRay R i) =
        (∑ v ∈ (R i).negative, a v) - t i :=
      «Σ».selectedSupport_at_selected_ray R hdisj a t i
    rw [hRdeg, hsum, hFselected] at hdegree
    rw [hdegree]
    ring
  · have hfocus := «Σ».selected_focus_of_not_blowup R hne i hi
    let e := «Σ».selectedRay R i
    let m := (R i).coefficient e
    have heN : e ∈ (R i).negative := hfocus.symm ▸ Finset.mem_singleton_self e
    have hm : 0 < m := (R i).coefficient_pos e heN
    have hnot (j : «Σ».BlowupIndices R) : ¬ «Σ».selectedStarFocus R j ⊆ (R i).positive := by
      have hji : (j : ι) ≠ i := fun hh => hi (hh ▸ j.property)
      exact «Σ».focus_not_subset_positive_of_disjoint (R j).negative (R j).negative_cone
        (R i) (hR i) (hdisj j i hji)
    have hPnew := «Σ».primitive_survives_simultaneous («Σ».selectedStarFocus R)
      (fun j => (R j).negative_cone) (fun j => hne j)
      («Σ».selectedStarFocus_disjoint R hdisj) (fun j => j.property) (R i).primitive hnot
    have hNnew := («Σ».selected_divisor_cone_iff R hne hdisj i hi heN).mpr (R i).negative_cone
    let S₀ := (R i).copyToFan («Σ».selectedFan R hne hdisj) hPnew hNnew
    refine ⟨m, hm, ⟨e, heN, rfl⟩, ?_, ?_⟩
    · intro v hv
      have hve : v = e := by simpa only [hfocus, Finset.mem_singleton] using hv
      simpa only [hve] using (le_rfl : m ≤ m)
    · intro S hSP a t
      rw [S.degree_unique S₀ hSP]
      change (R i).degree (simultaneousSupport (fun j => (R j).negative) a t) = _
      apply (R i).degree_change_one_negative _ a e heN (t i)
      · intro v hv
        apply simultaneousSupport_of_not_sum
        intro j hh
        by_cases hji : j = i
        · subst j
          have hh' : v = e := hh
          exact Finset.disjoint_left.mp (R i).disjoint (hh' ▸ hv) heN
        · have hh' : v = «Σ».selectedRay R j := hh
          exact «Σ».selected_ray_not_positive_of_ne R hR hne hdisj j i hji (hh' ▸ hv)
      · intro v hv
        have hfocus' : (R i).negative = {e} := hfocus
        rw [hfocus', Finset.erase_singleton] at hv
        exact (Finset.notMem_empty v hv).elim
      · rw [«Σ».selectedSupport_at_selected_ray R hdisj a t i, hfocus, Finset.sum_singleton]

include hR in
theorem selected_lift_degree_of_minimum (i : ι) (m : ℕ)
    (hmem : ∃ p ∈ (R i).negative, (R i).coefficient p = m)
    (hmin : ∀ v ∈ (R i).negative, m ≤ (R i).coefficient v)
    (S : («Σ».selectedFan R hne hdisj).PrimitiveRelation)
    (hSP : S.positive = (R i).positive) (a : Lattice n → ℝ) (t : ι → ℝ) :
    S.degree (simultaneousSupport (fun j => (R j).negative) a t) =
      (R i).degree a + (m : ℝ) * t i := by
  obtain ⟨m', hm', hmem', hmin', hdeg⟩ := «Σ».selected_minimum_lift_degree R hR hne hdisj i
  obtain ⟨p, hp, hpm⟩ := hmem
  obtain ⟨q, hq, hqm⟩ := hmem'
  have hlow := hmin q hq
  have hupp := hmin' p hp
  rw [hqm] at hlow
  rw [hpm] at hupp
  have heq : m' = m := by omega
  simpa only [heq] using hdeg S hSP a t

end SmoothCompleteFan

end PaperVerification.ToricGeometry
