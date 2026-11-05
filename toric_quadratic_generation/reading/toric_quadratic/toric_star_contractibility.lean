module

public import PaperVerification.ToricStarPushdown

@[expose] public section

/-!
# Contractibility descends when the exceptional ray is not positive

This is the precise part of Casagrande's blowup theorem used by the
correction argument when no exceptional divisor has positive degree.
It follows directly from the literal cone replacement condition and the
proved membership characterization of the actual star-subdivided fan.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable (t : Finset (Lattice n)) (ht : t ∈ «Σ».cones) (hne : t.Nonempty)

/-- Contractibility descends for the actual old-focus expansion of a new
primitive relation whose positive rays are old rays. -/
theorem contractible_of_star_focus_expansion (hcard : 2 ≤ t.card)
    (R : («Σ».starSubdivision t ht hne).PrimitiveRelation) (S : «Σ».PrimitiveRelation)
    (hP : S.positive = R.positive)
    (hN : S.negative = if (∑ v ∈ t, v) ∈ R.negative then
      R.negative.erase (∑ v ∈ t, v) ∪ t else R.negative)
    (hR : R.IsCombinatoriallyContractible) : S.IsCombinatoriallyContractible := by
  let e := ∑ v ∈ t, v
  let «Σ'» := «Σ».starSubdivision t ht hne
  have heold : e ∉ «Σ».rays := «Σ».sum_rays_not_mem_rays ht hcard
  have heP : e ∉ R.positive := by
    intro he
    exact heold (S.primitive.1 (hP.symm ▸ he))
  have hecone {u : Finset (Lattice n)} (hu : u ∈ «Σ».cones) : e ∉ u := by
    intro heu
    exact heold («Σ».ray_mem_of_mem_cone hu heu)
  intro ν hν hdisj hfocus x hx
  have hxR : x ∈ R.positive := hP ▸ hx
  have heν : e ∉ ν := hecone hν
  have hePx : e ∉ R.positive.erase x := fun h => heP (Finset.mem_of_mem_erase h)
  by_cases heN : e ∈ R.negative
  · rw [if_pos heN] at hN
    have htS : t ⊆ S.negative := by rw [hN]; exact Finset.subset_union_right
    obtain ⟨p, hp, hpN, hparentR⟩ :=
      («Σ».mem_starSubdivision_with_sum_iff t ht hne hcard heN).mp R.negative_cone
    have hpν : p ∉ ν := by
      intro hpn
      exact Finset.disjoint_left.mp hdisj hpn (Finset.mem_union_right _ (htS hp))
    have hNνold : (R.negative ∪ ν).erase e ∪ t ∈ «Σ».cones := by
      have hsets : (R.negative ∪ ν).erase e ∪ t = S.negative ∪ ν := by
        rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem heν, hN]
        ac_rfl
      simpa only [hsets] using hfocus
    have heNν : e ∈ R.negative ∪ ν := Finset.mem_union_left _ heN
    have hNνnew : R.negative ∪ ν ∈ «Σ'».cones :=
      («Σ».mem_starSubdivision_with_sum_iff t ht hne hcard heNν).mpr
        ⟨p, hp, by simpa using And.intro hpN hpν, hNνold⟩
    have hνnew : ν ∈ «Σ'».cones :=
      «Σ'».downward _ hNνnew ν Finset.subset_union_right
    have hdisjR : Disjoint ν (R.positive ∪ R.negative) := by
      apply Finset.disjoint_left.mpr
      intro v hvν hv
      rcases Finset.mem_union.mp hv with hvP | hvN
      · exact Finset.disjoint_left.mp hdisj hvν
          (Finset.mem_union_left _ (hP.symm ▸ hvP))
      · by_cases hve : v = e
        · exact heν (hve ▸ hvν)
        · exact Finset.disjoint_left.mp hdisj hvν (Finset.mem_union_right _ (by
            rw [hN]
            exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hve, hvN⟩)))
    have hnew := hR ν hνnew hdisjR hNνnew x hxR
    have heNew : e ∈ R.positive.erase x ∪ R.negative ∪ ν :=
      Finset.mem_union_left _ (Finset.mem_union_right _ heN)
    obtain ⟨q, hq, hqN, hold⟩ :=
      («Σ».mem_starSubdivision_with_sum_iff t ht hne hcard heNew).mp hnew
    have hsets : (R.positive.erase x ∪ R.negative ∪ ν).erase e ∪ t =
        S.positive.erase x ∪ S.negative ∪ ν := by
      rw [Finset.erase_union_distrib, Finset.erase_union_distrib,
        Finset.erase_eq_of_notMem hePx, Finset.erase_eq_of_notMem heν, hP, hN]
      ac_rfl
    change (R.positive.erase x ∪ R.negative ∪ ν).erase e ∪ t ∈ «Σ».cones at hold
    rw [hsets] at hold
    exact hold
  · rw [if_neg heN] at hN
    have hdisjR : Disjoint ν (R.positive ∪ R.negative) := by
      simpa only [hP, hN] using hdisj
    have hfocusR : R.negative ∪ ν ∈ «Σ».cones := by simpa only [hN] using hfocus
    by_cases htU : t ⊆ R.negative ∪ ν
    · have htN : ¬ t ⊆ R.negative :=
        ((«Σ».mem_starSubdivision_without_sum_iff t ht hne heN).mp R.negative_cone).2
      obtain ⟨p, hp, hpN⟩ := Finset.not_subset.mp htN
      have hpν : p ∈ ν := (Finset.mem_union.mp (htU hp)).resolve_left hpN
      let ν' := ν.erase p ∪ {e}
      have hsumset : R.negative ∪ ν' = starRaySet (R.negative ∪ ν) t p := by
        ext v
        simp only [ν', Finset.mem_union, Finset.mem_erase, Finset.mem_singleton,
          mem_starRaySet]
        change (v ∈ R.negative ∨ (v ≠ p ∧ v ∈ ν) ∨ v = e) ↔
          v = e ∨ (v ≠ p ∧ (v ∈ R.negative ∨ v ∈ ν))
        have hvp : v ∈ R.negative → v ≠ p := fun hv h => hpN (h ▸ hv)
        tauto
      have hNν' : R.negative ∪ ν' ∈ «Σ'».cones := by
        rw [hsumset]
        exact «Σ».starRaySet_mem_starSubdivision t ht hne hfocusR htU hp
      have hν' : ν' ∈ «Σ'».cones := «Σ'».downward _ hNν' ν' Finset.subset_union_right
      have hdisj' : Disjoint ν' (R.positive ∪ R.negative) := by
        apply Finset.disjoint_left.mpr
        intro v hv hvR
        rcases Finset.mem_union.mp hv with hvν | hve
        · exact Finset.disjoint_left.mp hdisjR (Finset.mem_of_mem_erase hvν) hvR
        · have hve := Finset.mem_singleton.mp hve
          subst v
          rcases Finset.mem_union.mp hvR with h | h
          · exact heP h
          · exact heN h
      have hnew := hR ν' hν' hdisj' hNν' x hxR
      have heNew : e ∈ R.positive.erase x ∪ R.negative ∪ ν' :=
        Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_singleton_self e))
      obtain ⟨q, hq, hqN, hold⟩ :=
        («Σ».mem_starSubdivision_with_sum_iff t ht hne hcard heNew).mp hnew
      have heνerase : e ∉ ν.erase p := fun h => heν (Finset.mem_of_mem_erase h)
      have hsets : (R.positive.erase x ∪ R.negative ∪ ν').erase e ∪ t =
          S.positive.erase x ∪ S.negative ∪ ν := by
        rw [hP, hN]
        apply Finset.Subset.antisymm
        · intro z hz
          rcases Finset.mem_union.mp hz with hz | hzt
          · obtain ⟨hze, hz⟩ := Finset.mem_erase.mp hz
            rcases Finset.mem_union.mp hz with hzPN | hzν'
            · exact Finset.mem_union_left _ hzPN
            · rcases Finset.mem_union.mp hzν' with hzν | hze'
              · exact Finset.mem_union_right _ (Finset.mem_of_mem_erase hzν)
              · exact (hze (Finset.mem_singleton.mp hze')).elim
          · rcases Finset.mem_union.mp (htU hzt) with hzN | hzν
            · exact Finset.mem_union_left _ (Finset.mem_union_right _ hzN)
            · exact Finset.mem_union_right _ hzν
        · intro z hz
          rcases Finset.mem_union.mp hz with hzPN | hzν
          · have hze : z ≠ e := by
              intro h
              rcases Finset.mem_union.mp hzPN with hzP | hzN
              · exact hePx (h ▸ hzP)
              · exact heN (h ▸ hzN)
            exact Finset.mem_union_left _ (Finset.mem_erase.mpr
              ⟨hze, Finset.mem_union_left _ hzPN⟩)
          · by_cases hzp : z = p
            · subst z
              exact Finset.mem_union_right _ hp
            · have hzνerase : z ∈ ν.erase p := Finset.mem_erase.mpr ⟨hzp, hzν⟩
              have hze : z ≠ e := fun h => heνerase (h ▸ hzνerase)
              exact Finset.mem_union_left _ (Finset.mem_erase.mpr
                ⟨hze, Finset.mem_union_right _ (Finset.mem_union_left _ hzνerase)⟩)
      change (R.positive.erase x ∪ R.negative ∪ ν').erase e ∪ t ∈ «Σ».cones at hold
      rw [hsets] at hold
      exact hold
    · have hNν' : R.negative ∪ ν ∈ «Σ'».cones :=
        «Σ».mem_starSubdivision_of_unchanged t ht hne hfocusR htU
      have hν' : ν ∈ «Σ'».cones := «Σ'».downward _ hNν' ν Finset.subset_union_right
      have hnew := hR ν hν' hdisjR hNν' x hxR
      have heNew : e ∉ R.positive.erase x ∪ R.negative ∪ ν := by
        simpa only [Finset.mem_union, not_or] using And.intro (And.intro hePx heN) heν
      have hold := ((«Σ».mem_starSubdivision_without_sum_iff t ht hne heNew).mp hnew).1
      simpa only [hP, hN] using hold

/-- The exact no-positive-exceptional pushdown theorem needed by the
simultaneous correction argument. The pushed class is an actual old
contractible primitive relation and all old divisor degrees are preserved. -/
theorem contractible_pushdown_without_positive_sum (hcard : 2 ≤ t.card)
    (R : («Σ».starSubdivision t ht hne).PrimitiveRelation)
    (heP : (∑ v ∈ t, v) ∉ R.positive) (hPt : R.positive ≠ t)
    (hR : R.IsCombinatoriallyContractible) :
    ∃ S : «Σ».PrimitiveRelation, S.positive = R.positive ∧
      S.IsCombinatoriallyContractible ∧
      ∀ a : Lattice n → ℝ, S.degree a = R.degree (starCoefficientBase a t) := by
  obtain ⟨S, hP, hN, hdegree⟩ :=
    «Σ».primitiveRelation_pushdown_without_positive_sum_data t ht hne hcard R heP hPt
  exact ⟨S, hP, «Σ».contractible_of_star_focus_expansion t ht hne hcard R S hP hN hR, hdegree⟩

end SmoothCompleteFan

end PaperVerification.ToricGeometry
