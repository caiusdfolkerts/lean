module

public import PaperVerification.ToricSimultaneousPrimitive
public import PaperVerification.ToricStarContractibility

@[expose] public section

/-!
# Genuine contractible pushdown through simultaneous disjoint stars

A primitive relation with no positive exceptional ray is either an
exceptional fiber relation or pushes to an old contractible primitive
relation. If a negative exceptional ray occurs, it is unique and its
correction contributes a nonnegative multiple of its prescribed height.
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

theorem simultaneous_old_relation_contractible
    (S : («Σ».simultaneousSubdivision T hT hne hdisj).PrimitiveRelation)
    (hS : S.IsCombinatoriallyContractible)
    (hPold : «Σ».IsPrimitiveCollection S.positive)
    (heP : ∀ i, (∑ v ∈ T i, v) ∉ S.positive)
    (heN : ∀ i, (∑ v ∈ T i, v) ∉ S.negative) :
    (S.copyToFan «Σ» hPold
      ((«Σ».simultaneous_cone_without_sums_iff T hT hne hdisj heN).mp S.negative_cone).1).IsCombinatoriallyContractible := by
  let Γ := «Σ».simultaneousSubdivision T hT hne hdisj
  have hNdata := («Σ».simultaneous_cone_without_sums_iff T hT hne hdisj heN).mp S.negative_cone
  intro ν hν hdisjν hfocus x hx
  have heν : ∀ i, (∑ v ∈ T i, v) ∉ ν := fun i hh =>
    «Σ».sum_rays_not_mem_rays (hT i) (hcard i) («Σ».ray_mem_of_mem_cone hν hh)
  by_cases hsome : ∃ i, T i ⊆ S.negative ∪ ν
  · obtain ⟨i, hi⟩ := hsome
    obtain ⟨p, hp, hpN⟩ := Finset.not_subset.mp (hNdata.2 i)
    have hpν : p ∈ ν := (Finset.mem_union.mp (hi hp)).resolve_left hpN
    let e := ∑ v ∈ T i, v
    let ν' := ν.erase p ∪ {e}
    have hsumset : S.negative ∪ ν' = starRaySet (S.negative ∪ ν) (T i) p := by
      ext v
      simp only [ν', Finset.mem_union, Finset.mem_erase, Finset.mem_singleton,
        mem_starRaySet]
      change (v ∈ S.negative ∨ (v ≠ p ∧ v ∈ ν) ∨ v = e) ↔
        v = e ∨ (v ≠ p ∧ (v ∈ S.negative ∨ v ∈ ν))
      have hvp : v ∈ S.negative → v ≠ p := fun hv h => hpN (h ▸ hv)
      tauto
    have hfocus' : S.negative ∪ ν' ∈ Γ.cones := by
      rw [hsumset]
      exact «Σ».starRaySet_mem_simultaneousSubdivision T hT hne hdisj i hfocus hi hp
    have hν' : ν' ∈ Γ.cones := Γ.downward _ hfocus' ν' Finset.subset_union_right
    have hdisj' : Disjoint ν' (S.positive ∪ S.negative) := by
      apply Finset.disjoint_left.mpr
      intro v hv hvS
      rcases Finset.mem_union.mp hv with hvν | hve
      · exact Finset.disjoint_left.mp hdisjν (Finset.mem_of_mem_erase hvν) hvS
      · have hve := Finset.mem_singleton.mp hve
        subst v
        rcases Finset.mem_union.mp hvS with hvP | hvN
        · exact heP i hvP
        · exact heN i hvN
    have hnew := hS ν' hν' hdisj' hfocus' x hx
    have heNew : e ∈ S.positive.erase x ∪ S.negative ∪ ν' :=
      Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_singleton_self e))
    have hsingle := («Σ».simultaneous_cone_over_sum_iff T hT hne hdisj hcard i heNew).mp hnew
    obtain ⟨q, hq, hqN, hold⟩ :=
      («Σ».mem_starSubdivision_with_sum_iff (T i) (hT i) (hne i) (hcard i) heNew).mp hsingle
    apply «Σ».downward _ hold _
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hvν
    · have hve : v ≠ e := by
        intro hh
        change v = (∑ w ∈ T i, w) at hh
        rcases Finset.mem_union.mp hv with hvP | hvN
        · exact heP i (hh ▸ Finset.mem_of_mem_erase hvP)
        · exact heN i (hh ▸ hvN)
      exact Finset.mem_union_left _ (Finset.mem_erase.mpr
        ⟨hve, Finset.mem_union_left _ hv⟩)
    · by_cases hvp : v = p
      · exact Finset.mem_union_right _ (hvp.symm ▸ hp)
      · have hve : v ≠ e := by
          intro hh
          change v = (∑ w ∈ T i, w) at hh
          exact heν i (hh ▸ hvν)
        exact Finset.mem_union_left _ (Finset.mem_erase.mpr
          ⟨hve, Finset.mem_union_right _ (Finset.mem_union_left _
            (Finset.mem_erase.mpr ⟨hvp, hvν⟩))⟩)
  · have hfocus' : S.negative ∪ ν ∈ Γ.cones :=
      «Σ».mem_simultaneousSubdivision_of_unchanged T hT hne hdisj hfocus
        (fun i hi => hsome ⟨i, hi⟩)
    have hν' := Γ.downward _ hfocus' ν Finset.subset_union_right
    have hnew := hS ν hν' hdisjν hfocus' x hx
    have heNew : ∀ i, (∑ v ∈ T i, v) ∉ S.positive.erase x ∪ S.negative ∪ ν := by
      intro i hh
      rcases Finset.mem_union.mp hh with hh | hh
      · rcases Finset.mem_union.mp hh with hh | hh
        · exact heP i (Finset.mem_of_mem_erase hh)
        · exact heN i hh
      · exact heν i hh
    exact ((«Σ».simultaneous_cone_without_sums_iff T hT hne hdisj heNew).mp hnew).1

/-- Full no-positive-exceptional pushdown, with an exact degree formula.
There is at most one exceptional contribution on the negative side. -/
theorem simultaneous_contractible_pushdown
    (S : («Σ».simultaneousSubdivision T hT hne hdisj).PrimitiveRelation)
    (hS : S.IsCombinatoriallyContractible)
    (heP : ∀ i, (∑ v ∈ T i, v) ∉ S.positive)
    (hneT : ∀ i, S.positive ≠ T i) :
    ∃ R : «Σ».PrimitiveRelation, R.positive = S.positive ∧
      R.IsCombinatoriallyContractible ∧
      ((∀ (a : Lattice n → ℝ) (t : ι → ℝ),
          S.degree (simultaneousSupport T a t) = R.degree a) ∨
        ∃ i : ι, (∑ v ∈ T i, v) ∈ S.negative ∧
          ∀ (a : Lattice n → ℝ) (t : ι → ℝ),
            S.degree (simultaneousSupport T a t) = R.degree a +
              (S.coefficient (∑ v ∈ T i, v) : ℝ) * t i) := by
  have hPold := «Σ».simultaneous_primitive_pushdown_collection T hT hne hdisj hcard
    S.primitive heP hneT
  by_cases hsome : ∃ i, (∑ v ∈ T i, v) ∈ S.negative
  · obtain ⟨i, hei⟩ := hsome
    let Γi := «Σ».starSubdivision (T i) (hT i) (hne i)
    have hPi := «Σ».simultaneous_old_primitive_single_star T hT hne hdisj hcard hPold S.primitive i
    have hNi := («Σ».simultaneous_cone_over_sum_iff T hT hne hdisj hcard i hei).mp S.negative_cone
    let Si := S.copyToFan Γi hPi hNi
    have hSi : Si.IsCombinatoriallyContractible := by
      apply S.copyToFan_contractible Γi hPi hNi
      · intro s hs
        exact «Σ».simultaneous_cone_over_sum_iff T hT hne hdisj hcard i (hs hei)
      · exact hS
    obtain ⟨R, hRP, hRN, hdeg⟩ :=
      «Σ».primitiveRelation_pushdown_without_positive_sum_data (T i) (hT i) (hne i)
        (hcard i) Si (heP i) (hneT i)
    have hR := «Σ».contractible_of_star_focus_expansion (T i) (hT i) (hne i)
      (hcard i) Si R hRP hRN hSi
    refine ⟨R, hRP, hR, Or.inr ⟨i, hei, ?_⟩⟩
    intro a t
    have hpos (v : Lattice n) (hv : v ∈ S.positive) :
        simultaneousSupport T a t v = starCoefficientBase a (T i) v := by
      rw [«Σ».simultaneousSupport_old T hT hcard a t v (hPold.1 hv)]
      simp only [starCoefficientBase,
        if_neg (fun hh : v = (∑ w ∈ T i, w) => heP i (hh ▸ hv))]
    have hnegold (v : Lattice n) (hv : v ∈ S.negative.erase (∑ w ∈ T i, w)) :
        v ∈ «Σ».rays := by
      have hvN := Finset.mem_of_mem_erase hv
      have hvr := («Σ».simultaneousSubdivision T hT hne hdisj).ray_mem_of_mem_cone
        S.negative_cone hvN
      rw [«Σ».simultaneous_rays_eq T hT hne hdisj hcard] at hvr
      rcases Finset.mem_union.mp hvr with hvr | hvr
      · exact hvr
      · obtain ⟨j, hj, hvj⟩ := Finset.mem_image.mp hvr
        have hij : i ≠ j := by
          intro hh
          subst j
          exact (Finset.mem_erase.mp hv).1 hvj.symm
        exact («Σ».simultaneous_no_common_sums T hT hne hdisj hcard i j hij
          S.negative_cone hei (hvj.symm ▸ hvN)).elim
    have hneg (v : Lattice n) (hv : v ∈ S.negative.erase (∑ w ∈ T i, w)) :
        simultaneousSupport T a t v = starCoefficientBase a (T i) v := by
      rw [«Σ».simultaneousSupport_old T hT hcard a t v (hnegold v hv)]
      simp only [starCoefficientBase, if_neg (Finset.mem_erase.mp hv).1]
    have hinj := «Σ».simultaneous_sum_rays_injective T hT hdisj
    have heq : simultaneousSupport T a t (∑ v ∈ T i, v) =
        starCoefficientBase a (T i) (∑ v ∈ T i, v) - t i := by
      rw [simultaneousSupport_at_sum T hinj]
      simp only [starCoefficientBase, if_pos rfl, ite_true]
    have hh := S.degree_change_one_negative (simultaneousSupport T a t)
      (starCoefficientBase a (T i)) (∑ v ∈ T i, v) hei (t i) hpos hneg heq
    rw [hh]
    exact congrArg (fun z => z + (S.coefficient (∑ v ∈ T i, v) : ℝ) * t i) (hdeg a).symm
  · have heN : ∀ i, (∑ v ∈ T i, v) ∉ S.negative := by simpa only [not_exists] using hsome
    have hNold := ((«Σ».simultaneous_cone_without_sums_iff T hT hne hdisj heN).mp S.negative_cone).1
    let R := S.copyToFan «Σ» hPold hNold
    have hR := «Σ».simultaneous_old_relation_contractible T hT hne hdisj hcard
      S hS hPold heP heN
    refine ⟨R, rfl, hR, Or.inl ?_⟩
    intro a t
    apply S.degree_congr_on_rays (simultaneousSupport T a t) a
    · intro v hv
      exact «Σ».simultaneousSupport_old T hT hcard a t v (hPold.1 hv)
    · intro v hv
      exact «Σ».simultaneousSupport_old T hT hcard a t v («Σ».ray_mem_of_mem_cone hNold hv)

end SmoothCompleteFan

end PaperVerification.ToricGeometry
