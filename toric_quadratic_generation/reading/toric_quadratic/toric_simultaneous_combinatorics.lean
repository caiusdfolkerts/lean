module

public import PaperVerification.ToricSimultaneousStars
public import PaperVerification.ToricStarCombinatorics

@[expose] public section

/-!
# Exact local and old-ray rules for simultaneous disjoint stars

The complete star of each exceptional ray is literally the same as in its
single subdivision. Cones with no exceptional ray are exactly the old cones
which contain none of the selected foci.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable {ι : Type*} [Fintype ι] (T : ι → Finset (Lattice n))
variable (hT : ∀ i, T i ∈ «Σ».cones) (hne : ∀ i, (T i).Nonempty)
variable (hdisj : «Σ».PairwiseDisjointFoci T) (hcard : ∀ i, 2 ≤ (T i).card)

include hT hdisj in
theorem simultaneous_sum_rays_injective :
    Function.Injective (fun i : ι => ∑ v ∈ T i, v) := by
  intro i j he
  change (∑ v ∈ T i, v) = ∑ v ∈ T j, v at he
  by_contra hij
  have hiTj : T i ⊆ T j := by
    apply («Σ».sum_rays_mem_cone_iff (hT i) (hT j)).mp
    rw [he]
    exact («Σ».sum_rays_mem_cone_iff (hT j) (hT j)).mpr (Finset.Subset.refl _)
  exact hdisj i j hij ⟨T j, hT j, Finset.union_subset hiTj (Finset.Subset.refl _)⟩

include hT hne hdisj hcard in
/-- Any generating chart containing a given exceptional ray is a chart of
that very focus. This uses actual cone membership of its sum vector. -/
theorem simultaneous_candidate_over_sum (i : ι)
    {C : Finset (Lattice n)} (hC : C ∈ «Σ».simultaneousCandidates T)
    (he : (∑ v ∈ T i, v) ∈ C) :
    ∃ U ∈ «Σ».cones, ∃ p ∈ T i, T i ⊆ U ∧ C = starRaySet U (T i) p := by
  rcases («Σ».mem_simultaneousCandidates T C).mp hC with ⟨hC, hnone⟩ |
    ⟨j, U, hU, p, hp, hTU, hCeq⟩
  · exact («Σ».sum_rays_not_mem_rays (hT i) (hcard i)
      («Σ».ray_mem_of_mem_cone hC he)).elim
  · have hiU : T i ⊆ U := by
      apply («Σ».sum_rays_mem_cone_iff (hT i) hU).mp
      exact latticeRayCone_starRaySet_le hTU p
        (latticeRayCone_generator _ (hCeq ▸ he))
    have hij : i = j := by
      by_contra hij
      exact hdisj i j hij ⟨U, hU, Finset.union_subset hiU hTU⟩
    subst j
    exact ⟨U, hU, p, hp, hTU, hCeq⟩

include hcard in
/-- The actual cone star of an exceptional ray is unchanged by all other
disjoint subdivisions. -/
theorem simultaneous_cone_over_sum_iff (i : ι) {s : Finset (Lattice n)}
    (he : (∑ v ∈ T i, v) ∈ s) :
    s ∈ («Σ».simultaneousSubdivision T hT hne hdisj).cones ↔
      s ∈ («Σ».starSubdivision (T i) (hT i) (hne i)).cones := by
  constructor
  · intro hs
    obtain ⟨C, hC, hsC⟩ :=
      (mem_finiteConeFamilyClosure («Σ».simultaneousCandidates T) s).mp hs
    obtain ⟨U, hU, p, hp, hTU, hCeq⟩ :=
      «Σ».simultaneous_candidate_over_sum T hT hne hdisj hcard i hC (hsC he)
    apply («Σ».starSubdivision (T i) (hT i) (hne i)).downward
      (starRaySet U (T i) p)
      («Σ».starRaySet_mem_starSubdivision (T i) (hT i) (hne i) hU hTU hp) s
    simpa only [hCeq] using hsC
  · intro hs
    obtain ⟨C, hC, hsC⟩ :=
      (mem_finiteConeFamilyClosure («Σ».starCandidates (T i)) s).mp hs
    rcases («Σ».mem_starCandidates (T i) C).mp hC with ⟨hC, hnone⟩ |
      ⟨U, hU, p, hp, hTU, hCeq⟩
    · exact («Σ».sum_rays_not_mem_rays (hT i) (hcard i)
        («Σ».ray_mem_of_mem_cone hC (hsC he))).elim
    · apply («Σ».simultaneousSubdivision T hT hne hdisj).downward
        (starRaySet U (T i) p)
        («Σ».starRaySet_mem_simultaneousSubdivision T hT hne hdisj i hU hTU hp) s
      simpa only [hCeq] using hsC

theorem simultaneous_cone_without_sums_iff {s : Finset (Lattice n)}
    (he : ∀ i, (∑ v ∈ T i, v) ∉ s) :
    s ∈ («Σ».simultaneousSubdivision T hT hne hdisj).cones ↔
      s ∈ «Σ».cones ∧ ∀ i, ¬ T i ⊆ s := by
  constructor
  · intro hs
    obtain ⟨C, hC, hsC⟩ :=
      (mem_finiteConeFamilyClosure («Σ».simultaneousCandidates T) s).mp hs
    rcases («Σ».mem_simultaneousCandidates T C).mp hC with ⟨hC, hnone⟩ |
      ⟨i, U, hU, p, hp, hTU, hCeq⟩
    · exact ⟨«Σ».downward C hC s hsC,
        fun i hi => hnone i (hi.trans hsC)⟩
    · have hsU : s ⊆ U.erase p := by
        intro v hv
        have hh : v ∈ starRaySet U (T i) p := hCeq ▸ hsC hv
        rcases (mem_starRaySet U (T i) p v).mp hh with hve | hvU
        · exact (he i (hve ▸ hv)).elim
        · exact Finset.mem_erase.mpr hvU
      refine ⟨«Σ».downward U hU s (hsU.trans (Finset.erase_subset p U)), ?_⟩
      intro j hj
      by_cases hji : j = i
      · subst j
        exact (Finset.mem_erase.mp (hsU (hj hp))).1 rfl
      · exact hdisj i j (Ne.symm hji) ⟨U, hU,
          Finset.union_subset hTU (hj.trans (hsU.trans (Finset.erase_subset p U)))⟩
  · rintro ⟨hs, hnone⟩
    exact «Σ».mem_simultaneousSubdivision_of_unchanged T hT hne hdisj hs hnone

theorem simultaneous_sum_mem_rays (i : ι) :
    (∑ v ∈ T i, v) ∈ («Σ».simultaneousSubdivision T hT hne hdisj).rays := by
  obtain ⟨p, hp⟩ := hne i
  apply («Σ».simultaneousSubdivision T hT hne hdisj).ray_mem_of_mem_cone
    («Σ».starRaySet_mem_simultaneousSubdivision T hT hne hdisj i
      (hT i) (Finset.Subset.refl _) hp)
  exact (mem_starRaySet (T i) (T i) p _).mpr (Or.inl rfl)

include hcard in
theorem simultaneous_old_ray_mem_rays {v : Lattice n} (hv : v ∈ «Σ».rays) :
    v ∈ («Σ».simultaneousSubdivision T hT hne hdisj).rays := by
  have hnone : ∀ i, ¬ T i ⊆ {v} := by
    intro i hh
    have hc := Finset.card_le_card hh
    simp only [Finset.card_singleton] at hc
    have hi := hcard i
    omega
  exact («Σ».simultaneousSubdivision T hT hne hdisj).ray_mem_of_mem_cone
    («Σ».mem_simultaneousSubdivision_of_unchanged T hT hne hdisj
      («Σ».singleton_mem_of_mem_rays hv) hnone) (Finset.mem_singleton_self v)

include hcard in
theorem simultaneous_rays_eq :
    («Σ».simultaneousSubdivision T hT hne hdisj).rays =
      «Σ».rays ∪ Finset.univ.image (fun i : ι => ∑ v ∈ T i, v) := by
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨s, hs, hvs⟩ :=
      ((«Σ».simultaneousSubdivision T hT hne hdisj).mem_rays_iff v).mp hv
    obtain ⟨C, hC, hsC⟩ :=
      (mem_finiteConeFamilyClosure («Σ».simultaneousCandidates T) s).mp hs
    rcases («Σ».mem_simultaneousCandidates T C).mp hC with ⟨hC, hnone⟩ |
      ⟨i, U, hU, p, hp, hTU, hCeq⟩
    · exact Finset.mem_union_left _ («Σ».ray_mem_of_mem_cone hC (hsC hvs))
    · have hh : v ∈ starRaySet U (T i) p := hCeq ▸ hsC hvs
      rcases (mem_starRaySet U (T i) p v).mp hh with hve | hvU
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨i, Finset.mem_univ i, hve.symm⟩)
      · exact Finset.mem_union_left _ («Σ».ray_mem_of_mem_cone hU hvU.2)
  · intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact «Σ».simultaneous_old_ray_mem_rays T hT hne hdisj hcard hv
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      exact «Σ».simultaneous_sum_mem_rays T hT hne hdisj i

include hcard in
/-- Distinct exceptional rays have no common cone. -/
theorem simultaneous_no_common_sums (i j : ι) (hij : i ≠ j)
    {s : Finset (Lattice n)}
    (hs : s ∈ («Σ».simultaneousSubdivision T hT hne hdisj).cones)
    (hei : (∑ v ∈ T i, v) ∈ s) : (∑ v ∈ T j, v) ∉ s := by
  intro hej
  obtain ⟨C, hC, hsC⟩ :=
    (mem_finiteConeFamilyClosure («Σ».simultaneousCandidates T) s).mp hs
  obtain ⟨U, hU, p, hp, hTU, hCeq⟩ :=
    «Σ».simultaneous_candidate_over_sum T hT hne hdisj hcard i hC (hsC hei)
  have hjU : T j ⊆ U := by
    apply («Σ».sum_rays_mem_cone_iff (hT j) hU).mp
    exact latticeRayCone_starRaySet_le hTU p
      (latticeRayCone_generator _ (hCeq ▸ hsC hej))
  exact hdisj i j hij ⟨U, hU, Finset.union_subset hTU hjU⟩

include hcard in
/-- A focus disjoint from all chosen centers has its entire cone star
literally preserved. This includes the codimension-one loci left unblown. -/
theorem simultaneous_cone_over_disjoint_focus_iff
    {A s : Finset (Lattice n)} (hA : A ∈ «Σ».cones)
    (hdisjA : ∀ i, ¬ ∃ U ∈ «Σ».cones, T i ∪ A ⊆ U) (hAs : A ⊆ s) :
    s ∈ («Σ».simultaneousSubdivision T hT hne hdisj).cones ↔ s ∈ «Σ».cones := by
  constructor
  · intro hs
    have he : ∀ i, (∑ v ∈ T i, v) ∉ s := by
      intro i hei
      obtain ⟨C, hC, hsC⟩ :=
        (mem_finiteConeFamilyClosure («Σ».simultaneousCandidates T) s).mp hs
      obtain ⟨U, hU, p, hp, hTU, hCeq⟩ :=
        «Σ».simultaneous_candidate_over_sum T hT hne hdisj hcard i hC (hsC hei)
      have hAU : A ⊆ U := by
        intro v hv
        have hve : v ≠ ∑ u ∈ T i, u := fun hh =>
          «Σ».sum_rays_not_mem_rays (hT i) (hcard i) (hh ▸ «Σ».ray_mem_of_mem_cone hA hv)
        have hh : v ∈ starRaySet U (T i) p := hCeq ▸ hsC (hAs hv)
        rcases (mem_starRaySet U (T i) p v).mp hh with hh | hh
        · exact (hve hh).elim
        · exact hh.2
      exact hdisjA i ⟨U, hU, Finset.union_subset hTU hAU⟩
    exact ((«Σ».simultaneous_cone_without_sums_iff T hT hne hdisj he).mp hs).1
  · intro hs
    exact «Σ».mem_simultaneousSubdivision_of_unchanged T hT hne hdisj hs
      (fun i hi => hdisjA i ⟨s, hs, Finset.union_subset hi hAs⟩)

end SmoothCompleteFan

end PaperVerification.ToricGeometry
