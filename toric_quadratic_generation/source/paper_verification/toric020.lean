module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Tauto
public import paper_verification.toric005
public import paper_verification.toric019

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.ToricSimultaneousStars
section Source_ToricSimultaneousStars

-- original header: module

-- original header: public import PaperVerification.ToricDisjointStarIntersections
-- original header: public import PaperVerification.ToricStarSubdivision
-- original header: public import PaperVerification.ToricStarPurity

-- original header: @[expose] public section

/-!
# The genuine simultaneous subdivision at pairwise disjoint focus cones

Each old cone contains at most one selected focus. The explicit finite
family therefore subdivides that cone once. Its smoothness, actual cone
intersections, completeness and full-cone extensions are proved below.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable {ι : Type*} [Fintype ι] (T : ι → Finset (Lattice n))

/-- Distinct focus loci have no common old cone. This is the literal finite
incidence conclusion proved for distinct large contractible relations. -/
def PairwiseDisjointFoci : Prop :=
  ∀ i j : ι, i ≠ j → ¬ ∃ U ∈ «Σ».cones, T i ∪ T j ⊆ U

def simultaneousCandidates : Finset (Finset (Lattice n)) :=
  «Σ».cones.filter (fun U => ∀ i, ¬ T i ⊆ U) ∪
    Finset.univ.biUnion (fun i : ι => «Σ».cones.biUnion
      (fun U => if T i ⊆ U then (T i).image (starRaySet U (T i)) else ∅))

theorem mem_simultaneousCandidates (s : Finset (Lattice n)) :
    s ∈ «Σ».simultaneousCandidates T ↔
      (s ∈ «Σ».cones ∧ ∀ i, ¬ T i ⊆ s) ∨
      ∃ i : ι, ∃ U ∈ «Σ».cones, ∃ p ∈ T i,
        T i ⊆ U ∧ s = starRaySet U (T i) p := by
  simp only [simultaneousCandidates, Finset.mem_union, Finset.mem_filter,
    Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro (hs | ⟨i, U, hU, hs⟩)
    · exact Or.inl hs
    · by_cases hTU : T i ⊆ U
      · rw [if_pos hTU] at hs
        obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hs
        exact Or.inr ⟨i, U, hU, p, hp, hTU, he.symm⟩
      · simp only [if_neg hTU, Finset.notMem_empty] at hs
  · rintro (hs | ⟨i, U, hU, p, hp, hTU, rfl⟩)
    · exact Or.inl hs
    · refine Or.inr ⟨i, U, hU, ?_⟩
      rw [if_pos hTU]
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩

theorem simultaneousCandidates_smooth :
    ∀ s ∈ «Σ».simultaneousCandidates T,
      ∃ b : Module.Basis (Fin n) ℤ (Lattice n), s ⊆ Finset.univ.image b := by
  intro s hs
  rcases («Σ».mem_simultaneousCandidates T s).mp hs with ⟨hs, hnone⟩ |
    ⟨i, U, hU, p, hp, hTU, rfl⟩
  · obtain ⟨b, I, rfl⟩ := «Σ».smooth s hs
    exact ⟨b, Finset.image_subset_image (Finset.subset_univ I)⟩
  · obtain ⟨b, I, he⟩ := «Σ».starRaySet_smooth hU hTU hp
    refine ⟨b, ?_⟩
    rw [he]
    exact Finset.image_subset_image (Finset.subset_univ I)

theorem simultaneousCandidates_intersection
    (hT : ∀ i, T i ∈ «Σ».cones) (hdisj : «Σ».PairwiseDisjointFoci T) :
    ∀ s ∈ «Σ».simultaneousCandidates T, ∀ u ∈ «Σ».simultaneousCandidates T,
      latticeRayCone s ⊓ latticeRayCone u = latticeRayCone (s ∩ u) := by
  intro s hs u hu
  rcases («Σ».mem_simultaneousCandidates T s).mp hs with ⟨hs, hnone⟩ |
    ⟨i, U, hU, p, hp, hTU, rfl⟩
  · rcases («Σ».mem_simultaneousCandidates T u).mp hu with ⟨hu, hnone'⟩ |
      ⟨j, V, hV, q, hq, hTV, rfl⟩
    · exact «Σ».intersection s hs u hu
    · rw [inf_comm, Finset.inter_comm]
      exact «Σ».star_cone_inter_unchanged hV (hT j) hs hTV (hnone j) q
  · rcases («Σ».mem_simultaneousCandidates T u).mp hu with ⟨hu, hnone'⟩ |
      ⟨j, V, hV, q, hq, hTV, rfl⟩
    · exact «Σ».star_cone_inter_unchanged hU (hT i) hu hTU (hnone' i) p
    · by_cases hij : i = j
      · subst j
        exact «Σ».star_cones_inter hU (hT i) hV hTU hTV hp hq
      · have hiV : ¬ T i ⊆ V := fun hh => hdisj i j hij
          ⟨V, hV, Finset.union_subset hh hTV⟩
        have hjU : ¬ T j ⊆ U := fun hh => hdisj i j hij
          ⟨U, hU, Finset.union_subset hTU hh⟩
        exact «Σ».star_cones_inter_disjoint_foci hU hV (hT i) (hT j)
          hTU hTV hiV hjU p q

theorem simultaneousCandidates_cover (hne : ∀ i, (T i).Nonempty) :
    ∀ x : Ambient n, ∃ s ∈ «Σ».simultaneousCandidates T, x ∈ latticeRayCone s := by
  intro x
  obtain ⟨U, hU, hx⟩ := «Σ».complete x
  by_cases hsome : ∃ i, T i ⊆ U
  · obtain ⟨i, hi⟩ := hsome
    obtain ⟨p, hp, hxp⟩ := latticeRayCone_star_cover hi (hne i) hx
    exact ⟨starRaySet U (T i) p,
      («Σ».mem_simultaneousCandidates T _).mpr (Or.inr ⟨i, U, hU, p, hp, hi, rfl⟩), hxp⟩
  · exact ⟨U, («Σ».mem_simultaneousCandidates T U).mpr
      (Or.inl ⟨hU, fun i hi => hsome ⟨i, hi⟩⟩), hx⟩

/-- A simultaneous subdivision constructed from actual finite cones. -/
def simultaneousSubdivision
    (hT : ∀ i, T i ∈ «Σ».cones) (hne : ∀ i, (T i).Nonempty)
    (hdisj : «Σ».PairwiseDisjointFoci T) : SmoothCompleteFan n :=
  fanOfFiniteSmoothCones («Σ».simultaneousCandidates T)
    («Σ».simultaneousCandidates_smooth T)
    («Σ».simultaneousCandidates_intersection T hT hdisj)
    («Σ».simultaneousCandidates_cover T hne)

theorem mem_simultaneousSubdivision_of_unchanged
    (hT : ∀ i, T i ∈ «Σ».cones) (hne : ∀ i, (T i).Nonempty)
    (hdisj : «Σ».PairwiseDisjointFoci T) {s : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (hnone : ∀ i, ¬ T i ⊆ s) :
    s ∈ («Σ».simultaneousSubdivision T hT hne hdisj).cones := by
  apply (mem_finiteConeFamilyClosure («Σ».simultaneousCandidates T) s).mpr
  exact ⟨s, («Σ».mem_simultaneousCandidates T s).mpr (Or.inl ⟨hs, hnone⟩),
    Finset.Subset.refl s⟩

theorem starRaySet_mem_simultaneousSubdivision
    (hT : ∀ i, T i ∈ «Σ».cones) (hne : ∀ i, (T i).Nonempty)
    (hdisj : «Σ».PairwiseDisjointFoci T) (i : ι)
    {U : Finset (Lattice n)} (hU : U ∈ «Σ».cones) (hTU : T i ⊆ U)
    {p : Lattice n} (hp : p ∈ T i) :
    starRaySet U (T i) p ∈ («Σ».simultaneousSubdivision T hT hne hdisj).cones := by
  apply (mem_finiteConeFamilyClosure («Σ».simultaneousCandidates T) _).mpr
  exact ⟨starRaySet U (T i) p, («Σ».mem_simultaneousCandidates T _).mpr
    (Or.inr ⟨i, U, hU, p, hp, hTU, rfl⟩), Finset.Subset.refl _⟩

theorem isPure_simultaneousSubdivision
    (hpure : «Σ».IsPure) (hT : ∀ i, T i ∈ «Σ».cones)
    (hne : ∀ i, (T i).Nonempty) (hdisj : «Σ».PairwiseDisjointFoci T) :
    («Σ».simultaneousSubdivision T hT hne hdisj).IsPure := by
  intro s hs
  obtain ⟨C, hC, hsC⟩ := (mem_finiteConeFamilyClosure («Σ».simultaneousCandidates T) s).mp hs
  rcases («Σ».mem_simultaneousCandidates T C).mp hC with ⟨hC, hnone⟩ |
    ⟨i, C', hC', p, hp, hTC', rfl⟩
  · obtain ⟨U, hU, hCU, hUcard⟩ := hpure C hC
    by_cases hsome : ∃ i, T i ⊆ U
    · obtain ⟨i, hi⟩ := hsome
      obtain ⟨p, hp, hpC⟩ := Finset.not_subset.mp (hnone i)
      refine ⟨starRaySet U (T i) p,
        «Σ».starRaySet_mem_simultaneousSubdivision T hT hne hdisj i hU hi hp, ?_, ?_⟩
      · intro v hv
        exact (mem_starRaySet U (T i) p v).mpr (Or.inr
          ⟨fun hvp => hpC (hvp ▸ hsC hv), hCU (hsC hv)⟩)
      · rw [«Σ».starRaySet_card hU hi hp, hUcard]
    · exact ⟨U, «Σ».mem_simultaneousSubdivision_of_unchanged T hT hne hdisj hU
        (fun i hi => hsome ⟨i, hi⟩), hsC.trans hCU, hUcard⟩
  · obtain ⟨U, hU, hCU, hUcard⟩ := hpure C' hC'
    have hTU := hTC'.trans hCU
    exact ⟨starRaySet U (T i) p,
      «Σ».starRaySet_mem_simultaneousSubdivision T hT hne hdisj i hU hTU hp,
      hsC.trans (starRaySet_mono hCU (T i) p),
      («Σ».starRaySet_card hU hTU hp).trans hUcard⟩

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricSimultaneousStars
-- END ORIGINAL PaperVerification.ToricSimultaneousStars


-- BEGIN ORIGINAL PaperVerification.ToricSimultaneousCombinatorics
section Source_ToricSimultaneousCombinatorics

-- original header: module

-- original header: public import PaperVerification.ToricSimultaneousStars
-- original header: public import PaperVerification.ToricStarCombinatorics

-- original header: @[expose] public section

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
end
end Source_ToricSimultaneousCombinatorics
-- END ORIGINAL PaperVerification.ToricSimultaneousCombinatorics


-- BEGIN ORIGINAL PaperVerification.ToricSimultaneousSupport
section Source_ToricSimultaneousSupport

-- original header: module

-- original header: public import PaperVerification.ToricSimultaneousCombinatorics
-- original header: public import PaperVerification.ToricStarStrictSupport

-- original header: @[expose] public section

/-!
# Support coefficients and strict support on simultaneous disjoint stars

Old coefficients are retained. At each new sum ray the coefficient is the
sum on its old focus minus the prescribed correction. A common sufficiently
small positive correction yields strict support on the constructed fan.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

/-- Pullback support with an independently prescribed correction at each
actual exceptional sum ray. The same expression applies over integers and
over reals. -/
def simultaneousSupport {n : ℕ} {ι A : Type*} [Fintype ι] [AddCommGroup A]
    (T : ι → Finset (Lattice n)) (a : Lattice n → A) (t : ι → A) : Lattice n → A :=
  fun v => a v + ∑ i, if v = ∑ w ∈ T i, w then (∑ w ∈ T i, a w) - a v - t i else 0

theorem simultaneousSupport_of_not_sum {n : ℕ} {ι A : Type*}
    [Fintype ι] [AddCommGroup A]
    (T : ι → Finset (Lattice n)) (a : Lattice n → A) (t : ι → A)
    (v : Lattice n) (hv : ∀ i, v ≠ ∑ w ∈ T i, w) :
    simultaneousSupport T a t v = a v := by
  simp only [simultaneousSupport, hv, if_false, Finset.sum_const_zero, add_zero]

theorem simultaneousSupport_at_sum {n : ℕ} {ι A : Type*}
    [Fintype ι] [AddCommGroup A]
    (T : ι → Finset (Lattice n))
    (hinj : Function.Injective (fun i : ι => ∑ w ∈ T i, w))
    (a : Lattice n → A) (t : ι → A) (i : ι) :
    simultaneousSupport T a t (∑ w ∈ T i, w) = (∑ w ∈ T i, a w) - t i := by
  unfold simultaneousSupport
  have hs : (∑ j, if (∑ w ∈ T i, w) = ∑ w ∈ T j, w then
      (∑ w ∈ T j, a w) - a (∑ w ∈ T i, w) - t j else 0) =
      (∑ w ∈ T i, a w) - a (∑ w ∈ T i, w) - t i := by
    simp only [hinj.eq_iff]
    simp
  rw [hs]
  abel

theorem simultaneousSupport_parameter {n : ℕ} {ι : Type*} [Fintype ι]
    (T : ι → Finset (Lattice n))
    (hinj : Function.Injective (fun i : ι => ∑ w ∈ T i, w))
    (a : Lattice n → ℝ) (ε : ℝ) (v : Lattice n) :
    simultaneousSupport T a (fun _ => ε) v =
      simultaneousSupport T a 0 v + ε * simultaneousSupport T 0 1 v := by
  by_cases he : ∃ i, v = ∑ w ∈ T i, w
  · obtain ⟨i, rfl⟩ := he
    rw [simultaneousSupport_at_sum T hinj, simultaneousSupport_at_sum T hinj,
      simultaneousSupport_at_sum T hinj]
    simp [sub_eq_add_neg]
  · have hv : ∀ i, v ≠ ∑ w ∈ T i, w := by simpa only [not_exists] using he
    rw [simultaneousSupport_of_not_sum T _ _ v hv,
      simultaneousSupport_of_not_sum T _ _ v hv,
      simultaneousSupport_of_not_sum T _ _ v hv]
    simp

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable {ι : Type*} [Fintype ι] (T : ι → Finset (Lattice n))
variable (hT : ∀ i, T i ∈ «Σ».cones) (hne : ∀ i, (T i).Nonempty)
variable (hdisj : «Σ».PairwiseDisjointFoci T) (hcard : ∀ i, 2 ≤ (T i).card)

include hT hcard in
theorem simultaneousSupport_old {A : Type*} [AddCommGroup A]
    (a : Lattice n → A) (t : ι → A) (v : Lattice n) (hv : v ∈ «Σ».rays) :
    simultaneousSupport T a t v = a v := by
  apply simultaneousSupport_of_not_sum
  intro i he
  exact «Σ».sum_rays_not_mem_rays (hT i) (hcard i) (he ▸ hv)

/-- A star chart has an explicitly chosen first-order linear perturbation,
with value minus one at the omitted pivot and zero at every other parent ray. -/
theorem star_chart_perturbation
    {U A : Finset (Lattice n)} (hU : U ∈ «Σ».cones) (hAU : A ⊆ U)
    {p : Lattice n} (hp : p ∈ A) :
    ∃ g : Ambient n →ₗ[ℝ] ℝ,
      (∀ v ∈ U, g (embed n v) = if v = p then -1 else 0) ∧
      g (embed n (∑ v ∈ A, v)) = -1 := by
  obtain ⟨b, I, J, hUI, hAJ, hJI⟩ := «Σ».adapted_basis_for_subcone hU hAU
  obtain ⟨j, hj, hpj⟩ := Finset.mem_image.mp (hAJ ▸ hp)
  let g : Ambient n →ₗ[ℝ] ℝ := -(integralBasisReal b).coord j
  have hgold (v : Lattice n) (hv : v ∈ U) :
      g (embed n v) = if v = p then -1 else 0 := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hUI ▸ hv)
    rw [← hpj, ← integralBasisReal_apply b i]
    simp only [g, LinearMap.neg_apply, Module.Basis.coord_apply,
      Module.Basis.repr_self_apply]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, b.injective.ne hij]
  refine ⟨g, hgold, ?_⟩
  rw [map_sum, map_sum]
  calc
    (∑ v ∈ A, g (embed n v)) = ∑ v ∈ A, if v = p then -1 else 0 :=
      Finset.sum_congr rfl (fun v hv => hgold v (hAU hv))
    _ = -1 := by simp [hp]

include hT hdisj hcard in
theorem simultaneousCandidate_lexicographic_support
    (a : Lattice n → ℝ) (ha : «Σ».IsStrictSupport a) :
    ∀ C ∈ «Σ».simultaneousCandidates T, ∃ L₀ L₁ : Ambient n →ₗ[ℝ] ℝ,
      (∀ v ∈ C, L₀ (embed n v) = simultaneousSupport T a 0 v ∧
        L₁ (embed n v) = simultaneousSupport T 0 1 v) ∧
      (∀ v ∈ «Σ».rays ∪ Finset.univ.image (fun i : ι => ∑ w ∈ T i, w), v ∉ C →
        L₀ (embed n v) < simultaneousSupport T a 0 v ∨
        (L₀ (embed n v) = simultaneousSupport T a 0 v ∧
          L₁ (embed n v) < simultaneousSupport T 0 1 v)) := by
  have hinj := «Σ».simultaneous_sum_rays_injective T hT hdisj
  have hold (v : Lattice n) (hv : v ∈ «Σ».rays) :
      simultaneousSupport T a 0 v = a v ∧
        simultaneousSupport T (0 : Lattice n → ℝ) 1 v = 0 := by
    exact ⟨«Σ».simultaneousSupport_old T hT hcard a 0 v hv,
      «Σ».simultaneousSupport_old T hT hcard 0 1 v hv⟩
  have hnew (i : ι) :
      simultaneousSupport T a 0 (∑ v ∈ T i, v) = ∑ v ∈ T i, a v ∧
      simultaneousSupport T (0 : Lattice n → ℝ) 1 (∑ v ∈ T i, v) = -1 := by
    simp only [simultaneousSupport_at_sum T hinj, Pi.zero_apply, Pi.one_apply,
      Finset.sum_const_zero, sub_zero, zero_sub, true_and]
  intro C hC
  rcases («Σ».mem_simultaneousCandidates T C).mp hC with ⟨hC, hnone⟩ |
    ⟨i, U, hU, p, hp, hTU, rfl⟩
  · obtain ⟨ℓ, heq, hlt⟩ := ha C hC
    refine ⟨ℓ, 0, ?_, ?_⟩
    · intro v hv
      obtain ⟨h₀, h₁⟩ := hold v («Σ».ray_mem_of_mem_cone hC hv)
      exact ⟨(heq v hv).trans h₀.symm, by simp only [LinearMap.zero_apply, h₁]⟩
    · intro v hv hvC
      left
      rcases Finset.mem_union.mp hv with hv | hv
      · rw [(hold v hv).1]
        exact hlt v hv hvC
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
        rw [(hnew i).1]
        exact «Σ».supporting_sum_strict_of_not_subset a (hT i) (hnone i) ℓ heq hlt
  · obtain ⟨ℓ, heq, hlt⟩ := ha U hU
    obtain ⟨g, hgold, hge⟩ := «Σ».star_chart_perturbation hU hTU hp
    have hℓe : ℓ (embed n (∑ v ∈ T i, v)) = ∑ v ∈ T i, a v := by
      rw [map_sum, map_sum]
      exact Finset.sum_congr rfl (fun v hv => heq v (hTU hv))
    refine ⟨ℓ, g, ?_, ?_⟩
    · intro v hv
      rcases (mem_starRaySet U (T i) p v).mp hv with hve | hv
      · subst v
        exact ⟨hℓe.trans (hnew i).1.symm, hge.trans (hnew i).2.symm⟩
      · obtain ⟨hvp, hvU⟩ := hv
        obtain ⟨h₀, h₁⟩ := hold v («Σ».ray_mem_of_mem_cone hU hvU)
        refine ⟨(heq v hvU).trans h₀.symm, ?_⟩
        rw [hgold v hvU, if_neg hvp, h₁]
    · intro v hv hvC
      rcases Finset.mem_union.mp hv with hv | hv
      · rw [(hold v hv).1, (hold v hv).2]
        by_cases hvU : v ∈ U
        · right
          have hvp : v = p := by
            by_contra hnot
            exact hvC ((mem_starRaySet U (T i) p v).mpr (Or.inr ⟨hnot, hvU⟩))
          refine ⟨heq v hvU, ?_⟩
          rw [hgold v hvU, if_pos hvp]
          norm_num
        · exact Or.inl (hlt v hv hvU)
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
        have hij : i ≠ j := by
          intro hh
          subst j
          exact hvC ((mem_starRaySet U (T i) p _).mpr (Or.inl rfl))
        left
        rw [(hnew j).1]
        have hjU : ¬ T j ⊆ U := fun hh => hdisj i j hij
          ⟨U, hU, Finset.union_subset hTU hh⟩
        exact «Σ».supporting_sum_strict_of_not_subset a (hT j) hjU ℓ heq hlt

include hcard in
/-- All sufficiently small common exceptional corrections give strict
support on the actual simultaneous subdivision. -/
theorem strictSupport_simultaneousSubdivision_all_small
    (a : Lattice n → ℝ) (ha : «Σ».IsStrictSupport a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      («Σ».simultaneousSubdivision T hT hne hdisj).IsStrictSupport
        (simultaneousSupport T a (fun _ => ε)) := by
  let C := «Σ».simultaneousCandidates T
  let R := «Σ».rays ∪ Finset.univ.image (fun i : ι => ∑ w ∈ T i, w)
  have hcharts := «Σ».simultaneousCandidate_lexicographic_support T hT hdisj hcard a ha
  choose L₀ L₁ hactive hinactive using hcharts
  let K₀ : Finset (Lattice n) → Ambient n →ₗ[ℝ] ℝ :=
    fun s => if hs : s ∈ C then L₀ s hs else 0
  let K₁ : Finset (Lattice n) → Ambient n →ₗ[ℝ] ℝ :=
    fun s => if hs : s ∈ C then L₁ s hs else 0
  have heq : ∀ s ∈ C, ∀ v ∈ s,
      K₀ s (embed n v) = simultaneousSupport T a 0 v ∧
      K₁ s (embed n v) = simultaneousSupport T 0 1 v := by
    intro s hs v hv
    simpa only [K₀, K₁, dif_pos hs] using hactive s hs v hv
  have hlex : ∀ s ∈ C, ∀ v ∈ R, v ∉ s →
      K₀ s (embed n v) < simultaneousSupport T a 0 v ∨
      (K₀ s (embed n v) = simultaneousSupport T a 0 v ∧
        K₁ s (embed n v) < simultaneousSupport T 0 1 v) := by
    intro s hs v hv hvs
    simpa only [K₀, K₁, dif_pos hs] using hinactive s hs v hv hvs
  obtain ⟨δ, hδ, hsmall⟩ := finite_lexicographic_support_perturbation_all_small
    C R (simultaneousSupport T a 0) (simultaneousSupport T 0 1) K₀ K₁ heq hlex
  have hinj := «Σ».simultaneous_sum_rays_injective T hT hdisj
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  refine strictSupport_fanOfFiniteSmoothCones C
    («Σ».simultaneousCandidates_smooth T)
    («Σ».simultaneousCandidates_intersection T hT hdisj)
    («Σ».simultaneousCandidates_cover T hne) R ?_
    (simultaneousSupport T a (fun _ => ε)) ?_
  · intro s hs v hv
    have hsnew : s ∈ («Σ».simultaneousSubdivision T hT hne hdisj).cones := by
      apply (mem_finiteConeFamilyClosure C s).mpr
      exact ⟨s, hs, Finset.Subset.refl _⟩
    have hvr := («Σ».simultaneousSubdivision T hT hne hdisj).ray_mem_of_mem_cone hsnew hv
    simpa only [«Σ».simultaneous_rays_eq T hT hne hdisj hcard] using hvr
  · intro s hs
    refine ⟨K₀ s + ε • K₁ s, ?_⟩
    simpa only [simultaneousSupport_parameter T hinj a ε] using hsmall ε hε hεδ s hs

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricSimultaneousSupport
-- END ORIGINAL PaperVerification.ToricSimultaneousSupport


-- BEGIN ORIGINAL PaperVerification.ToricSimultaneousPrimitive
section Source_ToricSimultaneousPrimitive

-- original header: module

-- original header: public import PaperVerification.ToricSimultaneousSupport
-- original header: public import PaperVerification.ToricRelationTransport

-- original header: @[expose] public section

/-!
# Primitive collections on simultaneous disjoint stars

Old-ray primitive collections are either one selected focus or an actual
old primitive collection. Collections with only one exceptional ray are
primitive already in that one local star subdivision.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable {ι : Type*} [Fintype ι] (T : ι → Finset (Lattice n))
variable (hT : ∀ i, T i ∈ «Σ».cones) (hne : ∀ i, (T i).Nonempty)
variable (hdisj : «Σ».PairwiseDisjointFoci T) (hcard : ∀ i, 2 ≤ (T i).card)

include hcard in
/-- An old primitive collection survives when it contains none of the
chosen focus cones. -/
theorem primitive_survives_simultaneous
    {P : Finset (Lattice n)} (hP : «Σ».IsPrimitiveCollection P)
    (hnot : ∀ i, ¬ T i ⊆ P) :
    («Σ».simultaneousSubdivision T hT hne hdisj).IsPrimitiveCollection P := by
  have he : ∀ i, (∑ v ∈ T i, v) ∉ P := fun i hh =>
    «Σ».sum_rays_not_mem_rays (hT i) (hcard i) (hP.1 hh)
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    exact «Σ».simultaneous_old_ray_mem_rays T hT hne hdisj hcard (hP.1 hv)
  · intro hh
    exact hP.2.1 ((«Σ».simultaneous_cone_without_sums_iff T hT hne hdisj he).mp hh).1
  · intro s hs
    exact «Σ».mem_simultaneousSubdivision_of_unchanged T hT hne hdisj
      (hP.2.2 s hs) (fun i hi => hnot i (hi.trans hs.subset))

include hcard in
theorem focus_isPrimitiveCollection_simultaneous (i : ι) :
    («Σ».simultaneousSubdivision T hT hne hdisj).IsPrimitiveCollection (T i) := by
  have he : ∀ j, (∑ v ∈ T j, v) ∉ T i := fun j hh =>
    «Σ».sum_rays_not_mem_rays (hT j) (hcard j) («Σ».ray_mem_of_mem_cone (hT i) hh)
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    exact «Σ».simultaneous_old_ray_mem_rays T hT hne hdisj hcard
      («Σ».ray_mem_of_mem_cone (hT i) hv)
  · intro hh
    exact ((«Σ».simultaneous_cone_without_sums_iff T hT hne hdisj he).mp hh).2 i
      (Finset.Subset.refl _)
  · intro s hs
    apply «Σ».mem_simultaneousSubdivision_of_unchanged T hT hne hdisj
      («Σ».downward (T i) (hT i) s hs.subset)
    intro j hjs
    by_cases hji : j = i
    · subst j
      exact (Finset.ssubset_iff_subset_ne.mp hs).2 (Finset.Subset.antisymm hs.subset hjs)
    · exact hdisj i j (Ne.symm hji) ⟨T i, hT i,
        Finset.union_subset (Finset.Subset.refl _) (hjs.trans hs.subset)⟩

def simultaneousExceptionalRelation (i : ι) :
    («Σ».simultaneousSubdivision T hT hne hdisj).PrimitiveRelation where
  positive := T i
  negative := {∑ v ∈ T i, v}
  coefficient := fun _ => 1
  primitive := «Σ».focus_isPrimitiveCollection_simultaneous T hT hne hdisj hcard i
  negative_cone := («Σ».simultaneousSubdivision T hT hne hdisj).singleton_mem_of_mem_rays
    («Σ».simultaneous_sum_mem_rays T hT hne hdisj i)
  coefficient_pos := by simp
  equation := by simp

theorem simultaneousExceptionalRelation_degree
    (a : Lattice n → ℝ) (t : ι → ℝ) (i : ι) :
    («Σ».simultaneousExceptionalRelation T hT hne hdisj hcard i).degree
      (simultaneousSupport T a t) = t i := by
  have hinj := «Σ».simultaneous_sum_rays_injective T hT hdisj
  simp only [PrimitiveRelation.degree, simultaneousExceptionalRelation, Nat.cast_one,
    Finset.sum_singleton, one_mul, simultaneousSupport_at_sum T hinj]
  have hold : (∑ v ∈ T i, simultaneousSupport T a t v) = ∑ v ∈ T i, a v := by
    apply Finset.sum_congr rfl
    intro v hv
    exact «Σ».simultaneousSupport_old T hT hcard a t v («Σ».ray_mem_of_mem_cone (hT i) hv)
  rw [hold]
  ring

include hcard in
/-- A primitive old-ray collection which is not one of the subdivided
foci is genuinely primitive on the original fan. -/
theorem simultaneous_primitive_pushdown_collection
    {P : Finset (Lattice n)}
    (hP : («Σ».simultaneousSubdivision T hT hne hdisj).IsPrimitiveCollection P)
    (he : ∀ i, (∑ v ∈ T i, v) ∉ P) (hneT : ∀ i, P ≠ T i) :
    «Σ».IsPrimitiveCollection P := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    have hh := hP.1 hv
    rw [«Σ».simultaneous_rays_eq T hT hne hdisj hcard] at hh
    rcases Finset.mem_union.mp hh with hh | hh
    · exact hh
    · obtain ⟨i, hi, hvi⟩ := Finset.mem_image.mp hh
      exact (he i (hvi.symm ▸ hv)).elim
  · intro hPold
    have hsome : ∃ i, T i ⊆ P := by
      by_contra hh
      apply hP.2.1
      exact «Σ».mem_simultaneousSubdivision_of_unchanged T hT hne hdisj hPold
        (fun i hi => hh ⟨i, hi⟩)
    obtain ⟨i, hi⟩ := hsome
    have hproper : T i ⊂ P := Finset.ssubset_iff_subset_ne.mpr ⟨hi, Ne.symm (hneT i)⟩
    exact («Σ».focus_isPrimitiveCollection_simultaneous T hT hne hdisj hcard i).2.1
      (hP.2.2 _ hproper)
  · intro s hs
    have hes : ∀ i, (∑ v ∈ T i, v) ∉ s := fun i hh => he i (hs.subset hh)
    exact ((«Σ».simultaneous_cone_without_sums_iff T hT hne hdisj hes).mp (hP.2.2 s hs)).1

include hcard in
/-- An old primitive collection whose proper subsets are simultaneous
cones is primitive on each individual star as well. -/
theorem simultaneous_old_primitive_single_star
    {P : Finset (Lattice n)} (hPold : «Σ».IsPrimitiveCollection P)
    (hP : («Σ».simultaneousSubdivision T hT hne hdisj).IsPrimitiveCollection P)
    (i : ι) : («Σ».starSubdivision (T i) (hT i) (hne i)).IsPrimitiveCollection P := by
  have he : ∀ j, (∑ v ∈ T j, v) ∉ P := fun j hh =>
    «Σ».sum_rays_not_mem_rays (hT j) (hcard j) (hPold.1 hh)
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    exact «Σ».old_ray_mem_starSubdivision_rays (T i) (hT i) (hne i) (hcard i) (hPold.1 hv)
  · intro hh
    exact hPold.2.1 ((«Σ».mem_starSubdivision_without_sum_iff (T i) (hT i) (hne i)
      (he i)).mp hh).1
  · intro s hs
    have hes : ∀ j, (∑ v ∈ T j, v) ∉ s := fun j hh => he j (hs.subset hh)
    have hcone := («Σ».simultaneous_cone_without_sums_iff T hT hne hdisj hes).mp (hP.2.2 s hs)
    exact «Σ».mem_starSubdivision_of_unchanged (T i) (hT i) (hne i) hcone.1 (hcone.2 i)

include hcard in
/-- A collection containing exactly one selected sum ray is already
primitive on the corresponding single subdivision. -/
theorem simultaneous_primitive_one_sum_single_star
    {P : Finset (Lattice n)}
    (hP : («Σ».simultaneousSubdivision T hT hne hdisj).IsPrimitiveCollection P)
    (i : ι) (hei : (∑ v ∈ T i, v) ∈ P)
    (heother : ∀ j, j ≠ i → (∑ v ∈ T j, v) ∉ P) :
    («Σ».starSubdivision (T i) (hT i) (hne i)).IsPrimitiveCollection P := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    have hh := hP.1 hv
    rw [«Σ».simultaneous_rays_eq T hT hne hdisj hcard] at hh
    rcases Finset.mem_union.mp hh with hh | hh
    · exact «Σ».old_ray_mem_starSubdivision_rays (T i) (hT i) (hne i) (hcard i) hh
    · obtain ⟨j, hj, hvj⟩ := Finset.mem_image.mp hh
      have hji : j = i := by
        by_contra hh
        exact heother j hh (hvj.symm ▸ hv)
      subst j
      simpa only [hvj] using «Σ».sum_mem_starSubdivision_rays (T i) (hT i) (hne i)
  · intro hh
    exact hP.2.1 ((«Σ».simultaneous_cone_over_sum_iff T hT hne hdisj hcard i hei).mpr hh)
  · intro s hs
    by_cases hes : (∑ v ∈ T i, v) ∈ s
    · exact («Σ».simultaneous_cone_over_sum_iff T hT hne hdisj hcard i hes).mp (hP.2.2 s hs)
    · have hall : ∀ j, (∑ v ∈ T j, v) ∉ s := by
        intro j hh
        by_cases hji : j = i
        · exact hes (hji ▸ hh)
        · exact heother j hji (hs.subset hh)
      have hcone := («Σ».simultaneous_cone_without_sums_iff T hT hne hdisj hall).mp (hP.2.2 s hs)
      exact «Σ».mem_starSubdivision_of_unchanged (T i) (hT i) (hne i) hcone.1 (hcone.2 i)

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricSimultaneousPrimitive
-- END ORIGINAL PaperVerification.ToricSimultaneousPrimitive


-- BEGIN ORIGINAL PaperVerification.ToricTwoExceptionalPositive
section Source_ToricTwoExceptionalPositive

-- original header: module

-- original header: public import PaperVerification.ToricFiberWalls
-- original header: public import Mathlib.Tactic.Tauto

-- original header: @[expose] public section

/-!
# Two positive exceptional rays: the actual wall argument

The proof uses only actual full cones, their integral bases, and neighboring
cones. A shared fiber direction would give two opposite rays at one wall.
Uniqueness forces those rays to agree, while the pair relation makes their
exceptional coordinates have opposite signs. Counting the remaining common
wall rays gives the base-dimension bound.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan.PrimitiveRelation

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} (R : «Σ».PrimitiveRelation)

/-- Replace one of the two positive rays in a neighboring wall cone.
The added ray is required to avoid the primitive relation's support; this
is later verified from its negative transverse coordinate. -/
theorem pair_transport_neighbor (hR : R.IsCombinatoriallyContractible)
    (e f : Lattice n) (hef : e ≠ f) (hpositive : R.positive = {e, f})
    (W : Finset (Lattice n)) (hW : Disjoint W R.positive)
    (hN : R.negative ⊆ W) (k z : Lattice n)
    (hk : k ∈ W) (hkN : k ∉ R.negative)
    (hzP : z ∉ R.positive) (hzN : z ∉ R.negative)
    (hzcone : insert z ((insert e W).erase k) ∈ «Σ».cones) :
    insert z ((insert f W).erase k) ∈ «Σ».cones := by
  let V := (W.erase k) \ R.negative
  let ν := insert z V
  have hNe : e ∉ R.negative := by
    intro he
    exact Finset.disjoint_left.mp R.disjoint
      (hpositive.symm ▸ Finset.mem_insert_self _ _) he
  have heW : e ∉ W := fun he => Finset.disjoint_left.mp hW he
    (hpositive.symm ▸ Finset.mem_insert_self _ _)
  have hfW : f ∉ W := fun hf => Finset.disjoint_left.mp hW hf
    (hpositive.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hke : k ≠ e := fun h => heW (h ▸ hk)
  have hkf : k ≠ f := fun h => hfW (h ▸ hk)
  have hNerase : R.negative ⊆ W.erase k := by
    intro u hu
    exact Finset.mem_erase.mpr ⟨fun h => hkN (h ▸ hu), hN hu⟩
  have hνsub : ν ⊆ insert z ((insert e W).erase k) := by
    intro u hu
    rcases Finset.mem_insert.mp hu with huz | huV
    · exact Finset.mem_insert.mpr (Or.inl huz)
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr
        ⟨(Finset.mem_erase.mp (Finset.mem_sdiff.mp huV).1).1,
          Finset.mem_insert_of_mem (Finset.mem_of_mem_erase (Finset.mem_sdiff.mp huV).1)⟩)
  have hν : ν ∈ «Σ».cones := «Σ».downward _ hzcone ν hνsub
  have hdisj : Disjoint ν (R.positive ∪ R.negative) := by
    apply Finset.disjoint_left.mpr
    intro u hu hPN
    rcases Finset.mem_insert.mp hu with huz | huV
    · subst u
      exact (Finset.mem_union.mp hPN).elim hzP hzN
    · obtain ⟨huW, huN⟩ := Finset.mem_sdiff.mp huV
      rcases Finset.mem_union.mp hPN with huP | huN'
      · exact Finset.disjoint_left.mp hW (Finset.mem_of_mem_erase huW) huP
      · exact huN huN'
  have hNν : R.negative ∪ ν ∈ «Σ».cones := by
    apply «Σ».downward _ hzcone
    apply Finset.union_subset
    · intro u hu
      exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr
        ⟨(Finset.mem_erase.mp (hNerase hu)).1, Finset.mem_insert_of_mem (hN hu)⟩)
    · exact hνsub
  have heP : e ∈ R.positive := hpositive.symm ▸ Finset.mem_insert_self _ _
  have hnew := hR ν hν hdisj hNν e heP
  have heq : R.positive.erase e ∪ R.negative ∪ ν =
      insert z ((insert f W).erase k) := by
    have hpos : R.positive.erase e = {f} := by
      rw [hpositive, Finset.erase_insert
        (by simpa only [Finset.mem_singleton] using hef)]
    rw [hpos]
    ext u
    have huN : u ∈ R.negative → u ≠ k ∧ u ∈ W := fun h =>
      Finset.mem_erase.mp (hNerase h)
    have huf : u = f → u ≠ k := by
      rintro rfl
      exact hkf.symm
    simp only [Finset.mem_union, Finset.mem_singleton,
      ν, V, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_erase]
    tauto
  exact heq ▸ hnew

/-- Two actual neighboring full bases identify the special coordinate by
a sign change. Coordinates at wall rays outside the focus are unchanged. -/
theorem pair_wall_coordinate_identities
    (e f : Lattice n) (hef : e ≠ f) (hpositive : R.positive = {e, f})
    (W : Finset (Lattice n)) (hN : R.negative ⊆ W)
    (b c : Module.Basis (Fin n) ℤ (Lattice n)) (j l : Fin n)
    (hb : insert e W = Finset.univ.image b) (hc : insert f W = Finset.univ.image c)
    (hbj : b j = e) (hcl : c l = f) (heW : e ∉ W) (hfW : f ∉ W)
    (i k : Fin n) (hik : b i = c k) (hiW : b i ∈ W) (hiN : b i ∉ R.negative) :
    c.coord l = -b.coord j ∧ c.coord k = b.coord i := by
  have hij : i ≠ j := fun h => heW (hbj ▸ (h ▸ hiW))
  have hkl : k ≠ l := by
    intro h
    exact hfW (hcl ▸ (h ▸ (hik ▸ hiW)))
  have hwall_b (u : Lattice n) (hu : u ∈ W) : b.coord j u = 0 := by
    rw [basis_coord_of_mem_ray_set b j (hb ▸ Finset.mem_insert_of_mem hu)]
    exact if_neg (show u ≠ b j from fun h => heW (hbj ▸ (h ▸ hu)))
  have hwall_c (u : Lattice n) (hu : u ∈ W) : c.coord l u = 0 := by
    rw [basis_coord_of_mem_ray_set c l (hc ▸ Finset.mem_insert_of_mem hu)]
    exact if_neg (show u ≠ c l from fun h => hfW (hcl ▸ (h ▸ hu)))
  have heq : e + f = ∑ u ∈ R.negative, (R.coefficient u : ℤ) • u := by
    simpa only [hpositive, Finset.sum_pair hef] using R.equation
  have hbf : b.coord j f = -1 := by
    have hn : (∑ u ∈ R.negative, (R.coefficient u : ℤ) * b.coord j u) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      rw [hwall_b u (hN hu), mul_zero]
    have h := congrArg (b.coord j) heq
    simp only [map_add, map_sum, map_smul, smul_eq_mul] at h
    rw [hn, ← hbj, Module.Basis.coord_apply, Module.Basis.repr_self_apply, if_pos rfl] at h
    omega
  have hce : c.coord l e = -1 := by
    have h := congrArg (c.coord l) heq
    have hn : (∑ u ∈ R.negative, (R.coefficient u : ℤ) * c.coord l u) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      rw [hwall_c u (hN hu), mul_zero]
    simp only [map_add, map_sum, map_smul, smul_eq_mul] at h
    have hcf : c.coord l f = 1 := by
      rw [← hcl, Module.Basis.coord_apply, Module.Basis.repr_self_apply, if_pos rfl]
    rw [hn, hcf] at h
    omega
  have hif : b.coord i f = 0 := by
    have hn : (∑ u ∈ R.negative, (R.coefficient u : ℤ) * b.coord i u) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      rw [basis_coord_of_mem_ray_set b i (hb ▸ Finset.mem_insert_of_mem (hN hu)),
        if_neg (show u ≠ b i from fun h => hiN (h ▸ hu)), mul_zero]
    have h := congrArg (b.coord i) heq
    simp only [map_add, map_sum, map_smul, smul_eq_mul] at h
    rw [hn, ← hbj, Module.Basis.coord_apply, Module.Basis.repr_self_apply,
      if_neg hij.symm, zero_add] at h
    exact h
  constructor
  · apply b.ext
    intro a
    by_cases haj : a = j
    · subst a
      simp only [hbj, hce, LinearMap.neg_apply]
      rw [← hbj, Module.Basis.coord_apply, Module.Basis.repr_self_apply, if_pos rfl]
    · have haw : b a ∈ W := by
        have hm : b a ∈ insert e W := hb.symm ▸ Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
        rcases Finset.mem_insert.mp hm with he | hw
        · exact (haj (b.injective (he.trans hbj.symm))).elim
        · exact hw
      simp only [hwall_c _ haw, LinearMap.neg_apply, Module.Basis.coord_apply,
        Module.Basis.repr_self_apply, if_neg haj, neg_zero]
  · apply c.ext
    intro a
    by_cases hal : a = l
    · subst a
      rw [hcl, hif, ← hcl, Module.Basis.coord_apply,
        Module.Basis.repr_self_apply, if_neg hkl.symm]
    · have haw : c a ∈ W := by
        have hm : c a ∈ insert f W := hc.symm ▸ Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
        rcases Finset.mem_insert.mp hm with he | hw
        · exact (hal (c.injective (he.trans hcl.symm))).elim
        · exact hw
      rw [basis_coord_of_mem_ray_set b i (hb ▸ Finset.mem_insert_of_mem haw), hik,
        basis_coord_of_mem_ray_set c k (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)]

/-- A common wall direction outside the pair focus cannot be a fiber
direction for both positive exceptional rays. -/
theorem pair_no_shared_fiber_direction (hR : R.IsCombinatoriallyContractible)
    (e f : Lattice n) (hef : e ≠ f) (hpositive : R.positive = {e, f})
    (W : Finset (Lattice n)) (hW : Disjoint W R.positive)
    (hN : R.negative ⊆ W)
    (b c : Module.Basis (Fin n) ℤ (Lattice n)) (j l i k : Fin n)
    (hb : insert e W = Finset.univ.image b) (hc : insert f W = Finset.univ.image c)
    (hbj : b j = e) (hcl : c l = f) (hik : b i = c k)
    (hiW : b i ∈ W) (hiN : b i ∉ R.negative)
    (z z' : Lattice n)
    (hz : insert z ((Finset.univ.erase i).image b) ∈ «Σ».cones)
    (hz' : insert z' ((Finset.univ.erase k).image c) ∈ «Σ».cones)
    (hzi : b.repr z i = -1) (hzj : 0 < b.repr z j)
    (hz'k : c.repr z' k = -1) (hz'l : 0 < c.repr z' l) : False := by
  have heW : e ∉ W := fun he => Finset.disjoint_left.mp hW he
    (hpositive.symm ▸ Finset.mem_insert_self _ _)
  have hfW : f ∉ W := fun hf => Finset.disjoint_left.mp hW hf
    (hpositive.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  obtain ⟨hl, hk⟩ := R.pair_wall_coordinate_identities e f hef hpositive W hN
    b c j l hb hc hbj hcl heW hfW i k hik hiW hiN
  have hij : i ≠ j := fun h => heW (hbj ▸ (h ▸ hiW))
  have hif : b.coord i f = 0 := by
    rw [← hk, ← hcl, Module.Basis.coord_apply, Module.Basis.repr_self_apply]
    apply if_neg
    intro h
    exact hfW (hcl ▸ (h ▸ (hik ▸ hiW)))
  have hzP : z ∉ R.positive := by
    intro h
    rcases (by simpa only [hpositive, Finset.mem_insert, Finset.mem_singleton] using h : z = e ∨ z = f) with h | h
    · rw [h, ← hbj, Module.Basis.repr_self_apply, if_neg hij.symm] at hzi
      omega
    · have hz0 : b.repr z i = 0 := by simpa only [h, Module.Basis.coord_apply] using hif
      omega
  have hzN : z ∉ R.negative := by
    intro h
    have hzU : z ∈ Finset.univ.image b := hb ▸ Finset.mem_insert_of_mem (hN h)
    have hzcoord := basis_coord_of_mem_ray_set b i hzU
    have hzne : z ≠ b i := fun he => hiN (he ▸ h)
    rw [if_neg hzne] at hzcoord
    change b.repr z i = 0 at hzcoord
    omega
  have hzactual : insert z ((insert e W).erase (b i)) ∈ «Σ».cones := by
    simpa only [Finset.image_erase b.injective, ← hb] using hz
  have htransport := R.pair_transport_neighbor hR e f hef hpositive W hW hN
    (b i) z hiW hiN hzP hzN hzactual
  have htransport' : insert z ((Finset.univ.erase k).image c) ∈ «Σ».cones := by
    simpa only [Finset.image_erase c.injective, ← hc, ← hik] using htransport
  have hzk : c.repr z k = -1 := by
    change c.coord k z = -1
    rw [hk]
    exact hzi
  have hzz' := «Σ».opposite_wall_ray_unique c k z z' htransport' hz' hzk hz'k
  have hsign : c.repr z l = -b.repr z j := by
    change c.coord l z = -b.coord j z
    rw [hl]
    rfl
  rw [← hzz'] at hz'l
  omega

/-- The common-wall counting form of Lemma 5.1(ii). The integers `d₁,d₂`
are the actual numbers of complementary wall directions in the two local
fiber configurations. -/
theorem pair_negative_card_bound_of_wall_data
    (hR : R.IsCombinatoriallyContractible)
    (e f : Lattice n) (hef : e ≠ f) (hpositive : R.positive = {e, f})
    (W : Finset (Lattice n)) (hW : Disjoint W R.positive)
    (hN : R.negative ⊆ W)
    (b c : Module.Basis (Fin n) ℤ (Lattice n)) (j l : Fin n)
    (hb : insert e W = Finset.univ.image b) (hc : insert f W = Finset.univ.image c)
    (hbj : b j = e) (hcl : c l = f)
    (F G : Finset (Fin n)) (hjF : j ∉ F) (hlG : l ∉ G)
    (d₁ d₂ : ℕ) (hFd : F.card + d₁ + 1 = n) (hGd : G.card + d₂ + 1 = n)
    (hF : ∀ i ∈ F, ∃ z : Lattice n,
      insert z ((Finset.univ.erase i).image b) ∈ «Σ».cones ∧
      b.repr z i = -1 ∧ 0 < b.repr z j)
    (hG : ∀ k ∈ G, ∃ z : Lattice n,
      insert z ((Finset.univ.erase k).image c) ∈ «Σ».cones ∧
      c.repr z k = -1 ∧ 0 < c.repr z l) :
    n ≤ R.negative.card + d₁ + d₂ + 1 := by
  let A := F.image b
  let B := G.image c
  have heW : e ∉ W := fun he => Finset.disjoint_left.mp hW he
    (hpositive.symm ▸ Finset.mem_insert_self _ _)
  have hfW : f ∉ W := fun hf => Finset.disjoint_left.mp hW hf
    (hpositive.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hAW : A ⊆ W := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hmem : b i ∈ insert e W :=
      hb.symm ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    rcases Finset.mem_insert.mp hmem with he | hw
    · exact (hjF ((b.injective (he.trans hbj.symm)) ▸ hi)).elim
    · exact hw
  have hBW : B ⊆ W := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    have hmem : c k ∈ insert f W :=
      hc.symm ▸ Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩
    rcases Finset.mem_insert.mp hmem with he | hw
    · exact (hlG ((c.injective (he.trans hcl.symm)) ▸ hk)).elim
    · exact hw
  have hcover : W \ R.negative ⊆ (W \ A) ∪ (W \ B) := by
    intro x hx
    obtain ⟨hxW, hxN⟩ := Finset.mem_sdiff.mp hx
    by_cases hxA : x ∈ A
    · by_cases hxB : x ∈ B
      · obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hxA
        obtain ⟨k, hk, hkx⟩ := Finset.mem_image.mp hxB
        obtain ⟨z, hz, hzi, hzj⟩ := hF i hi
        obtain ⟨z', hz', hz'k, hz'l⟩ := hG k hk
        have hiW : b i ∈ W := by simpa only [hix] using hxW
        have hiN : b i ∉ R.negative := by simpa only [hix] using hxN
        exact (R.pair_no_shared_fiber_direction hR e f hef hpositive W hW hN
          b c j l i k hb hc hbj hcl (hix.trans hkx.symm) hiW hiN
          z z' hz hz' hzi hzj hz'k hz'l).elim
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxW, hxB⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxW, hxA⟩)
  have hcount := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have hNcard := Finset.card_sdiff_add_card_eq_card hN
  have hAcard := Finset.card_sdiff_add_card_eq_card hAW
  have hBcard := Finset.card_sdiff_add_card_eq_card hBW
  have hAF : A.card = F.card := Finset.card_image_of_injective _ b.injective
  have hBG : B.card = G.card := Finset.card_image_of_injective _ c.injective
  have hWcard : W.card + 1 = n := by
    have h := congrArg Finset.card hb
    simpa only [Finset.card_insert_of_notMem heW,
      Finset.card_image_of_injective _ b.injective, Finset.card_fin] using h
  omega

end SmoothCompleteFan.PrimitiveRelation

end PaperVerification.ToricGeometry
end
end Source_ToricTwoExceptionalPositive
-- END ORIGINAL PaperVerification.ToricTwoExceptionalPositive


-- BEGIN ORIGINAL PaperVerification.ToricSelectedLoci
section Source_ToricSelectedLoci

-- original header: module

-- original header: public import PaperVerification.ToricSimultaneousPrimitive
-- original header: public import PaperVerification.ToricFiberWalls
-- original header: public import PaperVerification.ToricTwoExceptionalPositive

-- original header: @[expose] public section

/-!
# Selected disjoint loci, including the unblown divisors

Only focus cones of cardinality at least two are subdivided. A singleton
focus remains its original divisor ray. Every selected exceptional ray has
the same local wall data, and distinct selected rays have no common cone.
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

abbrev BlowupIndices := {i : ι // 2 ≤ (R i).negative.card}

def selectedStarFocus (i : «Σ».BlowupIndices R) : Finset (Lattice n) := (R i).negative

include hdisj in
theorem selectedStarFocus_disjoint :
    «Σ».PairwiseDisjointFoci («Σ».selectedStarFocus R) := by
  intro i j hij
  exact hdisj i j (fun hh => hij (Subtype.ext hh))

def selectedFan : SmoothCompleteFan n :=
  «Σ».simultaneousSubdivision («Σ».selectedStarFocus R)
    (fun i => (R i).negative_cone) (fun i => hne i)
    («Σ».selectedStarFocus_disjoint R hdisj)

def selectedRay (i : ι) : Lattice n := ∑ v ∈ (R i).negative, v

def selectedBaseDimension (i : ι) : ℕ := n - (R i).fiberDimension - (R i).negative.card

include hR in
theorem selected_dimension_eq (i : ι) :
    n = (R i).fiberDimension + (R i).negative.card + «Σ».selectedBaseDimension R i := by
  have hh := (R i).contractible_dimension_bound (hR i)
  unfold selectedBaseDimension
  omega

include hne in
theorem selected_focus_of_not_blowup (i : ι) (hi : ¬ 2 ≤ (R i).negative.card) :
    (R i).negative = {«Σ».selectedRay R i} := by
  have hpos := Finset.card_pos.mpr (hne i)
  have hc : (R i).negative.card = 1 := by omega
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
  simp only [selectedRay, hp, Finset.sum_singleton]

include hdisj in
theorem selectedRay_injective : Function.Injective («Σ».selectedRay R) :=
  «Σ».simultaneous_sum_rays_injective (fun i => (R i).negative)
    (fun i => (R i).negative_cone) hdisj

/-- Any cone of the selected fan has an actual old parent cone. -/
theorem selected_cone_old_parent {s : Finset (Lattice n)}
    (hs : s ∈ («Σ».selectedFan R hne hdisj).cones) :
    ∃ U ∈ «Σ».cones, latticeRayCone s ≤ latticeRayCone U := by
  obtain ⟨C, hC, hsC⟩ := (mem_finiteConeFamilyClosure
    («Σ».simultaneousCandidates («Σ».selectedStarFocus R)) s).mp hs
  rcases («Σ».mem_simultaneousCandidates («Σ».selectedStarFocus R) C).mp hC with
    ⟨hC, hnone⟩ | ⟨i, U, hU, p, hp, hTU, rfl⟩
  · exact ⟨C, hC, latticeRayCone_mono hsC⟩
  · exact ⟨U, hU, (latticeRayCone_mono hsC).trans (latticeRayCone_starRaySet_le hTU p)⟩

/-- All selected rays, both new and unblown, are pairwise disjoint in the
literal fan-incidence sense. -/
theorem selected_no_common_rays (i j : ι) (hij : i ≠ j)
    {s : Finset (Lattice n)} (hs : s ∈ («Σ».selectedFan R hne hdisj).cones)
    (hi : «Σ».selectedRay R i ∈ s) : «Σ».selectedRay R j ∉ s := by
  intro hj
  obtain ⟨U, hU, hsU⟩ := «Σ».selected_cone_old_parent R hne hdisj hs
  have hiU : (R i).negative ⊆ U :=
    («Σ».sum_rays_mem_cone_iff (R i).negative_cone hU).mp
      (hsU (latticeRayCone_generator s hi))
  have hjU : (R j).negative ⊆ U :=
    («Σ».sum_rays_mem_cone_iff (R j).negative_cone hU).mp
      (hsU (latticeRayCone_generator s hj))
  exact hdisj i j hij ⟨U, hU, Finset.union_subset hiU hjU⟩

/-- The full star of an unblown selected divisor is the original one. -/
theorem selected_divisor_cone_iff (i : ι) (hi : ¬ 2 ≤ (R i).negative.card)
    {s : Finset (Lattice n)} (he : «Σ».selectedRay R i ∈ s) :
    s ∈ («Σ».selectedFan R hne hdisj).cones ↔ s ∈ «Σ».cones := by
  have hfocus := «Σ».selected_focus_of_not_blowup R hne i hi
  apply «Σ».simultaneous_cone_over_disjoint_focus_iff («Σ».selectedStarFocus R)
    (fun j => (R j).negative_cone) (fun j => hne j)
    («Σ».selectedStarFocus_disjoint R hdisj) (fun j => j.property)
    (R i).negative_cone
  · intro j
    have hji : (j : ι) ≠ i := by
      intro hh
      exact hi (hh ▸ j.property)
    exact hdisj j i hji
  · simpa only [hfocus, Finset.singleton_subset_iff] using he

include hR in
/-- Every selected ray has the exact number of fiber walls claimed by
its contraction parameters, with all neighboring cones on the final fan. -/
theorem selected_fiber_wall_data (i : ι)
    {s : Finset (Lattice n)} (hs : s ∈ («Σ».selectedFan R hne hdisj).cones)
    (hscard : s.card = n) (he : «Σ».selectedRay R i ∈ s) :
    ∃ (b : Module.Basis (Fin n) ℤ (Lattice n)) (j : Fin n) (F : Finset (Fin n)),
      s = Finset.univ.image b ∧ b j = «Σ».selectedRay R i ∧ j ∉ F ∧
      F.card + «Σ».selectedBaseDimension R i + 1 = n ∧
      ∀ k ∈ F, ∃ z : Lattice n,
        insert z ((Finset.univ.erase k).image b) ∈ («Σ».selectedFan R hne hdisj).cones ∧
        b.repr z k = -1 ∧ 0 < b.repr z j := by
  have hdim := (R i).contractible_dimension_bound (hR i)
  have hr := (R i).fiberDimension_pos
  have hq := Finset.card_pos.mpr (hne i)
  by_cases hi : 2 ≤ (R i).negative.card
  · let i' : «Σ».BlowupIndices R := ⟨i, hi⟩
    have hsingle := («Σ».simultaneous_cone_over_sum_iff («Σ».selectedStarFocus R)
      (fun j => (R j).negative_cone) (fun j => hne j)
      («Σ».selectedStarFocus_disjoint R hdisj) (fun j => j.property) i' he).mp hs
    obtain ⟨b, j, F, hsb, hbj, hjF, hFcard, hF⟩ :=
      (R i).exceptional_fiber_wall_data (hR i) (hne i) hi hsingle hscard he
    refine ⟨b, j, F, hsb, hbj, hjF, ?_, ?_⟩
    · unfold selectedBaseDimension
      omega
    · intro k hk
      obtain ⟨z, hz, hzk, hzj⟩ := hF k hk
      have hjk : j ≠ k := fun hh => hjF (hh.symm ▸ hk)
      have hez : «Σ».selectedRay R i ∈ insert z ((Finset.univ.erase k).image b) := by
        apply Finset.mem_insert_of_mem
        exact Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨hjk, Finset.mem_univ j⟩, hbj⟩
      exact ⟨z, («Σ».simultaneous_cone_over_sum_iff («Σ».selectedStarFocus R)
        (fun j => (R j).negative_cone) (fun j => hne j)
        («Σ».selectedStarFocus_disjoint R hdisj) (fun j => j.property) i' hez).mpr hz,
        hzk, hzj⟩
  · have hfocus := «Σ».selected_focus_of_not_blowup R hne i hi
    have hold := («Σ».selected_divisor_cone_iff R hne hdisj i hi he).mp hs
    obtain ⟨b, j, F, hsb, hbj, hjF, hFcard, hF⟩ :=
      (R i).divisor_fiber_wall_data (hR i) («Σ».selectedRay R i) hfocus hold hscard he
    refine ⟨b, j, F, hsb, hbj, hjF, ?_, ?_⟩
    · have hc : (R i).negative.card = 1 := by simp only [hfocus, Finset.card_singleton]
      unfold selectedBaseDimension
      omega
    · intro k hk
      obtain ⟨z, hz, hzk, hzj⟩ := hF k hk
      have hjk : j ≠ k := fun hh => hjF (hh.symm ▸ hk)
      have hez : «Σ».selectedRay R i ∈ insert z ((Finset.univ.erase k).image b) := by
        apply Finset.mem_insert_of_mem
        exact Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨hjk, Finset.mem_univ j⟩, hbj⟩
      exact ⟨z, («Σ».selected_divisor_cone_iff R hne hdisj i hi hez).mpr hz, hzk, hzj⟩

/-- Two selected rays in a primitive collection already constitute the
whole positive collection, since their pair is an actual noncone. -/
theorem primitive_selected_pair_eq
    {P : Finset (Lattice n)} (hP : («Σ».selectedFan R hne hdisj).IsPrimitiveCollection P)
    (i j : ι) (hij : i ≠ j) (hi : «Σ».selectedRay R i ∈ P) (hj : «Σ».selectedRay R j ∈ P) :
    P = {«Σ».selectedRay R i, «Σ».selectedRay R j} := by
  have hsub : {«Σ».selectedRay R i, «Σ».selectedRay R j} ⊆ P := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hi, hj⟩
  by_contra hneP
  have hproper : {«Σ».selectedRay R i, «Σ».selectedRay R j} ⊂ P :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub, Ne.symm hneP⟩
  have hcone := hP.2.2 _ hproper
  exact «Σ».selected_no_common_rays R hne hdisj i j hij hcone
    (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricSelectedLoci
-- END ORIGINAL PaperVerification.ToricSelectedLoci


-- BEGIN ORIGINAL PaperVerification.ToricSelectedBounds
section Source_ToricSelectedBounds

-- original header: module

-- original header: public import PaperVerification.ToricSelectedLoci

-- original header: @[expose] public section

/-!
# The complete positive-selected-ray bounds

These are the numerical conclusions of Lemma 5.1(i),(ii), proved on the
actual selected fan. The unblown codimension-one loci are included.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan.PrimitiveRelation

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} (S : «Σ».PrimitiveRelation)

/-- A contractible primitive pair is represented by two actual full cones
with one common wall containing its entire negative focus. -/
theorem exists_full_pair_wall (hpure : «Σ».IsPure)
    (hS : S.IsCombinatoriallyContractible) (e f : Lattice n) (hef : e ≠ f)
    (hP : S.positive = {e, f}) :
    ∃ W : Finset (Lattice n), Disjoint W S.positive ∧ S.negative ⊆ W ∧
      insert e W ∈ «Σ».cones ∧ (insert e W).card = n ∧
      insert f W ∈ «Σ».cones ∧ (insert f W).card = n := by
  have heP : e ∈ S.positive := hP.symm ▸ Finset.mem_insert_self _ _
  have hfP : f ∈ S.positive := hP.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hcore := S.contractible_core_cone hS hfP
  have hcoreEq : S.positive.erase f ∪ S.negative = insert e S.negative := by
    rw [hP, Finset.erase_insert_of_ne hef, Finset.erase_singleton]
    ext v
    simp
  rw [hcoreEq] at hcore
  obtain ⟨U, hU, hcoreU, hUcard⟩ := hpure _ hcore
  have heU : e ∈ U := hcoreU (Finset.mem_insert_self _ _)
  have hNU : S.negative ⊆ U := (Finset.subset_insert _ _).trans hcoreU
  have hfU : f ∉ U := by
    intro hh
    apply S.primitive.2.1
    apply «Σ».downward U hU S.positive
    rw [hP]
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨heU, hh⟩
  let W := U.erase e
  have heW : e ∉ W := Finset.notMem_erase e U
  have hfW : f ∉ W := fun hh => hfU (Finset.mem_of_mem_erase hh)
  have hW : W ∈ «Σ».cones := «Σ».downward U hU W (Finset.erase_subset _ _)
  have hNW : S.negative ⊆ W := by
    intro v hv
    have hve : v ≠ e := fun hh => Finset.disjoint_left.mp S.disjoint heP (hh ▸ hv)
    exact Finset.mem_erase.mpr ⟨hve, hNU hv⟩
  have hfirst : insert e W = U := Finset.insert_erase heU
  have hsecond := S.fill_cone_with_positive_except hS hW hNW heP heW
  have hsecondEq : S.positive.erase e ∪ W = insert f W := by simp [hP, hef]
  rw [hsecondEq] at hsecond
  have hWdisj : Disjoint W S.positive := by
    apply Finset.disjoint_left.mpr
    intro v hv hvP
    rcases (by simpa only [hP, Finset.mem_insert, Finset.mem_singleton] using hvP :
      v = e ∨ v = f) with hh | hh
    · exact heW (hh ▸ hv)
    · exact hfW (hh ▸ hv)
  refine ⟨W, hWdisj, hNW, hfirst.symm ▸ hU, hfirst.symm ▸ hUcard, hsecond, ?_⟩
  have hcard := congrArg Finset.card hfirst
  rw [Finset.card_insert_of_notMem heW] at hcard
  rw [Finset.card_insert_of_notMem hfW]
  exact hcard.trans hUcard

end SmoothCompleteFan.PrimitiveRelation

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable {ι : Type*} [Fintype ι] (R : ι → «Σ».PrimitiveRelation)
variable (hR : ∀ i, (R i).IsCombinatoriallyContractible)
variable (hne : ∀ i, (R i).negative.Nonempty)
variable (hdisj : «Σ».PairwiseDisjointFoci (fun i => (R i).negative))

include hR in
/-- A primitive collection with exactly one positive selected ray has at
most `b+2` rays, including the unblown divisor case. -/
theorem selected_one_positive_card_bound
    (S : («Σ».selectedFan R hne hdisj).PrimitiveRelation)
    (i : ι) (hiS : «Σ».selectedRay R i ∈ S.positive)
    (hother : ∀ j, j ≠ i → «Σ».selectedRay R j ∉ S.positive) :
    S.positive.card ≤ «Σ».selectedBaseDimension R i + 2 := by
  have hdim := (R i).contractible_dimension_bound (hR i)
  by_cases hi : 2 ≤ (R i).negative.card
  · let i' : «Σ».BlowupIndices R := ⟨i, hi⟩
    have hsingle := «Σ».simultaneous_primitive_one_sum_single_star («Σ».selectedStarFocus R)
      (fun j => (R j).negative_cone) (fun j => hne j)
      («Σ».selectedStarFocus_disjoint R hdisj) (fun j => j.property)
      S.primitive i' hiS (by
        intro j hji
        exact hother j (fun hh => hji (Subtype.ext hh)))
    have hh := (R i).primitive_with_exceptional_card_bound (hR i) (hne i) hi hsingle hiS
    unfold selectedBaseDimension
    omega
  · have hfocus := «Σ».selected_focus_of_not_blowup R hne i hi
    have heStar : ∀ j : «Σ».BlowupIndices R,
        (∑ v ∈ «Σ».selectedStarFocus R j, v) ∉ S.positive := by
      intro j
      have hji : (j : ι) ≠ i := fun hh => hi (hh ▸ j.property)
      exact hother j hji
    have hneq : ∀ j : «Σ».BlowupIndices R, S.positive ≠ «Σ».selectedStarFocus R j := by
      intro j hh
      have heT : «Σ».selectedRay R i ∈ (R j).negative := by
        change «Σ».selectedRay R i ∈ «Σ».selectedStarFocus R j
        rw [← hh]
        exact hiS
      have hiT : (R i).negative ⊆ (R j).negative := by
        simpa only [hfocus, Finset.singleton_subset_iff] using heT
      have hij : i ≠ (j : ι) := fun h => hi (h.symm ▸ j.property)
      exact hdisj i j hij ⟨(R j).negative, (R j).negative_cone,
        Finset.union_subset hiT (Finset.Subset.refl _)⟩
    have hPold := «Σ».simultaneous_primitive_pushdown_collection («Σ».selectedStarFocus R)
      (fun j => (R j).negative_cone) (fun j => hne j)
      («Σ».selectedStarFocus_disjoint R hdisj) (fun j => j.property)
      S.primitive heStar hneq
    have hh := (R i).primitive_with_divisor_focus_card_bound (hR i)
      («Σ».selectedRay R i) hfocus hPold hiS
    have hc : (R i).negative.card = 1 := by simp only [hfocus, Finset.card_singleton]
    unfold selectedBaseDimension
    omega

include hR in
/-- The full two-positive bound of Lemma 5.1(ii), on the genuine selected
fan and with every local fiber direction constructed from the old fan. -/
theorem selected_two_positive_card_bound (hpure : «Σ».IsPure)
    (S : («Σ».selectedFan R hne hdisj).PrimitiveRelation)
    (hS : S.IsCombinatoriallyContractible)
    (i j : ι) (hij : i ≠ j)
    (hiS : «Σ».selectedRay R i ∈ S.positive) (hjS : «Σ».selectedRay R j ∈ S.positive) :
    S.positive.card = 2 ∧
      n ≤ S.negative.card + «Σ».selectedBaseDimension R i + «Σ».selectedBaseDimension R j + 1 := by
  have hP := «Σ».primitive_selected_pair_eq R hne hdisj S.primitive i j hij hiS hjS
  have hef : «Σ».selectedRay R i ≠ «Σ».selectedRay R j :=
    («Σ».selectedRay_injective R hdisj).ne hij
  have hΓpure := «Σ».isPure_simultaneousSubdivision («Σ».selectedStarFocus R) hpure
    (fun k => (R k).negative_cone) (fun k => hne k) («Σ».selectedStarFocus_disjoint R hdisj)
  obtain ⟨W, hW, hNW, hfirst, hfirstcard, hsecond, hsecondcard⟩ :=
    S.exists_full_pair_wall hΓpure hS («Σ».selectedRay R i) («Σ».selectedRay R j) hef hP
  obtain ⟨b, ib, F, hb, hbi, hib, hFcard, hF⟩ :=
    «Σ».selected_fiber_wall_data R hR hne hdisj i hfirst hfirstcard (Finset.mem_insert_self _ _)
  obtain ⟨c, jc, G, hc, hcj, hjc, hGcard, hG⟩ :=
    «Σ».selected_fiber_wall_data R hR hne hdisj j hsecond hsecondcard (Finset.mem_insert_self _ _)
  refine ⟨by simp only [hP, Finset.card_pair hef], ?_⟩
  exact S.pair_negative_card_bound_of_wall_data hS
    («Σ».selectedRay R i) («Σ».selectedRay R j) hef hP W hW hNW
    b c ib jc hb hc hbi hcj F G hib hjc
    («Σ».selectedBaseDimension R i) («Σ».selectedBaseDimension R j) hFcard hGcard hF hG

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricSelectedBounds
-- END ORIGINAL PaperVerification.ToricSelectedBounds


-- BEGIN ORIGINAL PaperVerification.ToricStarPushdown
section Source_ToricStarPushdown

-- original header: module
-- original header: public import PaperVerification.ToricStarCombinatorics
-- original header: @[expose] public section

/-!
# Primitive-relation pushdown when the exceptional ray is not positive

The old positive collection is proved primitive. If the exceptional ray
occurs negatively, its actual sum is expanded with positive integral
coefficients in an actual old cone. The resulting relation is constructed
and its degree pairing with every old divisor coefficient function is
proved to agree with pullback.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

def expandedRayCoefficient {ι : Type*} (s t : Finset ι) (e : ι)
    (c : ι → ℕ) (v : ι) : ℕ :=
  (if v ∈ s.erase e then c v else 0) + (if v ∈ t then c e else 0)

theorem sum_expandedRayCoefficient_smul {ι K E : Type*}
    [CommSemiring K] [AddCommMonoid E] [Module K E]
    (s t : Finset ι) (e : ι) (c : ι → ℕ) (v : ι → E) :
    (∑ i ∈ s.erase e ∪ t, (expandedRayCoefficient s t e c i : K) • v i) =
      (∑ i ∈ s.erase e, (c i : K) • v i) + (c e : K) • ∑ i ∈ t, v i := by
  let U := s.erase e ∪ t
  have hfirst : (∑ i ∈ U, ((if i ∈ s.erase e then c i else 0 : ℕ) : K) • v i) =
      ∑ i ∈ s.erase e, (c i : K) • v i := by
    calc
      (∑ i ∈ U, ((if i ∈ s.erase e then c i else 0 : ℕ) : K) • v i) =
          ∑ i ∈ s.erase e, ((if i ∈ s.erase e then c i else 0 : ℕ) : K) • v i := by
        symm
        apply Finset.sum_subset Finset.subset_union_left
        intro i _ hi
        simp only [if_neg hi, Nat.cast_zero, zero_smul]
      _ = ∑ i ∈ s.erase e, (c i : K) • v i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [if_pos hi]
  have hsecond : (∑ i ∈ U, ((if i ∈ t then c e else 0 : ℕ) : K) • v i) =
      (c e : K) • ∑ i ∈ t, v i := by
    calc
      (∑ i ∈ U, ((if i ∈ t then c e else 0 : ℕ) : K) • v i) =
          ∑ i ∈ t, ((if i ∈ t then c e else 0 : ℕ) : K) • v i := by
        symm
        apply Finset.sum_subset Finset.subset_union_right
        intro i _ hi
        simp only [if_neg hi, Nat.cast_zero, zero_smul]
      _ = ∑ i ∈ t, (c e : K) • v i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [if_pos hi]
      _ = (c e : K) • ∑ i ∈ t, v i := Finset.smul_sum.symm
  simp only [expandedRayCoefficient, Nat.cast_add, add_smul, Finset.sum_add_distrib]
  exact congrArg₂ (· + ·) hfirst hsecond

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable (t : Finset (Lattice n)) (ht : t ∈ «Σ».cones) (hne : t.Nonempty)

/-- Every nonexceptional primitive relation with no positive exceptional
coefficient has a genuine old primitive relation as pushdown. Degree
compatibility is universal over real coefficient functions. -/
theorem primitiveRelation_pushdown_without_positive_sum_data
    (hcard : 2 ≤ t.card) (R : («Σ».starSubdivision t ht hne).PrimitiveRelation)
    (heP : (∑ v ∈ t, v) ∉ R.positive) (hPt : R.positive ≠ t) :
    ∃ S : «Σ».PrimitiveRelation, S.positive = R.positive ∧
      S.negative = (if (∑ v ∈ t, v) ∈ R.negative then
        R.negative.erase (∑ v ∈ t, v) ∪ t else R.negative) ∧
      ∀ a : Lattice n → ℝ, S.degree a = R.degree (starCoefficientBase a t) := by
  let e := ∑ v ∈ t, v
  have hPold := «Σ».primitiveCollection_pushdown_without_sum t ht hne hcard R.primitive heP hPt
  have hpossum (a : Lattice n → ℝ) :
      (∑ v ∈ R.positive, starCoefficientBase a t v) = ∑ v ∈ R.positive, a v := by
    apply Finset.sum_congr rfl
    intro v hv
    have hve : v ≠ (∑ w ∈ t, w) := fun h => heP (h ▸ hv)
    simp only [starCoefficientBase, if_neg hve]
  by_cases heN : e ∈ R.negative
  · obtain ⟨p, hp, hpN, hNold⟩ :=
      («Σ».mem_starSubdivision_with_sum_iff t ht hne hcard heN).mp R.negative_cone
    let N := R.negative.erase e ∪ t
    let c := expandedRayCoefficient R.negative t e R.coefficient
    let Eclassical : Finset (Lattice n) := by
      letI : DecidableEq (Lattice n) := fun x y => Classical.propDecidable (x = y)
      exact R.negative.erase e
    let Nclassical : Finset (Lattice n) := by
      letI : DecidableEq (Lattice n) := fun x y => Classical.propDecidable (x = y)
      exact R.negative.erase e ∪ t
    have hEclassical : Eclassical = R.negative.erase e := by
      ext v
      simp only [Eclassical, Finset.mem_erase]
    have hNclassical : Nclassical = N := by
      ext v
      simp only [Nclassical, N, Finset.mem_union, Finset.mem_erase]
    have hexpand (K E : Type) [CommSemiring K] [AddCommMonoid E] [Module K E]
        (v : Lattice n → E) :
        (∑ i ∈ N, (c i : K) • v i) =
          (∑ i ∈ R.negative.erase e, (R.coefficient i : K) • v i) +
            (R.coefficient e : K) • ∑ i ∈ t, v i := by
      have h := sum_expandedRayCoefficient_smul (K := K) R.negative t e R.coefficient v
      change (∑ i ∈ Nclassical, (c i : K) • v i) =
        (∑ i ∈ Eclassical, (R.coefficient i : K) • v i) +
          (R.coefficient e : K) • ∑ i ∈ t, v i at h
      rw [hNclassical, hEclassical] at h
      exact h
    have hc : ∀ v ∈ N, 0 < c v := by
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · have hvN := Finset.mem_of_mem_erase hv
        have hpos := R.coefficient_pos v hvN
        simp only [c, expandedRayCoefficient, Finset.mem_erase,
          if_pos (Finset.mem_erase.mp hv)]
        omega
      · have hepos := R.coefficient_pos e heN
        simp only [c, expandedRayCoefficient, if_pos hv]
        omega
    have heq : (∑ v ∈ R.positive, v) = ∑ v ∈ N, (c v : ℤ) • v := by
      have hexpandZ := hexpand ℤ (Lattice n) id
      simp only [id_eq] at hexpandZ
      rw [hexpandZ]
      rw [R.equation]
      rw [← Finset.add_sum_erase R.negative (fun v => (R.coefficient v : ℤ) • v) heN]
      change (R.coefficient e : ℤ) • e + _ = _ + (R.coefficient e : ℤ) • e
      exact add_comm _ _
    let S : «Σ».PrimitiveRelation := ⟨R.positive, N, c, hPold, hNold, hc, heq⟩
    refine ⟨S, rfl, ?_, ?_⟩
    · change N = if e ∈ R.negative then N else R.negative
      rw [if_pos heN]
    intro a
    have hneg : (∑ v ∈ N, (c v : ℝ) * a v) =
        ∑ v ∈ R.negative, (R.coefficient v : ℝ) * starCoefficientBase a t v := by
      have hexpandReal := hexpand ℝ ℝ a
      simp only [smul_eq_mul] at hexpandReal
      rw [hexpandReal]
      rw [← Finset.add_sum_erase R.negative
        (fun v => (R.coefficient v : ℝ) * starCoefficientBase a t v) heN]
      have hrest : (∑ v ∈ R.negative.erase e,
          (R.coefficient v : ℝ) * starCoefficientBase a t v) =
          ∑ v ∈ R.negative.erase e, (R.coefficient v : ℝ) * a v := by
        apply Finset.sum_congr rfl
        intro v hv
        have hve := (Finset.mem_erase.mp hv).1
        change v ≠ (∑ w ∈ t, w) at hve
        simp only [starCoefficientBase, if_neg hve]
      have heval : starCoefficientBase a t e = ∑ w ∈ t, a w := by
        unfold starCoefficientBase
        exact if_pos rfl
      rw [hrest, heval]
      ring
    simp only [PrimitiveRelation.degree, S, hpossum, hneg]
  · have hNold := ((«Σ».mem_starSubdivision_without_sum_iff t ht hne heN).mp
      R.negative_cone).1
    let S : «Σ».PrimitiveRelation :=
      ⟨R.positive, R.negative, R.coefficient, hPold, hNold, R.coefficient_pos, R.equation⟩
    refine ⟨S, rfl, ?_, ?_⟩
    · change R.negative = if e ∈ R.negative then R.negative.erase e ∪ t else R.negative
      rw [if_neg heN]
    intro a
    have hneg : (∑ v ∈ R.negative,
        (R.coefficient v : ℝ) * starCoefficientBase a t v) =
        ∑ v ∈ R.negative, (R.coefficient v : ℝ) * a v := by
      apply Finset.sum_congr rfl
      intro v hv
      have hve : v ≠ e := fun h => heN (h ▸ hv)
      change v ≠ (∑ w ∈ t, w) at hve
      simp only [starCoefficientBase, if_neg hve]
    simp only [PrimitiveRelation.degree, S, hpossum, hneg]

theorem primitiveRelation_pushdown_without_positive_sum
    (hcard : 2 ≤ t.card) (R : («Σ».starSubdivision t ht hne).PrimitiveRelation)
    (heP : (∑ v ∈ t, v) ∉ R.positive) (hPt : R.positive ≠ t) :
    ∃ S : «Σ».PrimitiveRelation, S.positive = R.positive ∧
      ∀ a : Lattice n → ℝ, S.degree a = R.degree (starCoefficientBase a t) := by
  obtain ⟨S, hP, hN, hdegree⟩ :=
    «Σ».primitiveRelation_pushdown_without_positive_sum_data t ht hne hcard R heP hPt
  exact ⟨S, hP, hdegree⟩

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricStarPushdown
-- END ORIGINAL PaperVerification.ToricStarPushdown


-- BEGIN ORIGINAL PaperVerification.ToricStarContractibility
section Source_ToricStarContractibility

-- original header: module

-- original header: public import PaperVerification.ToricStarPushdown

-- original header: @[expose] public section

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
end
end Source_ToricStarContractibility
-- END ORIGINAL PaperVerification.ToricStarContractibility


-- BEGIN ORIGINAL PaperVerification.ToricSimultaneousPushdown
section Source_ToricSimultaneousPushdown

-- original header: module

-- original header: public import PaperVerification.ToricSimultaneousPrimitive
-- original header: public import PaperVerification.ToricStarContractibility

-- original header: @[expose] public section

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
end
end Source_ToricSimultaneousPushdown
-- END ORIGINAL PaperVerification.ToricSimultaneousPushdown


-- BEGIN ORIGINAL PaperVerification.ToricLargeLoci
section Source_ToricLargeLoci

-- original header: module

-- original header: public import PaperVerification.ToricContractibleWalls

-- original header: @[expose] public section

/-!
# Distinct large contraction loci have no common fan cone

The argument is entirely finite. At a common full cone, the large positive
ray sets overlap. Replacing across a shared positive wall gives the same
opposite ray by the actual fan intersection property. Its basis coordinates
then recover both primitive collections, proving they are equal.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- Two large contractible primitive relations whose focus cones lie in a
common full cone have the same positive primitive collection. -/
theorem positive_eq_of_large_common_full_cone
    (R S : «Σ».PrimitiveRelation)
    (hR : R.IsCombinatoriallyContractible) (hS : S.IsCombinatoriallyContractible)
    (hlarge : n < R.fiberDimension + S.fiberDimension)
    (U : Finset (Lattice n)) (hUcone : U ∈ «Σ».cones) (hUcard : U.card = n)
    (hRU : R.negative ⊆ U) (hSU : S.negative ⊆ U) :
    R.positive = S.positive := by
  have hRcount := R.positive_count_in_full_cone hR hUcone hUcard hRU
  have hScount := S.positive_count_in_full_cone hS hUcone hUcard hSU
  let A := R.positive ∩ U
  let B := S.positive ∩ U
  have hAB : (A ∩ B).Nonempty := by
    by_contra hempty
    have heq := Finset.not_nonempty_iff_eq_empty.mp hempty
    have hcount := Finset.card_union_add_card_inter A B
    have hsubset : A ∪ B ⊆ U :=
      Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
    have hbound := Finset.card_le_card hsubset
    rw [hUcard] at hbound
    rw [heq, Finset.card_empty, add_zero] at hcount
    change (A ∪ B).card = (R.positive ∩ U).card + (S.positive ∩ U).card at hcount
    rw [hRcount, hScount] at hcount
    omega
  obtain ⟨v, hv⟩ := hAB
  obtain ⟨hvA, hvB⟩ := Finset.mem_inter.mp hv
  obtain ⟨hvR, hvU⟩ := Finset.mem_inter.mp hvA
  have hvS := (Finset.mem_inter.mp hvB).1
  obtain ⟨b, hUb⟩ := «Σ».full_cone_basis hUcone hUcard
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (hUb ▸ hvU)
  obtain ⟨w, hwR, hwU, hRdiff, hwcone, hwcoord⟩ :=
    R.replacement_across_full_wall hR U hUcone b hUb hRU j hvR
  obtain ⟨z, hzS, hzU, hSdiff, hzcone, hzcoord⟩ :=
    S.replacement_across_full_wall hS U hUcone b hUb hSU j hvS
  have hwcone' : insert w ((Finset.univ.erase j).image b) ∈ «Σ».cones := by
    simpa only [hUb, Finset.image_erase b.injective] using hwcone
  have hzcone' : insert z ((Finset.univ.erase j).image b) ∈ «Σ».cones := by
    simpa only [hUb, Finset.image_erase b.injective] using hzcone
  have hwz : w = z := «Σ».opposite_wall_ray_unique b j w z hwcone' hzcone'
    ((hwcoord j).mp hvR) ((hzcoord j).mp hvS)
  subst z
  have houtside (P : Finset (Lattice n)) (hPdiff : P \ U = {w})
      {v : Lattice n} (hvP : v ∈ P) (hvw : v ≠ w) : v ∈ U := by
    by_contra hvU
    have h := Finset.mem_sdiff.mpr ⟨hvP, hvU⟩
    rw [hPdiff] at h
    exact hvw (Finset.mem_singleton.mp h)
  ext v
  by_cases hvw : v = w
  · subst v
    exact iff_of_true hwR hzS
  · constructor
    · intro hvP
      have hvU := houtside R.positive hRdiff hvP hvw
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hUb ▸ hvU)
      exact (hzcoord i).mpr ((hwcoord i).mp hvP)
    · intro hvP
      have hvU := houtside S.positive hSdiff hvP hvw
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hUb ▸ hvU)
      exact (hwcoord i).mpr ((hzcoord i).mp hvP)

/-- Distinct contractible classes with fiber dimensions whose sum exceeds
the ambient dimension have no common cone containing their focus rays.
This is the exact fan incidence form of disjoint contraction loci. -/
theorem no_common_cone_of_distinct_large_relations (hpure : «Σ».IsPure)
    (R S : «Σ».PrimitiveRelation)
    (hR : R.IsCombinatoriallyContractible) (hS : S.IsCombinatoriallyContractible)
    (hlarge : n < R.fiberDimension + S.fiberDimension)
    (hne : R.positive ≠ S.positive) :
    ¬ ∃ u ∈ «Σ».cones, R.negative ∪ S.negative ⊆ u := by
  rintro ⟨u, hu, hfocus⟩
  obtain ⟨U, hU, huU, hUcard⟩ := hpure u hu
  have hRU : R.negative ⊆ U := (Finset.subset_union_left.trans hfocus).trans huU
  have hSU : S.negative ⊆ U := (Finset.subset_union_right.trans hfocus).trans huU
  exact hne («Σ».positive_eq_of_large_common_full_cone R S hR hS hlarge U hU hUcard hRU hSU)

/-- In particular, every distinct pair of selected relations with `2r>n`
has disjoint focus loci in the precise common-cone sense. -/
theorem no_common_cone_of_two_large_relations (hpure : «Σ».IsPure)
    (R S : «Σ».PrimitiveRelation)
    (hR : R.IsCombinatoriallyContractible) (hS : S.IsCombinatoriallyContractible)
    (hlargeR : n < 2 * R.fiberDimension) (hlargeS : n < 2 * S.fiberDimension)
    (hne : R.positive ≠ S.positive) :
    ¬ ∃ u ∈ «Σ».cones, R.negative ∪ S.negative ⊆ u := by
  apply «Σ».no_common_cone_of_distinct_large_relations hpure R S hR hS (by omega) hne

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricLargeLoci
-- END ORIGINAL PaperVerification.ToricLargeLoci


-- BEGIN ORIGINAL PaperVerification.ToricDisjointStars
section Source_ToricDisjointStars

-- original header: module

-- original header: public import PaperVerification.ToricStarContractibility
-- original header: public import PaperVerification.ToricLargeLoci

-- original header: @[expose] public section

/-!
# A star subdivision leaves disjoint focus loci unchanged

Disjointness is the proved absence of a fan cone containing both focus ray
sets. Every cone over the second focus is then literally unchanged. This
also preserves every contractible primitive relation supported over that
focus, with its exact vector equation and coefficients.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable (t : Finset (Lattice n)) (ht : t ∈ «Σ».cones) (hne : t.Nonempty)

theorem focus_not_subset_of_disjoint {u : Finset (Lattice n)} (hu : u ∈ «Σ».cones)
    (hdisj : ¬ ∃ s ∈ «Σ».cones, t ∪ u ⊆ s) : ¬ t ⊆ u := by
  intro htu
  exact hdisj ⟨u, hu, Finset.union_subset htu (Finset.Subset.refl u)⟩

/-- The exceptional ray cannot occur in a new cone above an old focus
whose locus was disjoint from the subdivision center. -/
theorem sum_not_mem_new_cone_over_disjoint_focus (hcard : 2 ≤ t.card)
    {u s : Finset (Lattice n)} (hu : u ∈ «Σ».cones)
    (hdisj : ¬ ∃ z ∈ «Σ».cones, t ∪ u ⊆ z)
    (hs : s ∈ («Σ».starSubdivision t ht hne).cones) (hus : u ⊆ s) :
    (∑ v ∈ t, v) ∉ s := by
  intro he
  obtain ⟨p, hp, hps, hparent⟩ :=
    («Σ».mem_starSubdivision_with_sum_iff t ht hne hcard he).mp hs
  have heu : (∑ v ∈ t, v) ∉ u := by
    intro heu
    exact «Σ».sum_rays_not_mem_rays ht hcard («Σ».ray_mem_of_mem_cone hu heu)
  apply hdisj
  refine ⟨s.erase (∑ v ∈ t, v) ∪ t, hparent, ?_⟩
  apply Finset.union_subset
  · exact Finset.subset_union_right
  · intro v hv
    exact Finset.mem_union_left _ (Finset.mem_erase.mpr
      ⟨fun hve => heu (hve ▸ hv), hus hv⟩)

/-- The entire star of a disjoint old focus is unchanged, as a literal
equivalence of old and new cone membership. -/
theorem cone_over_disjoint_focus_iff (hcard : 2 ≤ t.card)
    {u s : Finset (Lattice n)} (hu : u ∈ «Σ».cones)
    (hdisj : ¬ ∃ z ∈ «Σ».cones, t ∪ u ⊆ z) (hus : u ⊆ s) :
    s ∈ («Σ».starSubdivision t ht hne).cones ↔ s ∈ «Σ».cones := by
  constructor
  · intro hs
    have he := «Σ».sum_not_mem_new_cone_over_disjoint_focus t ht hne hcard hu hdisj hs hus
    exact ((«Σ».mem_starSubdivision_without_sum_iff t ht hne he).mp hs).1
  · intro hs
    have hts : ¬ t ⊆ s := fun h => hdisj ⟨s, hs, Finset.union_subset h hus⟩
    exact «Σ».mem_starSubdivision_of_unchanged t ht hne hs hts

/-- A primitive collection survives unchanged if it does not contain the
subdivision focus. All its old rays remain actual new rays. -/
theorem primitiveCollection_survives_star (hcard : 2 ≤ t.card)
    {P : Finset (Lattice n)} (hP : «Σ».IsPrimitiveCollection P) (htP : ¬ t ⊆ P) :
    («Σ».starSubdivision t ht hne).IsPrimitiveCollection P := by
  have heP : (∑ v ∈ t, v) ∉ P :=
    fun h => «Σ».sum_rays_not_mem_rays ht hcard (hP.1 h)
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    exact «Σ».old_ray_mem_starSubdivision_rays t ht hne hcard (hP.1 hv)
  · intro hnew
    exact hP.2.1 ((«Σ».mem_starSubdivision_without_sum_iff t ht hne heP).mp hnew).1
  · intro s hs
    exact «Σ».mem_starSubdivision_of_unchanged t ht hne (hP.2.2 s hs)
      (fun hts => htP (hts.trans hs.subset))

include ht in
/-- A contractible relation whose focus is disjoint from the subdivision
center cannot have its whole positive collection contain that center. -/
theorem focus_not_subset_positive_of_disjoint
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible)
    (hdisj : ¬ ∃ s ∈ «Σ».cones, t ∪ R.negative ⊆ s) : ¬ t ⊆ R.positive := by
  intro htP
  have hPt : ¬ R.positive ⊆ t := fun h =>
    R.primitive.2.1 («Σ».downward t ht R.positive h)
  obtain ⟨p, hpP, hpt⟩ := Finset.not_subset.mp hPt
  have hcore := R.contractible_core_cone hR hpP
  apply hdisj
  refine ⟨R.positive.erase p ∪ R.negative, hcore, ?_⟩
  apply Finset.union_subset
  · intro v hv
    exact Finset.mem_union_left _ (Finset.mem_erase.mpr
      ⟨fun hvp => hpt (hvp ▸ hv), htP hv⟩)
  · exact Finset.subset_union_right

/-- Every contractible relation over a disjoint focus lifts with precisely
the same positive rays, negative rays, coefficients, and degree function. -/
theorem exists_unchanged_contractible_lift (hcard : 2 ≤ t.card)
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible)
    (hdisj : ¬ ∃ s ∈ «Σ».cones, t ∪ R.negative ⊆ s) :
    ∃ S : («Σ».starSubdivision t ht hne).PrimitiveRelation,
      S.positive = R.positive ∧ S.negative = R.negative ∧
      S.coefficient = R.coefficient ∧ S.IsCombinatoriallyContractible := by
  have hPnew := «Σ».primitiveCollection_survives_star t ht hne hcard R.primitive
    («Σ».focus_not_subset_positive_of_disjoint t ht R hR hdisj)
  have hNnew := («Σ».cone_over_disjoint_focus_iff t ht hne hcard R.negative_cone
    hdisj (Finset.Subset.refl R.negative)).mpr R.negative_cone
  let S : («Σ».starSubdivision t ht hne).PrimitiveRelation :=
    ⟨R.positive, R.negative, R.coefficient, hPnew, hNnew, R.coefficient_pos, R.equation⟩
  refine ⟨S, rfl, rfl, rfl, ?_⟩
  intro ν hν hνdisj hNν x hx
  have hNνold : R.negative ∪ ν ∈ «Σ».cones :=
    («Σ».cone_over_disjoint_focus_iff t ht hne hcard R.negative_cone hdisj
      Finset.subset_union_left).mp hNν
  have hνold : ν ∈ «Σ».cones := «Σ».downward _ hNνold ν Finset.subset_union_right
  have hreplace := hR ν hνold hνdisj hNνold x hx
  exact («Σ».cone_over_disjoint_focus_iff t ht hne hcard R.negative_cone hdisj
    (Finset.subset_union_right.trans Finset.subset_union_left)).mpr hreplace

/-- The new exceptional ray and any disjoint old focus have no common
cone, so later subdivisions over that focus remain disjoint from this
exceptional locus. -/
theorem no_common_cone_sum_and_disjoint_focus (hcard : 2 ≤ t.card)
    {u : Finset (Lattice n)} (hu : u ∈ «Σ».cones)
    (hdisj : ¬ ∃ s ∈ «Σ».cones, t ∪ u ⊆ s) :
    ¬ ∃ s ∈ («Σ».starSubdivision t ht hne).cones, insert (∑ v ∈ t, v) u ⊆ s := by
  rintro ⟨s, hs, hsub⟩
  have hus : u ⊆ s := (Finset.subset_insert _ _).trans hsub
  exact «Σ».sum_not_mem_new_cone_over_disjoint_focus t ht hne hcard hu hdisj hs hus
    (hsub (Finset.mem_insert_self _ _))

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricDisjointStars
-- END ORIGINAL PaperVerification.ToricDisjointStars


-- BEGIN ORIGINAL PaperVerification.ToricStarLift
section Source_ToricStarLift

-- original header: module

-- original header: public import PaperVerification.ToricDisjointStars

-- original header: @[expose] public section

/-!
# The explicit minimum-coefficient lift of an activated primitive relation

The lifted relation is constructed by replacing the focus sum with its new
ray and subtracting the minimum old coefficient. Positivity, the actual new
focus cone, the vector identity, and the complete degree formula are proved.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

def residualRayCoefficient {ι : Type*} (t : Finset ι) (m : ℕ)
    (c : ι → ℕ) (v : ι) : ℕ := if v ∈ t then c v - m else c v

theorem sum_residualRayCoefficient_smul {ι K E : Type*}
    [CommSemiring K] [AddCommMonoid E] [Module K E]
    (s t : Finset ι) (hts : t ⊆ s) (m : ℕ) (c : ι → ℕ)
    (hm : ∀ i ∈ t, m ≤ c i) (v : ι → E) :
    (∑ i ∈ s, (c i : K) • v i) =
      (∑ i ∈ s, (residualRayCoefficient t m c i : K) • v i) +
      (m : K) • ∑ i ∈ t, v i := by
  have hsplit (i : ι) : residualRayCoefficient t m c i +
      (if i ∈ t then m else 0) = c i := by
    by_cases hi : i ∈ t
    · simp only [residualRayCoefficient, if_pos hi]
      exact Nat.sub_add_cancel (hm i hi)
    · simp only [residualRayCoefficient, if_neg hi, add_zero]
  have hcast (i : ι) : (c i : K) = (residualRayCoefficient t m c i : K) +
      ((if i ∈ t then m else 0 : ℕ) : K) := by
    rw [← Nat.cast_add, hsplit]
  have hsecond : (∑ i ∈ s, ((if i ∈ t then m else 0 : ℕ) : K) • v i) =
      (m : K) • ∑ i ∈ t, v i := by
    calc
      (∑ i ∈ s, ((if i ∈ t then m else 0 : ℕ) : K) • v i) =
          ∑ i ∈ t, ((if i ∈ t then m else 0 : ℕ) : K) • v i := by
        symm
        apply Finset.sum_subset hts
        intro i _ hi
        simp only [if_neg hi, Nat.cast_zero, zero_smul]
      _ = ∑ i ∈ t, (m : K) • v i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [if_pos hi]
      _ = (m : K) • ∑ i ∈ t, v i := Finset.smul_sum.symm
  simp only [hcast, add_smul, Finset.sum_add_distrib, hsecond]

theorem sum_residual_filter {ι K E : Type*}
    [CommSemiring K] [AddCommMonoid E] [Module K E]
    (s : Finset ι) (c : ι → ℕ) (v : ι → E) :
    (∑ i ∈ s.filter (fun i => 0 < c i), (c i : K) • v i) =
      ∑ i ∈ s, (c i : K) • v i := by
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i hi hif
  have hc : c i = 0 := by
    have hnot : ¬ 0 < c i := fun h => hif (Finset.mem_filter.mpr ⟨hi, h⟩)
    omega
  simp only [hc, Nat.cast_zero, zero_smul]

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable (t : Finset (Lattice n)) (ht : t ∈ «Σ».cones) (hne : t.Nonempty)

/-- The exact relation lift and its universal degree identity. The minimum
coefficient is positive and attained on an actual focus ray. -/
theorem exists_minimum_coefficient_lift (hcard : 2 ≤ t.card)
    (R : «Σ».PrimitiveRelation) (htN : t ⊆ R.negative) :
    ∃ m : ℕ, 0 < m ∧ (∃ p ∈ t, R.coefficient p = m) ∧
      (∀ v ∈ t, m ≤ R.coefficient v) ∧
      ∃ S : («Σ».starSubdivision t ht hne).PrimitiveRelation,
        S.positive = R.positive ∧ ∀ a : Lattice n → ℝ,
          S.degree a = R.degree a + (m : ℝ) * ((∑ v ∈ t, a v) - a (∑ v ∈ t, v)) := by
  obtain ⟨p, hp, hmin⟩ := t.exists_min_image R.coefficient hne
  let m := R.coefficient p
  let e := ∑ v ∈ t, v
  let d := residualRayCoefficient t m R.coefficient
  let N := R.negative.filter (fun v => 0 < d v)
  let c : Lattice n → ℕ := fun v => if v = e then m else d v
  have hm : 0 < m := R.coefficient_pos p (htN hp)
  have heold : e ∉ «Σ».rays := «Σ».sum_rays_not_mem_rays ht hcard
  have heNold : e ∉ R.negative :=
    fun h => heold («Σ».ray_mem_of_mem_cone R.negative_cone h)
  have heP : e ∉ R.positive := fun h => heold (R.primitive.1 h)
  have heN : e ∉ N := fun h => heNold (Finset.mem_filter.mp h).1
  have hpN : p ∉ N := by
    intro h
    have hpzero : d p = 0 := by simp [d, residualRayCoefficient, hp, m]
    have hpos := (Finset.mem_filter.mp h).2
    rw [hpzero] at hpos
    omega
  have htP : ¬ t ⊆ R.positive := by
    intro h
    exact Finset.disjoint_left.mp R.disjoint (h hp) (htN hp)
  have hPnew := «Σ».primitiveCollection_survives_star t ht hne hcard R.primitive htP
  have hNnew : insert e N ∈ («Σ».starSubdivision t ht hne).cones := by
    apply («Σ».starSubdivision t ht hne).downward
      (starRaySet R.negative t p)
      («Σ».starRaySet_mem_starSubdivision t ht hne R.negative_cone htN hp)
    intro v hv
    apply (mem_starRaySet R.negative t p v).mpr
    rcases Finset.mem_insert.mp hv with hve | hvN
    · exact Or.inl hve
    · exact Or.inr ⟨fun hvp => hpN (hvp ▸ hvN), (Finset.mem_filter.mp hvN).1⟩
  have hc : ∀ v ∈ insert e N, 0 < c v := by
    intro v hv
    rcases Finset.mem_insert.mp hv with hve | hvN
    · subst v
      simpa only [c, if_pos rfl] using hm
    · have hve : v ≠ e := fun h => heN (h ▸ hvN)
      simpa only [c, if_neg hve] using (Finset.mem_filter.mp hvN).2
  have hsum (K E : Type) [CommSemiring K] [AddCommMonoid E] [Module K E]
      (v : Lattice n → E) :
      (∑ x ∈ insert e N, (c x : K) • v x) =
        (m : K) • v e + ∑ x ∈ R.negative, (d x : K) • v x := by
    rw [Finset.sum_insert heN]
    simp only [c, if_pos rfl]
    congr 1
    calc
      (∑ x ∈ N, ((if x = e then m else d x : ℕ) : K) • v x) =
          ∑ x ∈ N, (d x : K) • v x := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [if_neg (fun h : x = e => heN (h ▸ hx))]
      _ = ∑ x ∈ R.negative, (d x : K) • v x :=
        sum_residual_filter R.negative d v
  have heq : (∑ v ∈ R.positive, v) = ∑ v ∈ insert e N, (c v : ℤ) • v := by
    have hsumZ := hsum ℤ (Lattice n) id
    have hresidualZ := sum_residualRayCoefficient_smul (K := ℤ)
      R.negative t htN m R.coefficient hmin id
    simp only [id_eq] at hsumZ hresidualZ
    rw [R.equation, hsumZ, hresidualZ]
    exact add_comm _ _
  let S : («Σ».starSubdivision t ht hne).PrimitiveRelation :=
    ⟨R.positive, insert e N, c, hPnew, hNnew, hc, heq⟩
  refine ⟨m, hm, ⟨p, hp, rfl⟩, hmin, S, rfl, ?_⟩
  intro a
  have hnewsum := hsum ℝ ℝ a
  have holdsum := sum_residualRayCoefficient_smul (K := ℝ)
    R.negative t htN m R.coefficient hmin a
  simp only [smul_eq_mul] at hnewsum holdsum
  change (∑ v ∈ R.positive, a v) - (∑ v ∈ insert e N, (c v : ℝ) * a v) =
    ((∑ v ∈ R.positive, a v) - ∑ v ∈ R.negative, (R.coefficient v : ℝ) * a v) +
      (m : ℝ) * ((∑ v ∈ t, a v) - a e)
  rw [hnewsum, holdsum]
  ring

/-- Every primitive lift with this positive collection has exactly the
minimum-coefficient degree formula. Thus an actual extremal class pushing
to an activated old class is identified without assuming uniqueness of
its lift as an extra hypothesis. -/
theorem minimum_coefficient_lift_degree_unique (hcard : 2 ≤ t.card)
    (R : «Σ».PrimitiveRelation) (htN : t ⊆ R.negative) :
    ∃ m : ℕ, 0 < m ∧ (∃ p ∈ t, R.coefficient p = m) ∧
      (∀ v ∈ t, m ≤ R.coefficient v) ∧
      ∀ S : («Σ».starSubdivision t ht hne).PrimitiveRelation,
        S.positive = R.positive → ∀ a : Lattice n → ℝ,
          S.degree a = R.degree a + (m : ℝ) * ((∑ v ∈ t, a v) - a (∑ v ∈ t, v)) := by
  obtain ⟨m, hm, hminmem, hmin, S₀, hS₀, hdegree⟩ :=
    «Σ».exists_minimum_coefficient_lift t ht hne hcard R htN
  refine ⟨m, hm, hminmem, hmin, ?_⟩
  intro S hS a
  exact (S.degree_unique S₀ (hS.trans hS₀.symm) a).trans (hdegree a)

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricStarLift
-- END ORIGINAL PaperVerification.ToricStarLift


-- BEGIN ORIGINAL PaperVerification.ToricSimultaneousLift
section Source_ToricSimultaneousLift

-- original header: module

-- original header: public import PaperVerification.ToricSimultaneousPushdown
-- original header: public import PaperVerification.ToricStarLift

-- original header: @[expose] public section

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
end
end Source_ToricSimultaneousLift
-- END ORIGINAL PaperVerification.ToricSimultaneousLift


-- BEGIN ORIGINAL PaperVerification.ToricSelectedSupport
section Source_ToricSelectedSupport

-- original header: module

-- original header: public import PaperVerification.ToricSelectedBounds
-- original header: public import PaperVerification.ToricSimultaneousLift

-- original header: @[expose] public section

/-!
# Exact support coefficients at every selected locus

The same coefficient formula covers a newly inserted ray and an unblown
divisor ray. The finite degree identity records every positive and negative
selected contribution, so the correction estimates are ordinary arithmetic.
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

def selectedPullback (a : Lattice n → ℝ) : Lattice n → ℝ :=
  simultaneousSupport («Σ».selectedStarFocus R) a 0

include hdisj in
theorem selectedSupport_at_selected_ray (a : Lattice n → ℝ) (t : ι → ℝ) (i : ι) :
    simultaneousSupport (fun i => (R i).negative) a t («Σ».selectedRay R i) =
      (∑ v ∈ (R i).negative, a v) - t i :=
  simultaneousSupport_at_sum _ («Σ».selectedRay_injective R hdisj) a t i

include hne hdisj in
theorem selectedPullback_at_selected_ray (a : Lattice n → ℝ) (i : ι) :
    «Σ».selectedPullback R a («Σ».selectedRay R i) = ∑ v ∈ (R i).negative, a v := by
  by_cases hi : 2 ≤ (R i).negative.card
  · let i' : «Σ».BlowupIndices R := ⟨i, hi⟩
    have hinj := «Σ».simultaneous_sum_rays_injective («Σ».selectedStarFocus R)
      (fun j => (R j).negative_cone) («Σ».selectedStarFocus_disjoint R hdisj)
    simpa only [selectedPullback, selectedStarFocus, selectedRay, i', Pi.zero_apply, sub_zero] using
      simultaneousSupport_at_sum («Σ».selectedStarFocus R) hinj a 0 i'
  · have hf := «Σ».selected_focus_of_not_blowup R hne i hi
    have heold : «Σ».selectedRay R i ∈ «Σ».rays :=
      «Σ».ray_mem_of_mem_cone (R i).negative_cone (hf.symm ▸ Finset.mem_singleton_self _)
    rw [selectedPullback, «Σ».simultaneousSupport_old («Σ».selectedStarFocus R)
      (fun j => (R j).negative_cone) (fun j => j.property) a 0 _ heold, hf,
      Finset.sum_singleton]

include hne hdisj in
theorem selectedSupport_eq_pullback_sub (a : Lattice n → ℝ) (t : ι → ℝ) :
    simultaneousSupport (fun i => (R i).negative) a t =
      fun v => «Σ».selectedPullback R a v -
        ∑ i, if v = «Σ».selectedRay R i then t i else 0 := by
  funext v
  by_cases hex : ∃ i, v = «Σ».selectedRay R i
  · obtain ⟨i, rfl⟩ := hex
    rw [«Σ».selectedSupport_at_selected_ray R hdisj a t i,
      «Σ».selectedPullback_at_selected_ray R hne hdisj a i]
    have hs : (∑ j, if «Σ».selectedRay R i = «Σ».selectedRay R j then t j else 0) = t i := by
      simp only [(«Σ».selectedRay_injective R hdisj).eq_iff]
      simp
    rw [hs]
  · have hv : ∀ i, v ≠ «Σ».selectedRay R i := by simpa only [not_exists] using hex
    rw [simultaneousSupport_of_not_sum _ a t v hv]
    have hv' : ∀ i : «Σ».BlowupIndices R, v ≠ ∑ w ∈ «Σ».selectedStarFocus R i, w := fun i => hv i
    rw [selectedPullback, simultaneousSupport_of_not_sum _ a 0 v hv']
    simp only [hv, if_false, Finset.sum_const_zero, sub_zero]

include hR hne hdisj in
/-- A different selected ray cannot occur in either side of a selected
primitive relation. For the positive side this uses contraction replacement. -/
theorem selected_ray_not_positive_of_ne (i j : ι) (hij : i ≠ j) :
    «Σ».selectedRay R i ∉ (R j).positive := by
  by_cases hi : 2 ≤ (R i).negative.card
  · intro hh
    exact «Σ».sum_rays_not_mem_rays (R i).negative_cone hi ((R j).primitive.1 hh)
  · have hf := «Σ».selected_focus_of_not_blowup R hne i hi
    have hnot := «Σ».focus_not_subset_positive_of_disjoint (R i).negative
      (R i).negative_cone (R j) (hR j) (hdisj i j hij)
    intro hh
    apply hnot
    simpa only [hf, Finset.singleton_subset_iff] using hh

include hdisj in
theorem selected_ray_not_negative_of_ne (i j : ι) (hij : i ≠ j) :
    «Σ».selectedRay R i ∉ (R j).negative := by
  intro hh
  have hiN := («Σ».sum_rays_mem_cone_iff (R i).negative_cone (R j).negative_cone).mp
    (latticeRayCone_generator (R j).negative hh)
  exact hdisj i j hij ⟨(R j).negative, (R j).negative_cone,
    Finset.union_subset hiN (Finset.Subset.refl _)⟩

include hdisj in
theorem selectedSupport_on_blowup_focus (i : ι) (hi : 2 ≤ (R i).negative.card)
    (a : Lattice n → ℝ) (t : ι → ℝ) {v : Lattice n} (hv : v ∈ (R i).negative) :
    simultaneousSupport (fun j => (R j).negative) a t v = a v := by
  apply simultaneousSupport_of_not_sum
  intro j hh
  by_cases hji : j = i
  · subst j
    exact «Σ».sum_rays_not_mem_rays (R i).negative_cone hi
      (hh ▸ «Σ».ray_mem_of_mem_cone (R i).negative_cone hv)
  · apply «Σ».selected_ray_not_negative_of_ne R hdisj j i hji
    change (∑ w ∈ (R j).negative, w) ∈ (R i).negative
    exact hh ▸ hv

end SmoothCompleteFan

namespace SmoothCompleteFan.PrimitiveRelation

variable {n : ℕ} {Γ : SmoothCompleteFan n} (S : Γ.PrimitiveRelation)

theorem degree_sub_finite_ray_corrections {ι : Type*} [Fintype ι]
    (e : ι → Lattice n) (a : Lattice n → ℝ) (t : ι → ℝ) :
    S.degree (fun v => a v - ∑ i, if v = e i then t i else 0) =
      S.degree a - (∑ i, if e i ∈ S.positive then t i else 0) +
        ∑ i, if e i ∈ S.negative then (S.coefficient (e i) : ℝ) * t i else 0 := by
  have hp : (∑ v ∈ S.positive, ∑ i, if v = e i then t i else 0) =
      ∑ i, if e i ∈ S.positive then t i else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    simp
  have hn : (∑ v ∈ S.negative, (S.coefficient v : ℝ) *
      (∑ i, if v = e i then t i else 0)) =
      ∑ i, if e i ∈ S.negative then (S.coefficient (e i) : ℝ) * t i else 0 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    simp [mul_ite]
  simp only [degree, Finset.sum_sub_distrib, mul_sub, hp, hn]
  ring

end SmoothCompleteFan.PrimitiveRelation

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable {ι : Type*} [Fintype ι] (R : ι → «Σ».PrimitiveRelation)
variable (hne : ∀ i, (R i).negative.Nonempty)
variable (hdisj : «Σ».PairwiseDisjointFoci (fun i => (R i).negative))

theorem selected_support_degree
    (S : («Σ».selectedFan R hne hdisj).PrimitiveRelation)
    (a : Lattice n → ℝ) (t : ι → ℝ) :
    S.degree (simultaneousSupport (fun i => (R i).negative) a t) =
      S.degree («Σ».selectedPullback R a) -
        (∑ i, if «Σ».selectedRay R i ∈ S.positive then t i else 0) +
        ∑ i, if «Σ».selectedRay R i ∈ S.negative then
          (S.coefficient («Σ».selectedRay R i) : ℝ) * t i else 0 := by
  rw [«Σ».selectedSupport_eq_pullback_sub R hne hdisj a t]
  exact S.degree_sub_finite_ray_corrections («Σ».selectedRay R) («Σ».selectedPullback R a) t

theorem selected_support_degree_ge_pullback
    (S : («Σ».selectedFan R hne hdisj).PrimitiveRelation)
    (a : Lattice n → ℝ) (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i)
    (hpos : ∀ i, «Σ».selectedRay R i ∉ S.positive) :
    S.degree («Σ».selectedPullback R a) ≤
      S.degree (simultaneousSupport (fun i => (R i).negative) a t) := by
  rw [«Σ».selected_support_degree R hne hdisj S a t]
  have hp : (∑ i, if «Σ».selectedRay R i ∈ S.positive then t i else 0) = 0 := by
    simp only [hpos, if_false, Finset.sum_const_zero]
  rw [hp, sub_zero]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => by
    split_ifs
    · exact mul_nonneg (Nat.cast_nonneg _) (ht i)
    · exact le_rfl))

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricSelectedSupport
-- END ORIGINAL PaperVerification.ToricSelectedSupport


-- BEGIN ORIGINAL PaperVerification.ToricSelectedLift
section Source_ToricSelectedLift

-- original header: module

-- original header: public import PaperVerification.ToricSelectedSupport

-- original header: @[expose] public section

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
end
end Source_ToricSelectedLift
-- END ORIGINAL PaperVerification.ToricSelectedLift


-- BEGIN ORIGINAL PaperVerification.ToricSelectedNoPositive
section Source_ToricSelectedNoPositive

-- original header: module

-- original header: public import PaperVerification.ToricSelectedLift
-- original header: public import PaperVerification.ToricMinimumCoefficient

-- original header: @[expose] public section

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
end
end Source_ToricSelectedNoPositive
-- END ORIGINAL PaperVerification.ToricSelectedNoPositive


-- BEGIN ORIGINAL PaperVerification.ToricSimultaneousParents
section Source_ToricSimultaneousParents

-- original header: module

-- original header: public import PaperVerification.ToricSimultaneousCombinatorics
-- original header: public import PaperVerification.ToricFiberWalls

-- original header: @[expose] public section

/-! # Full-cone and wall parents in the simultaneous subdivision

These are incidence consequences of the constructed finite fan.  In
particular an exceptional endpoint has an actual old adjacent cone, and
its vector is the old endpoint ray plus a sum of common wall rays.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable {ι : Type*} [Fintype ι] (T : ι → Finset (Lattice n))
variable (hT : ∀ i,T i ∈ «Σ».cones) (hne : ∀ i,(T i).Nonempty)
variable (hdisj : «Σ».PairwiseDisjointFoci T)

/-- A full cone is one of the actual generating charts, without any
unproved maximal-cone or refinement assumption. -/
theorem full_simultaneous_cone_parent {s : Finset (Lattice n)}
    (hs : s ∈ («Σ».simultaneousSubdivision T hT hne hdisj).cones) (hscard : s.card=n) :
    (s ∈ «Σ».cones ∧ ∀ i,¬T i⊆s) ∨
      ∃ i : ι, ∃ U ∈ «Σ».cones,U.card=n ∧ T i⊆U ∧
        ∃ p ∈ T i,s=starRaySet U (T i) p := by
  obtain ⟨C,hC,hsC⟩ := (mem_finiteConeFamilyClosure («Σ».simultaneousCandidates T) s).mp hs
  obtain ⟨b,hb⟩ := «Σ».simultaneousCandidates_smooth T C hC
  have hCle : C.card≤n := by
    have h := Finset.card_le_card hb
    simpa only [Finset.card_image_of_injective _ b.injective,Finset.card_fin] using h
  have hsCeq : s=C := Finset.eq_of_subset_of_card_le hsC (by omega)
  rcases («Σ».mem_simultaneousCandidates T C).mp hC with ⟨hCold,hnone⟩ |
    ⟨i,U,hU,p,hp,hTU,hCeq⟩
  · exact Or.inl ⟨hsCeq.symm ▸ hCold,fun i ↦ hsCeq.symm ▸ hnone i⟩
  · have hseq : s=starRaySet U (T i) p := hsCeq.trans hCeq
    have hUcard : U.card=n := by
      rw [hseq,«Σ».starRaySet_card hU hTU hp] at hscard
      exact hscard
    exact Or.inr ⟨i,U,hU,hUcard,hTU,p,hp,hseq⟩

variable (hcard : ∀ i,2≤(T i).card)

include hcard in
/-- A wall opposite one exceptional ray contains only old rays and is an
actual old cone. Pairwise disjointness excludes every other exceptional ray. -/
theorem simultaneous_wall_below_sum_old (i : ι) (W : Finset (Lattice n))
    (hs : insert (∑ v ∈ T i,v) W ∈ («Σ».simultaneousSubdivision T hT hne hdisj).cones)
    (heW : (∑ v ∈ T i,v) ∉ W) :
    W ∈ «Σ».cones ∧ W⊆«Σ».rays ∧ ∀ k : ι,(∑ v ∈ T k,v) ∉ W := by
  have hnone (k : ι) : (∑ v ∈ T k,v) ∉ W := by
    by_cases hki : k=i
    · simpa only [hki] using heW
    · have hk := «Σ».simultaneous_no_common_sums T hT hne hdisj hcard i k (fun hik => hki hik.symm)
        hs (Finset.mem_insert_self _ _)
      exact fun hm ↦ hk (Finset.mem_insert_of_mem hm)
  have hWnew : W ∈ («Σ».simultaneousSubdivision T hT hne hdisj).cones :=
    («Σ».simultaneousSubdivision T hT hne hdisj).downward _ hs W (Finset.subset_insert _ _)
  have hWold := ((«Σ».simultaneous_cone_without_sums_iff T hT hne hdisj hnone).mp hWnew).1
  exact ⟨hWold,fun _ hu ↦ «Σ».ray_mem_of_mem_cone hWold hu,hnone⟩

include hcard in
/-- Removing the exceptional endpoint from a full chart recovers its exact
old wall. The missing old focus ray is the old endpoint. -/
theorem full_simultaneous_sum_endpoint_parent (i : ι) (W : Finset (Lattice n))
    (hs : insert (∑ v ∈ T i,v) W ∈ («Σ».simultaneousSubdivision T hT hne hdisj).cones)
    (hscard : (insert (∑ v ∈ T i,v) W).card=n)
    (heW : (∑ v ∈ T i,v) ∉ W) :
    ∃ p ∈ T i,p ∉ W ∧ insert p W ∈ «Σ».cones ∧ (insert p W).card=n ∧
      T i⊆insert p W ∧ (T i).erase p⊆W ∧
      (∑ v ∈ T i,v)=p+∑ v ∈ (T i).erase p,v := by
  have hsingle := («Σ».simultaneous_cone_over_sum_iff T hT hne hdisj hcard i
    (Finset.mem_insert_self _ _)).mp hs
  obtain ⟨U,hU,hUcard,hTU,p,hp,hseq⟩ :=
    «Σ».full_star_cone_parent (T i) (hT i) (hne i) (hcard i) hsingle hscard
      (Finset.mem_insert_self _ _)
  have heU : (∑ v ∈ T i,v) ∉ U := fun h ↦
    «Σ».sum_rays_not_mem_rays (hT i) (hcard i) («Σ».ray_mem_of_mem_cone hU h)
  have heUp : (∑ v ∈ T i,v) ∉ U.erase p := fun h ↦ heU (Finset.mem_of_mem_erase h)
  have hstar : starRaySet U (T i) p = insert (∑ v ∈ T i,v) (U.erase p) := by
    ext v
    simp only [mem_starRaySet, Finset.mem_insert, Finset.mem_erase]
  have hwall : W=U.erase p := by
    have h := congrArg (fun s : Finset (Lattice n) ↦ s.erase (∑ v ∈ T i,v))
      (hseq.trans hstar)
    simpa only [Finset.erase_insert_eq_erase,
      Finset.erase_eq_of_notMem heW,Finset.erase_eq_of_notMem heUp] using h
  have hparent : U=insert p W := by rw [hwall,Finset.insert_erase (hTU hp)]
  have hpW : p ∉ W := by rw [hwall]; exact Finset.notMem_erase p U
  have hrest : (T i).erase p⊆W := by
    rw [hwall]
    exact Finset.erase_subset_erase p hTU
  refine ⟨p,hp,hpW,hparent ▸ hU,hparent ▸ hUcard,hparent ▸ hTU,hrest,?_⟩
  exact (Finset.add_sum_erase (T i) (fun v ↦ v) hp).symm

include hcard in
/-- Each endpoint of a full wall has a genuine old endpoint parent.
The last disjunction records whether the endpoint was changed, and gives
the exact focus needed to compute its pulled-back support coefficient. -/
theorem full_simultaneous_endpoint_parent (W : Finset (Lattice n)) (x : Lattice n)
    (hW : ∀ i : ι,(∑ v ∈ T i,v) ∉ W)
    (hs : insert x W ∈ («Σ».simultaneousSubdivision T hT hne hdisj).cones)
    (hscard : (insert x W).card=n) :
    ∃ q : Lattice n, ∃ D : Finset (Lattice n),
      insert q W ∈ «Σ».cones ∧ (insert q W).card=n ∧ D⊆W ∧ x=q+∑ u ∈ D,u ∧
      ((x ∈ «Σ».rays ∧ q=x ∧ D=∅) ∨
        ∃ i : ι,x=(∑ v ∈ T i,v) ∧ q ∈ T i ∧ D=(T i).erase q) := by
  by_cases hex : ∃ i : ι,x=∑ v ∈ T i,v
  · obtain ⟨i,rfl⟩ := hex
    obtain ⟨q,hq,hqW,hqcone,hqcard,hTq,hD,hx⟩ :=
      «Σ».full_simultaneous_sum_endpoint_parent T hT hne hdisj hcard i W hs hscard (hW i)
    exact ⟨q,(T i).erase q,hqcone,hqcard,hD,hx,Or.inr ⟨i,rfl,hq,rfl⟩⟩
  · have hnone (i : ι) : (∑ v ∈ T i,v) ∉ insert x W := by
      intro hm
      rcases Finset.mem_insert.mp hm with heq | hm
      · exact hex ⟨i,heq.symm⟩
      · exact hW i hm
    have hold := ((«Σ».simultaneous_cone_without_sums_iff T hT hne hdisj hnone).mp hs).1
    refine ⟨x,∅,hold,hscard,Finset.empty_subset W,by simp,Or.inl ?_⟩
    exact ⟨«Σ».ray_mem_of_mem_cone hold (Finset.mem_insert_self _ _),rfl,rfl⟩

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricSimultaneousParents
-- END ORIGINAL PaperVerification.ToricSimultaneousParents


-- BEGIN ORIGINAL PaperVerification.ToricStarPositivePullback
section Source_ToricStarPositivePullback

-- original header: module

-- original header: public import PaperVerification.ToricContractibleEdgeDegrees
-- original header: public import Mathlib.Tactic.Abel

-- original header: @[expose] public section

/-! # Pullback degrees at positive exceptional endpoints

The supporting slack across an actual old wall is proved to be the length
of a genuine edge of the original polytope.  Replacing either endpoint
ray by its sum with wall rays does not change that slack when coefficients
are pulled back by the corresponding sum.  Thus the degree estimate uses
the literal old edge bound, without an assumed curve-pushforward theorem.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

/-- The normalized old wall slack is exactly a genuine primitive edge length. -/
theorem wall_support_slack_eq_edge_length
    (hP : P.Smooth) («Σ» : SmoothCompleteFan n)
    (hfan : «Σ».realCones=P.normalFan)
    (d : Module.Basis (Fin n) ℤ (Lattice n))
    (hU : Finset.univ.image d ∈ «Σ».cones) (j : Fin n) (q : Lattice n)
    (hqcone : insert q ((Finset.univ.erase j).image d) ∈ «Σ».cones)
    (hqcoord : d.repr q j = -1)
    (ℓ : Ambient n →ₗ[ℝ] ℝ)
    (hℓ : ∀ i, ℓ (embed n (d i))=(P.integralSupport (d i):ℝ)) :
    ∃ v w : Lattice n, P.IsEdge (embed n v) (embed n w) ∧
      (P.integralSupport q:ℝ)-ℓ (embed n q)=(latticeLength v w:ℝ) := by
  have hnormal : (latticeRayCone (Finset.univ.image d):Set (Ambient n)) ∈ P.normalFan := by
    rw [← hfan]
    exact ⟨Finset.univ.image d,hU,rfl⟩
  obtain ⟨x,hx,hxcone⟩ := hnormal
  obtain ⟨v,lengths,hv,hedges⟩ := P.full_normal_basis_edges hP x hx d hxcone.symm
  have hcone : P.normalCone (embed n v)=
      (latticeRayCone (Finset.univ.image d):Set (Ambient n)) := by
    rw [hv]
    exact hxcone.symm
  have hvP : embed n v ∈ P.carrier := hv.symm ▸ hx
  have hform : ℓ=-(dotProductEquiv ℝ (Fin n) (embed n v)) := by
    apply (integralBasisReal d).ext
    intro i
    rw [integralBasisReal_apply,hℓ i]
    have hactive : embed n (d i) ∈ P.normalCone (embed n v) := by
      rw [hcone]
      exact latticeRayCone_generator _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)
    have hs := (P.integralSupport_spec (d i) (embed n v) hvP).2.mpr hactive
    change (P.integralSupport (d i) : ℝ) =
      -dotProduct (embed n v) (embed n (d i))
    calc
      _ = -dotProduct (embed n (d i)) (embed n v) := hs.symm
      _ = _ := congrArg Neg.neg (dotProduct_comm _ _)
  let w := v+(lengths j:ℤ)•integralDualBasis d j
  have hedge : P.IsEdge (embed n v) (embed n w) := (hedges j).2
  have hactive := P.opposite_wall_normal_at_edge_endpoint hP «Σ» hfan v d hU
    hcone j (lengths j) (hedges j).1 hedge q hqcone (by omega)
  let f : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) (embed n q)
  have hqvalue : (P.integralSupport q:ℝ)=-f (embed n w) :=
    ((P.integralSupport_spec q (embed n w) (P.edge_endpoints_extreme hedge).2.1).2.mpr
      hactive).symm
  have hℓq : ℓ (embed n q)=-f (embed n v) := by
    rw [hform]
    change -dotProduct (embed n v) (embed n q) =
      -dotProduct (embed n q) (embed n v)
    exact congrArg Neg.neg (dotProduct_comm _ _)
  refine ⟨v,w,hedge,?_⟩
  rw [hqvalue,hℓq]
  have hdisp : embed n w-embed n v=(lengths j:ℝ)•integralBasisReal (integralDualBasis d) j := by
    simp only [w,map_add,embed_int_smul,Int.cast_natCast,
      integralBasisReal_apply,add_sub_cancel_left]
  calc
    -f (embed n w)- -f (embed n v) = -f (embed n w-embed n v) := by
      rw [map_sub]
      ring
    _ = (lengths j:ℝ) := by
      rw [hdisp,map_smul,smul_eq_mul,pairing_integral_dual_basis,hqcoord]
      simp
    _ = (latticeLength v w:ℝ) := by
      change (lengths j : ℝ) =
        (latticeLength v (v + (lengths j : ℤ) • integralDualBasis d j) : ℝ)
      rw [latticeLength_basis_direction]

end LatticePolytope

namespace SmoothCompleteFan.PrimitiveRelation

variable {n : ℕ} {Γ : SmoothCompleteFan n} (R : Γ.PrimitiveRelation)

/-- Replacing both endpoint rays by sums with common wall rays leaves the
primitive degree equal to the original supporting slack. -/
theorem degree_pullback_two_sum_rays
    (a b : Lattice n → ℝ) (W C D : Finset (Lattice n))
    (p q e x : Lattice n) (hC : C⊆W) (hD : D⊆W)
    (he : e=p+∑ u ∈ C,u) (hx : x=q+∑ u ∈ D,u)
    (hN : R.negative⊆W) (hP : R.positive \ insert e W={x})
    (hbW : ∀ u ∈ W,b u=a u)
    (hbe : b e=a p+∑ u ∈ C,a u) (hbx : b x=a q+∑ u ∈ D,a u)
    (ℓ : Ambient n →ₗ[ℝ] ℝ)
    (hℓW : ∀ u ∈ W,ℓ (embed n u)=a u) (hℓp : ℓ (embed n p)=a p) :
    R.degree b=a q-ℓ (embed n q) := by
  have hsum (T : Finset (Lattice n)) (hT : T⊆W) :
      ℓ (embed n (∑ u ∈ T,u))=∑ u ∈ T,a u := by
    simp only [map_sum]
    exact Finset.sum_congr rfl (fun u hu ↦ hℓW u (hT hu))
  have hℓe : ℓ (embed n e)=b e := by
    calc
      ℓ (embed n e)=ℓ (embed n p)+ℓ (embed n (∑ u ∈ C,u)) := by
        rw [he,map_add,map_add]
      _ = a p+∑ u ∈ C,a u := by rw [hℓp,hsum C hC]
      _ = b e := hbe.symm
  have hactive (u : Lattice n) (hu : u ∈ insert e W) : ℓ (embed n u)=b u := by
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact hℓe
    · exact (hℓW u hu).trans (hbW u hu).symm
  have hxP : x ∈ R.positive := by
    have hm : x ∈ R.positive \ insert e W := hP.symm ▸ Finset.mem_singleton_self x
    exact (Finset.mem_sdiff.mp hm).1
  have hrest (u : Lattice n) (hu : u ∈ R.positive) (hux : u≠x) :
      b u-ℓ (embed n u)=0 := by
    apply sub_eq_zero.mpr
    symm
    apply hactive
    by_contra hn
    have hm : u ∈ R.positive \ insert e W := Finset.mem_sdiff.mpr ⟨hu,hn⟩
    rw [hP] at hm
    exact hux (Finset.mem_singleton.mp hm)
  rw [R.degree_eq_sum_slack b ℓ (fun u hu ↦
    (hℓW u (hN hu)).trans (hbW u (hN hu)).symm)]
  rw [Finset.sum_eq_single x (fun u hu hux ↦ hrest u hu hux)
    (fun h ↦ False.elim (h hxP))]
  rw [hbx,hx,map_add,map_add,hsum D hD]
  ring

/-- The opposite old ray has primitive coefficient -1. This follows from
the actual relation equation; no normalization or pushforward is assumed. -/
theorem opposite_old_coordinate_of_two_sum_rays
    (d : Module.Basis (Fin n) ℤ (Lattice n)) (j : Fin n)
    (C D : Finset (Lattice n)) (q e x : Lattice n)
    (hC : C⊆(Finset.univ.erase j).image d)
    (hD : D⊆(Finset.univ.erase j).image d)
    (he : e=d j+∑ u ∈ C,u) (hx : x=q+∑ u ∈ D,u)
    (heP : e ∈ R.positive)
    (hN : R.negative⊆(Finset.univ.erase j).image d)
    (hP : R.positive \ insert e ((Finset.univ.erase j).image d)={x}) :
    d.repr q j = -1 := by
  let W := (Finset.univ.erase j).image d
  have hwall (u : Lattice n) (hu : u ∈ W) : d.coord j u=0 := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
    simp only [Module.Basis.coord_apply,Module.Basis.repr_self_apply,
      if_neg (Finset.mem_erase.mp hi).1]
  have hsum (T : Finset (Lattice n)) (hT : T⊆W) : d.coord j (∑ u ∈ T,u)=0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero (fun u hu ↦ hwall u (hT hu))
  have hecoord : d.coord j e=1 := by
    rw [he,map_add,hsum C hC]
    simp [Module.Basis.coord_apply]
  have hxcoord : d.coord j x=d.coord j q := by rw [hx,map_add,hsum D hD,add_zero]
  have hxdata : x ∈ R.positive ∧ x ∉ insert e W :=
    Finset.mem_sdiff.mp (hP.symm ▸ Finset.mem_singleton_self x)
  have hex : e≠x := by
    intro h
    exact hxdata.2 (Finset.mem_insert.mpr (Or.inl h.symm))
  have heRest : e ∈ R.positive.erase x := Finset.mem_erase.mpr ⟨hex,heP⟩
  have hrest : (∑ u ∈ R.positive.erase x,d.coord j u)=1 := by
    rw [Finset.sum_eq_single e]
    · exact hecoord
    · intro u hu hue
      apply hwall
      have huU : u ∈ insert e W := by
        by_contra hn
        have hm : u ∈ R.positive \ insert e W :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_of_mem_erase hu,hn⟩
        rw [hP] at hm
        exact (Finset.mem_erase.mp hu).1 (Finset.mem_singleton.mp hm)
      exact (Finset.mem_insert.mp huU).resolve_left hue
    · intro hn
      exact (hn heRest).elim
  have hnegative : (∑ u ∈ R.negative,(R.coefficient u:ℤ)*d.coord j u)=0 := by
    apply Finset.sum_eq_zero
    intro u hu
    rw [hwall u (hN hu),mul_zero]
  have h := congrArg (d.coord j) R.equation
  simp only [map_sum,map_smul,smul_eq_mul] at h
  rw [← Finset.add_sum_erase R.positive (fun u ↦ d.coord j u) hxdata.1,
    hrest,hxcoord,hnegative] at h
  change d.coord j q = -1
  omega

end SmoothCompleteFan.PrimitiveRelation

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

/-- The positive-exceptional pullback degree is an actual old edge length.
The two sum-ray descriptions allow either or both endpoints to be exceptional. -/
theorem positive_sum_pullback_degree_eq_edge_length
    (hP : P.Smooth) («Σ» : SmoothCompleteFan n) (hfan : «Σ».realCones=P.normalFan)
    (d : Module.Basis (Fin n) ℤ (Lattice n))
    (hU : Finset.univ.image d ∈ «Σ».cones) (j : Fin n)
    (C D : Finset (Lattice n)) (q e x : Lattice n)
    (hC : C⊆(Finset.univ.erase j).image d)
    (hD : D⊆(Finset.univ.erase j).image d)
    (he : e=d j+∑ u ∈ C,u) (hx : x=q+∑ u ∈ D,u)
    (hqcone : insert q ((Finset.univ.erase j).image d) ∈ «Σ».cones)
    (Γ : SmoothCompleteFan n) (R : Γ.PrimitiveRelation)
    (heP : e ∈ R.positive)
    (hN : R.negative⊆(Finset.univ.erase j).image d)
    (hPdiff : R.positive \ insert e ((Finset.univ.erase j).image d)={x})
    (b : Lattice n → ℝ)
    (hbW : ∀ u ∈ (Finset.univ.erase j).image d,b u=(P.integralSupport u:ℝ))
    (hbe : b e=(P.integralSupport (d j):ℝ)+∑ u ∈ C,(P.integralSupport u:ℝ))
    (hbx : b x=(P.integralSupport q:ℝ)+∑ u ∈ D,(P.integralSupport u:ℝ)) :
    ∃ v w : Lattice n, P.IsEdge (embed n v) (embed n w) ∧
      R.degree b=(latticeLength v w:ℝ) := by
  obtain ⟨ℓ,hℓ,hstrict⟩ := P.integralSupport_isStrictSupport «Σ» hfan _ hU
  have hℓi (i : Fin n) : ℓ (embed n (d i))=(P.integralSupport (d i):ℝ) :=
    hℓ (d i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)
  have hℓW (u : Lattice n) (hu : u ∈ (Finset.univ.erase j).image d) :
      ℓ (embed n u)=(P.integralSupport u:ℝ) :=
    hℓ u (Finset.image_subset_image (Finset.erase_subset j Finset.univ) hu)
  have hcoord := R.opposite_old_coordinate_of_two_sum_rays d j C D q e x
    hC hD he hx heP hN hPdiff
  have hdegree := R.degree_pullback_two_sum_rays (fun u ↦ (P.integralSupport u:ℝ)) b
    ((Finset.univ.erase j).image d) C D (d j) q e x hC hD he hx hN hPdiff
    hbW hbe hbx ℓ hℓW (hℓi j)
  obtain ⟨v,w,hedge,hslack⟩ := P.wall_support_slack_eq_edge_length hP «Σ» hfan d hU
    j q hqcone hcoord ℓ hℓi
  exact ⟨v,w,hedge,hdegree.trans hslack⟩

/-- A literal edge bound applies to a degree once the preceding theorem
identifies its genuine old edge. -/
theorem degree_lower_bound_of_edge_length {Γ : SmoothCompleteFan n}
    (R : Γ.PrimitiveRelation) (b : Lattice n → ℝ) {bound : ℕ}
    (hbound : P.EdgesAtLeast bound)
    (hdegree : ∃ v w : Lattice n,P.IsEdge (embed n v) (embed n w) ∧
      R.degree b=(latticeLength v w:ℝ)) : (bound:ℝ) ≤ R.degree b := by
  obtain ⟨v,w,hedge,hdegree⟩ := hdegree
  rw [hdegree]
  exact_mod_cast (P.edgesAtLeast_iff bound).mp hbound v w hedge

end LatticePolytope

end PaperVerification.ToricGeometry
end
end Source_ToricStarPositivePullback
-- END ORIGINAL PaperVerification.ToricStarPositivePullback


