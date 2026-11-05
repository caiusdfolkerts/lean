module

public import PaperVerification.ToricDisjointStarIntersections
public import PaperVerification.ToricStarSubdivision
public import PaperVerification.ToricStarPurity

@[expose] public section

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
