module

public import PaperVerification.ToricSimultaneousSupport
public import PaperVerification.ToricRelationTransport

@[expose] public section

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
