module

public import PaperVerification.ToricPrimitiveRelations

@[expose] public section

/-!
# Primitive collections meeting a contraction focus

The replacement condition forbids a different primitive collection from
containing the entire focus and also a positive ray of the contraction.
This is a finite-cone argument, independent of scheme contractions.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan.PrimitiveRelation

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} (R : «Σ».PrimitiveRelation)

/-- Every cone over the focus can be filled with all positive rays except
one ray which it already omits. -/
theorem fill_cone_with_positive_except (hR : R.IsCombinatoriallyContractible)
    {C : Finset (Lattice n)} (hC : C ∈ «Σ».cones) (hNC : R.negative ⊆ C)
    {u : Lattice n} (hu : u ∈ R.positive) (huC : u ∉ C) :
    R.positive.erase u ∪ C ∈ «Σ».cones := by
  let ν := C \ (R.positive ∪ R.negative)
  have hν : ν ∈ «Σ».cones := «Σ».downward C hC ν Finset.sdiff_subset
  have hdisj : Disjoint ν (R.positive ∪ R.negative) := by
    apply Finset.disjoint_left.mpr
    intro v hv hPN
    exact (Finset.mem_sdiff.mp hv).2 hPN
  have hNν : R.negative ∪ ν ∈ «Σ».cones :=
    «Σ».downward C hC _ (Finset.union_subset hNC Finset.sdiff_subset)
  have hreplace := hR ν hν hdisj hNν u hu
  apply «Σ».downward _ hreplace _
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  · by_cases hvP : v ∈ R.positive
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_erase.mpr ⟨fun he => huC (he ▸ hv), hvP⟩))
    · by_cases hvN : v ∈ R.negative
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hvN)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
          ⟨hv, by simpa only [Finset.mem_union, not_or] using And.intro hvP hvN⟩)

theorem positive_disjoint_of_focus_subset_primitive
    (hR : R.IsCombinatoriallyContractible)
    {Q : Finset (Lattice n)} (hQ : «Σ».IsPrimitiveCollection Q)
    (hNQ : R.negative ⊆ Q) (hneq : R.positive ≠ Q) :
    Disjoint R.positive Q := by
  have hnot : ¬ R.positive ⊆ Q := by
    intro hsubset
    exact R.primitive.2.1 (hQ.2.2 R.positive
      (Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, hneq⟩))
  obtain ⟨u, hu, huQ⟩ := Finset.not_subset.mp hnot
  apply Finset.disjoint_left.mpr
  intro x hxP hxQ
  let C := Q.erase x
  have hC : C ∈ «Σ».cones := hQ.2.2 C (Finset.erase_ssubset hxQ)
  have hNC : R.negative ⊆ C := by
    intro v hv
    have hvx : v ≠ x := by
      intro he
      exact Finset.disjoint_left.mp R.disjoint hxP (he ▸ hv)
    exact Finset.mem_erase.mpr ⟨hvx, hNQ hv⟩
  let ν := C \ (R.positive ∪ R.negative)
  have hνC : ν ⊆ C := Finset.sdiff_subset
  have hν : ν ∈ «Σ».cones := «Σ».downward C hC ν hνC
  have hdisj : Disjoint ν (R.positive ∪ R.negative) := by
    apply Finset.disjoint_left.mpr
    intro v hv hPN
    exact (Finset.mem_sdiff.mp hv).2 hPN
  have hNν : R.negative ∪ ν ∈ «Σ».cones :=
    «Σ».downward C hC _ (Finset.union_subset hNC hνC)
  have hreplace := hR ν hν hdisj hNν u hu
  apply hQ.2.1
  apply «Σ».downward _ hreplace Q
  intro v hv
  by_cases hvP : v ∈ R.positive
  · have hvu : v ≠ u := fun he => huQ (he ▸ hv)
    exact Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hvu, hvP⟩))
  · by_cases hvN : v ∈ R.negative
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hvN)
    · have hvx : v ≠ x := fun he => hvP (he.symm ▸ hxP)
      exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
        ⟨Finset.mem_erase.mpr ⟨hvx, hv⟩, by
          simpa only [Finset.mem_union, not_or] using And.intro hvP hvN⟩)

end SmoothCompleteFan.PrimitiveRelation

end PaperVerification.ToricGeometry
