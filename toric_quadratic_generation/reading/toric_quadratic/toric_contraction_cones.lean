module
public import PaperVerification.ToricPrimitiveRelations
public import Mathlib.Data.Finset.SDiff
public import Lean.Elab.Tactic.Omega
@[expose] public section
/-!
# Cone consequences of the actual contraction replacement condition

The hypotheses below are the explicit cone replacement condition in
Casagrande's theorem. In particular no geometric contraction, dimension
bound, or maximal-cone ray count is built into them.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan.PrimitiveRelation

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} (R : «Σ».PrimitiveRelation)

/-- A full-dimensional cone containing the negative focus of a contractible
primitive relation contains exactly `r` positive rays. This is the old-fan
part of Lemma 5.1(iii), with actual finite ray sets throughout. -/
theorem positive_count_in_full_cone (hR : R.IsCombinatoriallyContractible)
    {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones) (hcard : s.card = n)
    (hnegative : R.negative ⊆ s) :
    (R.positive ∩ s).card = R.fiberDimension := by
  let ν := s \ (R.positive ∪ R.negative)
  have hνs : ν ⊆ s := Finset.sdiff_subset
  have hνcone : ν ∈ «Σ».cones := «Σ».downward s hs ν hνs
  have hνdisjoint : Disjoint ν (R.positive ∪ R.negative) := by
    apply Finset.disjoint_left.mpr
    intro v hv hrest
    exact (Finset.mem_sdiff.mp hv).2 hrest
  have hnegativeν : R.negative ∪ ν ∈ «Σ».cones :=
    «Σ».downward s hs _ (Finset.union_subset hnegative hνs)
  obtain ⟨x, hx⟩ := «Σ».primitiveCollection_nonempty R.primitive
  have hexpanded := hR ν hνcone hνdisjoint hnegativeν x hx
  have hdim := «Σ».card_cone_le hexpanded
  have hposneg : Disjoint (R.positive.erase x) R.negative :=
    R.disjoint.mono_left (Finset.erase_subset x R.positive)
  have hcoreν : Disjoint (R.positive.erase x ∪ R.negative) ν := by
    apply Finset.disjoint_left.mpr
    intro v hv hvν
    apply (Finset.mem_sdiff.mp hvν).2
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.mem_union_left _ (Finset.mem_of_mem_erase hv)
    · exact Finset.mem_union_right _ hv
  rw [Finset.card_union_of_disjoint hcoreν,
    Finset.card_union_of_disjoint hposneg,
    Finset.card_erase_of_mem hx] at hdim
  have hpartition : (R.positive ∩ s) ∪ R.negative ∪ ν = s := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_union.mp hv with hv | hv
      · rcases Finset.mem_union.mp hv with hv | hv
        · exact (Finset.mem_inter.mp hv).2
        · exact hnegative hv
      · exact hνs hv
    · intro hv
      by_cases hvP : v ∈ R.positive
      · exact Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hvP, hv⟩))
      · by_cases hvT : v ∈ R.negative
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hvT)
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv, by
            simpa only [Finset.mem_union, not_or] using And.intro hvP hvT⟩)
  have hPT : Disjoint (R.positive ∩ s) R.negative :=
    R.disjoint.mono_left Finset.inter_subset_left
  have hPTν : Disjoint ((R.positive ∩ s) ∪ R.negative) ν := by
    apply Finset.disjoint_left.mpr
    intro v hv hvν
    apply (Finset.mem_sdiff.mp hvν).2
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.mem_union_left _ (Finset.mem_inter.mp hv).1
    · exact Finset.mem_union_right _ hv
  have hcounts : (R.positive ∩ s).card + R.negative.card + ν.card = n := by
    rw [← Finset.card_union_of_disjoint hPT,
      ← Finset.card_union_of_disjoint hPTν, hpartition, hcard]
  have hupper := R.positive_rays_in_cone_bound hs
  unfold fiberDimension at hupper ⊢
  omega

/-- There is a unique positive ray missing from every full cone over the
focus. The assertion is about the full ray set, not merely its cardinality. -/
theorem exists_unique_omitted_positive (hR : R.IsCombinatoriallyContractible)
    {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones) (hcard : s.card = n)
    (hnegative : R.negative ⊆ s) :
    ∃ x ∈ R.positive, R.positive \ s = {x} := by
  have hcount := R.positive_count_in_full_cone hR hs hcard hnegative
  have hsize := («Σ».primitiveCollection_card_bounds R.primitive).1
  have herase : (R.positive \ s).card = 1 := by
    have hsplit := Finset.card_sdiff_add_card_inter R.positive s
    unfold fiberDimension at hcount
    omega
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp herase
  refine ⟨x, ?_, hx⟩
  exact (Finset.mem_sdiff.mp (hx.symm ▸ Finset.mem_singleton_self x)).1

/-- The dimension of the negative focus is bounded by the complementary
fiber dimension, directly from the smooth cone supplied by replacement. -/
theorem focus_card_le_codimension (hR : R.IsCombinatoriallyContractible) :
    R.negative.card ≤ n - R.fiberDimension := by
  have h := R.contractible_dimension_bound hR
  omega

/-- A contraction with fiber dimension equal to the whole ambient dimension
has zero-dimensional focus; this is the numerical first step of the simplex
base case. No projective-space identification is claimed by this lemma. -/
theorem negative_eq_empty_of_fiberDimension_eq (hR : R.IsCombinatoriallyContractible)
    (hr : R.fiberDimension = n) : R.negative = ∅ := by
  apply Finset.card_eq_zero.mp
  have h := R.contractible_dimension_bound hR
  omega

end SmoothCompleteFan.PrimitiveRelation

end PaperVerification.ToricGeometry
