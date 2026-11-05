module

public import PaperVerification.ToricContractibleWalls

@[expose] public section

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
