module

public import PaperVerification.ToricPrimitiveOverlap
public import PaperVerification.ToricStarCombinatorics

@[expose] public section

/-!
# The one-positive-exceptional primitive bound

The bound in Lemma 5.1(i) follows from actual primitive-collection
minimality and contraction replacement. No dimension-of-fibers statement
or algebraic-geometric negativity theorem is assumed.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan.PrimitiveRelation

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} (R : «Σ».PrimitiveRelation)

/-- A primitive collection containing the exceptional ray is disjoint from
the old contraction's positive rays and from the old focus rays. -/
theorem primitive_with_exceptional_disjoint_fiber_rays
    (hR : R.IsCombinatoriallyContractible)
    (hne : R.negative.Nonempty) (hcard : 2 ≤ R.negative.card)
    {S : Finset (Lattice n)}
    (hS : («Σ».starSubdivision R.negative R.negative_cone hne).IsPrimitiveCollection S)
    (heS : (∑ v ∈ R.negative, v) ∈ S) :
    Disjoint S R.positive ∧ Disjoint S R.negative := by
  let T := R.negative
  let e := ∑ v ∈ T, v
  let «Σ'» := «Σ».starSubdivision T R.negative_cone hne
  have heold : e ∉ «Σ».rays := «Σ».sum_rays_not_mem_rays R.negative_cone hcard
  have heT : e ∉ T := fun h => heold («Σ».ray_mem_of_mem_cone R.negative_cone h)
  have heP : e ∉ R.positive := fun h => heold (R.primitive.1 h)
  have hST : Disjoint S T := by
    let E := «Σ».exceptionalPrimitiveRelation T R.negative_cone hne hcard
    have hE := «Σ».exceptionalPrimitiveRelation_contractible T R.negative_cone hne hcard
    have hNE : E.negative ⊆ S := Finset.singleton_subset_iff.mpr heS
    have hneq : E.positive ≠ S := by
      intro heq
      change T = S at heq
      exact heT (heq.symm ▸ heS)
    exact (E.positive_disjoint_of_focus_subset_primitive hE hS hNE hneq).symm
  refine ⟨?_, hST⟩
  apply Finset.disjoint_left.mpr
  intro x hxS hxP
  have hxe : x ≠ e := fun he => heP (he ▸ hxP)
  let A := S.erase e
  have hAnew : A ∈ «Σ'».cones := hS.2.2 A (Finset.erase_ssubset heS)
  have hA := («Σ».mem_starSubdivision_without_sum_iff T R.negative_cone hne
    (Finset.notMem_erase e S)).mp hAnew
  have hnotPA : ¬ R.positive ⊆ A := by
    intro h
    exact R.primitive.2.1 («Σ».downward A hA.1 R.positive h)
  obtain ⟨u, huP, huA⟩ := Finset.not_subset.mp hnotPA
  have huT : u ∉ T := fun h => Finset.disjoint_left.mp R.disjoint huP h
  have hxeS : e ∈ S.erase x := Finset.mem_erase.mpr ⟨Ne.symm hxe, heS⟩
  have hproper := hS.2.2 (S.erase x) (Finset.erase_ssubset hxS)
  obtain ⟨p, hpT, hpS, hparent⟩ :=
    («Σ».mem_starSubdivision_with_sum_iff T R.negative_cone hne hcard hxeS).mp hproper
  have hparent' : A.erase x ∪ T ∈ «Σ».cones := by
    change (S.erase x).erase e ∪ T ∈ «Σ».cones at hparent
    simpa only [A, Finset.erase_right_comm] using hparent
  have huC : u ∉ A.erase x ∪ T := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact huA (Finset.mem_of_mem_erase h)
    · exact huT h
  have hfilled := R.fill_cone_with_positive_except hR hparent'
    (Finset.subset_union_right : T ⊆ A.erase x ∪ T) huP huC
  have hAT : A ∪ T ∈ «Σ».cones := by
    apply «Σ».downward _ hfilled _
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · by_cases hzx : z = x
      · subst z
        have hxu : x ≠ u := by
          intro h
          exact huA (h ▸ Finset.mem_erase.mpr ⟨hxe, hxS⟩)
        exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hxu, hxP⟩)
      · exact Finset.mem_union_right _ (Finset.mem_union_left _
          (Finset.mem_erase.mpr ⟨hzx, hz⟩))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ hz)
  obtain ⟨p, hpT, hpA⟩ := Finset.not_subset.mp hA.2
  have hpS : p ∉ S := by
    intro hpS
    have hpe : p ≠ e := fun h => heT (h ▸ hpT)
    exact hpA (Finset.mem_erase.mpr ⟨hpe, hpS⟩)
  exact hS.2.1 ((«Σ».mem_starSubdivision_with_sum_iff T R.negative_cone hne hcard heS).mpr
    ⟨p, hpT, hpS, hAT⟩)

/-- The exact additive form of Lemma 5.1(i) after a nontrivial star:
`r + q + s ≤ n + 2`, equivalently `s ≤ b + 2` when `n=r+q+b`. -/
theorem primitive_with_exceptional_card_bound
    (hR : R.IsCombinatoriallyContractible)
    (hne : R.negative.Nonempty) (hcard : 2 ≤ R.negative.card)
    {S : Finset (Lattice n)}
    (hS : («Σ».starSubdivision R.negative R.negative_cone hne).IsPrimitiveCollection S)
    (heS : (∑ v ∈ R.negative, v) ∈ S) :
    R.fiberDimension + R.negative.card + S.card ≤ n + 2 := by
  let e := ∑ v ∈ R.negative, v
  let A := S.erase e
  have hsize :=
    ((«Σ».starSubdivision R.negative R.negative_cone hne).primitiveCollection_card_bounds hS).1
  have hAcard : A.card = S.card - 1 := Finset.card_erase_of_mem heS
  have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hxA⟩ := hAne
  have hxS := Finset.mem_of_mem_erase hxA
  have hxe := (Finset.mem_erase.mp hxA).1
  have he' : e ∈ S.erase x := Finset.mem_erase.mpr ⟨Ne.symm hxe, heS⟩
  obtain ⟨p, hp, hpn, hparent⟩ := («Σ».mem_starSubdivision_with_sum_iff R.negative
    R.negative_cone hne hcard he').mp (hS.2.2 _ (Finset.erase_ssubset hxS))
  have hparent' : A.erase x ∪ R.negative ∈ «Σ».cones := by
    change (S.erase x).erase e ∪ R.negative ∈ «Σ».cones at hparent
    simpa only [A, Finset.erase_right_comm] using hparent
  have hdisj := R.primitive_with_exceptional_disjoint_fiber_rays hR hne hcard hS heS
  obtain ⟨u, hu⟩ := «Σ».primitiveCollection_nonempty R.primitive
  have huC : u ∉ A.erase x ∪ R.negative := by
    intro hh
    rcases Finset.mem_union.mp hh with hh | hh
    · exact Finset.disjoint_left.mp hdisj.1
        (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hh)) hu
    · exact Finset.disjoint_left.mp R.disjoint hu hh
  have hfilled := R.fill_cone_with_positive_except hR hparent'
    Finset.subset_union_right hu huC
  have hdim := «Σ».card_cone_le hfilled
  have hPN : Disjoint (R.positive.erase u) R.negative :=
    R.disjoint.mono_left (Finset.erase_subset u R.positive)
  have hPA : Disjoint (R.positive.erase u) (A.erase x) := by
    apply Finset.disjoint_left.mpr
    intro v hvP hvA
    exact Finset.disjoint_left.mp hdisj.1
      (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hvA)) (Finset.mem_of_mem_erase hvP)
  have hAN : Disjoint (A.erase x) R.negative :=
    hdisj.2.mono_left ((Finset.erase_subset x A).trans (Finset.erase_subset e S))
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_right.mpr ⟨hPA, hPN⟩),
    Finset.card_union_of_disjoint hAN, Finset.card_erase_of_mem hu,
    Finset.card_erase_of_mem hxA, hAcard] at hdim
  unfold fiberDimension
  omega

/-- The codimension-one case uses the original divisor ray and makes no
subdivision. Its bound is the same additive formula with `q=1`. -/
theorem primitive_with_divisor_focus_card_bound
    (hR : R.IsCombinatoriallyContractible) (e : Lattice n)
    (hfocus : R.negative = {e})
    {S : Finset (Lattice n)} (hS : «Σ».IsPrimitiveCollection S) (heS : e ∈ S) :
    R.fiberDimension + 1 + S.card ≤ n + 2 := by
  have heN : e ∈ R.negative := hfocus.symm ▸ Finset.mem_singleton_self e
  have hneq : R.positive ≠ S := by
    intro he
    exact Finset.disjoint_left.mp R.disjoint (he.symm ▸ heS) heN
  have hdisj := R.positive_disjoint_of_focus_subset_primitive hR hS
    (by simpa only [hfocus, Finset.singleton_subset_iff] using heS) hneq
  let A := S.erase e
  have hsize := («Σ».primitiveCollection_card_bounds hS).1
  have hAcard : A.card = S.card - 1 := Finset.card_erase_of_mem heS
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < A.card by omega)
  have hxS := Finset.mem_of_mem_erase hx
  have hC := hS.2.2 (S.erase x) (Finset.erase_ssubset hxS)
  have hNC : R.negative ⊆ S.erase x := by
    rw [hfocus, Finset.singleton_subset_iff]
    exact Finset.mem_erase.mpr ⟨Ne.symm (Finset.mem_erase.mp hx).1, heS⟩
  obtain ⟨u, hu⟩ := «Σ».primitiveCollection_nonempty R.primitive
  have huC : u ∉ S.erase x := fun hh =>
    Finset.disjoint_left.mp hdisj hu (Finset.mem_of_mem_erase hh)
  have hfill := R.fill_cone_with_positive_except hR hC hNC hu huC
  have hdim := «Σ».card_cone_le hfill
  have hPC : Disjoint (R.positive.erase u) (S.erase x) :=
    hdisj.mono (Finset.erase_subset u R.positive) (Finset.erase_subset x S)
  rw [Finset.card_union_of_disjoint hPC, Finset.card_erase_of_mem hu,
    Finset.card_erase_of_mem hxS] at hdim
  unfold fiberDimension
  omega

end SmoothCompleteFan.PrimitiveRelation

end PaperVerification.ToricGeometry
