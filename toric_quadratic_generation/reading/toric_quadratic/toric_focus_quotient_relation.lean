module

public import PaperVerification.ToricQuotientFaceSupport
public import PaperVerification.ToricPrimitiveOverlap

@[expose] public section

/-!
# The actual projective-fiber relation on a contracted face

Quotienting the focus of a combinatorially contractible primitive relation
produces an actual primitive relation with empty focus in the saturated
quotient-star fan. Its replacement property, number of positive rays, and
support degree are proved from the original fan, rather than supplied as
bundle assumptions.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan.PrimitiveRelation

open Set
open scoped BigOperators Classical

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} (R : «Σ».PrimitiveRelation)
    (hR : R.IsCombinatoriallyContractible)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hI : I.image b = R.negative)

include hR in
theorem positive_lies_in_focus_star {v : Lattice n} (hv : v ∈ R.positive) :
    ∃ s ∈ «Σ».cones, R.negative ⊆ s ∧ v ∈ s \ R.negative := by
  have hcard := («Σ».primitiveCollection_card_bounds R.primitive).1
  obtain ⟨u, hu, huv⟩ := Finset.exists_mem_ne (by omega : 1 < R.positive.card) v
  refine ⟨R.positive.erase u ∪ R.negative, R.contractible_core_cone hR hu,
    Finset.subset_union_right, ?_⟩
  exact Finset.mem_sdiff.mpr
    ⟨Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨huv.symm, hv⟩),
      fun hvN => Finset.disjoint_left.mp R.disjoint hv hvN⟩

include hR hI in
theorem focusQuotient_injective_positive :
    Set.InjOn (coneQuotientLattice b I) (R.positive : Set (Lattice n)) := by
  intro v hv w hw he
  obtain ⟨s, hs, hNs, hvs⟩ := R.positive_lies_in_focus_star hR hv
  obtain ⟨t, ht, hNt, hwt⟩ := R.positive_lies_in_focus_star hR hw
  rw [← hI] at hNs hvs hNt hwt
  exact «Σ».coneQuotient_injective_star_rays b I hs ht hNs hNt hvs hwt he

include hR in
theorem focusQuotient_positive_ray {v : Lattice n} (hv : v ∈ R.positive) :
    coneQuotientLattice b I v ∈
      («Σ».completeQuotientStarFan b I (hI.symm ▸ R.negative_cone)).rays := by
  obtain ⟨s, hs, hNs, hvs⟩ := R.positive_lies_in_focus_star hR hv
  rw [← hI] at hNs hvs
  exact «Σ».projected_starRay_mem b I _ hs hNs hvs

include hR in
/-- The projected positive rays form a genuine primitive collection.
Minimality and failure to be a cone are both established in the quotient fan. -/
theorem focusQuotient_positive_primitive :
    («Σ».completeQuotientStarFan b I (hI.symm ▸ R.negative_cone)).IsPrimitiveCollection
      (R.positive.image (coneQuotientLattice b I)) := by
  let Ψ := «Σ».completeQuotientStarFan b I (hI.symm ▸ R.negative_cone)
  let P := R.positive.image (coneQuotientLattice b I)
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    exact R.focusQuotient_positive_ray hR b I hI hv
  · intro hP
    obtain ⟨s, hs, hIs, hPs⟩ := («Σ».mem_quotientStarCones b I P).mp hP
    have hsub : R.positive ⊆ s := by
      intro v hv
      have hvP : coneQuotientLattice b I v ∈ P := Finset.mem_image.mpr ⟨v, hv, rfl⟩
      rw [hPs] at hvP
      obtain ⟨w, hw, he⟩ := Finset.mem_image.mp hvP
      obtain ⟨t, ht, hNt, hvt⟩ := R.positive_lies_in_focus_star hR hv
      rw [← hI] at hNt hvt
      have hwv := «Σ».coneQuotient_injective_star_rays b I hs ht hIs hNt hw hvt he
      exact hwv ▸ (Finset.mem_sdiff.mp hw).1
    exact R.primitive.2.1 («Σ».downward s hs R.positive hsub)
  · intro Q hQ
    have hQP := (Finset.ssubset_iff_subset_ne.mp hQ).1
    have hnot : ¬ P ⊆ Q := by
      intro hPQ
      exact (ne_of_lt hQ) (Finset.Subset.antisymm hQP hPQ)
    obtain ⟨u, huP, huQ⟩ := Finset.not_subset.mp hnot
    obtain ⟨v, hv, hvu⟩ := Finset.mem_image.mp huP
    let C := R.positive.erase v ∪ R.negative
    have hC : C ∈ «Σ».cones := R.contractible_core_cone hR hv
    have hIC : I.image b ⊆ C := by
      rw [hI]
      exact Finset.subset_union_right
    let D := (C \ I.image b).image (coneQuotientLattice b I)
    have hD : D ∈ Ψ.cones := («Σ».mem_quotientStarCones b I D).mpr ⟨C, hC, hIC, rfl⟩
    apply Ψ.downward D hD Q
    intro w hw
    obtain ⟨z, hz, hzw⟩ := Finset.mem_image.mp (hQP hw)
    have hzv : z ≠ v := by
      intro he
      apply huQ
      have hwu : w = u := hzw.symm.trans (he ▸ hvu)
      exact hwu ▸ hw
    refine Finset.mem_image.mpr ⟨z, Finset.mem_sdiff.mpr ⟨?_, ?_⟩, hzw⟩
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hzv, hz⟩)
    · rw [hI]
      exact fun hzN => Finset.disjoint_left.mp R.disjoint hz hzN

/-- The literal primitive relation on the quotient-star fan. Its focus is
empty because the original positive sum belongs to the removed normal span. -/
def focusQuotientRelation :
    («Σ».completeQuotientStarFan b I (hI.symm ▸ R.negative_cone)).PrimitiveRelation where
  positive := R.positive.image (coneQuotientLattice b I)
  negative := ∅
  coefficient := fun _ => 0
  primitive := R.focusQuotient_positive_primitive hR b I hI
  negative_cone := («Σ».completeQuotientStarFan b I (hI.symm ▸ R.negative_cone)).empty_mem
  coefficient_pos := by simp
  equation := by
    rw [Finset.sum_empty, Finset.sum_image]
    · rw [← map_sum, R.equation, map_sum]
      apply Finset.sum_eq_zero
      intro v hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hI.symm ▸ hv)
      rw [map_smul, coneQuotientLattice_of_mem b I
        (Finset.mem_image.mpr ⟨i, hi, rfl⟩), smul_zero]
    · exact R.focusQuotient_injective_positive hR b I hI

theorem focusQuotientRelation_negative :
    (R.focusQuotientRelation hR b I hI).negative = ∅ := rfl

theorem focusQuotientRelation_fiberDimension :
    (R.focusQuotientRelation hR b I hI).fiberDimension = R.fiberDimension := by
  unfold fiberDimension
  change (R.positive.image (coneQuotientLattice b I)).card - 1 = R.positive.card - 1
  rw [Finset.card_image_of_injOn (R.focusQuotient_injective_positive hR b I hI)]

/-- The full replacement condition descends to the actual quotient fan. -/
theorem focusQuotientRelation_contractible :
    (R.focusQuotientRelation hR b I hI).IsCombinatoriallyContractible := by
  let Ψ := «Σ».completeQuotientStarFan b I (hI.symm ▸ R.negative_cone)
  intro ν hν hdisj hNν u hu
  change u ∈ R.positive.image (coneQuotientLattice b I) at hu
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨s, hs, hIs, hνs⟩ := («Σ».mem_quotientStarCones b I ν).mp hν
  have hNs : R.negative ⊆ s := hI ▸ hIs
  have hvN : v ∉ R.negative := fun hvN => Finset.disjoint_left.mp R.disjoint hv hvN
  have hvs : v ∉ s := by
    intro hvs
    have hvν : coneQuotientLattice b I v ∈ ν := by
      rw [hνs]
      exact Finset.mem_image.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hvs, hI.symm ▸ hvN⟩, rfl⟩
    apply Finset.disjoint_left.mp hdisj hvν
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
  let C := R.positive.erase v ∪ s
  have hC : C ∈ «Σ».cones := R.fill_cone_with_positive_except hR hs hNs hv hvs
  have hIC : I.image b ⊆ C := hIs.trans Finset.subset_union_right
  let D := (C \ I.image b).image (coneQuotientLattice b I)
  have hD : D ∈ Ψ.cones := («Σ».mem_quotientStarCones b I D).mpr ⟨C, hC, hIC, rfl⟩
  apply Ψ.downward D hD
  intro w hw
  change w ∈ (R.positive.image (coneQuotientLattice b I)).erase
      (coneQuotientLattice b I v) ∪ ∅ ∪ ν at hw
  rcases Finset.mem_union.mp hw with hwP | hwν
  · have hwP := Finset.mem_union.mp hwP
    rcases hwP with hwP | hwempty
    · obtain ⟨hwne, hwP⟩ := Finset.mem_erase.mp hwP
      obtain ⟨z, hz, hzw⟩ := Finset.mem_image.mp hwP
      have hzv : z ≠ v := fun he => hwne (hzw.symm.trans (congrArg _ he))
      refine Finset.mem_image.mpr ⟨z, Finset.mem_sdiff.mpr ⟨?_, ?_⟩, hzw⟩
      · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hzv, hz⟩)
      · rw [hI]
        exact fun hzN => Finset.disjoint_left.mp R.disjoint hz hzN
    · simp at hwempty
  · rw [hνs] at hwν
    obtain ⟨z, hz, hzw⟩ := Finset.mem_image.mp hwν
    exact Finset.mem_image.mpr ⟨z, Finset.mem_sdiff.mpr
      ⟨Finset.mem_union_right _ (Finset.mem_sdiff.mp hz).1,
        (Finset.mem_sdiff.mp hz).2⟩, hzw⟩

/-- Restriction preserves the actual degree of the contracted class.
The affine-origin correction cancels the original negative coefficients. -/
theorem focusQuotientRelation_degree (a : Lattice n → ℝ) :
    (R.focusQuotientRelation hR b I hI).degree
      («Σ».faceSupport b I (hI.symm ▸ R.negative_cone) a) = R.degree a := by
  let o := quotientFaceOrigin a b I
  let f : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) o
  have hp (v : Lattice n) (hv : v ∈ R.positive) :
      «Σ».faceSupport b I (hI.symm ▸ R.negative_cone) a (coneQuotientLattice b I v) =
        a v + f (embed n v) := by
    obtain ⟨s, hs, hNs, hvs⟩ := R.positive_lies_in_focus_star hR hv
    rw [← hI] at hNs hvs
    rw [«Σ».faceSupport_projected b I _ a hs hNs hvs]
    congr 1
    simpa [f, o, dotProductEquiv] using
      (dotProduct_comm (embed n v) (quotientFaceOrigin a b I))
  have hnegative (v : Lattice n) (hv : v ∈ R.negative) : f (embed n v) = -a v := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hI.symm ▸ hv)
    change (dotProductEquiv ℝ (Fin n) o) (embed n (b i)) = _
    rw [show (dotProductEquiv ℝ (Fin n) o) (embed n (b i)) =
        (dotProductEquiv ℝ (Fin n) (embed n (b i))) o from by
          simpa [dotProductEquiv] using (dotProduct_comm o (embed n (b i))),
      normal_pairing_eq_dual_coordinate, quotientFaceOrigin_coordinate, if_pos hi]
  have hsum : (∑ v ∈ R.positive, f (embed n v)) =
      -(∑ v ∈ R.negative, (R.coefficient v : ℝ) * a v) := by
    rw [← map_sum, ← map_sum, R.equation, map_sum, map_sum]
    simp only [embed_int_smul, Int.cast_natCast, map_smul, smul_eq_mul]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    rw [hnegative v hv, mul_neg]
  change (∑ u ∈ R.positive.image (coneQuotientLattice b I),
      «Σ».faceSupport b I (hI.symm ▸ R.negative_cone) a u) - 0 = _
  rw [sub_zero, Finset.sum_image]
  · rw [Finset.sum_congr rfl hp, Finset.sum_add_distrib, hsum]
    rfl
  · exact R.focusQuotient_injective_positive hR b I hI

end PaperVerification.ToricGeometry.SmoothCompleteFan.PrimitiveRelation
