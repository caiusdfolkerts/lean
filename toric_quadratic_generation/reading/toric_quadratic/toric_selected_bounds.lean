module

public import PaperVerification.ToricSelectedLoci

@[expose] public section

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
