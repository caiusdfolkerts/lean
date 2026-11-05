module

public import PaperVerification.ToricSelectedDegreeEstimates

@[expose] public section

/-!
# The complementary wall count in Proposition 5.2

Every full cone over a selected ray retains exactly `r` of the original
positive fiber rays. For a primitive pair this makes at most one common
fiber ray lie outside its actual wall. The remaining zero-coefficient wall
rays are bounded by the two actual base dimensions.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

/-- A finite-set form of the wall count. Both selected intersections are
counted inside `D`; their overlap can escape `N` only through the wall's
complement or through its zero-coefficient rays. -/
theorem two_intersections_card_le_wall_count {α : Type*} [DecidableEq α]
    (D U V W N : Finset α) (hNW : N ⊆ W) (b : ℕ)
    (hzero : (W \ N).card ≤ b) (hout : ((U ∩ V) \ W).card ≤ 1) :
    (D ∩ U).card + (D ∩ V).card ≤ D.card + (D ∩ N).card + b + 1 := by
  let C := (D ∩ U) ∩ V
  have hsub : C ⊆ (D ∩ N) ∪ (W \ N) ∪ ((U ∩ V) \ W) := by
    intro x hx
    obtain ⟨hxDU, hxV⟩ := Finset.mem_inter.mp hx
    obtain ⟨hxD, hxU⟩ := Finset.mem_inter.mp hxDU
    by_cases hxW : x ∈ W
    · by_cases hxN : x ∈ N
      · exact Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxD, hxN⟩))
      · exact Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxW, hxN⟩))
    · exact Finset.mem_union_right _
        (Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hxU, hxV⟩, hxW⟩)
  have hc := Finset.card_le_card hsub
  have hu1 := Finset.card_union_le ((D ∩ N) ∪ (W \ N)) ((U ∩ V) \ W)
  have hu2 := Finset.card_union_le (D ∩ N) (W \ N)
  have hC : C.card ≤ (D ∩ N).card + b + 1 := by omega
  have hUD : (D ∩ U) ∪ (D ∩ V) ⊆ D :=
    Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
  have hUcard := Finset.card_le_card hUD
  have hinter : (D ∩ U) ∩ (D ∩ V) = C := by
    ext x
    simp only [C, Finset.mem_inter]
    tauto
  have hcount := Finset.card_union_add_card_inter (D ∩ U) (D ∩ V)
  rw [hinter] at hcount
  omega

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable {ι : Type*} [Fintype ι] (R : ι → «Σ».PrimitiveRelation)
variable (hR : ∀ i, (R i).IsCombinatoriallyContractible)
variable (hne : ∀ i, (R i).negative.Nonempty)
variable (hdisj : «Σ».PairwiseDisjointFoci (fun i => (R i).negative))

include hne in
theorem selected_ray_not_own_positive (i : ι) :
    «Σ».selectedRay R i ∉ (R i).positive := by
  by_cases hi : 2 ≤ (R i).negative.card
  · intro hh
    exact «Σ».sum_rays_not_mem_rays (R i).negative_cone hi ((R i).primitive.1 hh)
  · have hf := «Σ».selected_focus_of_not_blowup R hne i hi
    exact fun hh => Finset.disjoint_left.mp (R i).disjoint hh
      (hf.symm ▸ Finset.mem_singleton_self _)

include hR in
/-- Exactly the original `r` positive fiber rays occur in every full cone
above the selected locus, after all disjoint subdivisions. -/
theorem selected_positive_count_full_cone (i : ι)
    {s : Finset (Lattice n)} (hs : s ∈ («Σ».selectedFan R hne hdisj).cones)
    (hscard : s.card = n) (he : «Σ».selectedRay R i ∈ s) :
    ((R i).positive ∩ s).card = (R i).fiberDimension := by
  by_cases hi : 2 ≤ (R i).negative.card
  · let i' : «Σ».BlowupIndices R := ⟨i, hi⟩
    have hsingle := («Σ».simultaneous_cone_over_sum_iff («Σ».selectedStarFocus R)
      (fun j => (R j).negative_cone) (fun j => hne j)
      («Σ».selectedStarFocus_disjoint R hdisj) (fun j => j.property) i' he).mp hs
    obtain ⟨U, hU, hUcard, hNU, p, hp, hseq⟩ :=
      «Σ».full_star_cone_parent (R i).negative (R i).negative_cone (hne i) hi
        hsingle hscard he
    have hpP : p ∉ (R i).positive := fun hh => Finset.disjoint_left.mp (R i).disjoint hh hp
    have heP := «Σ».selected_ray_not_own_positive R hne i
    have hinter : (R i).positive ∩ s = (R i).positive ∩ U := by
      rw [hseq]
      ext v
      simp only [starRaySet, Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ⟨hvP, hve | ⟨hvp, hvU⟩⟩
        · change v = «Σ».selectedRay R i at hve
          exact (heP (hve ▸ hvP)).elim
        · exact ⟨hvP, hvU⟩
      · rintro ⟨hvP, hvU⟩
        refine ⟨hvP, Or.inr ⟨?_, hvU⟩⟩
        exact fun hvp => hpP (hvp ▸ hvP)
    rw [hinter]
    exact (R i).positive_count_in_full_cone (hR i) hU hUcard hNU
  · have hf := «Σ».selected_focus_of_not_blowup R hne i hi
    have hold := («Σ».selected_divisor_cone_iff R hne hdisj i hi he).mp hs
    exact (R i).positive_count_in_full_cone (hR i) hold hscard
      (by simpa only [hf, Finset.singleton_subset_iff] using he)

include hR hne hdisj in
theorem selected_positive_missing_from_wall_card (i : ι) (W : Finset (Lattice n))
    (hs : insert («Σ».selectedRay R i) W ∈ («Σ».selectedFan R hne hdisj).cones)
    (hscard : (insert («Σ».selectedRay R i) W).card = n) :
    ((R i).positive \ W).card = 1 := by
  have hcount := «Σ».selected_positive_count_full_cone R hR hne hdisj i
    hs hscard (Finset.mem_insert_self _ _)
  have heP := «Σ».selected_ray_not_own_positive R hne i
  have hinter : (R i).positive ∩ insert («Σ».selectedRay R i) W = (R i).positive ∩ W := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨hvP, hve | hvW⟩
      · exact (heP (hve ▸ hvP)).elim
      · exact ⟨hvP, hvW⟩
    · rintro ⟨hvP, hvW⟩
      exact ⟨hvP, Or.inr hvW⟩
  rw [hinter] at hcount
  have hsplit := Finset.card_sdiff_add_card_inter (R i).positive W
  have htotal := (R i).positive_card_eq_fiberDimension_add_one
  omega

include hR in
/-- The weighted negative-wall estimate used for the complementary
two-positive bound. `D` may be any collection of at most `n` old rays. -/
theorem selected_pair_negative_weight_bound (hpure : «Σ».IsPure)
    (S : («Σ».selectedFan R hne hdisj).PrimitiveRelation)
    (hS : S.IsCombinatoriallyContractible) (i j : ι) (hij : i ≠ j)
    (hi : «Σ».selectedRay R i ∈ S.positive)
    (hj : «Σ».selectedRay R j ∈ S.positive)
    (D : Finset (Lattice n)) (hDcard : D.card ≤ n) :
    (((D ∩ (R i).positive).card : ℝ) + ((D ∩ (R j).positive).card : ℝ) -
      n - «Σ».selectedBaseDimension R i - «Σ».selectedBaseDimension R j - 1) ≤
      S.negativeWeightOn D := by
  have hP := «Σ».primitive_selected_pair_eq R hne hdisj S.primitive i j hij hi hj
  have hef := («Σ».selectedRay_injective R hdisj).ne hij
  have hΓpure := «Σ».isPure_simultaneousSubdivision («Σ».selectedStarFocus R) hpure
    (fun k => (R k).negative_cone) (fun k => hne k) («Σ».selectedStarFocus_disjoint R hdisj)
  obtain ⟨W, hWP, hNW, hfirst, hfirstcard, hsecond, hsecondcard⟩ :=
    S.exists_full_pair_wall hΓpure hS («Σ».selectedRay R i) («Σ».selectedRay R j) hef hP
  have heW : «Σ».selectedRay R i ∉ W := fun hh => Finset.disjoint_left.mp hWP hh hi
  have hWcard : W.card + 1 = n := by
    simpa only [Finset.card_insert_of_notMem heW] using hfirstcard
  have hqbound := («Σ».selected_two_positive_card_bound R hR hne hdisj
    hpure S hS i j hij hi hj).2
  have hzero : (W \ S.negative).card ≤
      «Σ».selectedBaseDimension R i + «Σ».selectedBaseDimension R j := by
    have hsplit := Finset.card_sdiff_add_card_eq_card hNW
    omega
  have hout : (((R i).positive ∩ (R j).positive) \ W).card ≤ 1 := by
    have hsub : ((R i).positive ∩ (R j).positive) \ W ⊆ (R i).positive \ W := by
      intro v hv
      obtain ⟨hvP, hvW⟩ := Finset.mem_sdiff.mp hv
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hvP).1, hvW⟩
    have hh := Finset.card_le_card hsub
    rw [«Σ».selected_positive_missing_from_wall_card R hR hne hdisj i W hfirst hfirstcard] at hh
    exact hh
  have hcount := two_intersections_card_le_wall_count D (R i).positive (R j).positive
    W S.negative hNW («Σ».selectedBaseDimension R i + «Σ».selectedBaseDimension R j)
    hzero hout
  have hcount' : (D ∩ (R i).positive).card + (D ∩ (R j).positive).card ≤
      n + (S.negative ∩ D).card + «Σ».selectedBaseDimension R i +
        «Σ».selectedBaseDimension R j + 1 := by
    rw [Finset.inter_comm D S.negative] at hcount
    omega
  have hcountR : ((D ∩ (R i).positive).card : ℝ) + ((D ∩ (R j).positive).card : ℝ) ≤
      (n : ℝ) + ((S.negative ∩ D).card : ℝ) + «Σ».selectedBaseDimension R i +
        «Σ».selectedBaseDimension R j + 1 := by exact_mod_cast hcount'
  have hweight := S.card_negative_inter_le_weight D
  linarith

theorem outside_cone_avoids_selected_rays {σ D : Finset (Lattice n)}
    (hσ : σ ∈ «Σ».cones) (hD : D ⊆ σ)
    (houtside : ∀ i, ¬ (R i).negative ⊆ σ) :
    ∀ i, «Σ».selectedRay R i ∉ D := by
  intro i hi
  exact houtside i ((«Σ».sum_rays_mem_cone_iff (R i).negative_cone hσ).mp
    (latticeRayCone_generator σ (hD hi)))

theorem outside_focus_selection_card_bound {σ D : Finset (Lattice n)}
    (hD : D ⊆ σ) (houtside : ∀ i, ¬ (R i).negative ⊆ σ) (i : ι) :
    ((R i).negative ∩ D).card + 1 ≤ (R i).negative.card := by
  have hproper : (R i).negative ∩ D ⊂ (R i).negative := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, ?_⟩
    intro heq
    exact houtside i (by
      rw [← heq]
      exact Finset.inter_subset_right.trans hD)
  exact Finset.card_lt_card hproper

end SmoothCompleteFan

end PaperVerification.ToricGeometry
