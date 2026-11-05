module

public import PaperVerification.ToricSimultaneousPrimitive
public import PaperVerification.ToricFiberWalls
public import PaperVerification.ToricTwoExceptionalPositive

@[expose] public section

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
