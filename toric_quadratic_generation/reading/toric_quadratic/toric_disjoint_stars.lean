module

public import PaperVerification.ToricStarContractibility
public import PaperVerification.ToricLargeLoci

@[expose] public section

/-!
# A star subdivision leaves disjoint focus loci unchanged

Disjointness is the proved absence of a fan cone containing both focus ray
sets. Every cone over the second focus is then literally unchanged. This
also preserves every contractible primitive relation supported over that
focus, with its exact vector equation and coefficients.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable (t : Finset (Lattice n)) (ht : t ∈ «Σ».cones) (hne : t.Nonempty)

theorem focus_not_subset_of_disjoint {u : Finset (Lattice n)} (hu : u ∈ «Σ».cones)
    (hdisj : ¬ ∃ s ∈ «Σ».cones, t ∪ u ⊆ s) : ¬ t ⊆ u := by
  intro htu
  exact hdisj ⟨u, hu, Finset.union_subset htu (Finset.Subset.refl u)⟩

/-- The exceptional ray cannot occur in a new cone above an old focus
whose locus was disjoint from the subdivision center. -/
theorem sum_not_mem_new_cone_over_disjoint_focus (hcard : 2 ≤ t.card)
    {u s : Finset (Lattice n)} (hu : u ∈ «Σ».cones)
    (hdisj : ¬ ∃ z ∈ «Σ».cones, t ∪ u ⊆ z)
    (hs : s ∈ («Σ».starSubdivision t ht hne).cones) (hus : u ⊆ s) :
    (∑ v ∈ t, v) ∉ s := by
  intro he
  obtain ⟨p, hp, hps, hparent⟩ :=
    («Σ».mem_starSubdivision_with_sum_iff t ht hne hcard he).mp hs
  have heu : (∑ v ∈ t, v) ∉ u := by
    intro heu
    exact «Σ».sum_rays_not_mem_rays ht hcard («Σ».ray_mem_of_mem_cone hu heu)
  apply hdisj
  refine ⟨s.erase (∑ v ∈ t, v) ∪ t, hparent, ?_⟩
  apply Finset.union_subset
  · exact Finset.subset_union_right
  · intro v hv
    exact Finset.mem_union_left _ (Finset.mem_erase.mpr
      ⟨fun hve => heu (hve ▸ hv), hus hv⟩)

/-- The entire star of a disjoint old focus is unchanged, as a literal
equivalence of old and new cone membership. -/
theorem cone_over_disjoint_focus_iff (hcard : 2 ≤ t.card)
    {u s : Finset (Lattice n)} (hu : u ∈ «Σ».cones)
    (hdisj : ¬ ∃ z ∈ «Σ».cones, t ∪ u ⊆ z) (hus : u ⊆ s) :
    s ∈ («Σ».starSubdivision t ht hne).cones ↔ s ∈ «Σ».cones := by
  constructor
  · intro hs
    have he := «Σ».sum_not_mem_new_cone_over_disjoint_focus t ht hne hcard hu hdisj hs hus
    exact ((«Σ».mem_starSubdivision_without_sum_iff t ht hne he).mp hs).1
  · intro hs
    have hts : ¬ t ⊆ s := fun h => hdisj ⟨s, hs, Finset.union_subset h hus⟩
    exact «Σ».mem_starSubdivision_of_unchanged t ht hne hs hts

/-- A primitive collection survives unchanged if it does not contain the
subdivision focus. All its old rays remain actual new rays. -/
theorem primitiveCollection_survives_star (hcard : 2 ≤ t.card)
    {P : Finset (Lattice n)} (hP : «Σ».IsPrimitiveCollection P) (htP : ¬ t ⊆ P) :
    («Σ».starSubdivision t ht hne).IsPrimitiveCollection P := by
  have heP : (∑ v ∈ t, v) ∉ P :=
    fun h => «Σ».sum_rays_not_mem_rays ht hcard (hP.1 h)
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    exact «Σ».old_ray_mem_starSubdivision_rays t ht hne hcard (hP.1 hv)
  · intro hnew
    exact hP.2.1 ((«Σ».mem_starSubdivision_without_sum_iff t ht hne heP).mp hnew).1
  · intro s hs
    exact «Σ».mem_starSubdivision_of_unchanged t ht hne (hP.2.2 s hs)
      (fun hts => htP (hts.trans hs.subset))

include ht in
/-- A contractible relation whose focus is disjoint from the subdivision
center cannot have its whole positive collection contain that center. -/
theorem focus_not_subset_positive_of_disjoint
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible)
    (hdisj : ¬ ∃ s ∈ «Σ».cones, t ∪ R.negative ⊆ s) : ¬ t ⊆ R.positive := by
  intro htP
  have hPt : ¬ R.positive ⊆ t := fun h =>
    R.primitive.2.1 («Σ».downward t ht R.positive h)
  obtain ⟨p, hpP, hpt⟩ := Finset.not_subset.mp hPt
  have hcore := R.contractible_core_cone hR hpP
  apply hdisj
  refine ⟨R.positive.erase p ∪ R.negative, hcore, ?_⟩
  apply Finset.union_subset
  · intro v hv
    exact Finset.mem_union_left _ (Finset.mem_erase.mpr
      ⟨fun hvp => hpt (hvp ▸ hv), htP hv⟩)
  · exact Finset.subset_union_right

/-- Every contractible relation over a disjoint focus lifts with precisely
the same positive rays, negative rays, coefficients, and degree function. -/
theorem exists_unchanged_contractible_lift (hcard : 2 ≤ t.card)
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible)
    (hdisj : ¬ ∃ s ∈ «Σ».cones, t ∪ R.negative ⊆ s) :
    ∃ S : («Σ».starSubdivision t ht hne).PrimitiveRelation,
      S.positive = R.positive ∧ S.negative = R.negative ∧
      S.coefficient = R.coefficient ∧ S.IsCombinatoriallyContractible := by
  have hPnew := «Σ».primitiveCollection_survives_star t ht hne hcard R.primitive
    («Σ».focus_not_subset_positive_of_disjoint t ht R hR hdisj)
  have hNnew := («Σ».cone_over_disjoint_focus_iff t ht hne hcard R.negative_cone
    hdisj (Finset.Subset.refl R.negative)).mpr R.negative_cone
  let S : («Σ».starSubdivision t ht hne).PrimitiveRelation :=
    ⟨R.positive, R.negative, R.coefficient, hPnew, hNnew, R.coefficient_pos, R.equation⟩
  refine ⟨S, rfl, rfl, rfl, ?_⟩
  intro ν hν hνdisj hNν x hx
  have hNνold : R.negative ∪ ν ∈ «Σ».cones :=
    («Σ».cone_over_disjoint_focus_iff t ht hne hcard R.negative_cone hdisj
      Finset.subset_union_left).mp hNν
  have hνold : ν ∈ «Σ».cones := «Σ».downward _ hNνold ν Finset.subset_union_right
  have hreplace := hR ν hνold hνdisj hNνold x hx
  exact («Σ».cone_over_disjoint_focus_iff t ht hne hcard R.negative_cone hdisj
    (Finset.subset_union_right.trans Finset.subset_union_left)).mpr hreplace

/-- The new exceptional ray and any disjoint old focus have no common
cone, so later subdivisions over that focus remain disjoint from this
exceptional locus. -/
theorem no_common_cone_sum_and_disjoint_focus (hcard : 2 ≤ t.card)
    {u : Finset (Lattice n)} (hu : u ∈ «Σ».cones)
    (hdisj : ¬ ∃ s ∈ «Σ».cones, t ∪ u ⊆ s) :
    ¬ ∃ s ∈ («Σ».starSubdivision t ht hne).cones, insert (∑ v ∈ t, v) u ⊆ s := by
  rintro ⟨s, hs, hsub⟩
  have hus : u ⊆ s := (Finset.subset_insert _ _).trans hsub
  exact «Σ».sum_not_mem_new_cone_over_disjoint_focus t ht hne hcard hu hdisj hs hus
    (hsub (Finset.mem_insert_self _ _))

end SmoothCompleteFan

end PaperVerification.ToricGeometry
