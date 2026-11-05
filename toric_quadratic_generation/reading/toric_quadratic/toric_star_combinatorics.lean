module
public import PaperVerification.ToricStarSubdivision
public import PaperVerification.ToricStarStrictSupport
public import Mathlib.Tactic.Tauto
@[expose] public section

/-!
# Exact cone combinatorics of the smooth star subdivision

The membership descriptions are derived from the constructed fan. They are
the finite combinatorial basis for the later primitive-relation pushdown.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable (t : Finset (Lattice n)) (ht : t ∈ «Σ».cones) (hne : t.Nonempty)

theorem starSubdivision_rays_subset :
    («Σ».starSubdivision t ht hne).rays ⊆ insert (∑ v ∈ t, v) «Σ».rays := by
  intro v hv
  obtain ⟨s, hs, hvs⟩ := ((«Σ».starSubdivision t ht hne).mem_rays_iff v).mp hv
  obtain ⟨u, hu, hsu⟩ := (mem_finiteConeFamilyClosure («Σ».starCandidates t) s).mp hs
  exact «Σ».starCandidates_subset_rays t u hu (hsu hvs)

/-- An old-ray set avoiding the new sum ray is a new cone exactly when it
was an old cone and did not contain the focus. -/
theorem mem_starSubdivision_without_sum_iff {s : Finset (Lattice n)}
    (he : (∑ v ∈ t, v) ∉ s) :
    s ∈ («Σ».starSubdivision t ht hne).cones ↔ s ∈ «Σ».cones ∧ ¬ t ⊆ s := by
  constructor
  · intro hs
    obtain ⟨u, hu, hsu⟩ := (mem_finiteConeFamilyClosure («Σ».starCandidates t) s).mp hs
    rcases («Σ».mem_starCandidates t u).mp hu with ⟨hu, htu⟩ |
      ⟨u', hu', p, hp, htu', rfl⟩
    · exact ⟨«Σ».downward u hu s hsu, fun hts => htu (hts.trans hsu)⟩
    · have hsub : s ⊆ u'.erase p := by
        intro v hv
        rcases (mem_starRaySet _ _ _ _).mp (hsu hv) with hve | ⟨hvp, hvu⟩
        · exact (he (hve ▸ hv)).elim
        · exact Finset.mem_erase.mpr ⟨hvp, hvu⟩
      refine ⟨«Σ».downward u' hu' s (hsub.trans (Finset.erase_subset p u')), ?_⟩
      intro hts
      exact (Finset.mem_erase.mp (hsub (hts hp))).1 rfl
  · rintro ⟨hs, hts⟩
    exact «Σ».mem_starSubdivision_of_unchanged t ht hne hs hts

/-- A cone containing the exceptional ray is characterized by replacing it
with the full old focus and omitting at least one focus ray. -/
theorem mem_starSubdivision_with_sum_iff (hcard : 2 ≤ t.card)
    {s : Finset (Lattice n)} (he : (∑ v ∈ t, v) ∈ s) :
    s ∈ («Σ».starSubdivision t ht hne).cones ↔
      ∃ p ∈ t, p ∉ s ∧ (s.erase (∑ v ∈ t, v) ∪ t) ∈ «Σ».cones := by
  let e := ∑ v ∈ t, v
  have heold : e ∉ «Σ».rays := «Σ».sum_rays_not_mem_rays ht hcard
  constructor
  · intro hs
    obtain ⟨u, hu, hsu⟩ := (mem_finiteConeFamilyClosure («Σ».starCandidates t) s).mp hs
    rcases («Σ».mem_starCandidates t u).mp hu with ⟨hu, htu⟩ |
      ⟨u', hu', p, hp, htu', rfl⟩
    · exact (heold («Σ».ray_mem_of_mem_cone hu (hsu he))).elim
    · have hpe : p ≠ e := fun h => heold (h ▸ «Σ».ray_mem_of_mem_cone ht hp)
      have hps : p ∉ s := by
        intro hps
        rcases (mem_starRaySet _ _ _ _).mp (hsu hps) with h | ⟨h, _⟩
        · exact hpe h
        · exact h rfl
      refine ⟨p, hp, hps, «Σ».downward u' hu' _ ?_⟩
      apply Finset.union_subset
      · intro v hv
        rcases (mem_starRaySet _ _ _ _).mp (hsu (Finset.mem_of_mem_erase hv)) with
          hve | ⟨_, hvu⟩
        · exact ((Finset.mem_erase.mp hv).1 hve).elim
        · exact hvu
      · exact htu'
  · rintro ⟨p, hp, hps, hparent⟩
    let u := s.erase e ∪ t
    have htu : t ⊆ u := Finset.subset_union_right
    have hnew := «Σ».starRaySet_mem_starSubdivision t ht hne hparent htu hp
    apply («Σ».starSubdivision t ht hne).downward _ hnew s
    intro v hv
    apply (mem_starRaySet _ _ _ _).mpr
    by_cases hve : v = e
    · exact Or.inl hve
    · refine Or.inr ⟨fun hvp => hps (hvp ▸ hv), ?_⟩
      exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hve, hv⟩)

/-- The exceptional ray belongs to the constructed fan. -/
theorem sum_mem_starSubdivision_rays :
    (∑ v ∈ t, v) ∈ («Σ».starSubdivision t ht hne).rays := by
  let p := hne.choose
  have hp : p ∈ t := hne.choose_spec
  apply ((«Σ».starSubdivision t ht hne).mem_rays_iff _).mpr
  exact ⟨starRaySet t t p,
    «Σ».starRaySet_mem_starSubdivision t ht hne ht (Finset.Subset.refl t) hp,
    (mem_starRaySet _ _ _ _).mpr (Or.inl rfl)⟩

/-- Every old ray remains a ray after a nontrivial smooth star subdivision. -/
theorem old_ray_mem_starSubdivision_rays (hcard : 2 ≤ t.card)
    {v : Lattice n} (hv : v ∈ «Σ».rays) :
    v ∈ («Σ».starSubdivision t ht hne).rays := by
  have hnot : ¬ t ⊆ {v} := by
    intro h
    have hle := Finset.card_le_card h
    simp only [Finset.card_singleton] at hle
    omega
  have hsingle := «Σ».mem_starSubdivision_of_unchanged t ht hne
    («Σ».singleton_mem_of_mem_rays hv) hnot
  exact ((«Σ».starSubdivision t ht hne).mem_rays_iff v).mpr
    ⟨{v}, hsingle, Finset.mem_singleton_self v⟩

/-- The ray set is exactly the old ray set with the single genuine sum ray
adjoined. -/
theorem starSubdivision_rays_eq (hcard : 2 ≤ t.card) :
    («Σ».starSubdivision t ht hne).rays = insert (∑ v ∈ t, v) «Σ».rays := by
  apply Finset.Subset.antisymm («Σ».starSubdivision_rays_subset t ht hne)
  intro v hv
  rcases Finset.mem_insert.mp hv with rfl | hv
  · exact «Σ».sum_mem_starSubdivision_rays t ht hne
  · exact «Σ».old_ray_mem_starSubdivision_rays t ht hne hcard hv

/-- The old focus is a primitive collection of the new fan. -/
theorem focus_isPrimitiveCollection_starSubdivision (hcard : 2 ≤ t.card) :
    («Σ».starSubdivision t ht hne).IsPrimitiveCollection t := by
  have het : (∑ v ∈ t, v) ∉ t := by
    intro he
    exact «Σ».sum_rays_not_mem_rays ht hcard («Σ».ray_mem_of_mem_cone ht he)
  have hnot : t ∉ («Σ».starSubdivision t ht hne).cones := by
    intro h
    exact ((«Σ».mem_starSubdivision_without_sum_iff t ht hne het).mp h).2
      (Finset.Subset.refl t)
  refine ⟨?_, hnot, ?_⟩
  · intro v hv
    exact «Σ».old_ray_mem_starSubdivision_rays t ht hne hcard
      («Σ».ray_mem_of_mem_cone ht hv)
  · intro s hst
    have hnot : ¬ t ⊆ s := by
      intro hts
      exact (Finset.ssubset_iff_subset_ne.mp hst).2
        (Finset.Subset.antisymm hst.subset hts)
    exact «Σ».mem_starSubdivision_of_unchanged t ht hne
      («Σ».downward t ht s hst.subset) hnot

/-- The exceptional primitive relation is the actual vector identity
`Σ focus rays = new sum ray`. -/
def exceptionalPrimitiveRelation (hcard : 2 ≤ t.card) :
    («Σ».starSubdivision t ht hne).PrimitiveRelation where
  positive := t
  negative := {∑ v ∈ t, v}
  coefficient := fun _ => 1
  primitive := «Σ».focus_isPrimitiveCollection_starSubdivision t ht hne hcard
  negative_cone := («Σ».starSubdivision t ht hne).singleton_mem_of_mem_rays
    («Σ».sum_mem_starSubdivision_rays t ht hne)
  coefficient_pos := by simp
  equation := by simp

theorem exceptionalPrimitiveRelation_degree (hcard : 2 ≤ t.card)
    (a : Lattice n → ℝ) :
    («Σ».exceptionalPrimitiveRelation t ht hne hcard).degree a =
      (∑ v ∈ t, a v) - a (∑ v ∈ t, v) := by
  simp [PrimitiveRelation.degree, exceptionalPrimitiveRelation]

/-- The exceptional primitive relation satisfies the full contraction
replacement condition, derived from the exact new-cone membership rule. -/
theorem exceptionalPrimitiveRelation_contractible (hcard : 2 ≤ t.card) :
    («Σ».exceptionalPrimitiveRelation t ht hne hcard).IsCombinatoriallyContractible := by
  let e := ∑ v ∈ t, v
  change ∀ ν ∈ («Σ».starSubdivision t ht hne).cones,
    Disjoint ν (t ∪ {e}) → {e} ∪ ν ∈ («Σ».starSubdivision t ht hne).cones →
      ∀ x ∈ t, t.erase x ∪ {e} ∪ ν ∈ («Σ».starSubdivision t ht hne).cones
  intro ν hν hdisj hcone x hx
  have heν : e ∉ ν := by
    intro he
    exact Finset.disjoint_left.mp hdisj he (Finset.mem_union_right _ (Finset.mem_singleton_self e))
  have hxν : x ∉ ν := by
    intro hxn
    exact Finset.disjoint_left.mp hdisj hxn (Finset.mem_union_left _ hx)
  have hxe : x ≠ e := by
    intro h
    have hxold := «Σ».ray_mem_of_mem_cone ht hx
    rw [h] at hxold
    exact «Σ».sum_rays_not_mem_rays ht hcard hxold
  have hecone : e ∈ {e} ∪ ν := Finset.mem_union_left _ (Finset.mem_singleton_self e)
  obtain ⟨p, hp, hpn, hparent⟩ :=
    («Σ».mem_starSubdivision_with_sum_iff t ht hne hcard hecone).mp hcone
  have hparentEq : ({e} ∪ ν).erase e ∪ t = ν ∪ t := by
    ext z
    by_cases hze : z = e
    · subst z
      simp [heν]
    · simp [Finset.mem_erase, hze]
  rw [hparentEq] at hparent
  have hsume : e ∈ t.erase x ∪ {e} ∪ ν :=
    Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self e))
  apply («Σ».mem_starSubdivision_with_sum_iff t ht hne hcard hsume).mpr
  refine ⟨x, hx, ?_, ?_⟩
  · simp [hxν, hxe]
  · have hsets : (t.erase x ∪ {e} ∪ ν).erase e ∪ t = ν ∪ t := by
      ext z
      by_cases hze : z = e
      · subst z
        simp [heν]
      · simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
        tauto
    change (t.erase x ∪ {e} ∪ ν).erase e ∪ t ∈ «Σ».cones
    rw [hsets]
    exact hparent

/-- Any other primitive collection avoiding the exceptional ray is a
primitive collection of the original fan. This is the old-positive part
of the primitive-collection transformation theorem. -/
theorem primitiveCollection_pushdown_without_sum (hcard : 2 ≤ t.card)
    {P : Finset (Lattice n)}
    (hP : («Σ».starSubdivision t ht hne).IsPrimitiveCollection P)
    (heP : (∑ v ∈ t, v) ∉ P) (hPt : P ≠ t) :
    «Σ».IsPrimitiveCollection P := by
  have htnew : t ∉ («Σ».starSubdivision t ht hne).cones :=
    («Σ».focus_isPrimitiveCollection_starSubdivision t ht hne hcard).2.1
  have hPold : P ∉ «Σ».cones := by
    intro hPold
    have htP : t ⊆ P := by
      by_contra hnot
      exact hP.2.1 («Σ».mem_starSubdivision_of_unchanged t ht hne hPold hnot)
    have hproper : t ⊂ P := Finset.ssubset_iff_subset_ne.mpr ⟨htP, Ne.symm hPt⟩
    exact htnew (hP.2.2 t hproper)
  refine ⟨?_, hPold, ?_⟩
  · intro v hv
    have h := «Σ».starSubdivision_rays_subset t ht hne (hP.1 hv)
    rcases Finset.mem_insert.mp h with hve | hvr
    · exact (heP (hve ▸ hv)).elim
    · exact hvr
  · intro s hs
    have hes : (∑ v ∈ t, v) ∉ s := fun h => heP (hs.subset h)
    exact ((«Σ».mem_starSubdivision_without_sum_iff t ht hne hes).mp (hP.2.2 s hs)).1

end SmoothCompleteFan

end PaperVerification.ToricGeometry
