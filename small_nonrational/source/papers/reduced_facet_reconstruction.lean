module
public import Papers.SelectedSupportCoordinateLift
public import Papers.TwoSupportNormals
public import Papers.ZeroColumnRestoration

@[expose] public section
noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.FixedCoordinateFlagDensity

open ChirotopeDensity PlaneRationalization

/-- A reduced relation matrix reconstructs the full labelled polytope when
at most two omitted facets have their outside-column ranks retained. All
other facets still have their complete relation spaces among the supported
rows. The conclusion is the ordinary rational realization density, with
no extra incidence or general-position hypothesis. -/
theorem rational_polytope_density_from_reduced_relations {c n d k : ℕ}
    (C : Matrix (Fin c) (Fin n) ℝ) (p : Fin n → Fin (d + 1) → ℝ)
    (hp : Spans p) (hfirst : ∀ i, p i 0 = 1) (hCp : C * Matrix.of p = 0)
    (hk : k ≤ 2) (H : Fin k → Finset (Fin n)) (hH : Function.Injective H)
    (hfacet : ∀ b, FacetMask p (H b))
    (hrelations : ∀ S, FacetMask p S → (∀ b, H b ≠ S) → SpansFacetRelations C p S)
    (hC : C ∈ closure {D : Matrix (Fin c) (Fin n) ℝ |
      RationalCoordinates D ∧ D.rank = C.rank ∧ PreservesZeroEntries C D ∧
      ∀ b, subsetRank C.col (H b)ᶜ = subsetRank D.col (H b)ᶜ}) :
    p ∈ closure {q : Fin n → Fin (d + 1) → ℝ |
      RationalCoordinates q ∧ (∀ i, q i 0 = 1) ∧ Spans q ∧
      LabelledPolytopeEquivalent p q} := by
  classical
  choose a ha using (fun b => (hfacet b).2.1)
  have hLI : LinearIndependent ℝ a :=
    at_most_two_strictSupport_normals_independent p hk H hH a ha
      (fun b => (hfacet b).ne_univ hp)
  have hcl := rational_selected_support_coordinate_lift C (Matrix.of p) hCp H a hLI
    (fun b => (ha b).1) hC
  let L : Finset (Finset (Fin n)) := (facetMasks p).filter (fun S => ∀ b, H b ≠ S)
  have hL (S : Finset (Fin n)) (hS : S ∈ L) : FacetMask p S :=
    (mem_facetMasks p S).mp (Finset.mem_filter.mp hS).1
  have hselection : ∀ S ∈ L, Nonempty (FacetRelationSelection C p S) := by
    intro S hS
    apply facetRelationSelection_of_spanning C p S
    exact hrelations S (hL S hS) (Finset.mem_filter.mp hS).2
  have hgeom := selected_facet_ranks_and_supports_stable C p L hselection
    (fun S hS => (hL S hS).2.1)
  have hnonzero : ∀ᶠ z : Matrix (Fin c) (Fin n) ℝ × (Fin n → Fin (d + 1) → ℝ)
      in 𝓝 (C, p), ∀ i, z.2 i 0 ≠ 0 := by
    apply eventually_all.mpr
    intro i
    have hq : Continuous (fun q : Fin n → Fin (d + 1) → ℝ => q i 0) :=
      (continuous_apply 0).comp (continuous_apply i)
    have ht : Continuous (fun z : Matrix (Fin c) (Fin n) ℝ ×
        (Fin n → Fin (d + 1) → ℝ) => z.2 i 0) := by
      simpa only [Function.comp_def] using hq.comp continuous_snd
    exact (ht.continuousAt (x := (C, p))).eventually_ne (by
      change p i 0 ≠ 0
      rw [hfirst i]
      exact one_ne_zero)
  have hlower : ∀ᶠ z : Matrix (Fin c) (Fin n) ℝ × (Fin n → Fin (d + 1) → ℝ)
      in 𝓝 (C, p), ∀ S : Finset (Fin n), subsetRank p S ≤ subsetRank z.2 S := by
    apply eventually_all.mpr
    intro S
    exact (continuous_snd.continuousAt (x := (C, p))).tendsto.eventually
      (eventually_subsetRank_ge p S)
  let F : Matrix (Fin c) (Fin n) ℝ × (Fin n → Fin (d + 1) → ℝ) →
      (Fin n → Fin (d + 1) → ℝ) := fun z => normalizePointRows z.2
  have hF : ContinuousAt F (C, p) :=
    (normalizePointRows_continuousAt p (fun i => by rw [hfirst i]; exact one_ne_zero)).comp_of_eq
      continuous_snd.continuousAt rfl
  have hbase : F (C, p) = p := normalizePointRows_self p hfirst
  have hc := mem_closure_image hF
    (mem_closure_inter_of_eventually hcl (hgeom.and (hnonzero.and hlower)))
  rw [hbase] at hc
  apply rational_polytope_density_from_facet_rank_density p hp hfirst
  apply closure_mono (s := F '' _) ?_ hc
  rintro _ ⟨⟨D, q⟩, ⟨hz, hg, hn, hl⟩, rfl⟩
  have hgeom' := hg hz.2.2.2.1 hz.2.2.2.2.1
  refine ⟨normalizePointRows_rational hz.2.1, ?_, ?_⟩
  · intro i
    exact div_self (hn i)
  · intro S hS
    rw [subsetRank_normalizePointRows_eq q S hn]
    by_cases he : ∃ b, H b = S
    · obtain ⟨b, rfl⟩ := he
      obtain ⟨v, hv, _, hzv⟩ := hz.2.2.2.2.2 b
      have hu := subsetRank_add_one_le_of_annihilator q (H b) v hv hzv
      have hpH := (hfacet b).2.2
      have hlo : subsetRank p (H b) ≤ subsetRank q (H b) := hl (H b)
      omega
    · apply hgeom'.1 S
      refine Finset.mem_filter.mpr ⟨hS, ?_⟩
      intro b hb
      exact he ⟨b, hb⟩

#print axioms rational_polytope_density_from_reduced_relations

end Papers.RationalityTen.FixedCoordinateFlagDensity
