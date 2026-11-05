module
public import PaperVerification.ToricStarFanFaces
public import PaperVerification.ToricFiniteConeFamily
@[expose] public section
/-!
# Smooth star subdivision of an actual complete fan

The subdivision is constructed from actual finite ray sets and their actual
nonnegative spans. Smoothness follows from an integral transvection,
completeness from the minimum-coefficient covering, and the fan intersection
condition from the proved old-face restrictions and local chart calculation.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- The generating cones of the star subdivision: retain cones not containing
the focus and subdivide each remaining cone at every focus ray. -/
def starCandidates (t : Finset (Lattice n)) : Finset (Finset (Lattice n)) :=
  «Σ».cones.biUnion (fun s => if t ⊆ s then t.image (starRaySet s t) else {s})

theorem mem_starCandidates (t s : Finset (Lattice n)) :
    s ∈ «Σ».starCandidates t ↔
      (s ∈ «Σ».cones ∧ ¬ t ⊆ s) ∨
      ∃ u ∈ «Σ».cones, ∃ v ∈ t, t ⊆ u ∧ s = starRaySet u t v := by
  constructor
  · intro hs
    obtain ⟨u, hu, hsu⟩ := Finset.mem_biUnion.mp hs
    by_cases htu : t ⊆ u
    · rw [if_pos htu] at hsu
      obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hsu
      exact Or.inr ⟨u, hu, v, hv, htu, he.symm⟩
    · rw [if_neg htu] at hsu
      have hsu := Finset.mem_singleton.mp hsu
      subst s
      exact Or.inl ⟨hu, htu⟩
  · rintro (⟨hs, hts⟩ | ⟨u, hu, v, hv, htu, rfl⟩)
    · apply Finset.mem_biUnion.mpr
      exact ⟨s, hs, by rw [if_neg hts]; exact Finset.mem_singleton_self s⟩
    · apply Finset.mem_biUnion.mpr
      refine ⟨u, hu, ?_⟩
      rw [if_pos htu]
      exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

theorem starCandidates_smooth (t : Finset (Lattice n)) :
    ∀ s ∈ «Σ».starCandidates t, ∃ b : Module.Basis (Fin n) ℤ (Lattice n),
      s ⊆ Finset.univ.image b := by
  intro s hs
  rcases («Σ».mem_starCandidates t s).mp hs with ⟨hs, hts⟩ |
    ⟨u, hu, v, hv, htu, rfl⟩
  · obtain ⟨b, I, rfl⟩ := «Σ».smooth s hs
    exact ⟨b, Finset.image_subset_image (Finset.subset_univ I)⟩
  · obtain ⟨b, I, he⟩ := «Σ».starRaySet_smooth hu htu hv
    refine ⟨b, ?_⟩
    rw [he]
    exact Finset.image_subset_image (Finset.subset_univ I)

theorem starCandidates_intersection (t : Finset (Lattice n)) (ht : t ∈ «Σ».cones) :
    ∀ s ∈ «Σ».starCandidates t, ∀ u ∈ «Σ».starCandidates t,
      latticeRayCone s ⊓ latticeRayCone u = latticeRayCone (s ∩ u) := by
  intro s hs u hu
  rcases («Σ».mem_starCandidates t s).mp hs with ⟨hs, hts⟩ |
    ⟨s', hs', v, hv, hts', rfl⟩
  · rcases («Σ».mem_starCandidates t u).mp hu with ⟨hu, htu⟩ |
      ⟨u', hu', w, hw, htu', rfl⟩
    · exact «Σ».intersection s hs u hu
    · rw [inf_comm, Finset.inter_comm]
      exact «Σ».star_cone_inter_unchanged hu' ht hs htu' hts w
  · rcases («Σ».mem_starCandidates t u).mp hu with ⟨hu, htu⟩ |
      ⟨u', hu', w, hw, htu', rfl⟩
    · exact «Σ».star_cone_inter_unchanged hs' ht hu hts' htu v
    · exact «Σ».star_cones_inter hs' ht hu' hts' htu' hv hw

theorem starCandidates_cover (t : Finset (Lattice n)) (ht : t.Nonempty) :
    ∀ x : Ambient n, ∃ s ∈ «Σ».starCandidates t, x ∈ latticeRayCone s := by
  intro x
  obtain ⟨s, hs, hx⟩ := «Σ».complete x
  by_cases hts : t ⊆ s
  · obtain ⟨v, hv, hxv⟩ := latticeRayCone_star_cover hts ht hx
    refine ⟨starRaySet s t v, ?_, hxv⟩
    exact («Σ».mem_starCandidates t _).mpr (Or.inr ⟨s, hs, v, hv, hts, rfl⟩)
  · exact ⟨s, («Σ».mem_starCandidates t s).mpr (Or.inl ⟨hs, hts⟩), hx⟩

/-- The smooth complete star-subdivided fan, with every defining geometric
property proved from the original fan and the nonempty focus cone. -/
def starSubdivision (t : Finset (Lattice n)) (ht : t ∈ «Σ».cones) (hne : t.Nonempty) :
    SmoothCompleteFan n :=
  fanOfFiniteSmoothCones («Σ».starCandidates t)
    («Σ».starCandidates_smooth t) («Σ».starCandidates_intersection t ht)
    («Σ».starCandidates_cover t hne)

/-- An unchanged old cone is literally a cone of the new fan. -/
theorem mem_starSubdivision_of_unchanged (t : Finset (Lattice n))
    (ht : t ∈ «Σ».cones) (hne : t.Nonempty) {s : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (hts : ¬ t ⊆ s) :
    s ∈ («Σ».starSubdivision t ht hne).cones := by
  apply (mem_finiteConeFamilyClosure («Σ».starCandidates t) s).mpr
  exact ⟨s, («Σ».mem_starCandidates t s).mpr (Or.inl ⟨hs, hts⟩), Finset.Subset.refl s⟩

/-- Every explicitly subdivided cone is literally a cone of the new fan. -/
theorem starRaySet_mem_starSubdivision (t : Finset (Lattice n))
    (ht : t ∈ «Σ».cones) (hne : t.Nonempty) {s : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (hts : t ⊆ s) {v : Lattice n} (hv : v ∈ t) :
    starRaySet s t v ∈ («Σ».starSubdivision t ht hne).cones := by
  apply (mem_finiteConeFamilyClosure («Σ».starCandidates t) _).mpr
  exact ⟨starRaySet s t v,
    («Σ».mem_starCandidates t _).mpr (Or.inr ⟨s, hs, v, hv, hts, rfl⟩),
    Finset.Subset.refl _⟩

end SmoothCompleteFan

end PaperVerification.ToricGeometry
