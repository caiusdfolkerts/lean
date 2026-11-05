module

public import PaperVerification.ToricStarSubdivision

@[expose] public section

/-!
# Full cone extensions survive star subdivision

Purity is derived from the original fan's full-cone extensions and the
explicit ray-set replacement. No general purity theorem is assumed.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

theorem starRaySet_mono {n : ℕ} {s u : Finset (Lattice n)}
    (hsu : s ⊆ u) (t : Finset (Lattice n)) (p : Lattice n) :
    starRaySet s t p ⊆ starRaySet u t p := by
  intro v hv
  apply (mem_starRaySet _ _ _ _).mpr
  rcases (mem_starRaySet _ _ _ _).mp hv with hsum | ⟨hvp, hvs⟩
  · exact Or.inl hsum
  · exact Or.inr ⟨hvp, hsu hvs⟩

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem starRaySet_card {s t : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (hts : t ⊆ s) {p : Lattice n} (hp : p ∈ t) :
    (starRaySet s t p).card = s.card := by
  obtain ⟨b, I, J, hsI, htJ, hJI⟩ := «Σ».adapted_basis_for_subcone hs hts
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (htJ ▸ hp)
  rw [hsI, htJ, lattice_starRaySet_basis b I J hJI j hj,
    Finset.card_image_of_injective I (starRayBasis b J j).injective,
    Finset.card_image_of_injective I b.injective]

/-- Every cone of the actual subdivided fan extends to a full cone whenever
that property holds for the original fan. -/
theorem isPure_starSubdivision (hpure : «Σ».IsPure)
    (t : Finset (Lattice n)) (ht : t ∈ «Σ».cones) (hne : t.Nonempty) :
    («Σ».starSubdivision t ht hne).IsPure := by
  intro c hc
  obtain ⟨u, hu, hcu⟩ := (mem_finiteConeFamilyClosure («Σ».starCandidates t) c).mp hc
  rcases («Σ».mem_starCandidates t u).mp hu with ⟨hu, htu⟩ |
    ⟨u', hu', p, hp, htu', rfl⟩
  · obtain ⟨s, hs, hus, hscard⟩ := hpure u hu
    by_cases hts : t ⊆ s
    · obtain ⟨p, hp, hpu⟩ := Finset.not_subset.mp htu
      refine ⟨starRaySet s t p,
        «Σ».starRaySet_mem_starSubdivision t ht hne hs hts hp, ?_, ?_⟩
      · intro v hv
        exact (mem_starRaySet _ _ _ _).mpr (Or.inr
          ⟨fun hvp => hpu (hvp ▸ hcu hv), hus (hcu hv)⟩)
      · rw [«Σ».starRaySet_card hs hts hp, hscard]
    · exact ⟨s, «Σ».mem_starSubdivision_of_unchanged t ht hne hs hts, hcu.trans hus, hscard⟩
  · obtain ⟨s, hs, hus, hscard⟩ := hpure u' hu'
    have hts := htu'.trans hus
    exact ⟨starRaySet s t p,
      «Σ».starRaySet_mem_starSubdivision t ht hne hs hts hp,
      hcu.trans (starRaySet_mono hus t p),
      («Σ».starRaySet_card hs hts hp).trans hscard⟩

end SmoothCompleteFan

end PaperVerification.ToricGeometry
