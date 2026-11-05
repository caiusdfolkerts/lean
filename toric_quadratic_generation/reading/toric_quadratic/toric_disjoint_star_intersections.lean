module

public import PaperVerification.ToricStarFanFaces

@[expose] public section

/-!
# Intersections of star charts over disjoint centers

Each exceptional sum ray is absent from the other old parent cone. Hence
both new charts restrict to ordinary faces of the old common face, and their
intersection is exactly their common-ray cone.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem star_cones_inter_disjoint_foci
    {U V T A : Finset (Lattice n)}
    (hU : U ∈ «Σ».cones) (hV : V ∈ «Σ».cones)
    (hT : T ∈ «Σ».cones) (hA : A ∈ «Σ».cones)
    (hTU : T ⊆ U) (hAV : A ⊆ V)
    (hTV : ¬ T ⊆ V) (hAU : ¬ A ⊆ U) (p q : Lattice n) :
    latticeRayCone (starRaySet U T p) ⊓ latticeRayCone (starRaySet V A q) =
      latticeRayCone (starRaySet U T p ∩ starRaySet V A q) := by
  let C := starRaySet U T p
  let D := starRaySet V A q
  have hC := latticeRayCone_starRaySet_le hTU p
  have hD := latticeRayCone_starRaySet_le hAV q
  have heD : (∑ v ∈ T, v) ∉ D := by
    intro he
    have hh := hD (latticeRayCone_generator D he)
    exact hTV ((«Σ».sum_rays_mem_cone_iff hT hV).mp hh)
  have heC : (∑ v ∈ A, v) ∉ C := by
    intro he
    have hh := hC (latticeRayCone_generator C he)
    exact hAU ((«Σ».sum_rays_mem_cone_iff hA hU).mp hh)
  have hCV : C ∩ V ∈ «Σ».cones := «Σ».downward V hV _ Finset.inter_subset_right
  have hDU : D ∩ U ∈ «Σ».cones := «Σ».downward U hU _ Finset.inter_subset_right
  have hmeet : latticeRayCone C ⊓ latticeRayCone D =
      (latticeRayCone C ⊓ latticeRayCone V) ⊓
        (latticeRayCone D ⊓ latticeRayCone U) := by
    ext x
    exact ⟨fun h => ⟨⟨h.1, hD h.2⟩, ⟨h.2, hC h.1⟩⟩,
      fun h => ⟨h.1.1, h.2.1⟩⟩
  rw [hmeet, «Σ».star_cone_inter_unchanged hU hT hV hTU hTV p,
    «Σ».star_cone_inter_unchanged hV hA hU hAV hAU q,
    «Σ».intersection (C ∩ V) hCV (D ∩ U) hDU]
  congr 1
  ext z
  constructor
  · intro hz
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hz).1).1,
        (Finset.mem_inter.mp (Finset.mem_inter.mp hz).2).1⟩
  · intro hz
    obtain ⟨hzC, hzD⟩ := Finset.mem_inter.mp hz
    have hzU : z ∈ U := by
      rcases (mem_starRaySet U T p z).mp hzC with hze | ⟨_, hzU⟩
      · exact (heD (hze ▸ hzD)).elim
      · exact hzU
    have hzV : z ∈ V := by
      rcases (mem_starRaySet V A q z).mp hzD with hze | ⟨_, hzV⟩
      · exact (heC (hze ▸ hzC)).elim
      · exact hzV
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_inter.mpr ⟨hzC, hzV⟩, Finset.mem_inter.mpr ⟨hzD, hzU⟩⟩

end SmoothCompleteFan

end PaperVerification.ToricGeometry
