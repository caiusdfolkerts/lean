module

public import Unimodular.VectorMatroid
public import Unimodular.SeriesParallelRealization

@[expose] public section

noncomputable section

open Set
open scoped Matroid

namespace Unimodular.SeriesParallel.MinorWitness

variable {m d n : ℕ} {fan : SmoothCompleteFan n} {U : Fin m → Lattice d}
  (h : MinorWitness fan U)

/-- A geometric minor witness gives an equality with Mathlib's ordinary
contraction and deletion, after the explicitly recorded injective relabeling.
The contracted set may be dependent and the real projection need not be onto. -/
theorem matroid_map_eq_minor :
    (VectorMatroid.ofFamily (K := ℝ) (fun j => embed (U j))).mapEmbedding h.chosen =
      (VectorMatroid.onSet (K := ℝ) (embed : Lattice n → Ambient n) fan.rays) ／
        (h.contracted : Set (Lattice n)) ＼
        ((fan.rays \ (h.contracted : Set (Lattice n))) \ Set.range h.chosen) := by
  have hC : (h.contracted : Set (Lattice n)) ⊆ fan.rays := h.contracted_rays
  have hR : Set.range h.chosen ⊆ fan.rays \ (h.contracted : Set (Lattice n)) := by
    rintro u ⟨j, rfl⟩
    exact ⟨h.chosen_rays j, h.disjoint j⟩
  exact VectorMatroid.mapEmbedding_eq_minor (embed : Lattice n → Ambient n)
    (fun j => embed (U j)) hC h.chosen hR h.projection h.kernel h.image

/-- The represented target is, with its labels embedded into the original ray
ground set, a genuine standard matroid minor of the fan ray matroid. -/
theorem matroid_isMinor :
    (VectorMatroid.ofFamily (K := ℝ) (fun j => embed (U j))).mapEmbedding h.chosen ≤m
      VectorMatroid.onSet (K := ℝ) (embed : Lattice n → Ambient n) fan.rays :=
  ⟨(h.contracted : Set (Lattice n)),
    (fan.rays \ (h.contracted : Set (Lattice n))) \ Set.range h.chosen,
    h.matroid_map_eq_minor⟩

end Unimodular.SeriesParallel.MinorWitness

namespace Unimodular.SeriesParallel

/-- The constructive program realization, now with its exact standard matroid
minor conclusion. The counts concern distinct primitive rays and actual real cones. -/
theorem program_fan_matroid_realization {m : ℕ} (P : SPProgram m) :
    ∃ (σ : SmoothCompleteFan m) (f : Fin m ↪ Lattice m),
      σ.PositiveCoordinateCriterion ∧
      (VectorMatroid.ofFamily (K := ℝ) (fun j => embed (P.columns j))).mapEmbedding f ≤m
        VectorMatroid.onSet (K := ℝ) (embed : Lattice m → Ambient m) σ.rays ∧
      σ.rays.ncard = 2 * m ∧ (σ.maximal.image basisCone).card = 2 ^ m := by
  obtain ⟨σ, hσ, ⟨h⟩, hrays, hcones⟩ := program_fan_realization P
  exact ⟨σ, h.chosen, hσ, h.matroid_isMinor, hrays, hcones⟩


/-- The complete geometric program realization: the target is an ordinary matroid
minor of the actual primitive facet-normal matroid of a deeply monotone smooth
reflexive polytope whose full face poset is isomorphic to that of the standard cube. -/
theorem program_cubical_polytope_matroid_realization {m : ℕ} (P : SPProgram m) :
    ∃ (σ : SmoothCompleteFan m) (Q : SmoothReflexivePresentation m)
      (f : Fin m ↪ Lattice m),
      σ.PositiveCoordinateCriterion ∧ Q.DeeplyMonotone ∧ Q.IsCombinatorialCube ∧
      (Q.normals : Set (Lattice m)) = σ.rays ∧
      (VectorMatroid.ofFamily (K := ℝ) (fun j => embed (P.columns j))).mapEmbedding f ≤m
        VectorMatroid.onSet (K := ℝ) (embed : Lattice m → Ambient m)
          (Q.normals : Set (Lattice m)) ∧
      σ.rays.ncard = 2 * m ∧ (σ.maximal.image basisCone).card = 2 ^ m := by
  obtain ⟨σ, Q, hσ, hQ, hcube, hnormals, ⟨h⟩, hrays, hcones⟩ :=
    program_cubical_polytope_realization P
  refine ⟨σ, Q, h.chosen, hσ, hQ, hcube, hnormals, ?_, hrays, hcones⟩
  rw [hnormals]
  exact h.matroid_isMinor

end Unimodular.SeriesParallel

end
