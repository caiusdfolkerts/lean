module

public import Unimodular.SeriesParallelMatroidSemantics
public import Unimodular.SeriesParallelMatroidMinor

@[expose] public section

open scoped Matroid

namespace Unimodular.SeriesParallel

/-- The constructive direction of Proposition 6.7, with the target an actual
Mathlib matroid, an actual standard matroid minor, and exact geometric ray/cone
counts. The chosen ambient dimension is `m`, hence satisfies the paper's bound.
The separate polytope construction identifies its anticanonical polytope. -/
theorem seriesParallel_fan_matroid_realization {m : ℕ} (M : Matroid (Fin m))
    (hM : IsSeriesParallelMatroid M) :
    ∃ (σ : SmoothCompleteFan m) (f : Fin m ↪ Lattice m),
      σ.PositiveCoordinateCriterion ∧
      M.mapEmbedding f ≤m
        VectorMatroid.onSet (K := ℝ) (embed : Lattice m → Ambient m) σ.rays ∧
      σ.rays.ncard = 2 * m ∧ (σ.maximal.image basisCone).card = 2 ^ m := by
  obtain ⟨P, _, rfl⟩ := (isSeriesParallelMatroid_iff_program M).mp hM
  exact program_fan_matroid_realization P

/-- The full geometric realization in Proposition 6.7: a series--parallel
matroid on `m` labeled elements occurs as an ordinary minor of the primitive
facet-normal matroid of a deeply monotone smooth reflexive polytope. The full
face poset is that of the `m`-cube, and the fan has exactly `2m` rays and `2^m`
maximal cones. -/
theorem seriesParallel_cubical_polytope_matroid_realization {m : ℕ}
    (M : Matroid (Fin m)) (hM : IsSeriesParallelMatroid M) :
    ∃ (σ : SmoothCompleteFan m) (Q : SmoothReflexivePresentation m)
      (f : Fin m ↪ Lattice m),
      σ.PositiveCoordinateCriterion ∧ Q.DeeplyMonotone ∧ Q.IsCombinatorialCube ∧
      (Q.normals : Set (Lattice m)) = σ.rays ∧
      M.mapEmbedding f ≤m
        VectorMatroid.onSet (K := ℝ) (embed : Lattice m → Ambient m)
          (Q.normals : Set (Lattice m)) ∧
      σ.rays.ncard = 2 * m ∧ (σ.maximal.image basisCone).card = 2 ^ m := by
  obtain ⟨P, _, rfl⟩ := (isSeriesParallelMatroid_iff_program M).mp hM
  exact program_cubical_polytope_matroid_realization P

#print axioms Unimodular.SeriesParallel.seriesParallel_fan_matroid_realization
#print axioms Unimodular.SeriesParallel.seriesParallel_cubical_polytope_matroid_realization

end Unimodular.SeriesParallel
