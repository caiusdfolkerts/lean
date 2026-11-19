module

public import Unimodular.SeriesParallelPrincipal
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

/-!
# The exact minor class with arbitrary element labels

The main geometric classification is independent of an enumeration by `Fin m`.
The full-ground theorem below retains the given label type, and the ground-set
theorem retains precisely the actual elements of an arbitrary Mathlib matroid.
No finiteness assumption on an ambient type containing unused labels is imposed.
-/

open Set
open scoped Matroid

namespace Unimodular.SeriesParallel

noncomputable section

/-- The exact minor-class statement of Theorem 1.2 for any full-ground matroid.
The finite construction supplies an enumeration in the forward direction; in
the reverse direction finiteness follows from the actual minor. Thus no
`Fintype` hypothesis or fixed labeling is needed. Empty targets still have a
positive-dimensional deeply monotone realization. -/
theorem finiteSeriesParallel_iff_normalMatroid_minor {E : Type*}
    (M : Matroid E) (hE : M.E = Set.univ) :
    FiniteSeriesParallel M ↔
      ∃ (n : ℕ), 0 < n ∧ ∃ (P : SmoothReflexivePresentation n) (f : E ↪ Lattice n),
        P.DeeplyMonotone ∧ M.mapEmbedding f ≤m
          VectorMatroid.onSet (K := ℝ) (embed : Lattice n → Ambient n)
            (P.normals : Set (Lattice n)) := by
  constructor
  · rintro ⟨m, e, hM⟩
    obtain ⟨n, hn, P, f, hP, hminor⟩ :=
      (seriesParallel_iff_normalMatroid_minor (M.mapEquiv e.symm)
        hM.ground_eq_univ).mp hM
    refine ⟨n, hn, P, e.symm.toEmbedding.trans f, hP, ?_⟩
    simpa only [Matroid.mapEquiv, EmbeddingTransport.map_comp] using hminor
  · rintro ⟨n, hn, P, f, hP, hminor⟩
    exact (GroundSeriesParallel.of_mapEmbedding f
      (deeplyMonotone_normalMatroid_all_minors_seriesParallel P hP hminor)).finite hE

/-- The classification for an arbitrary matroid on its actual ground set.
Loops and every other ground element are retained; only unused ambient labels
are removed by `restrictSubtype M.E`. Its equality with the original matroid
after the subtype inclusion is already proved in `GroundNormalization`.
This statement includes every finite matroid, regardless of its ambient type. -/
theorem groundSeriesParallel_iff_normalMatroid_minor {E : Type*}
    (M : Matroid E) :
    GroundSeriesParallel M ↔
      ∃ (n : ℕ), 0 < n ∧
        ∃ (P : SmoothReflexivePresentation n) (f : M.E ↪ Lattice n),
          P.DeeplyMonotone ∧ (M.restrictSubtype M.E).mapEmbedding f ≤m
            VectorMatroid.onSet (K := ℝ) (embed : Lattice n → Ambient n)
              (P.normals : Set (Lattice n)) := by
  rw [groundSeriesParallel_iff_finite_onGround]
  exact finiteSeriesParallel_iff_normalMatroid_minor (M.restrictSubtype M.E) (by simp)

/-- Proposition 6.7 with an arbitrary finite type of original element labels.
The ambient dimension is exactly the number of those elements, the minor is an
ordinary Mathlib minor after an explicit embedding of the original labels, and
the cube conclusion concerns the entire geometric face poset. -/
theorem finiteSeriesParallel_cubical_realization {E : Type*} [Fintype E]
    (M : Matroid E) (hM : FiniteSeriesParallel M) :
    ∃ (σ : SmoothCompleteFan (Fintype.card E))
      (Q : SmoothReflexivePresentation (Fintype.card E))
      (f : E ↪ Lattice (Fintype.card E)),
      σ.PositiveCoordinateCriterion ∧ Q.DeeplyMonotone ∧ Q.IsCombinatorialCube ∧
      (Q.normals : Set (Lattice (Fintype.card E))) = σ.rays ∧
      M.mapEmbedding f ≤m
        VectorMatroid.onSet (K := ℝ)
          (embed : Lattice (Fintype.card E) → Ambient (Fintype.card E))
          (Q.normals : Set _) ∧
      σ.rays.ncard = 2 * Fintype.card E ∧
      (σ.maximal.image basisCone).card = 2 ^ Fintype.card E ∧
      Q.normals.card = 2 * Fintype.card E ∧ Q.vertices.card = 2 ^ Fintype.card E := by
  classical
  let e := Fintype.equivFin E
  have hFin : HasSeriesParallelConstruction (M.mapEquiv e) :=
    (FiniteSeriesParallel.fin_iff _).mp (hM.relabel e)
  obtain ⟨σ, Q, f, hσ, hQ, hcube, hnorm, hminor, hrays, hcones, hfacets, hvertices⟩ :=
    abstract_seriesParallel_cubical_realization (M.mapEquiv e) hFin
  refine ⟨σ, Q, e.toEmbedding.trans f, hσ, hQ, hcube, hnorm, ?_,
    hrays, hcones, hfacets, hvertices⟩
  simpa only [Matroid.mapEquiv, EmbeddingTransport.map_comp] using hminor

/-- The constructive dimension/count statement on the exact finite ground of
an arbitrary matroid. Finiteness is derived from the standard series--parallel
construction, so no assumption on unused ambient labels is introduced. For a
nonempty ground the displayed dimension is positive and satisfies the paper's
bound with equality. -/
theorem groundSeriesParallel_cubical_realization {E : Type*}
    (M : Matroid E) (hM : GroundSeriesParallel M) :
    ∃ (σ : SmoothCompleteFan (Nat.card M.E))
      (Q : SmoothReflexivePresentation (Nat.card M.E))
      (f : M.E ↪ Lattice (Nat.card M.E)),
      σ.PositiveCoordinateCriterion ∧ Q.DeeplyMonotone ∧ Q.IsCombinatorialCube ∧
      (Q.normals : Set (Lattice (Nat.card M.E))) = σ.rays ∧
      (M.restrictSubtype M.E).mapEmbedding f ≤m
        VectorMatroid.onSet (K := ℝ)
          (embed : Lattice (Nat.card M.E) → Ambient (Nat.card M.E))
          (Q.normals : Set _) ∧
      σ.rays.ncard = 2 * Nat.card M.E ∧
      (σ.maximal.image basisCone).card = 2 ^ Nat.card M.E ∧
      Q.normals.card = 2 * Nat.card M.E ∧ Q.vertices.card = 2 ^ Nat.card M.E := by
  classical
  letI : Fintype M.E := hM.ground_finite.fintype
  rw [Nat.card_eq_fintype_card]
  exact finiteSeriesParallel_cubical_realization (M.restrictSubtype M.E) hM.finite_onGround

#print axioms Unimodular.SeriesParallel.finiteSeriesParallel_iff_normalMatroid_minor
#print axioms Unimodular.SeriesParallel.groundSeriesParallel_iff_normalMatroid_minor
#print axioms Unimodular.SeriesParallel.finiteSeriesParallel_cubical_realization
#print axioms Unimodular.SeriesParallel.groundSeriesParallel_cubical_realization

end
end Unimodular.SeriesParallel
