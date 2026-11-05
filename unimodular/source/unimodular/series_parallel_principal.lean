module

public import Unimodular.SeriesParallelGraphMinors

@[expose] public section

/-!
# Theorems 1.2 and 6.6 on the original geometric objects

The normal fan used here is constructed from the actual normal cones of the
polytope. Every primitive facet normal, with its original sign and integral
coordinates, remains an edge label throughout the statements below.
-/

open Set
open scoped Matroid

namespace Unimodular.SeriesParallel

noncomputable section

/-- The necessity assertion of Theorem 1.2 for the exact primitive facet-normal
matroid of the original deeply monotone smooth reflexive polytope. -/
theorem deeplyMonotone_normalMatroid_seriesParallel {n : ℕ}
    (P : SmoothReflexivePresentation n) (hP : P.DeeplyMonotone) :
    GroundSeriesParallel (VectorMatroid.onSet (K := ℝ)
      (embed : Lattice n → Ambient n) (P.normals : Set (Lattice n))) := by
  have h := fan_onSet_rayMatroid_seriesParallel P.normalFan P.normalFan_complete
    P.normalFan_regular (P.normalFan_positiveCriterion hP)
  have hr : {u : Lattice n | ConeBases.IsRay P.normalFan u} =
      (P.normals : Set (Lattice n)) := by
    ext u
    exact P.normalFan_ray_iff u
  change GroundSeriesParallel (VectorMatroid.onSet (K := ℝ)
    (embed : Lattice n → Ambient n) {u | ConeBases.IsRay P.normalFan u}) at h
  rwa [hr] at h

/-- Every ordinary deletion/contraction minor of the original normal
configuration is series--parallel, with its actual ground set retained. -/
theorem deeplyMonotone_normalMatroid_all_minors_seriesParallel {n : ℕ}
    (P : SmoothReflexivePresentation n) (hP : P.DeeplyMonotone)
    {M : Matroid (Lattice n)}
    (hM : M ≤m VectorMatroid.onSet (K := ℝ)
      (embed : Lattice n → Ambient n) (P.normals : Set (Lattice n))) :
    GroundSeriesParallel M := (deeplyMonotone_normalMatroid_seriesParallel P hP).minor hM

/-- The signed integral graphic refinement uses exactly an n-element integral
basis of the original n-dimensional lattice. The vertices are its n basis
vertices and one root; all original normals are retained as separate edge
labels, and the resulting actual graph excludes ordinary K4 graph minors. -/
theorem deeplyMonotone_integrally_graphic_no_K4 {n : ℕ}
    (P : SmoothReflexivePresentation n) (hP : P.DeeplyMonotone) :
    ∃ (b : Module.Basis (Fin n) ℤ (Lattice n))
      (s t : {u : Lattice n // u ∈ P.normals} → Option (Fin n)),
      (∀ u, u.val = basisVertex b (s u) - basisVertex b (t u)) ∧
        ¬(IncidenceGraph.ofIncidence s t).HasK4Minor := by
  classical
  let E := {u : Lattice n // u ∈ P.normals}
  letI : Fintype E := P.normals.finite_toSet.fintype
  obtain ⟨v, hv⟩ := P.vertices_nonempty
  let v' : {v // v ∈ P.vertices} := ⟨v, hv⟩
  let b := P.basis v'
  let labels : Fin n ↪ E :=
    { toFun := fun i => ⟨b i, P.basis_mem v' i⟩
      inj' := fun _ _ h => b.injective (congrArg Subtype.val h) }
  have hU : ∀ u : E, ConeBases.IsRay P.normalFan u.val :=
    fun u => (P.normalFan_ray_iff u.val).mpr u.property
  obtain ⟨c, hc⟩ := ray_family_integral_incidence P.normalFan P.normalFan_complete
    P.normalFan_regular (P.normalFan_positiveCriterion hP) b
      (fun u : E => u.val) hU labels (fun _ => rfl)
  choose s t hvec using hc
  refine ⟨c, s, t, hvec, ?_⟩
  apply IncidenceGraph.no_K4_minor_of_seriesParallel
  rw [IncidenceGraph.cycleMatroid_of_integral_incidence P.normalFan c
    (fun u : E => u.val) s t hvec]
  exact (ray_family_seriesParallel P.normalFan P.normalFan_complete
    P.normalFan_regular (P.normalFan_positiveCriterion hP) b
      (fun u : E => u.val) hU labels (fun _ => rfl)).groundConstruction

/-- The exact minor-class statement of Theorem 1.2. Both directions concern
ordinary Mathlib matroids and ordinary contraction/deletion minors. The ambient
polytope always has positive dimension; for the empty target we use a genuine
one-dimensional deeply monotone polytope and delete its entire normal set. -/
theorem seriesParallel_iff_normalMatroid_minor {m : ℕ} (M : Matroid (Fin m))
    (hE : M.E = Set.univ) :
    HasSeriesParallelConstruction M ↔
      ∃ (n : ℕ), 0 < n ∧ ∃ (P : SmoothReflexivePresentation n) (f : Fin m ↪ Lattice n),
        P.DeeplyMonotone ∧ M.mapEmbedding f ≤m
          VectorMatroid.onSet (K := ℝ) (embed : Lattice n → Ambient n)
            (P.normals : Set (Lattice n)) := by
  constructor
  · intro hM
    by_cases hm : m = 0
    · subst m
      obtain ⟨σ, P, g, hσ, hP, hcube, hnorm, hminor, hrays, hcones⟩ :=
        program_cubical_polytope_matroid_realization (SPProgram.addColoop SPProgram.empty)
      let f : Fin 0 ↪ Lattice 1 := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
      refine ⟨1, by decide, P, f, hP, ∅, Set.univ, ?_⟩
      rw [Matroid.contract_empty]
      have hM0 : M.E = ∅ := Set.eq_empty_of_isEmpty _
      have hground : (M.mapEmbedding f).E = ∅ := by simp [hM0]
      apply Matroid.ext_indep (by simp [hground, hM0])
      intro I hI
      have hI' : I = ∅ := by simpa only [hground, Set.subset_empty_iff] using hI
      subst I
      simp
    · obtain ⟨σ, P, f, hσ, hP, hcube, hnorm, hminor, hrays, hcones, hnc, hvc⟩ :=
        abstract_seriesParallel_cubical_realization M hM
      exact ⟨m, Nat.pos_of_ne_zero hm, P, f, hP, hminor⟩
  · rintro ⟨n, hn, P, f, hP, hminor⟩
    exact (GroundSeriesParallel.of_mapEmbedding f
      (deeplyMonotone_normalMatroid_all_minors_seriesParallel P hP hminor)).hasConstruction hE

#print axioms Unimodular.SeriesParallel.deeplyMonotone_normalMatroid_seriesParallel
#print axioms Unimodular.SeriesParallel.deeplyMonotone_normalMatroid_all_minors_seriesParallel
#print axioms Unimodular.SeriesParallel.deeplyMonotone_integrally_graphic_no_K4
#print axioms Unimodular.SeriesParallel.seriesParallel_iff_normalMatroid_minor

end
end Unimodular.SeriesParallel
