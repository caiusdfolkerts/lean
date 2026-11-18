module

public import Continuation.Geometry.OriginalPolytopeMatroid
public import Continuation.Geometry.SeriesParallelComponents

/-!
# The literal network-component conclusion on the original normal lattice

The original normal matroid is loopless, and its actual connected component
restrictions form a finite Mathlib direct sum. Every component has an explicit
eligible series-parallel network model supplied by the proved ordinary
construction equivalence. All original primitive-normal labels are retained.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open scoped Classical Matroid

universe u v

namespace Unimodular.OriginalSmoothReflexivePresentation

variable {N : Type u} [AddCommGroup N]
    {V : Type v} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} {ι : N →+ V} (P : OriginalSmoothReflexivePresentation n ι)

/-- Each original primitive facet normal evaluates to one at an incident
integral vertex. Consequently its actual real representing vector is nonzero. -/
theorem normalMatroid_loopless : P.normalMatroid.Loopless := by
  apply Matroid.loopless_iff_forall_isNonloop.mpr
  intro m hm
  have hmgeom : m ∈ P.geometricFacetNormals := hm
  have hmlist : m ∈ P.normals := by
    simpa only [P.geometricFacetNormals_eq_normals, Finset.mem_coe] using hmgeom
  obtain ⟨v, i, hi⟩ := P.normals_occur m hmlist
  have hactive : m v.val = 1 := by
    rw [← hi]
    exact P.basis_active v i
  have hnonzero : P.lattice.realCharacter m ≠ 0 := by
    intro hz
    have heval : P.lattice.realCharacter m (ι v.val) = (1 : ℝ) := by
      rw [TauCeti.Toric.IsIntegralLattice.realCharacter_apply]
      exact_mod_cast hactive
    rw [hz] at heval
    norm_num at heval
  apply Matroid.indep_singleton.mp
  change (VectorMatroid.onSet (K := ℝ)
    (fun m : N →+ ℤ => P.lattice.realCharacter m) P.geometricFacetNormals).Indep {m}
  rw [VectorMatroid.onSet_indep, linearIndepOn_singleton_iff]
  exact ⟨Set.singleton_subset_iff.mpr hmgeom, hnonzero⟩

/-- Looplessness is retained by each actual component restriction. -/
theorem normalMatroid_component_loopless
    (C : SeriesParallel.NetworkComponents.Block P.normalMatroid) :
    (SeriesParallel.NetworkComponents.matroid P.normalMatroid C).Loopless := by
  letI : P.normalMatroid.Loopless := P.normalMatroid_loopless
  exact (P.normalMatroid.restrict_isRestriction C.val
    (SeriesParallel.NetworkComponents.block_subset_ground P.normalMatroid C)).loopless

/-- Theorem 1.2's first conclusion as a literal finite direct sum of the
original normal matroid's loopless connected components, each with an actual
eligible network model. The coordinate basis is absent from the statement. -/
theorem theorem_1_2_original_lattice_direct_sum_networks
    (_hn : 1 ≤ n) (hP : P.DeeplyMonotone) :
    Finite (SeriesParallel.NetworkComponents.Block P.normalMatroid) ∧
    P.normalMatroid =
      Matroid.disjointSigma
        (SeriesParallel.NetworkComponents.matroid P.normalMatroid)
        (SeriesParallel.NetworkComponents.pairwise_disjoint P.normalMatroid) ∧
    ∀ C : SeriesParallel.NetworkComponents.Block P.normalMatroid,
      (SeriesParallel.NetworkComponents.matroid P.normalMatroid C).Connected ∧
      (SeriesParallel.NetworkComponents.matroid P.normalMatroid C).Loopless ∧
      ∃ (m : ℕ)
        (e : Fin m ≃ (SeriesParallel.NetworkComponents.matroid P.normalMatroid C).E)
        (G : SeriesParallel.RootedNetwork m m),
        G.HasEligibleConstruction ∧
        ((SeriesParallel.NetworkComponents.matroid P.normalMatroid C).restrictSubtype
          (SeriesParallel.NetworkComponents.matroid P.normalMatroid C).E).mapEquiv e.symm =
            G.cycleMatroid := by
  obtain ⟨hfinite, hsum, hcomponents⟩ :=
    SeriesParallel.NetworkComponents.direct_sum_network_components P.normalMatroid
      (P.deeplyMonotone_normalMatroid_seriesParallel hP)
  refine ⟨hfinite, hsum, ?_⟩
  intro C
  exact ⟨(hcomponents C).1, P.normalMatroid_component_loopless C, (hcomponents C).2⟩

end Unimodular.OriginalSmoothReflexivePresentation

#print axioms Unimodular.OriginalSmoothReflexivePresentation.normalMatroid_loopless
#print axioms Unimodular.OriginalSmoothReflexivePresentation.theorem_1_2_original_lattice_direct_sum_networks
