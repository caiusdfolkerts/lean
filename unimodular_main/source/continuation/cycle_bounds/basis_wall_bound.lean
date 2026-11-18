module

public import Continuation.CycleBounds.CircuitCycles

@[expose] public section

/-! # Actual Cartier interpolation gives the wall sum

An independent cone basis and one further ray determine a genuine circuit.
Applying the Cartier functional to its signed incidence relation identifies
its ceiling sum with the ordinary wall slack. No support-minimality assertion
about an informal wall relation is used as a hypothesis.
-/

noncomputable section
open scoped BigOperators Matroid
namespace Unimodular.CycleBounds
open SeriesParallel SeriesParallel.IncidenceGraph
attribute [local instance] Classical.propDecidable
variable {V E N : Type*}

/-- An extra nonloop incidence column in the span of an independent set belongs
to a genuine signed cycle contained in that set together with the extra label. -/
theorem signed_cycle_of_independent_span [Fintype V] (G : IncidenceGraph V E)
    (B : Finset E) (hB : G.cycleMatroid.Indep (B : Set E))
    (w : E) (hw : w ∈ G.edges) (hwB : w ∉ B)
    (hwspan : G.column w ∈ Submodule.span ℝ (G.column '' (B : Set E)))
    (hne : G.source w ≠ G.target w) :
    ∃ c : SignedCycle G, Set.range c.edges ⊆ insert w (B : Set E) ∧
      ∃ i, c.edges i = w ∧ c.signs i = 1 := by
  classical
  have hground : insert w (B : Set E) ⊆ G.cycleMatroid.E :=
    Set.insert_subset hw hB.subset_ground
  have hnot : ¬G.cycleMatroid.Indep (insert w (B : Set E)) := by
    intro hi
    have hli := ((VectorMatroid.onSet_indep _ _ _).mp hi).2
    exact (hli.notMem_span_of_insert hwB) hwspan
  have hdep : G.cycleMatroid.Dep (insert w (B : Set E)) :=
    (Matroid.not_indep_iff hground).mp hnot
  obtain ⟨C, hCsub, hC⟩ := hdep.exists_isCircuit_subset
  have hwC : w ∈ C := by
    by_contra hh
    apply hC.not_indep
    apply hB.subset
    intro x hx
    rcases hCsub hx with h | h
    · exact (hh (h ▸ hx)).elim
    · exact h
  obtain ⟨c, hc, i, hie, hiε⟩ := circuit_signed_cycle G hC hwC hne
  exact ⟨c, hc ▸ hCsub, i, hie, hiε⟩

/-- The normalized graphic wall bound in the form directly used for an actual
Cartier divisor: L interpolates the ceiling coefficients on one maximal-cone
basis, and the displayed expression is the wall slack at the adjacent ray. -/
theorem graphic_basis_wall_bound [Fintype V] [AddCommGroup N] [Module ℝ N]
    [FiniteDimensional ℝ N] (G : IncidenceGraph V E) (hK : ¬G.HasK4Minor)
    (v : E → N) (ι : N →ₗ[ℝ] (V → ℝ))
    (hι : ∀ e, ι (v e) = Pi.single (G.source e) 1 - Pi.single (G.target e) 1)
    (h : V → ℝ) (B : Finset E) (hB : G.cycleMatroid.Indep (B : Set E))
    (w : E) (hw : w ∈ G.edges) (hwB : w ∉ B)
    (hwspan : G.column w ∈ Submodule.span ℝ (G.column '' (B : Set E)))
    (hne : G.source w ≠ G.target w) (L : (V → ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀ e ∈ B, L (G.column e) = (⌈h (G.source e) - h (G.target e)⌉ : ℝ))
    (hlo : ∀ e ∈ insert w (B : Set E), -1 < h (G.source e) - h (G.target e))
    (hhi : ∀ e ∈ insert w (B : Set E), h (G.source e) - h (G.target e) < 1) :
    (⌈h (G.source w) - h (G.target w)⌉ : ℝ) - L (G.column w) ≤
      (Module.finrank ℝ (activeDirections v
        {e | e ∈ G.edges ∧ h (G.source e) = h (G.target e)}) : ℝ) := by
  classical
  obtain ⟨c, hc, i, hie, hiε⟩ := signed_cycle_of_independent_span G B hB w hw hwB hwspan hne
  let A : E → ℝ := fun e ↦ (⌈h (G.source e) - h (G.target e)⌉ : ℝ)
  have hother (j : Fin c.length) (hji : j ≠ i) : L (G.column (c.edges j)) = A (c.edges j) := by
    apply hL
    rcases hc (Set.mem_range_self j) with hj | hj
    · exact (hji (c.injective (hj.trans hie.symm))).elim
    · exact hj
  have hsumL : ∑ j, (c.signs j : ℝ) * L (G.column (c.edges j)) = 0 := by
    have hh := congrArg L c.relation
    simpa only [map_sum, map_smul, map_zero, smul_eq_mul] using hh
  have hdiff : ∑ j, (c.signs j : ℝ) * (A (c.edges j) - L (G.column (c.edges j))) =
      A w - L (G.column w) := by
    rw [Finset.sum_eq_single i]
    · simp [hie, hiε]
    · intro j _ hji
      rw [hother j hji, sub_self, mul_zero]
    · simp
  have heq : ∑ j, (c.signs j : ℝ) * A (c.edges j) = A w - L (G.column w) := by
    simpa only [mul_sub, Finset.sum_sub_distrib, hsumL, sub_zero] using hdiff
  have hb := graph_wall_bound G hK v ι hι h c.length c.positive c.vertices c.edges c.signs
    c.word c.oriented (fun j ↦ hlo _ (hc (Set.mem_range_self j)))
    (fun j ↦ hhi _ (hc (Set.mem_range_self j)))
  have hb' : (∑ j, (c.signs j : ℝ) * A (c.edges j)) ≤
      (Module.finrank ℝ (activeDirections v
        {e | e ∈ G.edges ∧ h (G.source e) = h (G.target e)}) : ℝ) := by
    dsimp only [A]
    exact_mod_cast hb
  rwa [heq] at hb'

#print axioms graphic_basis_wall_bound
end Unimodular.CycleBounds
