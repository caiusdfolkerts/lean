import cubical.pseudomanifold_circuit

/-!
# Indexed simplicial pseudomanifolds

The finite facet index is retained. A unique second facet across each
ridge, together with connectedness of the facet graph, implies that
the indexed boundary columns form a minimal cycle over `𝔽₂`.
-/

namespace Cubical.Simplicial

open scoped BigOperators

variable {V I : Type*} [DecidableEq V] [Fintype I]

/-- The dual graph on actual facet indices. -/
def indexedFacetGraph (σ : I → Finset V) : SimpleGraph I where
  Adj i j := i ≠ j ∧ ∃ r, r ∈ simplexBoundary (σ i) ∧ r ∈ simplexBoundary (σ j)
  symm := ⟨by rintro i j ⟨hij, r, hi, hj⟩; exact ⟨hij.symm, r, hj, hi⟩⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩

/-- Every ridge incident to a facet is incident to exactly one other
indexed facet. The final iff records all incidences, including multiplicity. -/
def RidgePairing (σ : I → Finset V) : Prop :=
  ∀ i r, r ∈ simplexBoundary (σ i) → ∃ j, i ≠ j ∧
    ∀ k, r ∈ simplexBoundary (σ k) ↔ k = i ∨ k = j

/-- Ridge pairing makes the total indexed simplicial boundary zero. -/
theorem RidgePairing.cycle {σ : I → Finset V} (hp : RidgePairing σ) :
    boundary (familyChain σ Finset.univ) = 0 := by
  classical
  ext r
  have he : boundary (familyChain σ Finset.univ) r =
      ((Finset.univ.filter (fun i => r ∈ simplexBoundary (σ i))).card : ZMod 2) := by
    simp only [familyChain, map_sum, Finsupp.finsetSum_apply, boundary_single_one_apply]
    exact Finset.sum_boole _ _
  rw [he]
  by_cases hex : ∃ i, r ∈ simplexBoundary (σ i)
  · obtain ⟨i, hi⟩ := hex
    obtain ⟨j, hij, hocc⟩ := hp i r hi
    have hf : Finset.univ.filter (fun k => r ∈ simplexBoundary (σ k)) = {i, j} := by
      ext k
      simp [hocc]
    rw [hf, Finset.card_pair hij]
    change (2 : ZMod 2) = 0
    decide
  · have hf : Finset.univ.filter (fun i => r ∈ simplexBoundary (σ i)) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact fun h => hex ⟨i, h⟩
    simp [hf]

/-- A zero-boundary subfamily is closed under adjacent indexed facets. -/
theorem RidgePairing.closed_under_adj {σ : I → Finset V} (hp : RidgePairing σ)
    (t : Finset I)
    (hzero : (∑ i ∈ t, boundary (Finsupp.single (σ i) 1)) = 0)
    {i j : I} (hij : (indexedFacetGraph σ).Adj i j) (hi : i ∈ t) : j ∈ t := by
  classical
  obtain ⟨hne, r, hir, hjr⟩ := hij
  obtain ⟨j', hij', hocc⟩ := hp i r hir
  have hjj' : j = j' := ((hocc j).mp hjr).resolve_left hne.symm
  subst j'
  by_contra hj
  have hsum : (∑ k ∈ t, boundary (Finsupp.single (σ k) 1) r) = 1 := by
    rw [Finset.sum_eq_single i]
    · rw [boundary_single_one_apply, ite_eq_left hir]
    · intro k hk hki
      have hkr : r ∉ simplexBoundary (σ k) := by
        intro h
        rcases (hocc k).mp h with h | h
        · exact hki h
        · exact hj (h ▸ hk)
      rw [boundary_single_one_apply, ite_eq_right hkr]
    · exact fun h => (h hi).elim
  have he := congrArg (fun c : Chain V => c r) hzero
  simp only [Finsupp.finsetSum_apply, Finsupp.zero_apply, hsum] at he
  exact one_ne_zero he

/-- A connected indexed simplicial pseudomanifold is a minimal
simplicial `𝔽₂` cycle. -/
theorem facetCircuit_of_ridgePairing_connected {σ : I → Finset V}
    (hp : RidgePairing σ) (hconn : (indexedFacetGraph σ).Connected) :
    IsFacetCircuit σ Finset.univ := by
  classical
  have hne : (Finset.univ : Finset I).Nonempty := by
    obtain ⟨i⟩ := hconn.nonempty
    exact ⟨i, Finset.mem_univ _⟩
  refine ⟨hne, ?_, ?_⟩
  · simpa only [familyChain, map_sum] using hp.cycle
  · intro t hts htne htz
    obtain ⟨i, hi⟩ := htne
    apply Finset.eq_univ_of_forall
    intro j
    obtain ⟨walk⟩ := hconn i j
    have hwalk : ∀ {a b : I}, (indexedFacetGraph σ).Walk a b → a ∈ t → b ∈ t := by
      intro a b w
      induction w with
      | nil => exact id
      | @cons a b c hab w ih => exact fun ha => ih (hp.closed_under_adj t htz hab ha)
    exact hwalk walk hi

end Cubical.Simplicial
