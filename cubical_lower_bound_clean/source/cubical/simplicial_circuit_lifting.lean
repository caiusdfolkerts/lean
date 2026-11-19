module

public import cubical.simplicial_families
public import cubical.simplicial_contraction

/-! # Lifting a minimal cycle through a vertex contraction -/

@[expose] public section

namespace Cubical.Simplicial

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

@[simp]
theorem setChain_eq_zero_iff (s : Finset (Finset V)) : setChain s = 0 ↔ s = ∅ := by
  constructor
  · intro h
    simpa using congrArg Finsupp.support h
  · rintro rfl
    simp [setChain]

theorem cone_eq_zero_of_common_vertex (v : V) (c : Chain V)
    (hv : ∀ s ∈ c.support, v ∈ s) : cone v c = 0 := by
  ext s
  rw [cone_apply]
  by_cases hvs : v ∈ s
  · rw [ite_eq_left hvs]
    change c (s.erase v) = 0
    by_contra h
    exact Finset.notMem_erase v s (hv _ (Finsupp.mem_support_iff.mpr h))
  · simp [hvs]

/-- An augmented simplicial cycle supported on a cone is zero. -/
theorem cycle_eq_zero_of_common_vertex (v : V) (c : Chain V)
    (hcycle : boundary c = 0) (hv : ∀ s ∈ c.support, v ∈ s) : c = 0 := by
  have h := boundary_cone_add_cone_boundary v c
  rw [cone_eq_zero_of_common_vertex v c hv, hcycle, map_zero, map_zero, zero_add] at h
  exact h.symm

theorem cycle_has_facet_avoiding (v : V) {s : Finset (Finset V)}
    (hne : s.Nonempty) (hcycle : boundary (setChain s) = 0) :
    ∃ t ∈ s, v ∉ t := by
  by_contra hn
  push Not at hn
  have hz := cycle_eq_zero_of_common_vertex v (setChain s) hcycle (by simpa using hn)
  exact hne.ne_empty ((setChain_eq_zero_iff s).mp hz)

/-- Facets not containing the contracted edge. -/
def offEdge (u v : V) (s : Finset (Finset V)) : Finset (Finset V) :=
  s.filter (fun t => ¬(u ∈ t ∧ v ∈ t))

@[simp]
theorem mem_offEdge (u v : V) (s : Finset (Finset V)) (t : Finset V) :
    t ∈ offEdge u v s ↔ t ∈ s ∧ ¬(u ∈ t ∧ v ∈ t) := by simp [offEdge]

/-- The vertex set of a simplex after identifying `v` with `u`. -/
def contractedSimplex (u v : V) (s : Finset V) : Finset V :=
  if v ∈ s then insert u (s.erase v) else s

theorem contract_setChain {u v : V} (huv : u ≠ v) (s : Finset (Finset V)) :
    contract u v (setChain s) = familyChain (contractedSimplex u v) (offEdge u v s) := by
  simp only [setChain, familyChain, offEdge, map_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hu : u ∈ t <;> by_cases hv : v ∈ t <;>
    simp [contract_single_of_ne huv, contractedSimplex, hu, hv]

@[simp]
theorem offEdge_idem (u v : V) (s : Finset (Finset V)) :
    offEdge u v (offEdge u v s) = offEdge u v s := by
  simp [offEdge, Finset.filter_filter]

theorem contract_offEdge {u v : V} (huv : u ≠ v) (s : Finset (Finset V)) :
    contract u v (setChain (offEdge u v s)) = contract u v (setChain s) := by
  rw [contract_setChain huv, offEdge_idem, contract_setChain huv]

theorem complete_offEdge {u v : V} (huv : u ≠ v) (s : Finset (Finset V)) :
    complete u v (setChain (offEdge u v s)) = complete u v (setChain s) := by
  simp only [setChain, offEdge, map_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases he : u ∈ t ∧ v ∈ t
  · simp [he, complete_single_of_edge huv t he.1 he.2]
  · simp [he]

theorem offEdge_nonempty_of_cycle (u v : V) {s : Finset (Finset V)}
    (hne : s.Nonempty) (hcycle : boundary (setChain s) = 0) :
    (offEdge u v s).Nonempty := by
  obtain ⟨t, ht, hu⟩ := cycle_has_facet_avoiding u hne hcycle
  exact ⟨t, by simp [ht, hu]⟩

theorem offEdge_complete_support {u v : V} (huv : u ≠ v) (s : Finset (Finset V))
    (hs : ∀ t ∈ s, ¬(u ∈ t ∧ v ∈ t)) :
    offEdge u v (complete u v (setChain s)).support = s := by
  ext t
  by_cases he : u ∈ t ∧ v ∈ t
  · have hnot : t ∉ s := fun h => hs t h he
    simp [he, hnot]
  · simp [he, Finsupp.mem_support_iff, complete_eq_of_not_edge huv _ _ he]

/-- Two cycles agreeing away from one edge agree everywhere. -/
theorem cycles_eq_of_offEdge_eq (u v : V) {s t : Finset (Finset V)}
    (hs : boundary (setChain s) = 0) (ht : boundary (setChain t) = 0)
    (hoff : offEdge u v s = offEdge u v t) : s = t := by
  have hc : boundary (setChain s + setChain t) = 0 := by simp [hs, ht]
  have hu : ∀ r ∈ (setChain s + setChain t).support, u ∈ r := by
    intro r hr
    by_contra hur
    have he : ¬(u ∈ r ∧ v ∈ r) := by simp [hur]
    have hm : r ∈ s ↔ r ∈ t := by
      have h := congrArg (fun x : Finset (Finset V) => r ∈ x) hoff
      simpa [he] using h
    have hz : (setChain s + setChain t) r = 0 := by
      simp only [Finsupp.add_apply, setChain_apply]
      simp only [hm]
      exact CharTwo.add_self_eq_zero _
    exact (Finsupp.mem_support_iff.mp hr) hz
  have hz := cycle_eq_zero_of_common_vertex u (setChain s + setChain t) hc hu
  apply setChain_injective
  have h := eq_neg_of_add_eq_zero_left hz
  simpa using h

/-- A minimal cycle of contracted facets lifts to a genuine minimal simplicial
cycle, using the explicit completion. -/
theorem complete_isFacetCircuit {u v : V} (huv : u ≠ v) (s : Finset (Finset V))
    (hoff : ∀ t ∈ s, ¬(u ∈ t ∧ v ∈ t))
    (hcir : IsFacetCircuit (contractedSimplex u v) s) :
    IsFacetCircuit id (complete u v (setChain s)).support := by
  let L := (complete u v (setChain s)).support
  change IsFacetCircuit id L
  have hLoff : offEdge u v L = s := offEdge_complete_support huv s hoff
  have hsfilter : offEdge u v s = s := by
    ext t
    simp only [mem_offEdge]
    exact ⟨And.left, fun h => ⟨h, hoff t h⟩⟩
  have hcontract : boundary (contract u v (setChain s)) = 0 := by
    rw [contract_setChain huv, hsfilter]
    exact hcir.cycle
  have hLcycle : boundary (setChain L) = 0 := by
    rw [show L = (complete u v (setChain s)).support from rfl, setChain_support_eq]
    exact complete_cycle u v hcontract
  have hLne : L.Nonempty := by
    obtain ⟨t, ht⟩ := hcir.nonempty
    have : t ∈ offEdge u v L := hLoff.symm ▸ ht
    exact ⟨t, (mem_offEdge u v L t).mp this |>.1⟩
  refine ⟨hLne, ?_, ?_⟩
  · simpa only [setChain, map_sum, id_eq] using hLcycle
  · intro t htL htne htz
    have htcycle : boundary (setChain t) = 0 := by
      simpa only [setChain, map_sum, id_eq] using htz
    have hts : offEdge u v t ⊆ s := by
      intro r hr
      rw [← hLoff]
      have h := (mem_offEdge u v t r).mp hr
      exact (mem_offEdge u v L r).mpr ⟨htL h.1, h.2⟩
    have htz' : boundary (familyChain (contractedSimplex u v) (offEdge u v t)) = 0 := by
      rw [← contract_setChain huv]
      exact contract_cycle u v htcycle
    have hmin : offEdge u v t = s := hcir.minimal _ hts
      (offEdge_nonempty_of_cycle u v htne htcycle)
      (by simpa only [familyChain, map_sum] using htz')
    exact cycles_eq_of_offEdge_eq u v htcycle hLcycle (hmin.trans hLoff.symm)

end Cubical.Simplicial
