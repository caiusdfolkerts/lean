module

public import cubical.simplicial_geometry
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! # The finite cycle decomposition used in Fogelsanger's theorem

Contraction retains the original facet indices and strictly reduces the used
vertex set. A partition into minimal
contracted cycles therefore retains duplicate simplices exactly. Each part
is completed by the explicit chain homotopy to a minimal ordinary cycle.
-/

@[expose] public section

namespace Cubical.Simplicial

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

abbrev EdgeCircuitPartition (u v : V) (s : Finset (Finset V)) :=
  Cubical.ZeroSumCircuitPartition
    (fun a => boundary (Finsupp.single (contractedSimplex u v a) 1)) (offEdge u v s)

theorem edgeCircuitPartition_exists {u v : V} (huv : u ≠ v)
    {s : Finset (Finset V)} (hcycle : boundary (setChain s) = 0) :
    Nonempty (EdgeCircuitPartition u v s) := by
  apply Cubical.zeroSumCircuitPartition_exists
  have h := contract_cycle u v hcycle
  rw [contract_setChain huv] at h
  simpa only [familyChain, map_sum] using h

/-- Complete one part of the contracted cycle partition. -/
noncomputable def liftedPart (u v : V) (a : Finset (Finset V)) : Finset (Finset V) :=
  (complete u v (setChain a)).support

theorem EdgeCircuitPartition.part_subset {u v : V} {s : Finset (Finset V)}
    (p : EdgeCircuitPartition u v s) {a : Finset (Finset V)} (ha : a ∈ p.parts) :
    a ⊆ offEdge u v s := by
  intro t ht
  rw [← p.cover]
  exact Finset.mem_biUnion.mpr ⟨a, ha, ht⟩

theorem EdgeCircuitPartition.part_offEdge {u v : V} {s : Finset (Finset V)}
    (p : EdgeCircuitPartition u v s) {a : Finset (Finset V)} (ha : a ∈ p.parts) :
    ∀ t ∈ a, ¬(u ∈ t ∧ v ∈ t) := by
  intro t ht
  exact (mem_offEdge u v s t).mp (p.part_subset ha ht) |>.2

theorem EdgeCircuitPartition.lifted_circuit {u v : V} (huv : u ≠ v)
    {s : Finset (Finset V)} (p : EdgeCircuitPartition u v s)
    {a : Finset (Finset V)} (ha : a ∈ p.parts) :
    IsFacetCircuit id (liftedPart u v a) :=
  complete_isFacetCircuit huv a (p.part_offEdge ha) (p.circuit a ha)

theorem EdgeCircuitPartition.lifted_offEdge {u v : V} (huv : u ≠ v)
    {s : Finset (Finset V)} (p : EdgeCircuitPartition u v s)
    {a : Finset (Finset V)} (ha : a ∈ p.parts) :
    offEdge u v (liftedPart u v a) = a :=
  offEdge_complete_support huv a (p.part_offEdge ha)

theorem EdgeCircuitPartition.lifted_cycle {u v : V} (huv : u ≠ v)
    {s : Finset (Finset V)} (p : EdgeCircuitPartition u v s)
    {a : Finset (Finset V)} (ha : a ∈ p.parts) :
    boundary (setChain (liftedPart u v a)) = 0 := by
  simpa only [familyChain, setChain, id_eq] using (p.lifted_circuit huv ha).cycle

theorem EdgeCircuitPartition.lifted_pure {u v : V} (huv : u ≠ v)
    {s : Finset (Finset V)} (p : EdgeCircuitPartition u v s)
    {n : ℕ} (hpure : Pure n id s) {a : Finset (Finset V)} (ha : a ∈ p.parts) :
    Pure n id (liftedPart u v a) := by
  apply pure_complete huv
  intro t ht
  exact hpure t ((mem_offEdge u v s t).mp (p.part_subset ha ht)).1

theorem EdgeCircuitPartition.contracted_pure {u v : V}
    {s : Finset (Finset V)} (p : EdgeCircuitPartition u v s)
    {n : ℕ} (hpure : Pure n id s) {a : Finset (Finset V)} (ha : a ∈ p.parts) :
    Pure n (contractedSimplex u v) a := by
  intro t ht
  rw [contractedSimplex_card (p.part_offEdge ha t ht)]
  exact hpure t ((mem_offEdge u v s t).mp (p.part_subset ha ht)).1

theorem EdgeCircuitPartition.lifted_vertices_eq {u v : V} (huv : u ≠ v)
    {s : Finset (Finset V)} (p : EdgeCircuitPartition u v s)
    {n : ℕ} (hpure : Pure n id s) {a : Finset (Finset V)} (ha : a ∈ p.parts) :
    vertices id (liftedPart u v a) = vertices id a := by
  apply complete_vertices_eq huv
  · intro t ht
    exact hpure t ((mem_offEdge u v s t).mp (p.part_subset ha ht)).1
  · exact p.part_offEdge ha
  · simpa only [liftedPart, setChain_support_eq] using p.lifted_cycle huv ha

theorem EdgeCircuitPartition.lifted_graph_le {u v : V} (huv : u ≠ v)
    {s : Finset (Finset V)} (p : EdgeCircuitPartition u v s)
    {n : ℕ} (hpure : Pure n id s) (he : (oneSkeleton id s).Adj u v)
    {a : Finset (Finset V)} (ha : a ∈ p.parts) :
    oneSkeleton id (liftedPart u v a) ≤ oneSkeleton id s := by
  apply complete_oneSkeleton_le huv
  · intro t ht
    exact hpure t ((mem_offEdge u v s t).mp (p.part_subset ha ht)).1
  · intro t ht
    exact ((mem_offEdge u v s t).mp (p.part_subset ha ht)).1
  · exact p.part_offEdge ha
  · simpa only [liftedPart, setChain_support_eq] using p.lifted_cycle huv ha
  · exact he

theorem EdgeCircuitPartition.lifted_has_edge {u v : V} (huv : u ≠ v)
    {s : Finset (Finset V)} (p : EdgeCircuitPartition u v s)
    (hs : IsFacetCircuit id s) (he : (oneSkeleton id s).Adj u v)
    {a : Finset (Finset V)} (ha : a ∈ p.parts) :
    (oneSkeleton id (liftedPart u v a)).Adj u v := by
  apply cycle_contains_edge_of_offEdge_subset hs
    (p.lifted_circuit huv ha).nonempty (p.lifted_cycle huv ha)
  · rw [p.lifted_offEdge huv ha]
    intro t ht
    exact ((mem_offEdge u v s t).mp (p.part_subset ha ht)).1
  · exact he

theorem EdgeCircuitPartition.contracted_vertices_card_lt {u v : V} (huv : u ≠ v)
    {s : Finset (Finset V)} (p : EdgeCircuitPartition u v s)
    (he : (oneSkeleton id s).Adj u v)
    {a : Finset (Finset V)} (ha : a ∈ p.parts) :
    (vertices (contractedSimplex u v) a).card < (vertices id s).card := by
  have huvS := oneSkeleton_adj_vertices he
  have hsub : vertices (contractedSimplex u v) a ⊆ (vertices id s).erase v := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := (mem_vertices (contractedSimplex u v) a x).mp hx
    have hts := (mem_offEdge u v s t).mp (p.part_subset ha ht) |>.1
    refine Finset.mem_erase.mpr ⟨?_, ?_⟩
    · intro hxv
      exact contractedSimplex_notMem huv t (hxv ▸ hxt)
    · rw [contractedSimplex_eq_image] at hxt
      obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hxt
      by_cases hyv : y = v
      · have hxu : x = u := by simpa [collapse, hyv] using hxy.symm
        exact hxu ▸ huvS.1
      · have hyx : y = x := by simpa [collapse, hyv] using hxy
        exact (mem_vertices id s x).mpr ⟨t, hts, hyx ▸ hy⟩
  exact (Finset.card_le_card hsub).trans_lt (Finset.card_erase_lt_of_mem huvS.2)

/-- The sum of the lifted cycles is exactly the original cycle. -/
theorem EdgeCircuitPartition.sum_lifted {u v : V} (huv : u ≠ v)
    {s : Finset (Finset V)} (p : EdgeCircuitPartition u v s)
    (hcycle : boundary (setChain s) = 0) :
    (∑ a ∈ p.parts, setChain (liftedPart u v a)) = setChain s := by
  simp only [liftedPart, setChain_support_eq, ← map_sum]
  have hsum : (∑ a ∈ p.parts, setChain a) = setChain (offEdge u v s) := by
    simp only [setChain]
    rw [← Finset.sum_biUnion p.pairwise_disjoint]
    change (∑ x ∈ p.parts.biUnion id, Finsupp.single x 1) = _
    rw [p.cover]
  rw [hsum, complete_offEdge huv, complete_of_cycle u v hcycle]

theorem EdgeCircuitPartition.facet_covered {u v : V} (huv : u ≠ v)
    {s : Finset (Finset V)} (p : EdgeCircuitPartition u v s)
    (hcycle : boundary (setChain s) = 0) {t : Finset V} (ht : t ∈ s) :
    ∃ a ∈ p.parts, t ∈ liftedPart u v a := by
  have he := congrArg (fun c : Chain V => c t) (p.sum_lifted huv hcycle)
  have hn : (∑ a ∈ p.parts, setChain (liftedPart u v a) t) ≠ 0 := by
    have hpos : setChain s t ≠ 0 := by simp [ht]
    simpa only [Finsupp.finsetSum_apply] using he.trans_ne hpos
  obtain ⟨a, ha, hta⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  exact ⟨a, ha, by simpa using hta⟩

/-- An original off-edge facet belongs to exactly its own lifted part. -/
theorem EdgeCircuitPartition.private_facet {u v : V} (huv : u ≠ v)
    {s : Finset (Finset V)} (p : EdgeCircuitPartition u v s)
    {a b : Finset (Finset V)} (ha : a ∈ p.parts) (hb : b ∈ p.parts)
    {t : Finset V} (ht : t ∈ a) :
    t ∈ liftedPart u v b ↔ a = b := by
  have hoff := p.part_offEdge ha t ht
  have hmem : t ∈ liftedPart u v b ↔ t ∈ b := by
    have h := congrArg (fun q : Finset (Finset V) => t ∈ q) (p.lifted_offEdge huv hb)
    simpa [hoff] using (Iff.of_eq h)
  rw [hmem]
  constructor
  · intro htb
    by_contra hne
    exact Finset.disjoint_left.mp (p.pairwise_disjoint ha hb hne) ht htb
  · rintro rfl
    exact ht

noncomputable def liftedSum (u v : V) (q : Finset (Finset (Finset V))) : Chain V :=
  ∑ a ∈ q, setChain (liftedPart u v a)

theorem EdgeCircuitPartition.liftedSum_cycle {u v : V} (huv : u ≠ v)
    {s : Finset (Finset V)} (p : EdgeCircuitPartition u v s)
    {q : Finset (Finset (Finset V))} (hq : q ⊆ p.parts) :
    boundary (liftedSum u v q) = 0 := by
  rw [liftedSum, map_sum]
  apply Finset.sum_eq_zero
  intro a ha
  exact p.lifted_cycle huv (hq ha)

theorem EdgeCircuitPartition.liftedSum_private {u v : V} (huv : u ≠ v)
    {s : Finset (Finset V)} (p : EdgeCircuitPartition u v s)
    {q : Finset (Finset (Finset V))} (hq : q ⊆ p.parts)
    {a : Finset (Finset V)} (ha : a ∈ p.parts) {t : Finset V} (ht : t ∈ a) :
    liftedSum u v q t = if a ∈ q then 1 else 0 := by
  simp only [liftedSum, Finsupp.finsetSum_apply]
  by_cases haq : a ∈ q
  · rw [ite_eq_left haq, Finset.sum_eq_single a]
    · simp [(p.private_facet huv ha ha ht).mpr rfl]
    · intro b hb hba
      have hnot : t ∉ liftedPart u v b := by
        rw [p.private_facet huv ha (hq hb) ht]
        exact hba.symm
      simp [hnot]
    · exact fun h => (h haq).elim
  · rw [ite_eq_right haq]
    apply Finset.sum_eq_zero
    intro b hb
    have hnot : t ∉ liftedPart u v b := by
      rw [p.private_facet huv ha (hq hb) ht]
      intro he
      exact haq (he ▸ hb)
    simp [hnot]

theorem EdgeCircuitPartition.liftedSum_ne_zero {u v : V} (huv : u ≠ v)
    {s : Finset (Finset V)} (p : EdgeCircuitPartition u v s)
    {q : Finset (Finset (Finset V))} (hq : q ⊆ p.parts) (hne : q.Nonempty) :
    liftedSum u v q ≠ 0 := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨t, ht⟩ := (p.circuit a (hq ha)).nonempty
  intro hz
  have hc := congrArg (fun c : Chain V => c t) hz
  rw [p.liftedSum_private huv hq (hq ha) ht, ite_eq_left ha] at hc
  exact one_ne_zero hc

theorem EdgeCircuitPartition.liftedSum_ne_original {u v : V} (huv : u ≠ v)
    {s : Finset (Finset V)} (p : EdgeCircuitPartition u v s)
    {q : Finset (Finset (Finset V))} (hq : q ⊆ p.parts) (hne : q ≠ p.parts) :
    liftedSum u v q ≠ setChain s := by
  obtain ⟨a, ha, haq⟩ : ∃ a ∈ p.parts, a ∉ q := by
    by_contra h
    push Not at h
    exact hne (Finset.Subset.antisymm hq h)
  obtain ⟨t, ht⟩ := (p.circuit a ha).nonempty
  have hts : t ∈ s := ((mem_offEdge u v s t).mp (p.part_subset ha ht)).1
  intro hz
  have hc := congrArg (fun c : Chain V => c t) hz
  rw [p.liftedSum_private huv hq ha ht, ite_eq_right haq,
    setChain_apply, ite_eq_left hts] at hc
  exact zero_ne_one hc

/-- Every proper cut of the partition has an added facet crossing the
cut. The proof is precisely the minimality of the original cycle. -/
theorem EdgeCircuitPartition.overlap_across_cut {u v : V} (huv : u ≠ v)
    {s : Finset (Finset V)} (p : EdgeCircuitPartition u v s)
    (hs : IsFacetCircuit id s) {q : Finset (Finset (Finset V))}
    (hq : q ⊆ p.parts) (hqne : q.Nonempty) (hqproper : q ≠ p.parts) :
    ∃ a ∈ q, ∃ b ∈ p.parts \ q, ∃ t : Finset V,
      t ∉ s ∧ t ∈ liftedPart u v a ∧ t ∈ liftedPart u v b := by
  let c := liftedSum u v q
  have hcne : c ≠ 0 := p.liftedSum_ne_zero huv hq hqne
  have hccycle : boundary c = 0 := p.liftedSum_cycle huv hq
  have hcnot : c ≠ setChain s := p.liftedSum_ne_original huv hq hqproper
  obtain ⟨t, htc, hts⟩ : ∃ t ∈ c.support, t ∉ s := by
    by_contra h
    push Not at h
    have hsupne : c.support.Nonempty := by simpa using hcne
    have heq : c.support = s := hs.minimal c.support h hsupne
      (by
        have hz : boundary (setChain c.support) = 0 := by
          rw [setChain_support_eq]
          exact hccycle
        simpa only [setChain, map_sum, id_eq] using hz)
    apply hcnot
    rw [← setChain_support_eq c, heq]
  have hcoef : (∑ a ∈ q, setChain (liftedPart u v a) t) ≠ 0 := by
    simpa only [c, liftedSum, Finsupp.finsetSum_apply] using Finsupp.mem_support_iff.mp htc
  obtain ⟨a, haq, hta⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcoef
  have hsum := Finset.sum_sdiff hq (f := fun a => setChain (liftedPart u v a))
  have hs_cycle : boundary (setChain s) = 0 := by
    simpa only [familyChain, setChain, id_eq] using hs.cycle
  rw [p.sum_lifted huv hs_cycle] at hsum
  have hsumt := congrArg (fun c : Chain V => c t) hsum
  have hother : (∑ b ∈ p.parts \ q, setChain (liftedPart u v b) t) ≠ 0 := by
    intro hz
    simp only [Finsupp.add_apply, Finsupp.finsetSum_apply,
      setChain_apply, ite_eq_right hts] at hsumt
    have hz' : (∑ b ∈ p.parts \ q, if t ∈ liftedPart u v b then (1 : ZMod 2) else 0) = 0 := by
      simpa only [setChain_apply] using hz
    rw [hz', zero_add] at hsumt
    exact hcoef (by simpa only [setChain_apply] using hsumt)
  obtain ⟨b, hbq, htb⟩ := Finset.exists_ne_zero_of_sum_ne_zero hother
  exact ⟨a, haq, b, hbq, t, hts, by simpa using hta, by simpa using htb⟩

/-- Edges of the overlap graph record an added complete simplex shared
by two lifted parts. -/
def overlapGraph {u v : V} {s : Finset (Finset V)} (p : EdgeCircuitPartition u v s) :
    SimpleGraph {a // a ∈ p.parts} where
  Adj a b := a ≠ b ∧ ∃ t : Finset V,
    t ∉ s ∧ t ∈ liftedPart u v a.val ∧ t ∈ liftedPart u v b.val
  symm := ⟨by
    rintro a b ⟨hne, t, ht, hta, htb⟩
    exact ⟨hne.symm, t, ht, htb, hta⟩⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩

theorem EdgeCircuitPartition.parts_nonempty {u v : V}
    {s : Finset (Finset V)} (p : EdgeCircuitPartition u v s)
    (hs : IsFacetCircuit id s) : p.parts.Nonempty := by
  have hc : boundary (setChain s) = 0 := by
    simpa only [familyChain, setChain, id_eq] using hs.cycle
  obtain ⟨t, ht⟩ := offEdge_nonempty_of_cycle u v hs.nonempty hc
  rw [← p.cover] at ht
  obtain ⟨a, ha, _⟩ := Finset.mem_biUnion.mp ht
  exact ⟨a, ha⟩

theorem EdgeCircuitPartition.overlap_connected {u v : V} (huv : u ≠ v)
    {s : Finset (Finset V)} (p : EdgeCircuitPartition u v s)
    (hs : IsFacetCircuit id s) : (overlapGraph p).Connected := by
  classical
  obtain ⟨a₀, ha₀⟩ := p.parts_nonempty hs
  let a : {a // a ∈ p.parts} := ⟨a₀, ha₀⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨a, ?_⟩
  intro b
  by_contra hreach
  let q := p.parts.filter (fun z => ∃ hz : z ∈ p.parts, (overlapGraph p).Reachable a ⟨z, hz⟩)
  have hq : q ⊆ p.parts := Finset.filter_subset _ _
  have hqa : a₀ ∈ q := by
    simp only [q, Finset.mem_filter]
    exact ⟨ha₀, ha₀, SimpleGraph.Reachable.refl a⟩
  have hqb : b.val ∉ q := by
    intro h
    obtain ⟨_, hb, hr⟩ := Finset.mem_filter.mp h
    exact hreach hr
  have hqne : q ≠ p.parts := fun h => hqb (h.symm ▸ b.property)
  obtain ⟨c, hcq, d, hdq, t, hts, htc, htd⟩ :=
    p.overlap_across_cut huv hs hq ⟨a₀, hqa⟩ hqne
  obtain ⟨hc, hcr, hr⟩ := Finset.mem_filter.mp hcq
  obtain ⟨hd, hdn⟩ := Finset.mem_sdiff.mp hdq
  have hcd : (⟨c, hc⟩ : {z // z ∈ p.parts}) ≠ ⟨d, hd⟩ := by
    intro he
    have hv := congrArg Subtype.val he
    change c = d at hv
    exact hdn (hv ▸ hcq)
  have had : (overlapGraph p).Reachable a ⟨d, hd⟩ := hr.trans
    (SimpleGraph.Adj.reachable ⟨hcd, t, hts, htc, htd⟩)
  exact hdn (Finset.mem_filter.mpr ⟨hd, hd, had⟩)

end Cubical.Simplicial
