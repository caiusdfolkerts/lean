module

public import cubical.simplicial_circuit_lifting
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-! # Homogeneity and the one-skeleton of simplicial cycles -/

@[expose] public section

namespace Cubical.Simplicial

open scoped BigOperators

variable {V I : Type*} [DecidableEq V] [DecidableEq I]

theorem boundary_support_mem {c : Chain V} {r : Finset V}
    (hr : r ∈ (boundary c).support) :
    ∃ t ∈ c.support, r ∈ simplexBoundary t := by
  have hn := Finsupp.mem_support_iff.mp hr
  rw [← setChain_support_eq c] at hn
  simp only [setChain, map_sum, Finsupp.finsetSum_apply] at hn
  obtain ⟨t, ht, htr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  refine ⟨t, ht, ?_⟩
  by_contra h
  exact htr (by rw [boundary_single_one_apply, if_neg h])

theorem pure_complete {u v : V} (huv : u ≠ v) {n : ℕ}
    {s : Finset (Finset V)} (hpure : Pure n id s) :
    Pure n id (complete u v (setChain s)).support := by
  intro t ht
  change t.card = n
  by_cases hts : t ∈ s
  · exact hpure t hts
  · have hn := Finsupp.mem_support_iff.mp ht
    rw [complete_coefficient huv, setChain_apply, if_neg hts, zero_add] at hn
    split_ifs at hn with he
    · obtain ⟨t', ht', hr⟩ := boundary_support_mem (Finsupp.mem_support_iff.mpr hn)
      have hc := simplexBoundary_card hr
      have hct := Finset.card_erase_add_one he.1
      have hp : t'.card = n := hpure t' (by simpa using ht')
      omega
    · exact (hn rfl).elim

/-- A neighboring facet across a ridge omits the removed vertex when the
cycle is homogeneous. -/
theorem cycle_has_neighbor_pure {n : ℕ} {s : Finset (Finset V)}
    (hpure : Pure n id s) (hcycle : boundary (setChain s) = 0)
    {t : Finset V} (ht : t ∈ s) {v : V} (hv : v ∈ t) :
    ∃ t' ∈ s, t' ≠ t ∧ t.erase v ⊆ t' ∧ v ∉ t' := by
  obtain ⟨t', ht', hne, hr⟩ := cycle_has_neighbor hcycle ht hv
  have hsub := simplexBoundary_subset hr
  refine ⟨t', ht', hne, hsub, ?_⟩
  intro hvt'
  have hsub' : t ⊆ t' := by
    intro x hx
    by_cases hxv : x = v
    · simpa [hxv] using hvt'
    · exact hsub (Finset.mem_erase.mpr ⟨hxv, hx⟩)
  have hct : t.card = n := hpure t ht
  have hct' : t'.card = n := hpure t' ht'
  exact hne (Finset.eq_of_subset_of_card_le hsub' (by omega)).symm

/-- The one-skeleton on an ambient vertex type. Vertices not used by the
family are isolated; rigidity statements use the induced support type. -/
def oneSkeleton (σ : I → Finset V) (s : Finset I) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ∃ i ∈ s, x ∈ σ i ∧ y ∈ σ i
  symm := ⟨by
    intro x y h
    obtain ⟨hne, i, hi, hx, hy⟩ := h
    exact ⟨hne.symm, i, hi, hy, hx⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

@[simp]
theorem oneSkeleton_adj (σ : I → Finset V) (s : Finset I) (x y : V) :
    (oneSkeleton σ s).Adj x y ↔
      x ≠ y ∧ ∃ i ∈ s, x ∈ σ i ∧ y ∈ σ i := Iff.rfl

/-- The graph of a family, with exactly its used vertices. -/
def supportGraph (σ : I → Finset V) (s : Finset I) :
    SimpleGraph {v // v ∈ vertices σ s} :=
  (oneSkeleton σ s).induce (vertices σ s : Set V)

theorem oneSkeleton_mono {σ : I → Finset V} {s t : Finset I} (h : s ⊆ t) :
    oneSkeleton σ s ≤ oneSkeleton σ t := by
  rintro x y ⟨hne, i, hi, hx, hy⟩
  exact ⟨hne, i, h hi, hx, hy⟩

theorem complete_oneSkeleton_le {u v : V} (huv : u ≠ v)
    {n : ℕ} {s t : Finset (Finset V)}
    (hpure : Pure n id s) (hsub : s ⊆ t)
    (hoff : ∀ a ∈ s, ¬(u ∈ a ∧ v ∈ a))
    (hcycle : boundary (complete u v (setChain s)) = 0)
    (he : (oneSkeleton id t).Adj u v) :
    oneSkeleton id (complete u v (setChain s)).support ≤ oneSkeleton id t := by
  let L := (complete u v (setChain s)).support
  have hpL : Pure n id L := pure_complete huv hpure
  have hcL : boundary (setChain L) = 0 := by
    simpa only [L, setChain_support_eq] using hcycle
  have hoL : offEdge u v L = s := offEdge_complete_support huv s hoff
  rintro x y ⟨hxy, a, ha, hx, hy⟩
  change a ∈ L at ha
  by_cases has : a ∈ s
  · exact ⟨hxy, a, hsub has, hx, hy⟩
  have hua : u ∈ a := by
    by_contra h
    have ham : a ∈ offEdge u v L := by simp [ha, h]
    exact has (hoL ▸ ham)
  have hva : v ∈ a := by
    by_contra h
    have ham : a ∈ offEdge u v L := by simp [ha, h]
    exact has (hoL ▸ ham)
  by_cases hxu : x = u
  · subst x
    by_cases hyv : y = v
    · simpa [hyv] using he
    · obtain ⟨a', ha', _, hss, hv'⟩ := cycle_has_neighbor_pure hpL hcL ha hva
      have ha's : a' ∈ s := hoL ▸ (by simp [ha', hv'] : a' ∈ offEdge u v L)
      exact ⟨hxy, a', hsub ha's,
        hss (Finset.mem_erase.mpr ⟨huv, hua⟩),
        hss (Finset.mem_erase.mpr ⟨hyv, hy⟩)⟩
  · by_cases hyu : y = u
    · subst y
      by_cases hxv : x = v
      · simpa [hxv] using he.symm
      · obtain ⟨a', ha', _, hss, hv'⟩ := cycle_has_neighbor_pure hpL hcL ha hva
        have ha's : a' ∈ s := hoL ▸ (by simp [ha', hv'] : a' ∈ offEdge u v L)
        exact ⟨hxy, a', hsub ha's,
          hss (Finset.mem_erase.mpr ⟨hxv, hx⟩),
          hss (Finset.mem_erase.mpr ⟨huv, hua⟩)⟩
    · obtain ⟨a', ha', _, hss, hu'⟩ := cycle_has_neighbor_pure hpL hcL ha hua
      have ha's : a' ∈ s := hoL ▸ (by simp [ha', hu'] : a' ∈ offEdge u v L)
      exact ⟨hxy, a', hsub ha's,
        hss (Finset.mem_erase.mpr ⟨hxu, hx⟩),
        hss (Finset.mem_erase.mpr ⟨hyu, hy⟩)⟩

/-- In a pure cycle with facets of size at least three, every edge has
at least `n - 1` common neighbors. This uses a second facet across a ridge,
not an assumption about links or a topological manifold. -/
theorem cycle_common_neighbors {n : ℕ} (hn : 3 ≤ n)
    {s : Finset (Finset V)} (hpure : Pure n id s)
    (hcycle : boundary (setChain s) = 0) {u v : V}
    (he : (oneSkeleton id s).Adj u v) :
    ∃ c : Finset V, c.card + 1 = n ∧
      ∀ w ∈ c, (oneSkeleton id s).Adj u w ∧ (oneSkeleton id s).Adj v w := by
  obtain ⟨huv, t, ht, hu, hv⟩ := he
  change u ∈ t at hu
  change v ∈ t at hv
  have hct : t.card = n := hpure t ht
  obtain ⟨x, hxt, hxu, hxv⟩ : ∃ x ∈ t, x ≠ u ∧ x ≠ v := by
    by_contra h
    push Not at h
    have hsub : t ⊆ {u, v} := by
      intro x hx
      by_cases hxu : x = u
      · simp [hxu]
      · simp [h x hx hxu]
    have hc := Finset.card_le_card hsub
    have hp : ({u, v} : Finset V).card ≤ 2 := by simp [huv]
    omega
  obtain ⟨t', ht', hne, hsub, hxn⟩ := cycle_has_neighbor_pure hpure hcycle ht hxt
  have hct' : t'.card = n := hpure t' ht'
  obtain ⟨w, hwt', hwnt⟩ : ∃ w ∈ t', w ∉ t := by
    by_contra h
    push Not at h
    exact hne (Finset.eq_of_subset_of_card_le h (by omega))
  let c := insert w ((t.erase u).erase v)
  have hwc : w ∉ (t.erase u).erase v := fun h =>
    hwnt (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
  refine ⟨c, ?_, ?_⟩
  · have hc1 := Finset.card_erase_add_one hu
    have hc2 := Finset.card_erase_add_one
      (Finset.mem_erase.mpr ⟨huv.symm, hv⟩ : v ∈ t.erase u)
    dsimp [c]
    rw [Finset.card_insert_of_notMem hwc]
    omega
  · intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · have hut' := hsub (Finset.mem_erase.mpr ⟨hxu.symm, hu⟩)
      have hvt' := hsub (Finset.mem_erase.mpr ⟨hxv.symm, hv⟩)
      exact ⟨⟨by intro h; exact hwnt (h ▸ hu), t', ht', hut', hwt'⟩,
        ⟨by intro h; exact hwnt (h ▸ hv), t', ht', hvt', hwt'⟩⟩
    · obtain ⟨hzv, hzu, hzt⟩ := Finset.mem_erase.mp hz |>.imp_right Finset.mem_erase.mp
      exact ⟨⟨hzu.symm, t, ht, hu, hzt⟩, ⟨hzv.symm, t, ht, hv, hzt⟩⟩

/-- A nonzero cycle whose facets away from an edge lie in a minimal
cycle must itself contain that edge. -/
theorem cycle_contains_edge_of_offEdge_subset {u v : V}
    {s t : Finset (Finset V)} (hs : IsFacetCircuit id s)
    (htne : t.Nonempty) (htcycle : boundary (setChain t) = 0)
    (hsub : offEdge u v t ⊆ s) (he : (oneSkeleton id s).Adj u v) :
    (oneSkeleton id t).Adj u v := by
  obtain ⟨huv, a, ha, hua, hva⟩ := he
  by_contra h
  have hoff : ∀ b ∈ t, ¬(u ∈ b ∧ v ∈ b) := by
    intro b hb he
    exact h ⟨huv, b, hb, he⟩
  have hts : t ⊆ s := by
    intro b hb
    exact hsub ((mem_offEdge u v t b).mpr ⟨hb, hoff b hb⟩)
  have hEq : t = s := hs.minimal t hts htne
    (by simpa only [setChain, map_sum, id_eq] using htcycle)
  exact hoff a (hEq.symm ▸ ha) ⟨hua, hva⟩

/-- Completion introduces facets, but no new vertices. -/
theorem complete_vertices_eq {u v : V} (huv : u ≠ v)
    {n : ℕ} {s : Finset (Finset V)}
    (hpure : Pure n id s) (hoff : ∀ a ∈ s, ¬(u ∈ a ∧ v ∈ a))
    (hcycle : boundary (complete u v (setChain s)) = 0) :
    vertices id (complete u v (setChain s)).support = vertices id s := by
  let L := (complete u v (setChain s)).support
  have hpL : Pure n id L := pure_complete huv hpure
  have hcL : boundary (setChain L) = 0 := by
    simpa only [L, setChain_support_eq] using hcycle
  have hoL : offEdge u v L = s := offEdge_complete_support huv s hoff
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨a, ha, hxa⟩ := (mem_vertices id L x).mp hx
    by_cases has : a ∈ s
    · exact (mem_vertices id s x).mpr ⟨a, has, hxa⟩
    have hua : u ∈ a := by
      by_contra h
      have ham : a ∈ offEdge u v L := by simp [ha, h]
      exact has (hoL ▸ ham)
    have hva : v ∈ a := by
      by_contra h
      have ham : a ∈ offEdge u v L := by simp [ha, h]
      exact has (hoL ▸ ham)
    by_cases hxu : x = u
    · subst x
      obtain ⟨a', ha', _, hss, hv'⟩ := cycle_has_neighbor_pure hpL hcL ha hva
      have ha's : a' ∈ s := hoL ▸ (by simp [ha', hv'] : a' ∈ offEdge u v L)
      exact (mem_vertices id s u).mpr
        ⟨a', ha's, hss (Finset.mem_erase.mpr ⟨huv, hua⟩)⟩
    · obtain ⟨a', ha', _, hss, hu'⟩ := cycle_has_neighbor_pure hpL hcL ha hua
      have ha's : a' ∈ s := hoL ▸ (by simp [ha', hu'] : a' ∈ offEdge u v L)
      exact (mem_vertices id s x).mpr
        ⟨a', ha's, hss (Finset.mem_erase.mpr ⟨hxu, hxa⟩)⟩
  · intro x hx
    obtain ⟨a, ha, hxa⟩ := (mem_vertices id s x).mp hx
    have haL : a ∈ L := (mem_offEdge u v L a).mp (hoL.symm ▸ ha) |>.1
    exact (mem_vertices id L x).mpr ⟨a, haL, hxa⟩

def collapse (u v x : V) : V := if x = v then u else x

theorem collapse_eq_iff {u v : V} (huv : u ≠ v) (x y : V) :
    collapse u v x = collapse u v y ↔
      x = y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  by_cases hx : x = v <;> by_cases hy : y = v
  · simp [collapse, hx, hy]
  · simp [collapse, hx, hy, Ne.symm hy, huv, huv.symm, eq_comm]
  · simp [collapse, hx, hy, huv, huv.symm]
  · simp [collapse, hx, hy]

theorem oneSkeleton_adj_vertices {σ : I → Finset V} {s : Finset I} {x y : V}
    (h : (oneSkeleton σ s).Adj x y) : x ∈ vertices σ s ∧ y ∈ vertices σ s := by
  obtain ⟨_, t, ht, hx, hy⟩ := h
  exact ⟨(mem_vertices σ s x).mpr ⟨t, ht, hx⟩,
    (mem_vertices σ s y).mpr ⟨t, ht, hy⟩⟩

theorem pure_nonempty_has_edge {n : ℕ} (hn : 2 ≤ n)
    {s : Finset (Finset V)} (hpure : Pure n id s) (hne : s.Nonempty) :
    ∃ u v : V, (oneSkeleton id s).Adj u v := by
  obtain ⟨t, ht⟩ := hne
  have hc : 1 < t.card := by have := hpure t ht; change t.card = n at this; omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hc
  exact ⟨u, v, huv, t, ht, hu, hv⟩

theorem contractedSimplex_eq_image (u v : V) (s : Finset V) :
    contractedSimplex u v s = s.image (collapse u v) := by
  ext x
  by_cases hv : v ∈ s
  · simp only [contractedSimplex, ite_eq_left hv, Finset.mem_insert, Finset.mem_erase,
      Finset.mem_image, collapse]
    constructor
    · rintro (rfl | ⟨hne, hx⟩)
      · exact ⟨v, hv, by simp⟩
      · exact ⟨x, hx, by simp [hne]⟩
    · rintro ⟨y, hy, he⟩
      by_cases hyv : y = v
      · left
        simpa [hyv] using he.symm
      · right
        have hyx : y = x := by simpa [hyv] using he
        subst y
        exact ⟨hyv, hy⟩
  · simp only [contractedSimplex, ite_eq_right hv, Finset.mem_image]
    constructor
    · intro hx
      refine ⟨x, hx, ?_⟩
      have hne : x ≠ v := fun he => hv (he ▸ hx)
      simp [collapse, hne]
    · rintro ⟨y, hy, he⟩
      have hne : y ≠ v := fun he => hv (he ▸ hy)
      have hyx : y = x := by simpa [collapse, hne] using he
      exact hyx ▸ hy

theorem contractedSimplex_card {u v : V} {s : Finset V}
    (hoff : ¬(u ∈ s ∧ v ∈ s)) : (contractedSimplex u v s).card = s.card := by
  by_cases hv : v ∈ s
  · have hu : u ∉ s := fun h => hoff ⟨h, hv⟩
    have huer : u ∉ s.erase v := fun h => hu (Finset.mem_of_mem_erase h)
    rw [contractedSimplex, ite_eq_left hv, Finset.card_insert_of_notMem huer]
    exact Finset.card_erase_add_one hv
  · simp [contractedSimplex, hv]

theorem contractedSimplex_notMem {u v : V} (huv : u ≠ v) (s : Finset V) :
    v ∉ contractedSimplex u v s := by
  by_cases hv : v ∈ s <;> simp [contractedSimplex, hv, huv.symm]

theorem contracted_vertices {u v : V} (huv : u ≠ v)
    (s : Finset (Finset V)) (hu : u ∈ vertices id s) :
    vertices (contractedSimplex u v) s = (vertices id s).erase v := by
  ext x
  simp only [mem_vertices, Finset.mem_erase, id_eq]
  constructor
  · rintro ⟨a, ha, hxa⟩
    refine ⟨fun hxv => contractedSimplex_notMem huv a (hxv ▸ hxa), ?_⟩
    by_cases hva : v ∈ a
    · rw [contractedSimplex, ite_eq_left hva] at hxa
      rcases Finset.mem_insert.mp hxa with rfl | hx
      · simpa only [mem_vertices, id_eq] using hu
      · exact ⟨a, ha, Finset.mem_of_mem_erase hx⟩
    · exact ⟨a, ha, by simpa [contractedSimplex, hva] using hxa⟩
  · rintro ⟨hxv, a, ha, hxa⟩
    refine ⟨a, ha, ?_⟩
    by_cases hva : v ∈ a
    · simp [contractedSimplex, hva, hxv, hxa]
    · simpa [contractedSimplex, hva] using hxa

end Cubical.Simplicial
