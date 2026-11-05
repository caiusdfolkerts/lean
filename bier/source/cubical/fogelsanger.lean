import cubical.simplicial_reindex
import cubical.simplicial_rigid_splitting
import cubical.generic_gluing
import cubical.rigidity_count

/-!
# Fogelsanger rigidity for finite minimal simplicial cycles

For `n ≥ 3`, the graph of every finite homogeneous minimal simplicial
cycle with `n` vertices in each facet is generically rigid in dimension
`n`. The proof includes indexed circuits, so duplicate facets after
contraction are handled by the complete-graph base case. An arbitrary
circuit is contracted, partitioned into minimal indexed cycles, lifted
by the explicit chain homotopy, split back geometrically, and glued
along its connected facet-overlap graph.
-/

namespace Cubical.Simplicial

open Module
open Cubical.Rigidity

variable {V E : Type*} [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Every lifted piece uses only vertices of the original simplicial
circuit. -/
theorem EdgeCircuitPartition.lifted_vertices_subset {u v : V} (huv : u ≠ v)
    {s : Finset (Finset V)} (p : EdgeCircuitPartition u v s)
    {n : ℕ} (hpure : Pure n id s) {a : Finset (Finset V)} (ha : a ∈ p.parts) :
    vertices id (liftedPart u v a) ⊆ vertices id s := by
  rw [p.lifted_vertices_eq huv hpure ha]
  intro x hx
  obtain ⟨t, ht, hxt⟩ := (mem_vertices id a x).mp hx
  exact (mem_vertices id s x).mpr
    ⟨t, ((mem_offEdge u v s t).mp (p.part_subset ha ht)).1, hxt⟩

/-- The lifted parts glue back to a generically rigid original graph. -/
theorem EdgeCircuitPartition.gluing {u v : V} (huv : u ≠ v)
    {s : Finset (Finset V)} (p : EdgeCircuitPartition u v s)
    {n : ℕ} (hn : 3 ≤ n) (hpure : Pure n id s)
    (hs : IsFacetCircuit id s) (he : (oneSkeleton id s).Adj u v)
    (hdim : finrank ℝ E = n)
    (hlocal : ∀ a ∈ p.parts,
      GenericallyRigid (supportGraph id (liftedPart u v a)) E) :
    GenericallyRigid (supportGraph id s) E := by
  classical
  let P := {a // a ∈ p.parts}
  let X := {x // x ∈ vertices id s}
  let W : P → Type _ := fun a => {x // x ∈ vertices id (liftedPart u v a.val)}
  let piece : ∀ a : P, SimpleGraph (W a) := fun a => supportGraph id (liftedPart u v a.val)
  let inc : ∀ a : P, W a ↪ X := fun a =>
    ⟨fun x => ⟨x.val, p.lifted_vertices_subset huv hpure a.property x.property⟩,
      fun x y h => Subtype.ext (congrArg (fun z : X => z.val) h)⟩
  have hsub : ∀ a x y, (piece a).Adj x y →
      (supportGraph id s).Adj (inc a x) (inc a y) := by
    intro a x y hxy
    exact p.lifted_graph_le huv hpure he a.property hxy
  have hcycle : boundary (setChain s) = 0 := by
    simpa only [familyChain, setChain, id_eq] using hs.cycle
  have hcover : ∀ x : X, ∃ a w, inc a w = x := by
    intro x
    obtain ⟨t, ht, hxt⟩ := (mem_vertices id s x.val).mp x.property
    obtain ⟨a, ha, hta⟩ := p.facet_covered huv hcycle ht
    refine ⟨⟨a, ha⟩, ⟨x.val, (mem_vertices id _ x.val).mpr ⟨t, hta, hxt⟩⟩, ?_⟩
    rfl
  have hexcommon : ∀ a b : P, ∃ c : Finset X, ∀ hab : (overlapGraph p).Adj a b,
      (∀ x ∈ c, x ∈ Set.range (inc a) ∧ x ∈ Set.range (inc b)) ∧
        finrank ℝ E ≤ c.card := by
    intro a b
    by_cases hab : (overlapGraph p).Adj a b
    · obtain ⟨_, t, _, hta, htb⟩ := hab
      let emb : t ↪ X := ⟨fun x => ⟨x.val,
        p.lifted_vertices_subset huv hpure a.property
          ((mem_vertices id _ x.val).mpr ⟨t, hta, x.property⟩)⟩,
        fun x y h => Subtype.ext (congrArg (fun z : X => z.val) h)⟩
      let c : Finset X := Finset.univ.map emb
      refine ⟨c, fun _ => ⟨?_, ?_⟩⟩
      · intro x hx
        obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hx
        constructor
        · exact ⟨⟨y.val, (mem_vertices id _ y.val).mpr ⟨t, hta, y.property⟩⟩, rfl⟩
        · exact ⟨⟨y.val, (mem_vertices id _ y.val).mpr ⟨t, htb, y.property⟩⟩, rfl⟩
      · have hc : c.card = t.card := by simp [c]
        have htcard := p.lifted_pure huv hpure a.property t hta
        change t.card = n at htcard
        omega
    · exact ⟨∅, fun h => (hab h).elim⟩
  choose common hcommon using hexcommon
  exact genericallyRigid_of_connected_cover (supportGraph id s) (overlapGraph p)
    (p.overlap_connected huv hs) piece inc hsub hcover common
    (fun a b h => (hcommon a b h).1) (fun a b h => (hcommon a b h).2)
    (by omega) (fun a => hlocal a.val a.property)

/-- The inductive form uses facet-set indices, which include every
indexed family created by a contraction. -/
private theorem fogelsanger_indexed_aux {n : ℕ} (hn : 3 ≤ n)
    (hdim : finrank ℝ E = n) (σ : Finset V → Finset V)
    (s : Finset (Finset V)) (hpure : Pure n σ s) (hs : IsFacetCircuit σ s) :
    GenericallyRigid (supportGraph σ s) E := by
  classical
  have aux : ∀ m : ℕ, ∀ (τ : Finset V → Finset V) (r : Finset (Finset V)),
      (vertices τ r).card = m → Pure n τ r → IsFacetCircuit τ r →
        GenericallyRigid (supportGraph τ r) E := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro τ r hm hpure hcycle
      rcases hcycle.injective_or_pair with hinj | ⟨i, hi, j, hj, hij, hτ, hr⟩
      · let S := r.image τ
        have hS : IsFacetCircuit id S := hcycle.image hinj
        have hpS : Pure n id S := hpure.image
        have hcardS : (vertices id S).card = m := by simpa only [S, vertices_image] using hm
        have hboundary : boundary (setChain S) = 0 := by
          simpa only [familyChain, setChain, id_eq] using hS.cycle
        obtain ⟨u, v, he⟩ := pure_nonempty_has_edge (by omega : 2 ≤ n) hpS hS.nonempty
        have huv : u ≠ v := he.ne
        obtain ⟨p⟩ := edgeCircuitPartition_exists huv hboundary
        have hparts : ∀ a ∈ p.parts,
            GenericallyRigid (supportGraph id (liftedPart u v a)) E := by
          intro a ha
          have hlt : (vertices (contractedSimplex u v) a).card < m := by
            rw [← hcardS]
            exact p.contracted_vertices_card_lt huv he ha
          have hc := ih _ hlt (contractedSimplex u v) a rfl
            (p.contracted_pure hpS ha) (p.circuit a ha)
          exact p.lifted_genericallyRigid huv hn hpS hS he ha hc hdim
        have hrigid : GenericallyRigid (supportGraph id S) E :=
          p.gluing huv hn hpS hS he hdim hparts
        exact hrigid.of_iso (supportGraphImageIso τ r).symm
      · exact genericallyRigid_pair hpure hi hτ hr hdim
  exact aux (vertices σ s).card σ s rfl hpure hs

/-- **Fogelsanger's minimal cycle rigidity theorem**, including indexed
facet families: in dimension `n ≥ 3`, the support graph of every finite
minimal homogeneous simplicial cycle whose facets have `n` vertices is
generically infinitesimally rigid in Euclidean dimension `n`.

The cycle condition is the augmented simplicial boundary over `ZMod 2`;
minimality is among nonempty indexed subfamilies. -/
theorem IsFacetCircuit.genericallyRigid {I : Type*} [DecidableEq I]
    {n : ℕ} {σ : I → Finset V} {s : Finset I}
    (hs : IsFacetCircuit σ s) (hn : 3 ≤ n) (hpure : Pure n σ s)
    (hdim : finrank ℝ E = n) :
    GenericallyRigid (supportGraph σ s) E := by
  classical
  rcases hs.injective_or_pair with hinj | ⟨i, hi, j, hj, hij, hσ, hs⟩
  · have h := fogelsanger_indexed_aux hn hdim id (s.image σ) hpure.image (hs.image hinj)
    exact h.of_iso (supportGraphImageIso σ s).symm
  · exact genericallyRigid_pair hpure hi hσ hs hdim

/-- The edge-count consequence of minimal simplicial cycle rigidity. -/
theorem IsFacetCircuit.edge_count {I : Type*} [DecidableEq I]
    {n : ℕ} {σ : I → Finset V} {s : Finset I}
    (hs : IsFacetCircuit σ s) (hn : 3 ≤ n) (hpure : Pure n σ s)
    [Fintype (supportGraph σ s).edgeSet] :
    n * (vertices σ s).card ≤ Fintype.card (supportGraph σ s).edgeSet + (n + 1).choose 2 := by
  obtain ⟨p, hp⟩ := hs.genericallyRigid (E := EuclideanSpace ℝ (Fin n)) hn hpure (by simp)
  simpa only [finrank_euclideanSpace, Fintype.card_fin, Fintype.card_coe] using hp.edge_count

end Cubical.Simplicial
