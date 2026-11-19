module

public import cubical.simplicial_families
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Connected simplicial pseudomanifolds are minimal `𝔽₂` cycles

The hypotheses are explicit finite incidence and dual-graph connectivity.
No topological classification or rigidity property is assumed.
-/

@[expose] public section

namespace Cubical.Simplicial

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

theorem boundary_setChain_apply (s : Finset (Finset V)) (r : Finset V) :
    boundary (setChain s) r =
      ((s.filter (fun t => r ∈ simplexBoundary t)).card : ZMod 2) := by
  simp only [setChain, map_sum, Finsupp.finsetSum_apply, boundary_single_one_apply]
  exact Finset.sum_boole _ _

/-- The graph of facets joined across codimension-one faces. -/
def facetGraph (s : Finset (Finset V)) : SimpleGraph {t // t ∈ s} where
  Adj t t' := t ≠ t' ∧ ∃ r, r ∈ simplexBoundary t.val ∧ r ∈ simplexBoundary t'.val
  symm := ⟨by rintro t t' ⟨hne, r, ht, ht'⟩; exact ⟨hne.symm, r, ht', ht⟩⟩
  loopless := ⟨by intro t; simp⟩

/-- Every ridge is either absent or incident to exactly two facets. -/
def RidgeDegreeTwo (s : Finset (Finset V)) : Prop :=
  ∀ r : Finset V, (s.filter (fun t => r ∈ simplexBoundary t)).card = 0 ∨
    (s.filter (fun t => r ∈ simplexBoundary t)).card = 2

theorem RidgeDegreeTwo.cycle {s : Finset (Finset V)} (h : RidgeDegreeTwo s) :
    boundary (setChain s) = 0 := by
  ext r
  rw [boundary_setChain_apply]
  rcases h r with hz | ht
  · norm_num [hz]
  · rw [ht]
    change (2 : ZMod 2) = 0
    decide

theorem RidgeDegreeTwo.closed_under_dual_adj {s t : Finset (Finset V)}
    (hdeg : RidgeDegreeTwo s) (hts : t ⊆ s) (hcycle : boundary (setChain t) = 0)
    {a b : {x // x ∈ s}} (hab : (facetGraph s).Adj a b) (ha : a.val ∈ t) :
    b.val ∈ t := by
  obtain ⟨hne, r, hra, hrb⟩ := hab
  have hne' : a.val ≠ b.val := by intro h; exact hne (Subtype.ext h)
  have hfa : a.val ∈ s.filter (fun x => r ∈ simplexBoundary x) :=
    Finset.mem_filter.mpr ⟨a.property, hra⟩
  have hfb : b.val ∈ s.filter (fun x => r ∈ simplexBoundary x) :=
    Finset.mem_filter.mpr ⟨b.property, hrb⟩
  have hcard : (s.filter (fun x => r ∈ simplexBoundary x)).card = 2 := by
    rcases hdeg r with hz | ht
    · have := Finset.card_pos.mpr ⟨a.val, hfa⟩
      omega
    · exact ht
  have hpair : ({a.val, b.val} : Finset (Finset V)) =
      s.filter (fun x => r ∈ simplexBoundary x) := by
    apply Finset.eq_of_subset_of_card_le
    · simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, hfa, hfb]
    · simp [hcard, hne']
  obtain ⟨v, hv, hvr⟩ := Finset.mem_image.mp hra
  have hvr' : a.val.erase v = r := hvr
  obtain ⟨c, hct, hcne, hcr⟩ := cycle_has_neighbor hcycle ha hv
  have hcf : c ∈ s.filter (fun x => r ∈ simplexBoundary x) := by
    refine Finset.mem_filter.mpr ⟨hts hct, ?_⟩
    simpa [hvr'] using hcr
  rw [← hpair] at hcf
  rcases Finset.mem_insert.mp hcf with heq | heq
  · exact (hcne heq).elim
  · have hcb : c = b.val := Finset.mem_singleton.mp heq
    simpa [hcb] using hct

/-- A finite connected simplicial pseudomanifold is a minimal augmented `𝔽₂`
cycle. This is the combinatorial bridge used for convex polytope boundaries. -/
theorem facetCircuit_of_ridgeDegreeTwo_connected {s : Finset (Finset V)}
    (hdeg : RidgeDegreeTwo s) (hconn : (facetGraph s).Connected) :
    IsFacetCircuit id s := by
  have hne : s.Nonempty := by
    obtain ⟨a⟩ := hconn.nonempty
    exact ⟨a.val, a.property⟩
  refine ⟨hne, ?_, ?_⟩
  · simpa only [setChain, map_sum, id_eq] using hdeg.cycle
  · intro t hts htne htz
    have hcycle : boundary (setChain t) = 0 := by
      simpa only [setChain, map_sum, id_eq] using htz
    obtain ⟨a, ha⟩ := htne
    have hwalk : ∀ {x y : {z // z ∈ s}}, (facetGraph s).Walk x y →
        x.val ∈ t → y.val ∈ t := by
      intro x y w
      induction w with
      | nil => exact id
      | @cons x y z hxy w ih =>
          intro hx
          exact ih (hdeg.closed_under_dual_adj hts hcycle hxy hx)
    apply Finset.Subset.antisymm hts
    intro b hb
    obtain ⟨w⟩ := hconn ⟨a, hts ha⟩ ⟨b, hb⟩
    exact hwalk w ha

end Cubical.Simplicial
