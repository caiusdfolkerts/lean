module

public import cubical.simplicial_chains
public import cubical.circuit_decomposition

/-!
# Simplicial families and minimal cycles

The index set of a family is kept separate from its vertex sets, allowing two
copies of one simplex after a contraction.  Ordinary simplicial complexes are
the special case where the family map is injective.
-/

@[expose] public section

namespace Cubical.Simplicial

open scoped BigOperators

variable {V I : Type*} [DecidableEq V] [DecidableEq I]

theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  exact (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a

/-- The chain represented by a finite set of simplices. -/
noncomputable def setChain (s : Finset (Finset V)) : Chain V :=
  ∑ t ∈ s, Finsupp.single t 1

@[simp]
theorem setChain_apply (s : Finset (Finset V)) (t : Finset V) :
    setChain s t = if t ∈ s then 1 else 0 := by
  simp [setChain, Finsupp.single_apply]

@[simp]
theorem setChain_support (s : Finset (Finset V)) : (setChain s).support = s := by
  ext t
  simp [Finsupp.mem_support_iff, setChain_apply]

@[simp]
theorem setChain_support_eq (c : Chain V) : setChain c.support = c := by
  ext t
  rcases zmod_two_cases (c t) with h | h <;> simp [Finsupp.mem_support_iff, h]

theorem setChain_injective : Function.Injective (setChain (V := V)) := by
  intro s t h
  simpa using congrArg Finsupp.support h

/-- The chain represented by an indexed finite family, retaining multiplicities. -/
noncomputable def familyChain (σ : I → Finset V) (s : Finset I) : Chain V :=
  ∑ i ∈ s, Finsupp.single (σ i) 1

omit [DecidableEq I] in
theorem familyChain_eq_setChain_image (σ : I → Finset V) (s : Finset I)
    (hinj : Set.InjOn σ s) : familyChain σ s = setChain (s.image σ) := by
  rw [familyChain, setChain, Finset.sum_image hinj]

/-- A homogeneous family has `n` vertices in each of its facets. -/
def Pure (n : ℕ) (σ : I → Finset V) (s : Finset I) : Prop :=
  ∀ i ∈ s, (σ i).card = n

/-- The set of vertices used by an indexed simplicial family. -/
def vertices (σ : I → Finset V) (s : Finset I) : Finset V := s.biUnion σ

omit [DecidableEq I] in
@[simp]
theorem mem_vertices (σ : I → Finset V) (s : Finset I) (v : V) :
    v ∈ vertices σ s ↔ ∃ i ∈ s, v ∈ σ i := by
  simp [vertices]

/-- Minimal cycle condition on the augmented boundary columns. -/
abbrev IsFacetCircuit (σ : I → Finset V) (s : Finset I) : Prop :=
  Cubical.IsZeroSumCircuit (fun i => boundary (Finsupp.single (σ i) 1)) s

omit [DecidableEq I] in
theorem IsFacetCircuit.cycle {σ : I → Finset V} {s : Finset I}
    (h : IsFacetCircuit σ s) : boundary (familyChain σ s) = 0 := by
  simpa [familyChain, map_sum] using h.sum_eq_zero

/-- A repeated facet in a minimal cycle forces the two-copy trivial circuit. -/
theorem IsFacetCircuit.eq_pair_of_duplicate {σ : I → Finset V} {s : Finset I}
    (h : IsFacetCircuit σ s) {i j : I} (hi : i ∈ s) (hj : j ∈ s)
    (hij : i ≠ j) (hσ : σ i = σ j) : s = {i, j} := by
  symm
  apply h.minimal
  · simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, hi, hj]
  · simp
  · simp [hij, hσ, chain_add_self]

theorem IsFacetCircuit.injective_or_pair {σ : I → Finset V} {s : Finset I}
    (h : IsFacetCircuit σ s) :
    Set.InjOn σ s ∨ ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ σ i = σ j ∧ s = {i, j} := by
  classical
  by_cases hinj : Set.InjOn σ s
  · exact Or.inl hinj
  · right
    simp only [Set.InjOn] at hinj
    push Not at hinj
    obtain ⟨i, hi, j, hj, hσ, hij⟩ := hinj
    exact ⟨i, hi, j, hj, hij, hσ, h.eq_pair_of_duplicate hi hj hij hσ⟩

/-- The codimension-one faces of a simplex. -/
def simplexBoundary (s : Finset V) : Finset (Finset V) := s.image s.erase

theorem boundary_single_one_eq_setChain (s : Finset V) :
    boundary (Finsupp.single s 1) = setChain (simplexBoundary s) := by
  rw [boundary_single, setChain, simplexBoundary, Finset.sum_image (s.erase_injOn)]

theorem boundary_single_one_apply (s t : Finset V) :
    boundary (Finsupp.single s 1) t = if t ∈ simplexBoundary s then 1 else 0 := by
  rw [boundary_single_one_eq_setChain, setChain_apply]

theorem boundary_single_one_ne_zero (s : Finset V) (hs : s.Nonempty) :
    boundary (Finsupp.single s 1) ≠ 0 := by
  obtain ⟨v, hv⟩ := hs
  intro h
  have he := congrArg (fun c : Chain V => c (s.erase v)) h
  have hm : s.erase v ∈ simplexBoundary s := Finset.mem_image.mpr ⟨v, hv, rfl⟩
  rw [boundary_single_one_apply, ite_eq_left hm] at he
  exact one_ne_zero he

/-- Every codimension-one face in a cycle has another incident facet.
This is an incidence consequence of parity, not a manifold assumption. -/
theorem cycle_has_neighbor {s : Finset (Finset V)}
    (hcycle : boundary (setChain s) = 0) {t : Finset V} (ht : t ∈ s)
    {v : V} (hv : v ∈ t) :
    ∃ t' ∈ s, t' ≠ t ∧ t.erase v ∈ simplexBoundary t' := by
  classical
  by_contra hno
  push Not at hno
  have he := congrArg (fun c : Chain V => c (t.erase v)) hcycle
  have hm : t.erase v ∈ simplexBoundary t := Finset.mem_image.mpr ⟨v, hv, rfl⟩
  have hsum : (∑ t' ∈ s, boundary (Finsupp.single t' 1) (t.erase v)) = 1 := by
    rw [Finset.sum_eq_single t]
    · rw [boundary_single_one_apply, ite_eq_left hm]
    · intro t' ht' hne
      rw [boundary_single_one_apply, ite_eq_right (hno t' ht' hne)]
    · exact fun h => (h ht).elim
  exact one_ne_zero (by
    simpa only [setChain, map_sum, Finsupp.finsetSum_apply, Finsupp.zero_apply, hsum] using he)

theorem simplexBoundary_subset {s t : Finset V} (h : t ∈ simplexBoundary s) : t ⊆ s := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h
  exact Finset.erase_subset _ _

theorem simplexBoundary_card {s t : Finset V} (h : t ∈ simplexBoundary s) :
    t.card + 1 = s.card := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h
  exact Finset.card_erase_add_one hv

end Cubical.Simplicial
