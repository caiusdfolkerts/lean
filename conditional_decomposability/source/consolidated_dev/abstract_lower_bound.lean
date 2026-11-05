module
public import consolidated.deletion_geometry
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Basis.Bilinear
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Polynomial
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic
public import Mathlib.Topology.Algebra.Module.Cardinality
public import Mathlib.Topology.Baire.Lemmas

set_option Elab.async false

section BundlePart0
/- Source: Cubical/SimplicialChains.lean -/







/-!
# Finite simplicial chains over `𝔽₂`

Chains are finitely supported functions on finite vertex sets.  The empty
simplex is retained, so the boundary is the augmented boundary.  No topological
or rigidity assertion is built into these definitions.
-/

@[expose] public section

namespace Cubical.Simplicial

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

abbrev Chain (V : Type*) := Finset V →₀ ZMod 2

omit [DecidableEq V] in
@[simp]
theorem chain_add_self (c : Chain V) : c + c = 0 := by
  ext s
  exact CharTwo.add_self_eq_zero (c s)

/-- The augmented simplicial boundary over the field with two elements. -/
noncomputable def boundary : Chain V →ₗ[ZMod 2] Chain V :=
  Finsupp.linearCombination (ZMod 2)
    (fun s : Finset V => ∑ v ∈ s, Finsupp.single (s.erase v) 1)

@[simp]
theorem boundary_single (s : Finset V) (a : ZMod 2) :
    boundary (Finsupp.single s a) = ∑ v ∈ s, Finsupp.single (s.erase v) a := by
  simp [boundary, Finset.smul_sum, Finsupp.smul_single]

theorem boundary_boundary_single (s : Finset V) (a : ZMod 2) :
    boundary (boundary (Finsupp.single s a)) = 0 := by
  simp only [boundary_single, map_sum]
  rw [Finset.sum_sigma']
  refine Finset.sum_involution (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_
  · intro p hp
    dsimp
    rw [Finset.erase_right_comm]
    exact chain_add_self _
  · intro p hp _ hfix
    have hp' := Finset.mem_sigma.mp hp
    have hne := (Finset.mem_erase.mp hp'.2).1
    exact hne (congrArg Sigma.fst hfix)
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_erase] at hp ⊢
    exact ⟨hp.2.2, Ne.symm hp.2.1, hp.1⟩
  · intro p hp
    rfl

theorem boundary_comp_boundary :
    (boundary (V := V)).comp boundary = 0 := by
  apply Finsupp.lhom_ext
  intro s a
  exact boundary_boundary_single s a

@[simp]
theorem boundary_boundary (c : Chain V) : boundary (boundary c) = 0 :=
  LinearMap.congr_fun boundary_comp_boundary c

/-- Cone a chain to a vertex; simplices already containing the vertex map to zero. -/
noncomputable def cone (v : V) : Chain V →ₗ[ZMod 2] Chain V :=
  Finsupp.linearCombination (ZMod 2)
    (fun s : Finset V => if v ∈ s then 0 else Finsupp.single (insert v s) 1)

@[simp]
theorem cone_single (v : V) (s : Finset V) (a : ZMod 2) :
    cone v (Finsupp.single s a) =
      if v ∈ s then 0 else Finsupp.single (insert v s) a := by
  by_cases hv : v ∈ s <;> simp [cone, hv, Finsupp.smul_single]

theorem boundary_cone_add_cone_boundary_single (v : V) (s : Finset V) (a : ZMod 2) :
    boundary (cone v (Finsupp.single s a)) + cone v (boundary (Finsupp.single s a)) =
      Finsupp.single s a := by
  by_cases hv : v ∈ s
  · simp only [cone_single, hv, ↓reduceIte, map_zero, zero_add, boundary_single, map_sum]
    rw [Finset.sum_eq_single v]
    · simp [Finset.insert_erase hv]
    · intro w hw hwv
      simp [Finset.mem_erase, hwv.symm, hv]
    · exact fun h => (h hv).elim
  · simp only [cone_single, hv, ↓reduceIte, boundary_single, map_sum]
    rw [Finset.sum_insert hv]
    have heq : (∑ w ∈ s, Finsupp.single ((insert v s).erase w) a) =
        ∑ w ∈ s, cone v (Finsupp.single (s.erase w) a) := by
      apply Finset.sum_congr rfl
      intro w hw
      have hwv : w ≠ v := by intro h; subst w; exact hv hw
      simp [cone_single, hv, Finset.erase_insert_of_ne hwv.symm]
    rw [heq]
    simp only [cone_single, Finset.mem_erase, hv, and_false, ↓reduceIte]
    rw [add_assoc, chain_add_self, add_zero]
    rw [Finset.erase_insert hv]

theorem boundary_cone_add_cone_boundary (v : V) (c : Chain V) :
    boundary (cone v c) + cone v (boundary c) = c := by
  have h : (boundary (V := V)).comp (cone v) + (cone v).comp boundary = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro s a
    exact boundary_cone_add_cone_boundary_single v s a
  exact LinearMap.congr_fun h c

end Cubical.Simplicial

end
end BundlePart0

section BundlePart1
/- Source: Cubical/CircuitDecomposition.lean -/






/-! # Decomposition of a finite zero-sum family into minimal zero-sum families -/

@[expose] public section

namespace Cubical

open scoped BigOperators

variable {I W : Type*} [DecidableEq I] [AddCommGroup W]

/-- A nonempty zero-sum family with no nonempty proper zero-sum subfamily.
Indices are retained, so repeated vectors cause no loss of multiplicity. -/
structure IsZeroSumCircuit (f : I → W) (s : Finset I) : Prop where
  nonempty : s.Nonempty
  sum_eq_zero : ∑ i ∈ s, f i = 0
  minimal : ∀ t ⊆ s, t.Nonempty → (∑ i ∈ t, f i) = 0 → t = s

theorem exists_zeroSumCircuit_subset (f : I → W) (s : Finset I)
    (hne : s.Nonempty) (hsum : ∑ i ∈ s, f i = 0) :
    ∃ t ⊆ s, IsZeroSumCircuit f t := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hmin : ∀ t ⊆ s, t.Nonempty → (∑ i ∈ t, f i) = 0 → t = s
    · exact ⟨s, Finset.Subset.rfl, ⟨hne, hsum, hmin⟩⟩
    · push Not at hmin
      obtain ⟨t, hts, htne, htz, htneq⟩ := hmin
      obtain ⟨u, hut, hu⟩ := ih t (Finset.ssubset_iff_subset_ne.mpr ⟨hts, htneq⟩) htne htz
      exact ⟨u, hut.trans hts, hu⟩

/-- A finite partition with minimal zero-sum parts. -/
structure ZeroSumCircuitPartition (f : I → W) (s : Finset I) where
  parts : Finset (Finset I)
  circuit : ∀ t ∈ parts, IsZeroSumCircuit f t
  pairwise_disjoint : (↑parts : Set (Finset I)).Pairwise Disjoint
  cover : parts.biUnion id = s

theorem zeroSumCircuitPartition_exists (f : I → W) (s : Finset I)
    (hsum : ∑ i ∈ s, f i = 0) : Nonempty (ZeroSumCircuitPartition f s) := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases he : s = ∅
    · subst s
      exact ⟨⟨∅, by simp, by simp, by simp⟩⟩
    · have hne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr he
      obtain ⟨t, hts, ht⟩ := exists_zeroSumCircuit_subset f s hne hsum
      have hstrict : s \ t ⊂ s := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩
        intro heq
        obtain ⟨i, hi⟩ := ht.nonempty
        have hin : i ∈ s \ t := by
          rw [heq]
          exact hts hi
        exact (Finset.mem_sdiff.mp hin).2 hi
      have hrem : ∑ i ∈ s \ t, f i = 0 := by
        have h := Finset.sum_sdiff hts (f := f)
        simpa [hsum, ht.sum_eq_zero] using h
      obtain ⟨p⟩ := ih (s \ t) hstrict hrem
      have hpartsub : ∀ u ∈ p.parts, u ⊆ s \ t := by
        intro u hu i hi
        rw [← p.cover]
        exact Finset.mem_biUnion.mpr ⟨u, hu, hi⟩
      have hdisj : ∀ u ∈ p.parts, Disjoint t u := by
        intro u hu
        apply Finset.disjoint_left.mpr
        intro i hit hiu
        exact (Finset.mem_sdiff.mp (hpartsub u hu hiu)).2 hit
      refine ⟨⟨insert t p.parts, ?_, ?_, ?_⟩⟩
      · intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu
        · exact ht
        · exact p.circuit u hu
      · intro u hu v hv huv
        rcases Finset.mem_insert.mp hu with rfl | hu
        · rcases Finset.mem_insert.mp hv with rfl | hv
          · exact (huv rfl).elim
          · exact hdisj v hv
        · rcases Finset.mem_insert.mp hv with rfl | hv
          · exact (hdisj u hu).symm
          · exact p.pairwise_disjoint hu hv huv
      · rw [Finset.biUnion_insert, p.cover]
        exact Finset.union_sdiff_of_subset hts

end Cubical

end
end BundlePart1

section BundlePart2
/- Source: Cubical/SimplicialFamilies.lean -/





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

end
end BundlePart2

section BundlePart3
/- Source: Cubical/SimplicialContraction.lean -/




/-! # Vertex contraction and its chain homotopy over `𝔽₂` -/

@[expose] public section

namespace Cubical.Simplicial

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
@[simp]
theorem chain_neg (c : Chain V) : -c = c := by
  exact neg_eq_iff_add_eq_zero.mpr (chain_add_self c)

/-- Keep the simplices containing a specified vertex. -/
noncomputable def star (v : V) : Chain V →ₗ[ZMod 2] Chain V :=
  Finsupp.linearCombination (ZMod 2)
    (fun s : Finset V => if v ∈ s then Finsupp.single s 1 else 0)

/-- Erase a specified vertex, and send simplices not containing it to zero. -/
noncomputable def eraseVertex (v : V) : Chain V →ₗ[ZMod 2] Chain V :=
  Finsupp.linearCombination (ZMod 2)
    (fun s : Finset V => if v ∈ s then Finsupp.single (s.erase v) 1 else 0)

@[simp]
theorem star_single (v : V) (s : Finset V) (a : ZMod 2) :
    star v (Finsupp.single s a) = if v ∈ s then Finsupp.single s a else 0 := by
  by_cases hv : v ∈ s <;> simp [star, hv, Finsupp.smul_single]

@[simp]
theorem eraseVertex_single (v : V) (s : Finset V) (a : ZMod 2) :
    eraseVertex v (Finsupp.single s a) =
      if v ∈ s then Finsupp.single (s.erase v) a else 0 := by
  by_cases hv : v ∈ s <;> simp [eraseVertex, hv, Finsupp.smul_single]

theorem boundary_star_add_star_boundary_single (v : V) (s : Finset V) (a : ZMod 2) :
    boundary (star v (Finsupp.single s a)) + star v (boundary (Finsupp.single s a)) =
      eraseVertex v (Finsupp.single s a) := by
  by_cases hv : v ∈ s
  · have hs : star v (boundary (Finsupp.single s a)) =
        ∑ w ∈ s.erase v, Finsupp.single (s.erase w) a := by
      rw [boundary_single, map_sum, ← Finset.add_sum_erase s _ hv]
      have hz : star v (Finsupp.single (s.erase v) a) = 0 := by simp
      rw [hz, zero_add]
      apply Finset.sum_congr rfl
      intro w hw
      have hwv := (Finset.mem_erase.mp hw).1
      simp [star_single, Finset.mem_erase, hv, hwv.symm]
    rw [star_single, ite_eq_left hv, hs, eraseVertex_single, ite_eq_left hv, boundary_single,
      ← Finset.add_sum_erase s _ hv, add_assoc, chain_add_self, add_zero]
  · simp only [star_single, hv, ↓reduceIte, map_zero, zero_add, boundary_single,
      map_sum, eraseVertex_single]
    apply Finset.sum_eq_zero
    intro w hw
    simp [Finset.mem_erase, hv]

theorem boundary_star_add_star_boundary (v : V) (c : Chain V) :
    boundary (star v c) + star v (boundary c) = eraseVertex v c := by
  have h : (boundary (V := V)).comp (star v) + (star v).comp boundary = eraseVertex v := by
    apply Finsupp.lhom_ext
    intro s a
    exact boundary_star_add_star_boundary_single v s a
  exact LinearMap.congr_fun h c

/-- The vertex contraction sending `v` to `u`, with collapsed simplices set to zero. -/
noncomputable def contract (u v : V) : Chain V →ₗ[ZMod 2] Chain V :=
  LinearMap.id + star v + (cone u).comp (eraseVertex v)

@[simp]
theorem contract_single (u v : V) (s : Finset V) (a : ZMod 2) :
    contract u v (Finsupp.single s a) =
      if v ∈ s then cone u (Finsupp.single (s.erase v) a) else Finsupp.single s a := by
  by_cases hv : v ∈ s <;> simp [contract, hv, chain_add_self]

theorem contract_single_of_ne {u v : V} (huv : u ≠ v) (s : Finset V) (a : ZMod 2) :
    contract u v (Finsupp.single s a) =
      if u ∈ s ∧ v ∈ s then 0
      else if v ∈ s then Finsupp.single (insert u (s.erase v)) a else Finsupp.single s a := by
  by_cases hu : u ∈ s <;> by_cases hv : v ∈ s <;>
    simp [contract_single, cone_single, Finset.mem_erase, hu, hv, huv]

/-- A concrete chain homotopy from vertex contraction to the identity. -/
theorem contract_homotopy (u v : V) (c : Chain V) :
    contract u v c = c + boundary (cone u (star v c)) + cone u (star v (boundary c)) := by
  have hc := boundary_cone_add_cone_boundary u (star v c)
  have hc' := eq_sub_of_add_eq hc
  rw [sub_eq_add_neg, chain_neg] at hc'
  simp only [contract, LinearMap.add_apply, LinearMap.id_apply, LinearMap.comp_apply]
  rw [hc']
  simp only [add_assoc]
  rw [← map_add, boundary_star_add_star_boundary]

/-- Vertex contraction commutes with the augmented simplicial boundary. -/
theorem boundary_contract (u v : V) (c : Chain V) :
    boundary (contract u v c) = contract u v (boundary c) := by
  rw [contract_homotopy, map_add, map_add, boundary_boundary, add_zero,
    contract_homotopy, boundary_boundary, map_zero, map_zero, add_zero]

/-- Contraction therefore sends simplicial cycles to simplicial cycles. -/
theorem contract_cycle (u v : V) {c : Chain V} (hc : boundary c = 0) :
    boundary (contract u v c) = 0 := by
  rw [boundary_contract, hc, map_zero]

@[simp]
theorem star_apply (v : V) (c : Chain V) (s : Finset V) :
    star v c s = if v ∈ s then c s else 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
      by_cases hv : v ∈ s <;> simp [hc, hd, hv]
  | single t a =>
      by_cases hts : t = s
      · subst t
        by_cases hv : v ∈ s <;> simp [hv]
      · by_cases ht : v ∈ t <;> by_cases hs : v ∈ s <;>
          simp [star_single, ht, hs, hts]

@[simp]
theorem cone_apply (v : V) (c : Chain V) (s : Finset V) :
    cone v c s = if v ∈ s then c (s.erase v) else 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
      by_cases hv : v ∈ s <;> simp [hc, hd, hv]
  | single t a =>
      by_cases hs : v ∈ s
      · by_cases ht : v ∈ t
        · have hne : t ≠ s.erase v := by
            intro h; rw [h] at ht; exact Finset.notMem_erase v s ht
          simp [cone_single, hs, ht, hne]
        · have heq : insert v t = s ↔ t = s.erase v := by
            constructor
            · intro h
              rw [← h, Finset.erase_insert ht]
            · intro h
              rw [h, Finset.insert_erase hs]
          simp [cone_single, hs, ht, Finsupp.single_apply, heq]
      · have hne : insert v t ≠ s := by
          intro h; apply hs; rw [← h]; exact Finset.mem_insert_self _ _
        by_cases ht : v ∈ t <;> simp [cone_single, hs, ht, hne]

/-- The completion used in a Fogelsanger decomposition. -/
noncomputable def complete (u v : V) : Chain V →ₗ[ZMod 2] Chain V :=
  LinearMap.id + ((cone u).comp (star v)).comp boundary

theorem complete_apply (u v : V) (c : Chain V) :
    complete u v c = c + cone u (star v (boundary c)) := rfl

theorem complete_coefficient {u v : V} (huv : u ≠ v) (c : Chain V) (s : Finset V) :
    complete u v c s = c s + if u ∈ s ∧ v ∈ s then boundary c (s.erase u) else 0 := by
  rw [complete_apply, Finsupp.add_apply, cone_apply, star_apply]
  by_cases hu : u ∈ s <;> by_cases hv : v ∈ s <;>
    simp [hu, hv, Finset.mem_erase, huv.symm]

theorem complete_eq_of_not_edge {u v : V} (huv : u ≠ v) (c : Chain V) (s : Finset V)
    (hs : ¬(u ∈ s ∧ v ∈ s)) : complete u v c s = c s := by
  simp [complete_coefficient huv, hs]

theorem boundary_complete (u v : V) (c : Chain V) :
    boundary (complete u v c) = boundary (contract u v c) := by
  rw [complete_apply, map_add, contract_homotopy, map_add, map_add,
    boundary_boundary, add_zero]

/-- A cycle after contraction has a canonically completed cycle before contraction. -/
theorem complete_cycle (u v : V) {c : Chain V}
    (hc : boundary (contract u v c) = 0) : boundary (complete u v c) = 0 := by
  rw [boundary_complete, hc]

theorem complete_of_cycle (u v : V) {c : Chain V} (hc : boundary c = 0) :
    complete u v c = c := by
  simp [complete_apply, hc]

theorem contract_homotopy_term {u v : V} (huv : u ≠ v) (c : Chain V) :
    contract u v (cone u (star v c)) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [map_add, hc, hd]
  | single s a =>
      by_cases hv : v ∈ s <;> by_cases hu : u ∈ s <;>
        simp [star_single, cone_single, contract_single_of_ne huv, hv, hu, huv.symm]

theorem contract_complete {u v : V} (huv : u ≠ v) (c : Chain V) :
    contract u v (complete u v c) = contract u v c := by
  rw [complete_apply, map_add, contract_homotopy_term huv, add_zero]

theorem complete_single_of_edge {u v : V} (huv : u ≠ v) (s : Finset V)
    (hu : u ∈ s) (hv : v ∈ s) (a : ZMod 2) :
    complete u v (Finsupp.single s a) = 0 := by
  rw [complete_apply, boundary_single, map_sum, map_sum, Finset.sum_eq_single u]
  · simp [star_single, cone_single, Finset.mem_erase, huv.symm, hu, hv,
      Finset.insert_erase hu, chain_add_self]
  · intro w hw hwu
    by_cases hvw : v ∈ s.erase w
    · simp [star_single, cone_single, Finset.mem_erase, hu, hvw, hwu.symm]
    · simp [star_single, hvw]
  · exact fun h => (h hu).elim

end Cubical.Simplicial

end
end BundlePart3

section BundlePart4
/- Source: Cubical/SimplicialCircuitLifting.lean -/





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

end
end BundlePart4

section BundlePart5
/- Source: Cubical/SimplicialGeometry.lean -/





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

end
end BundlePart5

section BundlePart6
/- Source: Cubical/Pinning.lean -/







/-!
# Pinning an infinitesimal Euclidean motion

The linear-algebra fact used in Section 2 of the manuscript is proved here
without appealing to the even-rank theorem for skew-symmetric matrices.
A skew-adjoint real linear map of rank at most one is zero.  Consequently,
an infinitesimal Euclidean motion which vanishes at `dim V` affinely
independent points vanishes everywhere.
-/

@[expose] public section

namespace Cubical.Pinning

open Module
open scoped Pointwise

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- A real skew-adjoint map has no nonzero rank-one case. -/
theorem skew_eq_zero_of_finrank_range_le_one
    (A : V →ₗ[ℝ] V)
    (hskew : ∀ x y : V, inner ℝ (A x) y = -inner ℝ x (A y))
    (hrank : finrank ℝ (LinearMap.range A) ≤ 1) : A = 0 := by
  obtain ⟨y, hy⟩ := (finrank_le_one_iff (K := ℝ)
    (V := LinearMap.range A)).mp hrank
  obtain ⟨x, hx⟩ := y.property
  obtain ⟨c, hc⟩ := hy ⟨A (y : V), ⟨(y : V), rfl⟩⟩
  have hc' : c • (y : V) = A (y : V) := congrArg Subtype.val hc
  have hxy : inner ℝ x (y : V) = 0 := by
    have h := hskew x x
    rw [hx, real_inner_comm x (y : V)] at h
    linarith
  have hyy : inner ℝ (y : V) (y : V) = 0 := by
    have h := hskew x (y : V)
    rw [hx, ← hc', inner_smul_right, hxy] at h
    simpa using h
  have hyzero : (y : V) = 0 := inner_self_eq_zero.mp hyy
  ext z
  obtain ⟨a, ha⟩ := hy ⟨A z, ⟨z, rfl⟩⟩
  have ha' : a • (y : V) = A z := congrArg Subtype.val ha
  simpa [hyzero] using ha'.symm

/-- Killing a subspace of codimension at most one kills a skew-adjoint map. -/
theorem skew_eq_zero_of_large_kernel
    (A : V →ₗ[ℝ] V)
    (hskew : ∀ x y : V, inner ℝ (A x) y = -inner ℝ x (A y))
    (hker : finrank ℝ V ≤ finrank ℝ (LinearMap.ker A) + 1) : A = 0 := by
  apply skew_eq_zero_of_finrank_range_le_one A hskew
  have h := A.finrank_range_add_finrank_ker
  omega

omit [FiniteDimensional ℝ V] in
/-- If an affine map vanishes on a set, its linear part kills the span of all
differences of points of that set. -/
theorem vectorSpan_le_ker_of_pinned
    {ι : Type*} (A : V →ₗ[ℝ] V) (t : V) (q : ι → V)
    (hpin : ∀ i, t + A (q i) = 0) :
    vectorSpan ℝ (Set.range q) ≤ LinearMap.ker A := by
  rw [vectorSpan_def, Submodule.span_le]
  rintro z ⟨x, ⟨i, rfl⟩, y, ⟨j, rfl⟩, rfl⟩
  change A (q i - q j) = 0
  rw [map_sub, sub_eq_zero]
  exact add_left_cancel ((hpin i).trans (hpin j).symm)

/-- A Euclidean infinitesimal motion pinned on at least `dim V` affinely
independent points is the zero motion.  The cardinal hypothesis permits both
a facet simplex and a full-dimensional simplex. -/
theorem rigid_motion_pinned_on_affine_independent
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (A : V →ₗ[ℝ] V) (t : V) (q : ι → V)
    (hskew : ∀ x y : V, inner ℝ (A x) y = -inner ℝ x (A y))
    (hind : AffineIndependent ℝ q)
    (hcard : finrank ℝ V ≤ Fintype.card ι)
    (hpin : ∀ i, t + A (q i) = 0) :
    A = 0 ∧ t = 0 ∧ ∀ x : V, t + A x = 0 := by
  have hle := Submodule.finrank_mono (vectorSpan_le_ker_of_pinned A t q hpin)
  have hdim := hind.finrank_vectorSpan_add_one
  have hA : A = 0 := skew_eq_zero_of_large_kernel A hskew (by omega)
  have ht : t = 0 := by
    simpa [hA] using hpin (Classical.arbitrary ι)
  exact ⟨hA, ht, by simp [hA, ht]⟩

end Cubical.Pinning

end
end BundlePart6

section BundlePart7
/- Source: Cubical/Rigidity.lean -/
@[expose] public section




/-!
# Infinitesimal rigidity, gluing, and coning

These definitions use actual infinitesimal Euclidean motions, rather than a
nullity bound which can become misleading for degenerate placements.
The graph may have any vertex type; finiteness is needed only for later rank
arguments and is not needed by the elementary rigidity lemmas here.
-/

namespace Cubical.Rigidity

open Module
open scoped InnerProductSpace

variable {V E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The defining skew-adjoint identity for an infinitesimal rotation. -/
def IsSkew (A : E →ₗ[ℝ] E) : Prop :=
  ∀ x y : E, ⟪A x, y⟫_ℝ = -⟪x, A y⟫_ℝ

/-- Infinitesimal preservation of the length of every edge. -/
def IsMotion (G : SimpleGraph V) (p u : V → E) : Prop :=
  ∀ a b, G.Adj a b → ⟪p a - p b, u a - u b⟫_ℝ = 0

/-- Restriction of an ambient Euclidean infinitesimal motion. -/
def IsTrivialMotion (p u : V → E) : Prop :=
  ∃ t : E, ∃ A : E →ₗ[ℝ] E, IsSkew A ∧ ∀ v, u v = t + A (p v)

/-- All infinitesimal motions are Euclidean motions. -/
def IsRigid (G : SimpleGraph V) (p : V → E) : Prop :=
  ∀ u : V → E, IsMotion G p u → IsTrivialMotion p u

theorem IsSkew.inner_self {A : E →ₗ[ℝ] E} (hA : IsSkew A) (x : E) :
    ⟪x, A x⟫_ℝ = 0 := by
  have h := hA x x
  have hc := real_inner_comm x (A x)
  linarith

theorem IsSkew.sub {A B : E →ₗ[ℝ] E} (hA : IsSkew A) (hB : IsSkew B) :
    IsSkew (A - B) := by
  intro x y
  simp only [LinearMap.sub_apply, inner_sub_left, inner_sub_right, hA x y, hB x y]
  ring

theorem IsTrivialMotion.isMotion {G : SimpleGraph V} {p u : V → E}
    (hu : IsTrivialMotion p u) : IsMotion G p u := by
  obtain ⟨t, A, hA, hu⟩ := hu
  intro a b _
  rw [hu a, hu b]
  have hsub : t + A (p a) - (t + A (p b)) = A (p a - p b) := by
    rw [map_sub]
    abel
  rw [hsub]
  exact hA.inner_self _

theorem IsMotion.sub_const {G : SimpleGraph V} {p u : V → E}
    (hu : IsMotion G p u) (t : E) : IsMotion G p (fun v => u v - t) := by
  intro a b hab
  have h : (u a - t) - (u b - t) = u a - u b := by abel
  rw [h]
  exact hu a b hab

theorem IsRigid.mono {G H : SimpleGraph V} (hGH : G ≤ H) {p : V → E}
    (hG : IsRigid G p) : IsRigid H p := by
  intro u hu
  exact hG u (fun a b hab => hu a b (hGH hab))

/-- An ambient rigid motion is uniquely determined by `dim E` affinely
independent point values. This includes a facet's vertices. -/
theorem trivial_motion_agreement
    [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] [Nonempty ι]
    (t s : E) (A B : E →ₗ[ℝ] E)
    (hA : IsSkew A) (hB : IsSkew B) (q : ι → E)
    (hq : AffineIndependent ℝ q) (hcard : finrank ℝ E ≤ Fintype.card ι)
    (hagree : ∀ i, t + A (q i) = s + B (q i)) :
    ∀ x, t + A x = s + B x := by
  have hpin : ∀ i, (t - s) + (A - B) (q i) = 0 := by
    intro i
    simp only [LinearMap.sub_apply]
    calc
      (t - s) + (A (q i) - B (q i)) = (t + A (q i)) - (s + B (q i)) := by abel
      _ = 0 := sub_eq_zero.mpr (hagree i)
  have hzero := Pinning.rigid_motion_pinned_on_affine_independent
    (A - B) (t - s) q (hA.sub hB) hq hcard hpin
  intro x
  have h := hzero.2.2 x
  simp only [LinearMap.sub_apply] at h
  apply sub_eq_zero.mp
  convert h using 1
  abel

/-- Gluing two rigid restrictions with an affinely independent overlap of
at least the ambient dimension. All edges are edges of the ambient graph. -/
theorem IsRigid.union
    [FiniteDimensional ℝ E] {G : SimpleGraph V} {p : V → E}
    (S T : Set V)
    (hS : IsRigid (G.induce S) (fun v : S => p v))
    (hT : IsRigid (G.induce T) (fun v : T => p v))
    {ι : Type*} [Fintype ι] [Nonempty ι] (q : ι → V)
    (hqS : ∀ i, q i ∈ S) (hqT : ∀ i, q i ∈ T)
    (hq : AffineIndependent ℝ (p ∘ q))
    (hcard : finrank ℝ E ≤ Fintype.card ι) :
    IsRigid (G.induce (S ∪ T)) (fun v : ↥(S ∪ T) => p v) := by
  intro u hu
  let uS : S → E := fun v => u ⟨v, Or.inl v.property⟩
  let uT : T → E := fun v => u ⟨v, Or.inr v.property⟩
  have huS : IsMotion (G.induce S) (fun v : S => p v) uS := by
    intro a b hab
    exact hu ⟨a, Or.inl a.property⟩ ⟨b, Or.inl b.property⟩ hab
  have huT : IsMotion (G.induce T) (fun v : T => p v) uT := by
    intro a b hab
    exact hu ⟨a, Or.inr a.property⟩ ⟨b, Or.inr b.property⟩ hab
  obtain ⟨s, A, hA, huA⟩ := hS uS huS
  obtain ⟨t, B, hB, huB⟩ := hT uT huT
  have hagree : ∀ i, s + A (p (q i)) = t + B (p (q i)) := by
    intro i
    rw [← huA ⟨q i, hqS i⟩, ← huB ⟨q i, hqT i⟩]
  have hall := trivial_motion_agreement s t A B hA hB (p ∘ q) hq hcard hagree
  refine ⟨s, A, hA, ?_⟩
  intro v
  rcases v.property with hv | hv
  · exact huA ⟨v, hv⟩
  · exact (huB ⟨v, hv⟩).trans (hall (p v)).symm

/-- The graph cone with a fresh apex `none`. -/
def coneGraph (G : SimpleGraph V) : SimpleGraph (Option V) where
  Adj a b := match a, b with
    | none, none => False
    | none, some _ => True
    | some _, none => True
    | some a, some b => G.Adj a b
  symm := ⟨by
    intro a b hab
    cases a <;> cases b <;> simp_all [G.adj_comm]⟩
  loopless := ⟨by
    intro a
    cases a <;> simp⟩

/-- The usual cone placement: the apex is zero and the old placement lies
in the affine hyperplane with last coordinate one. -/
noncomputable def conePlacement (p : V → E) : Option V → WithLp 2 (E × ℝ)
  | none => 0
  | some v => WithLp.toLp 2 (p v, 1)

/-- The skew block matrix associated with a base translation and rotation. -/
noncomputable def coneSkew (A : E →ₗ[ℝ] E) (t : E) :
    WithLp 2 (E × ℝ) →ₗ[ℝ] WithLp 2 (E × ℝ) where
  toFun x := WithLp.toLp 2 (A (WithLp.ofLp x).1 + (WithLp.ofLp x).2 • t,
    -⟪t, (WithLp.ofLp x).1⟫_ℝ)
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    simp only [WithLp.ofLp_add, Prod.fst_add, Prod.snd_add,
      map_add, add_smul, inner_add_right]
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> abel
  map_smul' c x := by
    apply WithLp.ofLp_injective 2
    simp [map_smul, smul_add, smul_smul, inner_smul_right]

theorem coneSkew_isSkew {A : E →ₗ[ℝ] E} (hA : IsSkew A) (t : E) :
    IsSkew (coneSkew A t) := by
  intro x y
  simp only [coneSkew, LinearMap.coe_mk, AddHom.coe_mk, WithLp.prod_inner_apply,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
  rw [hA (WithLp.ofLp x).1 (WithLp.ofLp y).1,
    real_inner_comm (WithLp.ofLp x).1 t]
  simp only [RCLike.conj_to_real, inner_neg_left, inner_neg_right, Real.inner_apply]
  ring

/-- Coning an infinitesimally rigid framework preserves rigidity, in one
higher Euclidean dimension. The proof is an explicit block-matrix argument. -/
theorem IsRigid.cone {G : SimpleGraph V} {p : V → E}
    (hp : IsRigid G p) : IsRigid (coneGraph G) (conePlacement p) := by
  intro u hu
  let v : Option V → WithLp 2 (E × ℝ) := fun a => u a - u none
  have hv : IsMotion (coneGraph G) (conePlacement p) v := hu.sub_const (u none)
  have hv0 : v none = 0 := sub_self _
  let w : V → E := fun a => (WithLp.ofLp (v (some a))).1
  have hw : IsMotion G p w := by
    intro a b hab
    have h := hv (some a) (some b) hab
    simpa [conePlacement, WithLp.prod_inner_apply, w] using h
  obtain ⟨t, A, hA, hwA⟩ := hp w hw
  have hlast : ∀ a, (WithLp.ofLp (v (some a))).2 = -⟪t, p a⟫_ℝ := by
    intro a
    have h := hv (some a) none trivial
    simp [conePlacement, hv0, WithLp.prod_inner_apply] at h
    have hwval : (v (some a)).fst = t + A (p a) := hwA a
    rw [hwval, inner_add_right, hA.inner_self] at h
    rw [real_inner_comm t (p a)] at h
    change (v (some a)).snd = -⟪t, p a⟫_ℝ
    linarith
  refine ⟨u none, coneSkew A t, coneSkew_isSkew hA t, ?_⟩
  intro a
  cases a with
  | none => simp [conePlacement]
  | some a =>
    have hvval : v (some a) = coneSkew A t (conePlacement p (some a)) := by
      apply WithLp.ofLp_injective 2
      apply Prod.ext
      · simpa [coneSkew, conePlacement, w, add_comm] using hwA a
      · simpa [coneSkew, conePlacement] using hlast a
    change u (some a) = u none + coneSkew A t (conePlacement p (some a))
    rw [← hvval]
    dsimp [v]
    abel

end Cubical.Rigidity

end
end BundlePart7

section BundlePart8
/- Source: Cubical/Exactness.lean -/
@[expose] public section




/-!
# Stability of exact finite-dimensional complexes

If continuously varying linear maps form a complex at every parameter and
are exact at one parameter, they remain exact nearby. The proof preserves
independence of bases of the two images and then uses rank-nullity.
This avoids any formula for the dimension of a special kernel.
-/

namespace Cubical.Exactness

open Module Filter
open scoped Topology

variable {α X Y Z : Type*} [TopologicalSpace α]
  [AddCommGroup X] [Module ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]

omit [FiniteDimensional ℝ Y] in
/-- The rank of a continuous matrix family cannot decrease close to a fixed
parameter. Continuity is required only after evaluating at each vector. -/
theorem eventually_finrank_range_ge (f : α → X →ₗ[ℝ] Y) (a₀ : α)
    (hf : ∀ x, ContinuousAt (fun a => f a x) a₀) :
    ∀ᶠ a in 𝓝 a₀, finrank ℝ (LinearMap.range (f a₀)) ≤
      finrank ℝ (LinearMap.range (f a)) := by
  classical
  let r := finrank ℝ (LinearMap.range (f a₀))
  let b := Module.finBasis ℝ (LinearMap.range (f a₀))
  let v : Fin r → X := fun i =>
    Classical.choose (LinearMap.mem_range.mp (b i).property)
  have hv : ∀ i, f a₀ (v i) = (b i).val := fun i =>
    Classical.choose_spec (LinearMap.mem_range.mp (b i).property)
  have hli : LinearIndependent ℝ (fun i => f a₀ (v i)) := by
    have hb := b.linearIndependent.map' (LinearMap.range (f a₀)).subtype
      (Submodule.ker_subtype _)
    convert hb using 1
    funext i
    exact hv i
  have hcont : ContinuousAt (fun a => fun i => f a (v i)) a₀ :=
    continuousAt_pi.mpr fun i => hf (v i)
  have hevent : ∀ᶠ a in 𝓝 a₀, LinearIndependent ℝ (fun i => f a (v i)) :=
    hcont.tendsto.eventually hli.eventually
  filter_upwards [hevent] with a ha
  let u : Fin r → LinearMap.range (f a) := fun i =>
    ⟨f a (v i), LinearMap.mem_range_self _ _⟩
  have hu : LinearIndependent ℝ u :=
    LinearIndependent.of_comp (LinearMap.range (f a)).subtype ha
  simpa only [Fintype.card_fin] using hu.fintype_card_le_finrank

omit [FiniteDimensional ℝ Z] in
/-- Exactness is an open condition among continuously varying complexes. -/
theorem eventually_range_eq_ker
    (f : α → X →ₗ[ℝ] Y) (g : α → Y →ₗ[ℝ] Z) (a₀ : α)
    (hf : ∀ x, ContinuousAt (fun a => f a x) a₀)
    (hg : ∀ y, ContinuousAt (fun a => g a y) a₀)
    (hcomplex : ∀ a, (g a).comp (f a) = 0)
    (hexact : LinearMap.range (f a₀) = LinearMap.ker (g a₀)) :
    ∀ᶠ a in 𝓝 a₀, LinearMap.range (f a) = LinearMap.ker (g a) := by
  filter_upwards [eventually_finrank_range_ge f a₀ hf,
    eventually_finrank_range_ge g a₀ hg] with a hfr hgr
  have hle : LinearMap.range (f a) ≤ LinearMap.ker (g a) := by
    rintro y ⟨x, rfl⟩
    change g a (f a x) = 0
    exact LinearMap.congr_fun (hcomplex a) x
  apply Submodule.eq_of_le_of_finrank_le hle
  have hbase := (g a₀).finrank_range_add_finrank_ker
  have hnew := (g a).finrank_range_add_finrank_ker
  rw [hexact] at hfr
  omega

end Cubical.Exactness

end
end BundlePart8

section BundlePart9
/- Source: Cubical/RigidityLinear.lean -/
@[expose] public section



/-!
# Rigidity as exactness of a linear complex

The map from translations and skew-adjoint operators to velocity fields has
range exactly the trivial motions. The edge derivative map has kernel
exactly the infinitesimal motions. Thus genuine infinitesimal rigidity is
the exactness of this complex; in particular it is open in the placement.
-/

namespace Cubical.Rigidity

open Module Filter
open scoped InnerProductSpace Topology

variable {V E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The vector space of infinitesimal rotations. -/
def skewSubmodule : Submodule ℝ (E →ₗ[ℝ] E) where
  carrier := IsSkew
  zero_mem' := by intro x y; simp
  add_mem' hA hB := by
    intro x y
    simp only [LinearMap.add_apply, inner_add_left, inner_add_right, hA x y, hB x y]
    ring
  smul_mem' c A hA := by
    intro x y
    simp only [LinearMap.smul_apply, real_inner_smul_left, real_inner_smul_right,
      hA x y]
    ring

/-- Translation and rotation parameters. -/
abbrev EuclideanMotionParameters (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] := E × (skewSubmodule (E := E))

/-- Evaluation of a Euclidean infinitesimal motion at a placement. -/
noncomputable def trivialMotionMap (p : V → E) :
    EuclideanMotionParameters E →ₗ[ℝ] (V → E) where
  toFun a v := a.1 + a.2.val (p v)
  map_add' a b := by
    funext v
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, LinearMap.add_apply,
      Pi.add_apply]
    abel
  map_smul' c a := by
    funext v
    simp [smul_add]

/-- Directed edges are convenient linear coordinates; opposite orientations
give the same equation, which does not change its kernel. -/
abbrev DirectedEdge (G : SimpleGraph V) := {e : V × V // G.Adj e.1 e.2}

/-- The edge-length derivative map. -/
noncomputable def motionMap (G : SimpleGraph V) (p : V → E) :
    (V → E) →ₗ[ℝ] (DirectedEdge G → ℝ) where
  toFun u e := ⟪p e.val.1 - p e.val.2, u e.val.1 - u e.val.2⟫_ℝ
  map_add' u v := by
    funext e
    simp only [Pi.add_apply]
    have h : (u e.val.1 + v e.val.1) - (u e.val.2 + v e.val.2) =
      (u e.val.1 - u e.val.2) + (v e.val.1 - v e.val.2) := by abel
    rw [h, inner_add_right]
  map_smul' c u := by
    funext e
    simp [← smul_sub, real_inner_smul_right]

@[simp]
theorem mem_ker_motionMap (G : SimpleGraph V) (p u : V → E) :
    u ∈ LinearMap.ker (motionMap G p) ↔ IsMotion G p u := by
  constructor
  · intro hu a b hab
    exact congrFun (LinearMap.mem_ker.mp hu) ⟨(a, b), hab⟩
  · intro hu
    apply LinearMap.mem_ker.mpr
    funext e
    exact hu e.val.1 e.val.2 e.property

@[simp]
theorem mem_range_trivialMotionMap (p u : V → E) :
    u ∈ LinearMap.range (trivialMotionMap p) ↔ IsTrivialMotion p u := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.1, a.2.val, a.2.property, fun _ => rfl⟩
  · rintro ⟨t, A, hA, hu⟩
    refine ⟨(t, ⟨A, hA⟩), ?_⟩
    funext v
    exact (hu v).symm

theorem range_trivialMotionMap_le_ker (G : SimpleGraph V) (p : V → E) :
    LinearMap.range (trivialMotionMap p) ≤ LinearMap.ker (motionMap G p) := by
  intro u hu
  exact (mem_ker_motionMap G p u).mpr ((mem_range_trivialMotionMap p u).mp hu).isMotion

theorem motionMap_comp_trivialMotionMap (G : SimpleGraph V) (p : V → E) :
    (motionMap G p).comp (trivialMotionMap p) = 0 := by
  apply LinearMap.ext
  intro a
  funext e
  have hu := range_trivialMotionMap_le_ker G p (LinearMap.mem_range_self (trivialMotionMap p) a)
  exact congrFun (LinearMap.mem_ker.mp hu) e

theorem isRigid_iff_range_eq_ker (G : SimpleGraph V) (p : V → E) :
    IsRigid G p ↔ LinearMap.range (trivialMotionMap p) = LinearMap.ker (motionMap G p) := by
  constructor
  · intro h
    apply le_antisymm (range_trivialMotionMap_le_ker G p)
    intro u hu
    exact (mem_range_trivialMotionMap p u).mpr (h u ((mem_ker_motionMap G p u).mp hu))
  · intro h u hu
    apply (mem_range_trivialMotionMap p u).mp
    rw [h]
    exact (mem_ker_motionMap G p u).mpr hu

section Continuity

variable [Fintype V] [FiniteDimensional ℝ E]
  {α : Type*} [TopologicalSpace α]

omit [Fintype V] in
/-- Continuity of each trivial-motion velocity field with respect to the placement. -/
theorem continuousAt_trivialMotionMap (p : α → V → E) (a₀ : α)
    (hp : ∀ v, ContinuousAt (fun a => p a v) a₀)
    (u : EuclideanMotionParameters E) :
    ContinuousAt (fun a => trivialMotionMap (p a) u) a₀ := by
  apply continuousAt_pi.mpr
  intro v
  exact continuousAt_const.add (u.2.val.continuous_of_finiteDimensional.continuousAt.comp (hp v))

omit [Fintype V] [FiniteDimensional ℝ E] in
/-- Continuity of each edge-derivative vector with respect to the placement. -/
theorem continuousAt_motionMap (G : SimpleGraph V) (p : α → V → E) (a₀ : α)
    (hp : ∀ v, ContinuousAt (fun a => p a v) a₀) (u : V → E) :
    ContinuousAt (fun a => motionMap G (p a) u) a₀ := by
  apply continuousAt_pi.mpr
  intro e
  exact ((hp e.val.1).sub (hp e.val.2)).inner continuousAt_const

/-- Actual infinitesimal rigidity persists under sufficiently small perturbations. -/
theorem IsRigid.eventually {G : SimpleGraph V} (p : α → V → E) (a₀ : α)
    (hp : ∀ v, ContinuousAt (fun a => p a v) a₀)
    (hrigid : IsRigid G (p a₀)) :
    ∀ᶠ a in 𝓝 a₀, IsRigid G (p a) := by
  classical
  have h := Exactness.eventually_range_eq_ker
    (fun a => trivialMotionMap (p a)) (fun a => motionMap G (p a)) a₀
    (continuousAt_trivialMotionMap p a₀ hp)
    (continuousAt_motionMap G p a₀ hp)
    (fun a => motionMap_comp_trivialMotionMap G (p a))
    ((isRigid_iff_range_eq_ker G (p a₀)).mp hrigid)
  exact h.mono fun a ha => (isRigid_iff_range_eq_ker G (p a)).mpr ha

end Continuity

end Cubical.Rigidity

end
end BundlePart9

section BundlePart10
/- Source: Cubical/AffinePath.lean -/
@[expose] public section
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/









/-!
# Linear independence along an affine path

These elementary polynomial-minor lemmas are adapted from Bryan Gin-ge Chen's
`CombinatorialRigidity/Mathlib/LinearAlgebra/Matrix/Rank.lean`, commit
`021c2284bc387efee3c3b20a18eb5f769638b578` (Apache 2.0).
They are checked against this project's pinned Lean and Mathlib versions.
-/

namespace Matrix
variable {m n : Type*}

/-- **Linear independence of rows from a specialized nonzero minor.** Let `M : ι → κ → R` be
a (possibly rectangular) family of rows over an integral domain `R`, with `ι` finite. If there
is a column selection `e : ι → κ` and a ring homomorphism `φ : R →+* S` into a commutative ring
`S` such that the square submatrix `(i, j) ↦ M i (e j)` has a determinant whose
image under `φ` is nonzero, then the rows `M` are linearly independent over `R`.

This is the "a polynomial minor with a nonzero specialization is itself nonzero, hence the generic
rows are independent" reflection: a nonzero specialized minor det forces the `R`-det to be nonzero
(`φ 0 = 0`), so the chosen square submatrix has independent rows
(`linearIndependent_rows_of_det_ne_zero`), and the full rows are independent by composing with the
column-projection linear map `(κ → R) → (ι → R)` (`LinearIndependent.of_comp`). No coefficient-wise
reflection along `φ` is used — that would be false when `φ` has a nontrivial kernel; the argument
routes through the minor's determinant instead. -/
theorem linearIndependent_rows_of_specialized_submatrix_det_ne_zero
    {ι κ R S : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [IsDomain R]
    [CommRing S] (M : ι → κ → R) (φ : R →+* S) (e : ι → κ)
    (hdet : φ (Matrix.of (fun i j : ι => M i (e j))).det ≠ 0) :
    LinearIndependent R M := by
  have hRne : (Matrix.of (fun i j : ι => M i (e j))).det ≠ 0 := fun h => hdet (by rw [h, map_zero])
  let f : (κ → R) →ₗ[R] (ι → R) := LinearMap.pi (fun i => LinearMap.proj (e i))
  refine LinearIndependent.of_comp f ?_
  have hcomp : (f ∘ M) = (fun i j : ι => M i (e j)) := by funext i j; rfl
  rw [hcomp]
  exact Matrix.linearIndependent_rows_of_det_ne_zero hRne

/-- **A matrix with linearly independent rows over a field has a nonsingular maximal minor.**
Let `M : Matrix m n K` over a field `K` with `m` and `n` finite. If the rows of `M` are linearly
independent, then there is a square column selection `e : m → n` such that the `m × m` submatrix
`(i, j) ↦ M i (e j)` has nonzero determinant.

This is the "full row rank ⟹ nonzero square minor" extraction: the columns `Mᵀ.row : n → (m → K)`
span a subspace of `K`-dimension `M.rank = #m` (`LinearIndependent.rank_matrix` + `rank_transpose`),
which is all of `m → K`, so `Mᵀ.row` is a spanning family. Extracting a linearly independent
spanning subfamily (`exists_linearIndependent'`) gives a basis, necessarily of size `#m`; reindexing
it by `m` yields `e : m → n` with `Mᵀ.row ∘ e` linearly independent, i.e. the transpose of the
selected minor has independent rows, i.e. the minor has nonzero determinant
(`linearIndependent_rows_iff_isUnit` + `det_transpose` + `isUnit_iff_ne_zero`). -/
theorem exists_submatrix_det_ne_zero_of_linearIndependent_rows
    {m n K : Type*} [Field K] [Fintype m] [DecidableEq m] [Finite n] {M : Matrix m n K}
    (h : LinearIndependent K M.row) :
    ∃ e : m → n, (Matrix.of (fun i j : m => M i (e j))).det ≠ 0 := by
  classical
  have : Fintype n := Fintype.ofFinite n
  -- The columns of `M` (= rows of `Mᵀ`) span all of `m → K`.
  have hrank : Module.finrank K (Submodule.span K (Set.range Mᵀ.row)) = Fintype.card m := by
    rw [← Mᵀ.rank_eq_finrank_span_row, rank_transpose, h.rank_matrix]
  have hspan : Submodule.span K (Set.range Mᵀ.row) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [hrank, Module.finrank_fintype_fun_eq_card])
  -- Extract a linearly independent spanning subfamily of the columns.
  obtain ⟨κ, a, _, hsp, hli⟩ := exists_linearIndependent' K Mᵀ.row
  rw [hspan] at hsp
  -- It is a basis of `m → K`, so it has exactly `#m` elements: `κ ≃ m`.
  let b : Module.Basis κ K (m → K) := Module.Basis.mk hli (by rw [hsp])
  have : Fintype κ := FiniteDimensional.fintypeBasisIndex b
  have hcard : Fintype.card κ = Fintype.card m := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_fintype_fun_eq_card]
  let em : m ≃ κ := (Fintype.equivOfCardEq hcard).symm
  refine ⟨a ∘ em, ?_⟩
  -- The transpose of the selected minor has rows `Mᵀ.row ∘ a ∘ em`, which are LI.
  set N : Matrix m m K := Matrix.of (fun i j : m => M i ((a ∘ em) j)) with hN
  have hrow : Nᵀ.row = Mᵀ.row ∘ a ∘ em := rfl
  have hLIN : LinearIndependent K Nᵀ.row := by rw [hrow]; exact hli.comp ⇑em em.injective
  have : IsUnit Nᵀ := Matrix.linearIndependent_row_iff_isUnit.mp hLIN
  rw [← Matrix.det_transpose]
  exact isUnit_iff_ne_zero.mp (Nᵀ.isUnit_iff_isUnit_det.mp this)

/-- **Linear independence is cofinite along an affine path.** Let `A B : Matrix m n K` over a
field `K`. If the rows of `A + t₀ • B` are linearly independent for some `t₀ : K`, then the rows
of `A + t • B` are linearly independent for all but finitely many `t : K`.

The proof uses a maximal minor rather than the Gram determinant
`det ((A + t • B) * (A + t • B)ᵀ)`, which detects independence only over a linearly ordered field
(over `ℂ` the single row `(1, i)` is independent, while `1 + i² = 0`): a column selection `e`
witnessing the rows LI at `t₀` (`exists_submatrix_det_ne_zero_of_linearIndependent_rows`) picks
out a *single* minor `Q := det (P selected on columns e) : Polynomial K` of the
polynomial-entry matrix `P := X • C(B) + C(A)`, whose evaluation at `t` is the specialized minor's
determinant (`(evalRingHom t).map_det`). `Q` is nonzero (nonzero at `t₀`), hence has finitely many
roots (`Polynomial.finite_setOfPred_isRoot`); at any non-root `t` the specialized minor is
nonsingular, so the rows are LI there too
(`linearIndependent_rows_of_specialized_submatrix_det_ne_zero`). No infiniteness or characteristic
hypothesis on `K` is needed: the argument only uses that a nonzero univariate polynomial has
finitely many roots. -/
theorem finite_setOf_not_linearIndependent_rows_along_affine_path
    {K : Type*} [Field K] [Finite m] [Finite n] (A B : Matrix m n K) {t₀ : K}
    (h : LinearIndependent K (A + t₀ • B).row) :
    {t : K | ¬ LinearIndependent K (A + t • B).row}.Finite := by
  classical
  have : Fintype m := Fintype.ofFinite m
  have : Fintype n := Fintype.ofFinite n
  -- Column selection witnessing LI at `t₀`.
  obtain ⟨e, he⟩ := exists_submatrix_det_ne_zero_of_linearIndependent_rows h
  -- Polynomial-entry matrix `P` whose evaluation at `t` is `A + t • B`.
  let P : Matrix m n (Polynomial K) :=
    (Polynomial.X : Polynomial K) • B.map Polynomial.C + A.map Polynomial.C
  -- The single witnessing minor polynomial `Q := det (P selected on columns `e`)`.
  let Q : Polynomial K := (Matrix.of (fun i j : m => P i (e j))).det
  have hP_eval : ∀ t : K, P.map (Polynomial.evalRingHom t) = A + t • B := by
    intro t; ext i j
    change Polynomial.eval t (P i j) = (A + t • B) i j
    simp only [P, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
    ring
  have hQ_eval : ∀ t : K, Q.eval t = (Matrix.of (fun i j : m => (A + t • B) i (e j))).det := by
    intro t
    change (Polynomial.evalRingHom t) Q = _
    rw [(Polynomial.evalRingHom t).map_det, RingHom.mapMatrix_apply]
    congr 1
    ext i j
    change Polynomial.eval t (P i (e j)) = (A + t • B) i (e j)
    have := congrFun (congrFun (hP_eval t) i) (e j)
    simpa [Matrix.map_apply] using this
  have hQ_ne : Q ≠ 0 := fun hQ0 => by
    have := hQ_eval t₀
    rw [hQ0, Polynomial.eval_zero] at this
    exact he this.symm
  -- The bad-`t` set is contained in `Q`'s finite root set.
  refine (Polynomial.finite_setOfPred_isRoot hQ_ne).subset fun t ht => ?_
  rw [Set.mem_ofPred_eq] at ht
  rw [Set.mem_ofPred_eq, Polynomial.IsRoot, hQ_eval]
  by_contra h_ne
  exact ht (linearIndependent_rows_of_specialized_submatrix_det_ne_zero
    (A + t • B).row (RingHom.id K) e (by rwa [RingHom.id_apply]))

end Matrix

/-- **Vector-form polynomial-along-line.** For a finite-dim `W`-vector space over a field `K` and
an affine family `t ↦ fun i => a i + t • b i : K → ι → W` (with `ι` finite), if the family
is linearly independent at some `t₀ : K`, then it is LI for all but finitely many `t : K`.

Vector analogue of `Matrix.finite_setOf_not_linearIndependent_rows_along_affine_path`,
derived by pulling along a basis-induced isomorphism `W ≃ₗ[K] (Fin (finrank K W) → K)`. No
infiniteness or characteristic hypothesis on `K` is needed. -/
theorem LinearIndependent.finite_setOf_not_along_affine_path
    {K ι W : Type*} [Field K] [Finite ι] [AddCommGroup W] [Module K W] [Module.Finite K W]
    {a b : ι → W} {t₀ : K}
    (h : LinearIndependent K (fun i => a i + t₀ • b i)) :
    {t : K | ¬ LinearIndependent K (fun i => a i + t • b i)}.Finite := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  -- Pick a basis of `W` and identify `W` with `Fin n → K`.
  let φ : W ≃ₗ[K] (Fin (Module.finrank K W) → K) := (Module.finBasis K W).equivFun
  let A : Matrix ι (Fin (Module.finrank K W)) K := Matrix.of (fun i j => φ (a i) j)
  let B : Matrix ι (Fin (Module.finrank K W)) K := Matrix.of (fun i j => φ (b i) j)
  -- The affine matrix family `A + t • B` has rows `φ ∘ (a · + t • b ·)`.
  have h_row : ∀ t : K, (A + t • B).row = ⇑φ ∘ fun i => a i + t • b i := by
    intro t
    funext i j
    change A i j + t • B i j = φ (a i + t • b i) j
    rw [map_add, map_smul]
    rfl
  -- LI of the affine family ↔ LI of matrix rows, via the LinearEquiv `φ`.
  have h_iff : ∀ t : K,
      LinearIndependent K (fun i => a i + t • b i) ↔
      LinearIndependent K (A + t • B).row := by
    intro t
    rw [h_row t]
    exact (LinearMap.linearIndependent_iff φ.toLinearMap (LinearEquiv.ker φ)).symm
  -- Apply the matrix-form helper.
  refine (Matrix.finite_setOf_not_linearIndependent_rows_along_affine_path A B
    ((h_iff t₀).mp h)).subset fun t ht => ?_
  rw [Set.mem_ofPred_eq] at ht ⊢
  rwa [← h_iff]


end
end BundlePart10

section BundlePart11
/- Source: Cubical/GenericExactness.lean -/
@[expose] public section




/-!
# Generic exactness along an affine path

An affine family of finite-dimensional complexes that is exact at one
parameter is exact except at finitely many parameters. The argument uses
polynomial minors, then rank-nullity. No formula for a specific kernel is
assumed.
-/

namespace Cubical.Exactness

open Module

variable {X Y Z : Type*}
  [AddCommGroup X] [Module ℝ X] [FiniteDimensional ℝ X]
  [AddCommGroup Y] [Module ℝ Y] [FiniteDimensional ℝ Y]
  [AddCommGroup Z] [Module ℝ Z] [FiniteDimensional ℝ Z]

/-- The rank of an affine family is at least its rank at a fixed parameter,
except at finitely many parameters. -/
theorem finite_setOf_finrank_range_lt (f : ℝ → X →ₗ[ℝ] Y) (t₀ : ℝ)
    (hf : ∀ x, ∃ a b : Y, ∀ t, f t x = a + t • b) :
    {t : ℝ | finrank ℝ (LinearMap.range (f t)) <
      finrank ℝ (LinearMap.range (f t₀))}.Finite := by
  classical
  let r := finrank ℝ (LinearMap.range (f t₀))
  let basis := Module.finBasis ℝ (LinearMap.range (f t₀))
  let v : Fin r → X := fun i =>
    Classical.choose (LinearMap.mem_range.mp (basis i).property)
  have hv : ∀ i, f t₀ (v i) = (basis i).val := fun i =>
    Classical.choose_spec (LinearMap.mem_range.mp (basis i).property)
  have hli : LinearIndependent ℝ (fun i => f t₀ (v i)) := by
    have hb := basis.linearIndependent.map' (LinearMap.range (f t₀)).subtype
      (Submodule.ker_subtype _)
    convert hb using 1
    funext i
    exact hv i
  choose a b hab using fun i => hf (v i)
  have hli' : LinearIndependent ℝ (fun i => a i + t₀ • b i) := by
    convert hli using 1
    funext i
    exact (hab i t₀).symm
  refine hli'.finite_setOf_not_along_affine_path.subset ?_
  intro t ht hgood
  have hgood' : LinearIndependent ℝ (fun i => f t (v i)) := by
    convert hgood using 1
    funext i
    exact hab i t
  let u : Fin r → LinearMap.range (f t) := fun i =>
    ⟨f t (v i), LinearMap.mem_range_self _ _⟩
  have hu : LinearIndependent ℝ u :=
    LinearIndependent.of_comp (LinearMap.range (f t)).subtype hgood'
  have hle := hu.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hle
  exact Nat.not_lt_of_ge hle ht

/-- An affine family of complexes that is exact at one parameter is exact
outside a finite set of real parameters. -/
theorem finite_setOf_range_ne_ker
    (f : ℝ → X →ₗ[ℝ] Y) (g : ℝ → Y →ₗ[ℝ] Z) (t₀ : ℝ)
    (hf : ∀ x, ∃ a b : Y, ∀ t, f t x = a + t • b)
    (hg : ∀ y, ∃ a b : Z, ∀ t, g t y = a + t • b)
    (hcomplex : ∀ t, (g t).comp (f t) = 0)
    (hexact : LinearMap.range (f t₀) = LinearMap.ker (g t₀)) :
    {t : ℝ | LinearMap.range (f t) ≠ LinearMap.ker (g t)}.Finite := by
  refine ((finite_setOf_finrank_range_lt f t₀ hf).union
    (finite_setOf_finrank_range_lt g t₀ hg)).subset ?_
  intro t ht
  by_contra hbad
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hbad
  apply ht
  have hle : LinearMap.range (f t) ≤ LinearMap.ker (g t) := by
    rintro y ⟨x, rfl⟩
    change g t (f t x) = 0
    exact LinearMap.congr_fun (hcomplex t) x
  apply Submodule.eq_of_le_of_finrank_le hle
  have hbase := (g t₀).finrank_range_add_finrank_ker
  have hnew := (g t).finrank_range_add_finrank_ker
  rw [hexact] at hbad
  omega

end Cubical.Exactness

end
end BundlePart11

section BundlePart12
/- Source: Cubical/GenericRigidity.lean -/
@[expose] public section





/-!
# Generic placements for rigidity and independence

A graph is generically rigid when it has an infinitesimally rigid placement.
We justify this terminology by proving that such placements form an open
dense set. The proof uses exactness of the actual motion complex, rather
than a dimension bound that might fail to characterize rigid motions at
degenerate placements.
-/

open Module Filter
open scoped InnerProductSpace Topology

namespace Cubical

/-- A property attained somewhere and having only finitely many failures
along each affine line through a good point holds densely. -/
theorem dense_of_finite_bad_along_affine_path
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (P : X → Prop) (hP : ∃ x, P x)
    (hline : ∀ a b : X, ∀ t₀ : ℝ, P (a + t₀ • b) →
      {t : ℝ | ¬ P (a + t • b)}.Finite) : Dense {x | P x} := by
  rw [dense_iff_inter_open]
  rintro U hU ⟨a, ha⟩
  obtain ⟨q, hq⟩ := hP
  have hgood : P (a + (1 : ℝ) • (q - a)) := by simpa using hq
  have hbad := hline a (q - a) 1 hgood
  have hdense := hbad.countable.dense_compl ℝ
  let line : ℝ → X := fun t => a + t • (q - a)
  have hcont : Continuous line := continuous_const.add (continuous_id.smul continuous_const)
  have hopen : IsOpen (line ⁻¹' U) := hU.preimage hcont
  have hne : (line ⁻¹' U).Nonempty := ⟨0, by simpa [line] using ha⟩
  obtain ⟨t, htU, htgood⟩ := hdense.inter_open_nonempty _ hopen hne
  exact ⟨line t, htU, by simpa [line] using htgood⟩

/-- Finite intersections of open dense sets are dense. -/
theorem dense_iInter_finite {X I : Type*} [TopologicalSpace X] [Finite I]
    (s : I → Set X) (ho : ∀ i, IsOpen (s i)) (hd : ∀ i, Dense (s i)) :
    Dense (⋂ i, s i) := by
  rw [← Set.sInter_range]
  exact (Set.finite_range s).dense_sInter (by simpa using ho) (by simpa using hd)

end Cubical

namespace Cubical.Rigidity

variable {V E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Existence of an infinitesimally rigid Euclidean placement. The open
density theorem below shows this is the usual generic rigidity property. -/
def GenericallyRigid (G : SimpleGraph V) (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] : Prop := ∃ p : V → E, IsRigid G p

section Finite

variable [Fintype V] [FiniteDimensional ℝ E]

/-- Infinitesimal rigidity can fail only finitely often along an affine
path that contains one rigid placement. -/
theorem IsRigid.finite_setOf_not_along_affine_path {G : SimpleGraph V}
    (p q : V → E) (t₀ : ℝ)
    (hrigid : IsRigid G (fun v => p v + t₀ • q v)) :
    {t : ℝ | ¬ IsRigid G (fun v => p v + t • q v)}.Finite := by
  classical
  let f : ℝ → EuclideanMotionParameters E →ₗ[ℝ] (V → E) :=
    fun t => trivialMotionMap (fun v => p v + t • q v)
  let g : ℝ → (V → E) →ₗ[ℝ] (DirectedEdge G → ℝ) :=
    fun t => motionMap G (fun v => p v + t • q v)
  have hf : ∀ a, ∃ x y : V → E, ∀ t, f t a = x + t • y := by
    intro a
    refine ⟨fun v => a.1 + a.2.val (p v), fun v => a.2.val (q v), ?_⟩
    intro t
    funext v
    simp only [f, trivialMotionMap, LinearMap.coe_mk, AddHom.coe_mk,
      map_add, map_smul, Pi.add_apply, Pi.smul_apply]
    abel
  have hg : ∀ u, ∃ x y : DirectedEdge G → ℝ, ∀ t, g t u = x + t • y := by
    intro u
    refine ⟨motionMap G p u, motionMap G q u, ?_⟩
    intro t
    funext e
    simp only [g, motionMap, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.add_apply, Pi.smul_apply]
    have hs : p e.val.1 + t • q e.val.1 - (p e.val.2 + t • q e.val.2) =
        (p e.val.1 - p e.val.2) + t • (q e.val.1 - q e.val.2) := by module
    rw [hs, inner_add_left, real_inner_smul_left]
    rfl
  have hbad := Exactness.finite_setOf_range_ne_ker f g t₀ hf hg
    (fun t => motionMap_comp_trivialMotionMap G _) 
    ((isRigid_iff_range_eq_ker G _).mp hrigid)
  convert hbad using 1
  ext t
  exact not_congr (isRigid_iff_range_eq_ker G _)

/-- Rigid placements form an open set. -/
theorem isOpen_setOf_isRigid (G : SimpleGraph V) :
    IsOpen {p : V → E | IsRigid G p} := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  exact hp.eventually (fun q => q) p (fun v => (continuous_apply v).continuousAt)

/-- A generically rigid graph has a dense set of rigid placements. -/
theorem GenericallyRigid.dense {G : SimpleGraph V} (hG : GenericallyRigid G E) :
    Dense {p : V → E | IsRigid G p} := by
  apply Cubical.dense_of_finite_bad_along_affine_path _ hG
  intro p q t₀ h
  exact h.finite_setOf_not_along_affine_path p q t₀

omit [Fintype V] in
/-- Restricting an ambient placement to an embedded finite vertex set
preserves the open nature of rigidity. -/
theorem isOpen_setOf_isRigid_precomp {W : Type*} [Fintype W]
    (G : SimpleGraph W) (i : W ↪ V) :
    IsOpen {p : V → E | IsRigid G (p ∘ i)} := by
  have hc : Continuous (fun p : V → E => p ∘ i) :=
    continuous_pi fun w => continuous_apply (i w)
  exact (isOpen_setOf_isRigid (E := E) G).preimage hc

/-- Rigid placements on any embedded finite vertex set occur densely
among ambient placements. -/
theorem GenericallyRigid.dense_precomp {W : Type*} [Fintype W]
    {G : SimpleGraph W} (hG : GenericallyRigid G E) (i : W ↪ V) :
    Dense {p : V → E | IsRigid G (p ∘ i)} := by
  apply Cubical.dense_of_finite_bad_along_affine_path
  · obtain ⟨q, hq⟩ := hG
    refine ⟨Function.extend i q 0, ?_⟩
    simpa only [Function.extend_comp i.injective] using hq
  · intro p q t₀ h
    exact h.finite_setOf_not_along_affine_path (p ∘ i) (q ∘ i) t₀

omit [Fintype V] [FiniteDimensional ℝ E] in
/-- Independence of an embedded finite tuple is open in the placement. -/
theorem isOpen_setOf_linearIndependent_precomp {C : Type*} [Fintype C]
    (c : C ↪ V) :
    IsOpen {p : V → E | LinearIndependent ℝ (p ∘ c)} := by
  have hc : Continuous (fun p : V → E => p ∘ c) :=
    continuous_pi fun i => continuous_apply (c i)
  exact (isOpen_setOfPred_linearIndependent (𝕜 := ℝ) (E := E) (ι := C)).preimage hc

/-- Every tuple whose size is at most the ambient dimension is linearly
independent at a dense set of ambient placements. -/
theorem dense_setOf_linearIndependent_precomp {C : Type*} [Fintype C]
    (c : C ↪ V) (hcard : Fintype.card C ≤ finrank ℝ E) :
    Dense {p : V → E | LinearIndependent ℝ (p ∘ c)} := by
  classical
  apply Cubical.dense_of_finite_bad_along_affine_path
  · obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
      (β := Fin (finrank ℝ E)) (by simpa using hcard)
    let q : C → E := fun i => Module.finBasis ℝ E (e i)
    have hq : LinearIndependent ℝ q :=
      (Module.finBasis ℝ E).linearIndependent.comp e e.injective
    refine ⟨Function.extend c q 0, ?_⟩
    simpa only [Function.extend_comp c.injective] using hq
  · intro p q t₀ h
    exact h.finite_setOf_not_along_affine_path

/-- A simultaneous placement for finitely many generically rigid graphs
on embedded vertex subsets and finitely many independent vertex tuples. -/
theorem exists_simultaneous_rigid_and_independent
    {I J : Type*} [Finite I] [Finite J]
    {W : I → Type*} [∀ i, Fintype (W i)]
    {C : J → Type*} [∀ j, Fintype (C j)]
    (G : ∀ i, SimpleGraph (W i)) (inc : ∀ i, W i ↪ V)
    (hG : ∀ i, GenericallyRigid (G i) E)
    (tuple : ∀ j, C j ↪ V)
    (hcard : ∀ j, Fintype.card (C j) ≤ finrank ℝ E) :
    ∃ p : V → E, (∀ i, IsRigid (G i) (p ∘ inc i)) ∧
      (∀ j, LinearIndependent ℝ (p ∘ tuple j)) := by
  have hR : Dense {p : V → E | ∀ i, IsRigid (G i) (p ∘ inc i)} := by
    simpa only [Set.mem_iInter, Set.mem_ofPred_eq, Set.ofPred_forall] using
      Cubical.dense_iInter_finite (fun i => {p : V → E | IsRigid (G i) (p ∘ inc i)})
        (fun i => isOpen_setOf_isRigid_precomp (G i) (inc i))
        (fun i => (hG i).dense_precomp (inc i))
  have hI : Dense {p : V → E | ∀ j, LinearIndependent ℝ (p ∘ tuple j)} := by
    simpa only [Set.mem_iInter, Set.mem_ofPred_eq, Set.ofPred_forall] using
      Cubical.dense_iInter_finite (fun j => {p : V → E | LinearIndependent ℝ (p ∘ tuple j)})
        (fun j => isOpen_setOf_linearIndependent_precomp (tuple j))
        (fun j => dense_setOf_linearIndependent_precomp (tuple j) (hcard j))
  have ho : IsOpen {p : V → E | ∀ j, LinearIndependent ℝ (p ∘ tuple j)} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun j => isOpen_setOf_linearIndependent_precomp (tuple j)
  exact (hR.inter_of_isOpen_right hI ho).nonempty

/-- Every set of at most `dim E` vertices is sent to linearly independent
vectors. This is a convenient stronger form of the affine general
position needed for pinning and splitting. -/
def InGeneralLinearPosition (p : V → E) : Prop :=
  ∀ s : Finset V, s.card ≤ finrank ℝ E →
    LinearIndependent ℝ (fun v : s => p v)

omit [Fintype V] [FiniteDimensional ℝ E] in
/-- General linear position applies to any injectively indexed tuple of
at most the ambient dimension. -/
theorem InGeneralLinearPosition.linearIndependent {p : V → E}
    (hp : InGeneralLinearPosition p) {C : Type*} [Fintype C]
    (c : C → V) (hc : Function.Injective c)
    (hcard : Fintype.card C ≤ finrank ℝ E) :
    LinearIndependent ℝ (p ∘ c) := by
  classical
  let s : Finset V := Finset.univ.image c
  have hs : s.card ≤ finrank ℝ E := by
    simpa [s, Finset.card_image_of_injective _ hc] using hcard
  let j : C → s := fun i => ⟨c i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hj : Function.Injective j := by
    intro a b hab
    exact hc (congrArg Subtype.val hab)
  exact (hp s hs).comp j hj

omit [Fintype V] [FiniteDimensional ℝ E] in
/-- Differences from one point in a small injective tuple are independent
in general linear position. -/
theorem InGeneralLinearPosition.differences {p : V → E}
    (hp : InGeneralLinearPosition p) {C : Type*} [Fintype C]
    (root : V) (c : C → V) (hc : Function.Injective c)
    (hne : ∀ i, c i ≠ root)
    (hcard : Fintype.card C + 1 ≤ finrank ℝ E) :
    LinearIndependent ℝ (fun i => p root - p (c i)) := by
  classical
  let q : Option C → V := fun i => i.elim root c
  have hq : Function.Injective q := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b => exact False.elim (hne b hab.symm)
    | some a =>
      cases b with
      | none => exact False.elim (hne a hab)
      | some b => exact congrArg some (hc hab)
  have hind := (hp.linearIndependent q hq (by simpa using hcard)).affineIndependent
  have hdiff := (affineIndependent_iff_linearIndependent_vsub ℝ (p ∘ q) none).mp hind
  let j : C → {i : Option C // i ≠ none} := fun i => ⟨some i, Option.some_ne_none i⟩
  have hj : Function.Injective j := by
    intro a b hab
    exact Option.some.inj (congrArg Subtype.val hab)
  have hneg := (hdiff.comp j hj).neg
  change LinearIndependent ℝ (fun i => -(p (c i) - p root)) at hneg
  simpa only [neg_sub] using hneg

/-- Finitely many generically rigid subgraphs admit one shared placement
in general linear position. -/
theorem exists_simultaneous_rigid_in_general_position
    {I : Type*} [Finite I] {W : I → Type*} [∀ i, Fintype (W i)]
    (G : ∀ i, SimpleGraph (W i)) (inc : ∀ i, W i ↪ V)
    (hG : ∀ i, GenericallyRigid (G i) E) :
    ∃ p : V → E, (∀ i, IsRigid (G i) (p ∘ inc i)) ∧ InGeneralLinearPosition p := by
  classical
  let J := {s : Finset V // s.card ≤ finrank ℝ E}
  let tuple : ∀ s : J, s.val ↪ V := fun s => ⟨Subtype.val, Subtype.val_injective⟩
  obtain ⟨p, hpG, hpI⟩ := exists_simultaneous_rigid_and_independent G inc hG tuple
    (fun s => by simpa using s.property)
  exact ⟨p, hpG, fun s hs => hpI ⟨s, hs⟩⟩

/-- A generically rigid graph has a rigid placement in general position. -/
theorem GenericallyRigid.exists_in_general_position {G : SimpleGraph V}
    (hG : GenericallyRigid G E) :
    ∃ p : V → E, IsRigid G p ∧ InGeneralLinearPosition p := by
  obtain ⟨p, hp, hpos⟩ := exists_simultaneous_rigid_in_general_position
    (fun _ : Unit => G) (fun _ => Function.Embedding.refl V) (fun _ => hG)
  exact ⟨p, hp (), hpos⟩

end Finite

end Cubical.Rigidity

end
end BundlePart12

section BundlePart13
/- Source: Cubical/VertexSplitting.lean -/
@[expose] public section



/-!
# Vertex splitting

A new vertex is placed at `p root + t • r`. The derivative equation for
the edge from the root to its split copy is divided by `t`; at zero the
resulting linear system remains meaningful. Exactness of this system at
zero forces exactness nearby and therefore rigidity at a nonzero split.
-/

namespace Cubical.Rigidity

open Module Filter
open scoped InnerProductSpace Topology
attribute [local instance] Classical.propDecidable

variable {V E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Collapse the new vertex onto the designated old vertex. -/
def collapseVertex (root : V) : Option V → V
  | none => root
  | some v => v

/-- The two orientations of the edge between the split vertices. -/
def IsSplitEdge (root : V) (a b : Option V) : Prop :=
  (a = none ∧ b = some root) ∨ (a = some root ∧ b = none)

/-- Split along a one-parameter line, leaving every old point fixed. -/
def splitPlacement (p : V → E) (root : V) (r : E) (t : ℝ) : Option V → E
  | none => p root + t • r
  | some v => p v

@[simp] theorem splitPlacement_zero (p : V → E) (root : V) (r : E) (v : Option V) :
    splitPlacement p root r 0 v = p (collapseVertex root v) := by
  cases v <;> simp [splitPlacement, collapseVertex]

/-- A system of edge constraints with specified normal vectors. -/
noncomputable def edgeConstraintMap (G : SimpleGraph V) (n : DirectedEdge G → E) :
    (V → E) →ₗ[ℝ] (DirectedEdge G → ℝ) where
  toFun u e := ⟪n e, u e.val.1 - u e.val.2⟫_ℝ
  map_add' u v := by
    funext e
    simp only [Pi.add_apply]
    have h : (u e.val.1 + v e.val.1) - (u e.val.2 + v e.val.2) =
      (u e.val.1 - u e.val.2) + (v e.val.1 - v e.val.2) := by abel
    rw [h, inner_add_right]
  map_smul' c u := by
    funext e
    simp [← smul_sub, real_inner_smul_right]

/-- The split edge uses the normal `r`, including when `t = 0`; every
other edge uses the ordinary edge vector. -/
noncomputable def splitConstraintMap (H : SimpleGraph (Option V))
    (p : V → E) (root : V) (r : E) (t : ℝ) :
    (Option V → E) →ₗ[ℝ] (DirectedEdge H → ℝ) := by
  classical
  exact edgeConstraintMap H fun e =>
    if IsSplitEdge root e.val.1 e.val.2 then r else
      splitPlacement p root r t e.val.1 - splitPlacement p root r t e.val.2

@[simp]
theorem splitConstraintMap_apply (H : SimpleGraph (Option V))
    (p : V → E) (root : V) (r : E) (t : ℝ) (u : Option V → E)
    (e : DirectedEdge H) :
    splitConstraintMap H p root r t u e =
      if IsSplitEdge root e.val.1 e.val.2 then ⟪r, u e.val.1 - u e.val.2⟫_ℝ
      else ⟪splitPlacement p root r t e.val.1 - splitPlacement p root r t e.val.2,
        u e.val.1 - u e.val.2⟫_ℝ := by
  classical
  simp only [splitConstraintMap, edgeConstraintMap, LinearMap.coe_mk, AddHom.coe_mk]
  split <;> rfl

/-- Trivial motions solve the normalized split system at every parameter,
including its coincident-vertex limit. -/
theorem splitConstraintMap_comp_trivialMotionMap
    (H : SimpleGraph (Option V)) (p : V → E) (root : V) (r : E) (t : ℝ) :
    (splitConstraintMap H p root r t).comp
      (trivialMotionMap (splitPlacement p root r t)) = 0 := by
  classical
  apply LinearMap.ext
  intro a
  funext e
  change splitConstraintMap H p root r t
    (trivialMotionMap (splitPlacement p root r t) a) e = 0
  rw [splitConstraintMap_apply]
  split_ifs with he
  · rcases he with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · simp only [ha, hb, trivialMotionMap, LinearMap.coe_mk, AddHom.coe_mk,
        splitPlacement, map_add, map_smul]
      have hsub : a.1 + (a.2.val (p root) + t • a.2.val r) -
          (a.1 + a.2.val (p root)) = t • a.2.val r := by abel
      rw [hsub, real_inner_smul_right, a.2.property.inner_self, mul_zero]
    · simp only [ha, hb, trivialMotionMap, LinearMap.coe_mk, AddHom.coe_mk,
        splitPlacement, map_add, map_smul]
      have hsub : a.1 + a.2.val (p root) -
          (a.1 + (a.2.val (p root) + t • a.2.val r)) = -(t • a.2.val r) := by abel
      rw [hsub, inner_neg_right, real_inner_smul_right, a.2.property.inner_self,
        mul_zero, neg_zero]
  · exact ((mem_range_trivialMotionMap _ _).mp
      (LinearMap.mem_range_self (trivialMotionMap _) a)).isMotion
      e.val.1 e.val.2 e.property

/-- At a nonzero parameter the normalized system and the ordinary
rigidity system have the same kernel. -/
theorem splitConstraintMap_ker_eq (H : SimpleGraph (Option V))
    (p : V → E) (root : V) (r : E) {t : ℝ} (ht : t ≠ 0) :
    LinearMap.ker (splitConstraintMap H p root r t) =
      LinearMap.ker (motionMap H (splitPlacement p root r t)) := by
  classical
  ext u
  simp only [LinearMap.mem_ker, funext_iff, Pi.zero_apply]
  constructor <;> intro hu e
  · have h := hu e
    rw [splitConstraintMap_apply] at h
    change ⟪splitPlacement p root r t e.val.1 - splitPlacement p root r t e.val.2,
      u e.val.1 - u e.val.2⟫_ℝ = 0
    split_ifs at h with he
    · rcases he with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · simp only [ha, hb] at h
        simp only [ha, hb, splitPlacement, add_sub_cancel_left,
          real_inner_smul_left, h, mul_zero]
      · have hs : p root - (p root + t • r) = -(t • r) := by abel
        simp only [ha, hb] at h
        simp only [ha, hb, splitPlacement, hs, inner_neg_left,
          real_inner_smul_left, h, mul_zero, neg_zero]
    · exact h
  · rw [splitConstraintMap_apply]
    have h := hu e
    change ⟪splitPlacement p root r t e.val.1 - splitPlacement p root r t e.val.2,
      u e.val.1 - u e.val.2⟫_ℝ = 0 at h
    split_ifs with he
    · rcases he with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · simp only [ha, hb, splitPlacement, add_sub_cancel_left, real_inner_smul_left] at h
        simpa only [ha, hb] using (mul_eq_zero.mp h).resolve_left ht
      · have hs : p root - (p root + t • r) = -(t • r) := by abel
        simp only [ha, hb, splitPlacement, hs, inner_neg_left, real_inner_smul_left,
          neg_eq_zero] at h
        simpa only [ha, hb] using (mul_eq_zero.mp h).resolve_left ht
    · exact h

/-- The normalized equations always imply the ordinary equations, even at
zero where the split edge's ordinary equation vanishes identically. -/
theorem splitConstraintMap_ker_le (H : SimpleGraph (Option V))
    (p : V → E) (root : V) (r : E) (t : ℝ) :
    LinearMap.ker (splitConstraintMap H p root r t) ≤
      LinearMap.ker (motionMap H (splitPlacement p root r t)) := by
  classical
  intro u hu
  rw [mem_ker_motionMap]
  intro a b hab
  have h := congrFun (LinearMap.mem_ker.mp hu) ⟨(a, b), hab⟩
  rw [splitConstraintMap_apply] at h
  simp only [Pi.zero_apply] at h
  split_ifs at h with he
  · rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [splitPlacement, add_sub_cancel_left, real_inner_smul_left, h, mul_zero]
    · have hs : p root - (p root + t • r) = -(t • r) := by abel
      simp only [splitPlacement, hs, inner_neg_left, real_inner_smul_left, h, mul_zero, neg_zero]
  · exact h

/-- Exactness at the coincident-vertex limit. The separating hypothesis
says that the common-neighbor differences, together with `r`, span space. -/
theorem splitConstraintMap_exact_at_zero
    {G : SimpleGraph V} {H : SimpleGraph (Option V)}
    (p : V → E) (root : V) (r : E) (hp : IsRigid G p)
    (hroot : H.Adj none (some root))
    (hcover : ∀ a b, G.Adj a b → ∃ x y : Option V,
      collapseVertex root x = a ∧ collapseVertex root y = b ∧ H.Adj x y)
    {C : Type*} (c : C → V)
    (hleft : ∀ i, H.Adj none (some (c i)))
    (hright : ∀ i, H.Adj (some root) (some (c i)))
    (hsep : ∀ z : E, (∀ i, ⟪p root - p (c i), z⟫_ℝ = 0) → ⟪r, z⟫_ℝ = 0 → z = 0) :
    LinearMap.range (trivialMotionMap (splitPlacement p root r 0)) =
      LinearMap.ker (splitConstraintMap H p root r 0) := by
  apply le_antisymm
  · rintro u ⟨a, rfl⟩
    apply LinearMap.mem_ker.mpr
    exact LinearMap.congr_fun (splitConstraintMap_comp_trivialMotionMap H p root r 0) a
  · intro u hu
    let δ := u none - u (some root)
    have hδ : δ = 0 := by
      apply hsep δ
      · intro i
        have hne : c i ≠ root := by
          intro hi
          have hbad := hright i
          simp [hi] at hbad
        have hL := congrFun (LinearMap.mem_ker.mp hu) ⟨(none, some (c i)), hleft i⟩
        have hR := congrFun (LinearMap.mem_ker.mp hu)
          ⟨(some root, some (c i)), hright i⟩
        simp [splitConstraintMap_apply, IsSplitEdge, splitPlacement, hne] at hL hR
        dsimp [δ]
        simp only [inner_sub_right] at hL hR ⊢
        linarith
      · have h := congrFun (LinearMap.mem_ker.mp hu) ⟨(none, some root), hroot⟩
        simpa [splitConstraintMap_apply, IsSplitEdge, δ] using h
    have heq : u none = u (some root) := sub_eq_zero.mp hδ
    have huCollapsed : ∀ x : Option V, u x = u (some (collapseVertex root x)) := by
      intro x
      cases x with
      | none => exact heq
      | some a => rfl
    have huMotion := (mem_ker_motionMap H _ u).mp
      (splitConstraintMap_ker_le H p root r 0 hu)
    have huBase : IsMotion G p (fun a => u (some a)) := by
      intro a b hab
      obtain ⟨x, y, hx, hy, hxy⟩ := hcover a b hab
      have h := huMotion x y hxy
      simpa only [splitPlacement_zero, huCollapsed x, huCollapsed y, hx, hy] using h
    obtain ⟨s, A, hA, hrep⟩ := hp (fun a => u (some a)) huBase
    apply (mem_range_trivialMotionMap _ u).mpr
    refine ⟨s, A, hA, ?_⟩
    intro x
    rw [splitPlacement_zero, huCollapsed x]
    exact hrep (collapseVertex root x)

section ContinuousSplit

variable [Fintype V] [FiniteDimensional ℝ E]

omit [Fintype V] [FiniteDimensional ℝ E] in
theorem continuous_splitPlacement (p : V → E) (root : V) (r : E) (v : Option V) :
    Continuous (fun t : ℝ => splitPlacement p root r t v) := by
  cases v with
  | none => exact continuous_const.add (continuous_id.smul continuous_const)
  | some v => exact continuous_const

omit [Fintype V] [FiniteDimensional ℝ E] in
theorem continuousAt_splitConstraintMap (H : SimpleGraph (Option V))
    (p : V → E) (root : V) (r : E) (t₀ : ℝ) (u : Option V → E) :
    ContinuousAt (fun t => splitConstraintMap H p root r t u) t₀ := by
  apply continuousAt_pi.mpr
  intro e
  by_cases he : IsSplitEdge root e.val.1 e.val.2
  · simp only [splitConstraintMap_apply, he, ite_eq_left]
    exact continuousAt_const
  · simp only [splitConstraintMap_apply, he]
    exact ((continuous_splitPlacement p root r e.val.1).continuousAt.sub
      (continuous_splitPlacement p root r e.val.2).continuousAt).inner continuousAt_const

/-- Vertex splitting preserves rigidity when the common-neighbor
differences together with a single direction span the ambient space.
Only the new vertex moves; all old coordinates are retained. -/
theorem exists_rigid_split_of_separating_direction
    {G : SimpleGraph V} {H : SimpleGraph (Option V)}
    (p : V → E) (root : V) (r : E) (hp : IsRigid G p)
    (hroot : H.Adj none (some root))
    (hcover : ∀ a b, G.Adj a b → ∃ x y : Option V,
      collapseVertex root x = a ∧ collapseVertex root y = b ∧ H.Adj x y)
    {C : Type*} (c : C → V)
    (hleft : ∀ i, H.Adj none (some (c i)))
    (hright : ∀ i, H.Adj (some root) (some (c i)))
    (hsep : ∀ z : E, (∀ i, ⟪p root - p (c i), z⟫_ℝ = 0) → ⟪r, z⟫_ℝ = 0 → z = 0) :
    ∃ t : ℝ, 0 < t ∧ IsRigid H (splitPlacement p root r t) := by
  classical
  have hevent := Exactness.eventually_range_eq_ker
    (fun t : ℝ => trivialMotionMap (splitPlacement p root r t))
    (fun t : ℝ => splitConstraintMap H p root r t) 0
    (continuousAt_trivialMotionMap _ 0
      (fun v => (continuous_splitPlacement p root r v).continuousAt))
    (continuousAt_splitConstraintMap H p root r 0)
    (splitConstraintMap_comp_trivialMotionMap H p root r)
    (splitConstraintMap_exact_at_zero p root r hp hroot hcover c hleft hright hsep)
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, hexact⟩ := (hpos.and (hevent.filter_mono nhdsWithin_le_nhds)).exists
  refine ⟨t, ht, (isRigid_iff_range_eq_ker H _).mpr ?_⟩
  rw [hexact, splitConstraintMap_ker_eq H p root r ht.ne']

omit [Fintype V] in
/-- A family spanning codimension at most one admits one additional
normal that separates every vector. -/
theorem exists_separating_direction {C : Type*} (v : C → E)
    (hdim : finrank ℝ E ≤ finrank ℝ (Submodule.span ℝ (Set.range v)) + 1) :
    ∃ r : E, ∀ z : E, (∀ i, ⟪v i, z⟫_ℝ = 0) → ⟪r, z⟫_ℝ = 0 → z = 0 := by
  let K : Submodule ℝ E := Submodule.span ℝ (Set.range v)
  have hdimK : finrank ℝ Kᗮ ≤ 1 := by
    have h := K.finrank_add_finrank_orthogonal
    change finrank ℝ E ≤ finrank ℝ K + 1 at hdim
    omega
  obtain ⟨r, hr⟩ := (finrank_le_one_iff (K := ℝ) (V := Kᗮ)).mp hdimK
  refine ⟨r, ?_⟩
  intro z hz hrz
  have hzK : z ∈ Kᗮ := by
    apply (K.mem_orthogonal z).mpr
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hz i
    | zero => simp
    | add x y _ _ hx hy => simp [inner_add_left, hx, hy]
    | smul c x _ hx => simp [real_inner_smul_left, hx]
  obtain ⟨a, ha⟩ := hr ⟨z, hzK⟩
  have ha' : a • (r : E) = z := congrArg Subtype.val ha
  have hz0 : ⟪z, z⟫_ℝ = 0 := by
    calc
      ⟪z, z⟫_ℝ = ⟪a • (r : E), z⟫_ℝ := by rw [ha']
      _ = a * ⟪(r : E), z⟫_ℝ := real_inner_smul_left _ _ _
      _ = 0 := by rw [hrz, mul_zero]
  exact inner_self_eq_zero.mp hz0

/-- Whiteley's vertex-splitting principle, with an arbitrary finite
ambient dimension and at least `dim E - 1` independent common-neighbor
differences. The old placement is preserved point by point. -/
theorem exists_rigid_vertex_split
    {G : SimpleGraph V} {H : SimpleGraph (Option V)}
    (p : V → E) (root : V) (hp : IsRigid G p)
    (hroot : H.Adj none (some root))
    (hcover : ∀ a b, G.Adj a b → ∃ x y : Option V,
      collapseVertex root x = a ∧ collapseVertex root y = b ∧ H.Adj x y)
    {C : Type*} [Fintype C] (c : C → V)
    (hleft : ∀ i, H.Adj none (some (c i)))
    (hright : ∀ i, H.Adj (some root) (some (c i)))
    (hind : LinearIndependent ℝ (fun i => p root - p (c i)))
    (hcard : finrank ℝ E ≤ Fintype.card C + 1) :
    ∃ q : Option V → E, IsRigid H q ∧ ∀ v, q (some v) = p v := by
  have hdim : finrank ℝ E ≤
      finrank ℝ (Submodule.span ℝ (Set.range (fun i => p root - p (c i)))) + 1 := by
    rw [finrank_span_eq_card hind]
    exact hcard
  obtain ⟨r, hr⟩ := exists_separating_direction (fun i => p root - p (c i)) hdim
  obtain ⟨t, _, ht⟩ := exists_rigid_split_of_separating_direction
    p root r hp hroot hcover c hleft hright hr
  exact ⟨splitPlacement p root r t, ht, fun _ => rfl⟩

end ContinuousSplit

end Cubical.Rigidity

end
end BundlePart13

section BundlePart14
/- Source: Cubical/GenericVertexSplitting.lean -/
@[expose] public section



/-!
# Generic vertex splitting and relabelling

The geometric splitting theorem combines with generic placements in
general position. Relabelling is explicit, so the final theorem applies
to arbitrary finite vertex types and a collapse with one double fiber.
-/

namespace Cubical.Rigidity

open Module

variable {V W E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Relabelling every vertex by an equivalence preserves genuine rigidity. -/
theorem isRigid_comap_iff (G : SimpleGraph W) (e : V ≃ W) (p : W → E) :
    IsRigid (G.comap e) (p ∘ e) ↔ IsRigid G p := by
  constructor
  · intro h u hu
    have hm : IsMotion (G.comap e) (p ∘ e) (u ∘ e) := by
      intro a b hab
      exact hu (e a) (e b) hab
    obtain ⟨t, A, hA, h⟩ := h _ hm
    exact ⟨t, A, hA, fun w => by simpa using h (e.symm w)⟩
  · intro h u hu
    have hm : IsMotion G p (u ∘ e.symm) := by
      intro a b hab
      have hab' : (G.comap e).Adj (e.symm a) (e.symm b) := by simpa using hab
      simpa using hu (e.symm a) (e.symm b) hab'
    obtain ⟨t, A, hA, h⟩ := h _ hm
    exact ⟨t, A, hA, fun v => by simpa using h (e v)⟩

/-- Generic rigidity is invariant under bijective vertex relabelling. -/
theorem genericallyRigid_comap_iff (G : SimpleGraph W) (e : V ≃ W) :
    GenericallyRigid (G.comap e) E ↔ GenericallyRigid G E := by
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p ∘ e.symm, (isRigid_comap_iff G e _).mp ?_⟩
    simpa only [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id] using hp
  · rintro ⟨p, hp⟩
    exact ⟨p ∘ e, (isRigid_comap_iff G e p).mpr hp⟩

/-- Splitting one vertex preserves generic rigidity when the two split
vertices are adjacent and have `dim E - 1` distinct common neighbors. -/
theorem GenericallyRigid.vertex_split_option [Fintype V] [FiniteDimensional ℝ E]
    {G : SimpleGraph V} {H : SimpleGraph (Option V)} (hG : GenericallyRigid G E)
    (root : V) (hroot : H.Adj none (some root))
    (hcover : ∀ a b, G.Adj a b → ∃ x y : Option V,
      collapseVertex root x = a ∧ collapseVertex root y = b ∧ H.Adj x y)
    {C : Type*} [Fintype C] (c : C → V) (hc : Function.Injective c)
    (hleft : ∀ i, H.Adj none (some (c i)))
    (hright : ∀ i, H.Adj (some root) (some (c i)))
    (hdim : finrank ℝ E = Fintype.card C + 1) :
    GenericallyRigid H E := by
  obtain ⟨p, hp, hpos⟩ := hG.exists_in_general_position
  have hne : ∀ i, c i ≠ root := by
    intro i hi
    have h := hright i
    rw [hi] at h
    exact H.irrefl h
  have hind := hpos.differences root c hc hne (by omega)
  obtain ⟨q, hq, _⟩ := exists_rigid_vertex_split p root hp hroot hcover c
    hleft hright hind (by omega)
  exact ⟨q, hq⟩

/-- Enlarging a graph without changing its vertices preserves generic
rigidity. -/
theorem GenericallyRigid.mono {G H : SimpleGraph V}
    (hG : GenericallyRigid G E) (hGH : G ≤ H) : GenericallyRigid H E := by
  obtain ⟨p, hp⟩ := hG
  exact ⟨p, hp.mono hGH⟩

/-- Transport generic rigidity through a graph isomorphism. -/
theorem GenericallyRigid.of_iso {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : GenericallyRigid G E) (e : G ≃g H) : GenericallyRigid H E := by
  apply (genericallyRigid_comap_iff H e.toEquiv).mp
  have he : H.comap e.toEquiv = G := by
    ext a b
    exact e.map_adj_iff
  rwa [he]

/-- A collapse with exactly one double fiber can be undone while
preserving generic rigidity, provided the split edge and enough common
neighbors are present. -/
theorem GenericallyRigid.of_vertex_collapse [Fintype V] [Fintype W]
    [FiniteDimensional ℝ E] {G : SimpleGraph W} {H : SimpleGraph V}
    (hG : GenericallyRigid G E) (f : V → W) (a b : V) (hab : a ≠ b)
    (hfsurj : Function.Surjective f)
    (hfiber : ∀ x y, f x = f y ↔ x = y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a))
    (hedge : H.Adj a b)
    (hcover : ∀ w z, G.Adj w z → ∃ x y, f x = w ∧ f y = z ∧ H.Adj x y)
    {C : Type*} [Fintype C] (c : C → V) (hc : Function.Injective c)
    (hcommon : ∀ i, H.Adj a (c i) ∧ H.Adj b (c i))
    (hdim : finrank ℝ E = Fintype.card C + 1) :
    GenericallyRigid H E := by
  classical
  have hfab : f a = f b := (hfiber a b).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have hex : ∀ w, ∃ x, f x = w ∧ x ≠ b := by
    intro w
    obtain ⟨x, hx⟩ := hfsurj w
    by_cases hxb : x = b
    · exact ⟨a, by simpa only [hxb, ← hfab] using hx, hab⟩
    · exact ⟨x, hx, hxb⟩
  choose s hsf hsne using hex
  have hsinj : Function.Injective s := by
    intro w z h
    calc w = f (s w) := (hsf w).symm
         _ = f (s z) := congrArg f h
         _ = z := hsf z
  have hsection : ∀ x, x ≠ b → s (f x) = x := by
    intro x hxb
    rcases (hfiber (s (f x)) x).mp (hsf (f x)) with h | ⟨_, hx⟩ | ⟨hs, _⟩
    · exact h
    · exact False.elim (hxb hx)
    · exact False.elim (hsne (f x) hs)
  let e : Option W ≃ V := Equiv.ofBijective (fun w => w.elim b s) (by
    constructor
    · intro w z h
      cases w with
      | none =>
        cases z with
        | none => rfl
        | some z => exact False.elim (hsne z h.symm)
      | some w =>
        cases z with
        | none => exact False.elim (hsne w h)
        | some z => exact congrArg some (hsinj h)
    · intro x
      by_cases hxb : x = b
      · exact ⟨none, hxb.symm⟩
      · exact ⟨some (f x), hsection x hxb⟩)
  have he_none : e none = b := rfl
  have he_some : ∀ w, e (some w) = s w := fun _ => rfl
  have he_root : e (some (f a)) = a := hsection a hab
  have hcomm : ∀ z : Option W, collapseVertex (f a) z = f (e z) := by
    intro z
    cases z with
    | none => exact hfab
    | some w => exact (hsf w).symm
  let H' := H.comap e
  have hedge' : H'.Adj none (some (f a)) := by
    change H.Adj (e none) (e (some (f a)))
    rw [he_none, he_root]
    exact hedge.symm
  have hcover' : ∀ w z, G.Adj w z → ∃ x y : Option W,
      collapseVertex (f a) x = w ∧ collapseVertex (f a) y = z ∧ H'.Adj x y := by
    intro w z hwz
    obtain ⟨x, y, hx, hy, hxy⟩ := hcover w z hwz
    refine ⟨e.symm x, e.symm y, ?_, ?_, ?_⟩
    · simpa only [hcomm, Equiv.apply_symm_apply] using hx
    · simpa only [hcomm, Equiv.apply_symm_apply] using hy
    · change H.Adj (e (e.symm x)) (e (e.symm y))
      simpa only [Equiv.apply_symm_apply] using hxy
  have hc' : Function.Injective (f ∘ c) := by
    intro i j hij
    rcases (hfiber (c i) (c j)).mp hij with h | ⟨hi, _⟩ | ⟨hi, _⟩
    · exact hc h
    · exact False.elim ((hcommon i).1.ne' hi)
    · exact False.elim ((hcommon i).2.ne' hi)
  have hleft : ∀ i, H'.Adj none (some ((f ∘ c) i)) := by
    intro i
    change H.Adj b (s (f (c i)))
    rw [hsection (c i) (hcommon i).2.ne']
    exact (hcommon i).2
  have hright : ∀ i, H'.Adj (some (f a)) (some ((f ∘ c) i)) := by
    intro i
    change H.Adj (s (f a)) (s (f (c i)))
    rw [hsection a hab, hsection (c i) (hcommon i).2.ne']
    exact (hcommon i).1
  have hH' := hG.vertex_split_option (f a) hedge' hcover' (f ∘ c) hc' hleft hright hdim
  exact (genericallyRigid_comap_iff H e).mp hH'

/-- Finset version of vertex splitting: any set of at least `dim E - 1`
common neighbors supplies the required independent subfamily. -/
theorem GenericallyRigid.of_vertex_collapse_finset [Fintype V] [Fintype W]
    [FiniteDimensional ℝ E] {G : SimpleGraph W} {H : SimpleGraph V}
    (hG : GenericallyRigid G E) (f : V → W) (a b : V) (hab : a ≠ b)
    (hfsurj : Function.Surjective f)
    (hfiber : ∀ x y, f x = f y ↔ x = y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a))
    (hedge : H.Adj a b)
    (hcover : ∀ w z, G.Adj w z → ∃ x y, f x = w ∧ f y = z ∧ H.Adj x y)
    (common : Finset V) (hcommon : ∀ x ∈ common, H.Adj a x ∧ H.Adj b x)
    (hdim : 0 < finrank ℝ E) (hcard : finrank ℝ E ≤ common.card + 1) :
    GenericallyRigid H E := by
  classical
  obtain ⟨c, hcsub, hccard⟩ := Finset.exists_subset_card_eq
    (s := common) (n := finrank ℝ E - 1) (by omega)
  exact hG.of_vertex_collapse f a b hab hfsurj hfiber hedge hcover
    (fun x : c => x.val) Subtype.val_injective
    (fun x => hcommon x.val (hcsub x.property)) (by simpa using (by omega :
      finrank ℝ E = c.card + 1))

end Cubical.Rigidity

end
end BundlePart14

section BundlePart15
/- Source: Cubical/CompleteRigidity.lean -/
@[expose] public section




/-!
# Complete graphs as rigidity bases

A complete graph on `d` orthonormal basis vectors is infinitesimally rigid
in dimension `d`. A complete graph on these vectors and the origin is
also rigid. Both statements use the full Euclidean-motion definition.
-/

namespace Cubical.Rigidity

open Module
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Skew-adjointness can be checked on a basis. -/
theorem isSkew_of_basis {ι : Type*} (b : Module.Basis ι ℝ E) (A : E →ₗ[ℝ] E)
    (h : ∀ i j, ⟪A (b i), b j⟫_ℝ = -⟪b i, A (b j)⟫_ℝ) : IsSkew A := by
  let B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ := (innerₛₗ ℝ).comp A
  let C : E →ₗ[ℝ] E →ₗ[ℝ] ℝ := -(innerₛₗ ℝ).compl₂ A
  have he : B = C := LinearMap.ext_basis b b h
  intro x y
  exact congrArg (fun f : E →ₗ[ℝ] E →ₗ[ℝ] ℝ => f x y) he

/-- The complete graph on an orthonormal basis is infinitesimally rigid,
including its translation component normal to the basis simplex. -/
theorem isRigid_complete_basis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) : IsRigid (⊤ : SimpleGraph ι) b := by
  intro u hu
  let t : E := b.repr.symm (WithLp.toLp 2 (fun i => ⟪b i, u i⟫_ℝ))
  have ht : ∀ i, ⟪b i, t⟫_ℝ = ⟪b i, u i⟫_ℝ := by
    intro i
    rw [← b.repr_apply_apply]
    simp [t]
  let r : ι → E := fun i => u i - t
  have hdiag : ∀ i, ⟪b i, r i⟫_ℝ = 0 := by
    intro i
    simp only [r, inner_sub_right, ht, sub_self]
  let A : E →ₗ[ℝ] E := b.toBasis.constr ℝ r
  have hAb : ∀ i, A (b i) = r i := fun i => b.toBasis.constr_basis ℝ r i
  have hskew : IsSkew A := by
    apply isSkew_of_basis b.toBasis A
    intro i j
    change ⟪A (b i), b j⟫_ℝ = -⟪b i, A (b j)⟫_ℝ
    rw [hAb, hAb]
    have hdist : ⟪b i - b j, r i - r j⟫_ℝ = 0 := by
      have hr : r i - r j = u i - u j := by dsimp [r]; abel
      rw [hr]
      by_cases hij : i = j
      · simp [hij]
      · exact hu i j hij
    simp only [inner_sub_left, inner_sub_right, hdiag] at hdist
    have hcomm := real_inner_comm (r i) (b j)
    linarith
  refine ⟨t, A, hskew, ?_⟩
  intro i
  rw [hAb]
  dsimp [r]
  abel

/-- The placement obtained by adjoining the origin to a basis. -/
def basisWithOrigin {ι : Type*} (b : ι → E) : Option ι → E
  | none => 0
  | some i => b i

/-- The complete graph on a basis and the origin is infinitesimally rigid. -/
theorem isRigid_complete_basisWithOrigin {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ E) :
    IsRigid (⊤ : SimpleGraph (Option ι)) (basisWithOrigin b) := by
  intro u hu
  let t := u none
  let r : ι → E := fun i => u (some i) - t
  have hdiag : ∀ i, ⟪b i, r i⟫_ℝ = 0 := by
    intro i
    have h := hu (some i) none (Option.some_ne_none i)
    simpa only [basisWithOrigin, sub_zero] using h
  let A : E →ₗ[ℝ] E := b.constr ℝ r
  have hAb : ∀ i, A (b i) = r i := fun i => b.constr_basis ℝ r i
  have hskew : IsSkew A := by
    apply isSkew_of_basis b A
    intro i j
    rw [hAb, hAb]
    have hdist : ⟪b i - b j, r i - r j⟫_ℝ = 0 := by
      have hr : r i - r j = u (some i) - u (some j) := by dsimp [r]; abel
      rw [hr]
      by_cases hij : i = j
      · simp [hij]
      · exact hu (some i) (some j) (by simpa using hij)
    simp only [inner_sub_left, inner_sub_right, hdiag] at hdist
    have hcomm := real_inner_comm (r i) (b j)
    linarith
  refine ⟨t, A, hskew, ?_⟩
  intro i
  cases i with
  | none => simp [basisWithOrigin, t]
  | some i =>
    simp only [basisWithOrigin, hAb]
    dsimp [r]
    abel

/-- A complete graph with as many vertices as the ambient dimension is
generically rigid. -/
theorem genericallyRigid_complete_of_card_eq_dim {V : Type*} [Fintype V]
    [FiniteDimensional ℝ E] (hcard : Fintype.card V = finrank ℝ E) :
    GenericallyRigid (⊤ : SimpleGraph V) E := by
  let e : V ≃ Fin (finrank ℝ E) := Fintype.equivOfCardEq (by simpa using hcard)
  have hG : GenericallyRigid (⊤ : SimpleGraph (Fin (finrank ℝ E))) E :=
    ⟨stdOrthonormalBasis ℝ E, isRigid_complete_basis _⟩
  have h := (genericallyRigid_comap_iff _ e).mpr hG
  have he : (⊤ : SimpleGraph (Fin (finrank ℝ E))).comap e = ⊤ := by
    ext a b
    simp [e.injective.ne_iff]
  rwa [he] at h

/-- A complete graph with `dim E + 1` vertices is generically rigid. -/
theorem genericallyRigid_complete_of_card_eq_dim_add_one {V : Type*} [Fintype V]
    [FiniteDimensional ℝ E] (hcard : Fintype.card V = finrank ℝ E + 1) :
    GenericallyRigid (⊤ : SimpleGraph V) E := by
  let e : V ≃ Option (Fin (finrank ℝ E)) := Fintype.equivOfCardEq (by simpa using hcard)
  have hG : GenericallyRigid (⊤ : SimpleGraph (Option (Fin (finrank ℝ E)))) E :=
    ⟨basisWithOrigin (Module.finBasis ℝ E), isRigid_complete_basisWithOrigin _⟩
  have h := (genericallyRigid_comap_iff _ e).mpr hG
  have he : (⊤ : SimpleGraph (Option (Fin (finrank ℝ E)))).comap e = ⊤ := by
    ext a b
    simp [e.injective.ne_iff]
  rwa [he] at h

end Cubical.Rigidity

end
end BundlePart15

section BundlePart16
/- Source: Cubical/SimplicialReindex.lean -/
@[expose] public section



/-!
# Reindexing finite simplicial circuits

Injectively indexed facet families are equivalent to their ordinary
facet sets. Repeated facets in a minimal circuit give the complete-graph
base case. These facts retain every multiplicity introduced by contraction.
-/

namespace Cubical.Simplicial

open scoped BigOperators
open Cubical.Rigidity
open Module

variable {V I : Type*} [DecidableEq V] [DecidableEq I]

/-- Passing from an injectively indexed family to its image preserves
minimality of the simplicial cycle. -/
theorem IsFacetCircuit.image {σ : I → Finset V} {s : Finset I}
    (hs : IsFacetCircuit σ s) (hinj : Set.InjOn σ s) :
    IsFacetCircuit id (s.image σ) := by
  classical
  refine ⟨hs.nonempty.image σ, ?_, ?_⟩
  · simpa only [Finset.sum_image hinj, id_eq] using hs.sum_eq_zero
  · intro t hts htne htz
    let r := s.filter (fun i => σ i ∈ t)
    have hrs : r ⊆ s := Finset.filter_subset _ _
    have hri : r.image σ = t := by
      ext a
      constructor
      · intro ha
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
        exact (Finset.mem_filter.mp hi).2
      · intro ha
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hts ha)
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, ha⟩, rfl⟩
    have hrne : r.Nonempty := by
      have h : (r.image σ).Nonempty := hri.symm ▸ htne
      exact Finset.image_nonempty.mp h
    have hrcycle : (∑ i ∈ r, boundary (Finsupp.single (σ i) 1)) = 0 := by
      rw [← Finset.sum_image (f := fun a : Finset V => boundary (Finsupp.single a 1))
        (hinj.mono hrs), hri]
      exact htz
    have hre := hs.minimal r hrs hrne hrcycle
    simpa only [hre] using hri.symm

/-- Homogeneity survives passage to the ordinary image family. -/
theorem Pure.image {n : ℕ} {σ : I → Finset V} {s : Finset I}
    (hs : Pure n σ s) : Pure n id (s.image σ) := by
  intro t ht
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
  exact hs i hi

@[simp]
theorem vertices_image (σ : I → Finset V) (s : Finset I) :
    vertices id (s.image σ) = vertices σ s := by
  ext v
  simp only [mem_vertices, Finset.mem_image, id_eq]
  aesop

@[simp]
theorem oneSkeleton_image (σ : I → Finset V) (s : Finset I) :
    oneSkeleton id (s.image σ) = oneSkeleton σ s := by
  ext v w
  simp only [oneSkeleton_adj, Finset.mem_image, id_eq]
  aesop

/-- The one-skeleton depends on the facet vertex sets, not on their
injective labelling. In fact multiplicities do not affect this graph. -/
noncomputable def supportGraphImageIso (σ : I → Finset V) (s : Finset I) :
    supportGraph σ s ≃g supportGraph id (s.image σ) where
  toEquiv := Finset.equivOfEq (vertices_image σ s).symm
  map_rel_iff' := by
    intro a b
    change (oneSkeleton id (s.image σ)).Adj a.val b.val ↔
      (oneSkeleton σ s).Adj a.val b.val
    rw [oneSkeleton_image]

/-- A two-copy facet family has a complete support graph. -/
theorem supportGraph_pair_eq_top {σ : I → Finset V} {i j : I}
    (hσ : σ i = σ j) : supportGraph σ {i, j} = ⊤ := by
  ext a b
  change ((a.val ≠ b.val) ∧ ∃ k ∈ ({i, j} : Finset I),
    a.val ∈ σ k ∧ b.val ∈ σ k) ↔ a ≠ b
  have ha : a.val ∈ σ i := by
    have h := a.property
    simpa [vertices, hσ] using h
  have hb : b.val ∈ σ i := by
    have h := b.property
    simpa [vertices, hσ] using h
  constructor
  · intro h hab
    exact h.1 (congrArg Subtype.val hab)
  · intro h
    exact ⟨fun hab => h (Subtype.ext hab), i, by simp, ha, hb⟩

/-- Duplicate minimal circuits provide the dimension-sized complete
rigidity base. -/
theorem genericallyRigid_pair {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} {σ : I → Finset V} {s : Finset I}
    (hpure : Pure n σ s) {i j : I} (hi : i ∈ s)
    (hσ : σ i = σ j) (hs : s = {i, j}) (hdim : finrank ℝ E = n) :
    GenericallyRigid (supportGraph σ s) E := by
  subst s
  rw [supportGraph_pair_eq_top hσ]
  apply genericallyRigid_complete_of_card_eq_dim
  have hv : vertices σ {i, j} = σ i := by simp [vertices, hσ]
  simpa only [Fintype.card_coe, hv, hdim] using hpure i hi

end Cubical.Simplicial

end
end BundlePart16

section BundlePart17
/- Source: Cubical/SimplicialFogelsangerDecomposition.lean -/





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

end
end BundlePart17

section BundlePart18
/- Source: Cubical/SimplicialRigidSplitting.lean -/
@[expose] public section



/-! # Rigidity of the completed parts under vertex splitting -/

namespace Cubical.Simplicial

open Module
open Cubical.Rigidity

variable {V E : Type*} [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The completed part is obtained from its contracted family by a
genuine Whiteley vertex split. All support and fiber claims are proved
from the explicit finite simplicial chains. -/
theorem EdgeCircuitPartition.lifted_genericallyRigid {u v : V} (huv : u ≠ v)
    {s : Finset (Finset V)} (p : EdgeCircuitPartition u v s)
    {n : ℕ} (hn : 3 ≤ n) (hpure : Pure n id s)
    (hs : IsFacetCircuit id s) (he : (oneSkeleton id s).Adj u v)
    {a : Finset (Finset V)} (ha : a ∈ p.parts)
    (hG : GenericallyRigid (supportGraph (contractedSimplex u v) a) E)
    (hdim : finrank ℝ E = n) :
    GenericallyRigid (supportGraph id (liftedPart u v a)) E := by
  classical
  let L := liftedPart u v a
  let X := {x // x ∈ vertices id L}
  let Y := {x // x ∈ vertices (contractedSimplex u v) a}
  have hvertices : vertices id L = vertices id a :=
    EdgeCircuitPartition.lifted_vertices_eq huv p hpure ha
  have hEdge : (oneSkeleton id L).Adj u v := p.lifted_has_edge huv hs he ha
  have hmem := oneSkeleton_adj_vertices hEdge
  have humem : u ∈ vertices id a := hvertices ▸ hmem.1
  have hvL : v ∈ vertices id L := hmem.2
  have hcontract : vertices (contractedSimplex u v) a = (vertices id L).erase v := by
    rw [contracted_vertices huv a humem, hvertices]
  let uL : X := ⟨u, hmem.1⟩
  let vL : X := ⟨v, hvL⟩
  let f : X → Y := fun x => ⟨collapse u v x.val, by
    rw [hcontract]
    by_cases hxv : x.val = v
    · simpa [collapse, hxv, huv] using hmem.1
    · simpa [collapse, hxv] using x.property⟩
  have hsurj : Function.Surjective f := by
    intro y
    have hymem : y.val ∈ (vertices id L).erase v := by
      rw [← hcontract]
      exact y.property
    have hy := Finset.mem_erase.mp hymem
    refine ⟨⟨y.val, hy.2⟩, ?_⟩
    apply Subtype.ext
    simp only [f]
    exact ite_eq_right hy.1
  have hfiber : ∀ x y : X, f x = f y ↔
      x = uL ∧ y = vL ∨ x = vL ∧ y = uL ∨ x = y := by
    intro x y
    constructor
    · intro h
      have hv : collapse u v x.val = collapse u v y.val :=
        congrArg (fun z : Y => z.val) h
      rcases (collapse_eq_iff huv x.val y.val).mp hv with hxy | hxy | hxy
      · exact Or.inr (Or.inr (Subtype.ext hxy))
      · exact Or.inl ⟨Subtype.ext hxy.1, Subtype.ext hxy.2⟩
      · exact Or.inr (Or.inl ⟨Subtype.ext hxy.1, Subtype.ext hxy.2⟩)
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl)
      · apply Subtype.ext
        simp [f, uL, vL, collapse, huv]
      · apply Subtype.ext
        simp [f, uL, vL, collapse, huv]
      · rfl
  have hcover : ∀ w z : Y, (supportGraph (contractedSimplex u v) a).Adj w z →
      ∃ x y : X, f x = w ∧ f y = z ∧ (supportGraph id L).Adj x y := by
    intro w z hwz
    obtain ⟨hwz, t, ht, hwt, hzt⟩ := hwz
    rw [contractedSimplex_eq_image] at hwt hzt
    obtain ⟨x, hxt, hxw⟩ := Finset.mem_image.mp hwt
    obtain ⟨y, hyt, hyz⟩ := Finset.mem_image.mp hzt
    have htL : t ∈ L := (mem_offEdge u v L t).mp
      ((p.lifted_offEdge huv ha).symm ▸ ht) |>.1
    have hxL : x ∈ vertices id L := (mem_vertices id L x).mpr ⟨t, htL, hxt⟩
    have hyL : y ∈ vertices id L := (mem_vertices id L y).mpr ⟨t, htL, hyt⟩
    refine ⟨⟨x, hxL⟩, ⟨y, hyL⟩, Subtype.ext hxw, Subtype.ext hyz, ?_⟩
    refine ⟨?_, t, htL, hxt, hyt⟩
    intro hxy
    change x = y at hxy
    apply hwz
    exact hxw.symm.trans (hxy ▸ hyz)
  obtain ⟨c, hc, hcommon⟩ := cycle_common_neighbors hn (p.lifted_pure huv hpure ha)
    (p.lifted_cycle huv ha) hEdge
  let inc : c ↪ X := ⟨fun x => ⟨x.val,
    (oneSkeleton_adj_vertices (hcommon x.val x.property).1).2⟩, by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : X => z.val) hxy⟩
  let common : Finset X := Finset.univ.map inc
  have hcommonX : ∀ x ∈ common, (supportGraph id L).Adj uL x ∧
      (supportGraph id L).Adj vL x := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hx
    exact hcommon y.val y.property
  apply hG.of_vertex_collapse_finset f uL vL
    (fun h => huv (congrArg Subtype.val h)) hsurj
    (fun x y => by simpa only [or_comm, or_left_comm, or_assoc] using hfiber x y)
    hEdge hcover common hcommonX
  · omega
  · have hcard : common.card = c.card := by simp [common]
    omega

end Cubical.Simplicial

end
end BundlePart18

section BundlePart19
/- Source: Cubical/GenericGluing.lean -/
@[expose] public section




/-!
# Gluing a connected family of rigid subgraphs

A connected family of rigid subgraphs covering all vertices is rigid
when every adjacent pair overlaps in at least the ambient dimension
many points in general position. Local Euclidean motions agree on each
overlap; connectedness makes one Euclidean motion valid everywhere.
-/

namespace Cubical.Rigidity

open Module

variable {V I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- At one general-position placement, rigidity glues across any
connected family of embedded subgraphs with sufficiently large overlaps. -/
theorem isRigid_of_connected_cover [Fintype V] [FiniteDimensional ℝ E]
    {W : I → Type*} [∀ i, Fintype (W i)]
    (G : SimpleGraph V) (K : SimpleGraph I) (hK : K.Connected)
    (piece : ∀ i, SimpleGraph (W i)) (inc : ∀ i, W i ↪ V)
    (hsub : ∀ i a b, (piece i).Adj a b → G.Adj (inc i a) (inc i b))
    (hcover : ∀ v, ∃ i w, inc i w = v)
    (common : I → I → Finset V)
    (hcommon : ∀ i j, K.Adj i j → ∀ v ∈ common i j,
      v ∈ Set.range (inc i) ∧ v ∈ Set.range (inc j))
    (hcard : ∀ i j, K.Adj i j → finrank ℝ E ≤ (common i j).card)
    (hdim : 0 < finrank ℝ E)
    (p : V → E) (hpos : InGeneralLinearPosition p)
    (hlocal : ∀ i, IsRigid (piece i) (p ∘ inc i)) :
    IsRigid G p := by
  classical
  intro u hu
  have hm : ∀ i, IsMotion (piece i) (p ∘ inc i) (u ∘ inc i) := by
    intro i a b hab
    exact hu (inc i a) (inc i b) (hsub i a b hab)
  choose t A hA heval using fun i => hlocal i (u ∘ inc i) (hm i)
  have hagree : ∀ i j, K.Adj i j → ∀ x : E, t i + A i x = t j + A j x := by
    intro i j hij
    obtain ⟨q⟩ := Function.Embedding.nonempty_of_card_le
      (α := Fin (finrank ℝ E)) (β := common i j) (by simpa using hcard i j hij)
    let c : Fin (finrank ℝ E) → V := fun a => (q a).val
    have hc : Function.Injective c := Subtype.val_injective.comp q.injective
    have hli : AffineIndependent ℝ (p ∘ c) :=
      (hpos.linearIndependent c hc (by simp)).affineIndependent
    have hpinned : ∀ a, t i + A i (p (c a)) = t j + A j (p (c a)) := by
      intro a
      obtain ⟨wi, hwi⟩ := (hcommon i j hij (c a) (q a).property).1
      obtain ⟨wj, hwj⟩ := (hcommon i j hij (c a) (q a).property).2
      have hi := heval i wi
      have hj := heval j wj
      simp only [Function.comp_apply, hwi, hwj] at hi hj
      exact hi.symm.trans hj
    have : Nonempty (Fin (finrank ℝ E)) := ⟨⟨0, hdim⟩⟩
    exact trivial_motion_agreement (t i) (t j) (A i) (A j) (hA i) (hA j)
      (p ∘ c) hli (by simp) hpinned
  have hall : ∀ i j, ∀ x : E, t i + A i x = t j + A j x := by
    intro i j
    obtain ⟨walk⟩ := hK i j
    induction walk with
    | nil => intro x; rfl
    | @cons i k j hik walk ih =>
      intro x
      exact (hagree i k hik x).trans (ih x)
  let i₀ : I := Classical.choice hK.nonempty
  refine ⟨t i₀, A i₀, hA i₀, ?_⟩
  intro v
  obtain ⟨i, w, hw⟩ := hcover v
  have h := heval i w
  simp only [Function.comp_apply, hw] at h
  exact h.trans (hall i i₀ (p v))

/-- Generic rigidity glues across a finite connected covering family
of subgraphs, with overlap size at least the ambient dimension. -/
theorem genericallyRigid_of_connected_cover [Fintype V] [Finite I]
    [FiniteDimensional ℝ E] {W : I → Type*} [∀ i, Fintype (W i)]
    (G : SimpleGraph V) (K : SimpleGraph I) (hK : K.Connected)
    (piece : ∀ i, SimpleGraph (W i)) (inc : ∀ i, W i ↪ V)
    (hsub : ∀ i a b, (piece i).Adj a b → G.Adj (inc i a) (inc i b))
    (hcover : ∀ v, ∃ i w, inc i w = v)
    (common : I → I → Finset V)
    (hcommon : ∀ i j, K.Adj i j → ∀ v ∈ common i j,
      v ∈ Set.range (inc i) ∧ v ∈ Set.range (inc j))
    (hcard : ∀ i j, K.Adj i j → finrank ℝ E ≤ (common i j).card)
    (hdim : 0 < finrank ℝ E)
    (hlocal : ∀ i, GenericallyRigid (piece i) E) :
    GenericallyRigid G E := by
  obtain ⟨p, hp, hpos⟩ := exists_simultaneous_rigid_in_general_position piece inc hlocal
  exact ⟨p, isRigid_of_connected_cover G K hK piece inc hsub hcover common
    hcommon hcard hdim p hpos hp⟩

end Cubical.Rigidity

end
end BundlePart19

section BundlePart20
/- Source: Cubical/RigidityCount.lean -/
@[expose] public section






/-!
# Edge counts from genuine infinitesimal rigidity

The edge derivative map has one coordinate per unoriented graph edge.
The space of infinitesimal rotations injects into the strictly upper
triangular coefficients of an orthonormal basis. Rank-nullity therefore
gives the usual rigidity lower bound on edges, with the correct constant.
-/

namespace Cubical.Rigidity

open Module
open scoped InnerProductSpace

variable {V E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Strictly ordered pairs of basis indices parametrize the independent
coefficients of a skew-adjoint operator. -/
abbrev UpperPair (k : ℕ) := {ij : Fin k × Fin k // ij.1 < ij.2}

/-- Read the upper triangular coefficients of a skew-adjoint operator. -/
noncomputable def skewCoordinates [FiniteDimensional ℝ E] :
    skewSubmodule (E := E) →ₗ[ℝ] (UpperPair (finrank ℝ E) → ℝ) where
  toFun A ij := ⟪stdOrthonormalBasis ℝ E ij.val.1,
    A.val (stdOrthonormalBasis ℝ E ij.val.2)⟫_ℝ
  map_add' A B := by funext ij; simp [inner_add_right]
  map_smul' c A := by funext ij; simp [real_inner_smul_right]

/-- Skew-adjointness determines every matrix coefficient from those
strictly above the diagonal. -/
theorem skewCoordinates_injective [FiniteDimensional ℝ E] :
    Function.Injective (skewCoordinates (E := E)) := by
  intro A B h
  apply Subtype.ext
  let b := stdOrthonormalBasis ℝ E
  apply b.toBasis.ext
  intro j
  apply b.repr.injective
  ext i
  simp only [b.repr_apply_apply]
  change ⟪b i, A.val (b j)⟫_ℝ = ⟪b i, B.val (b j)⟫_ℝ
  rcases lt_trichotomy i j with hij | hij | hji
  · exact congrFun h ⟨(i, j), hij⟩
  · subst j
    rw [A.property.inner_self, B.property.inner_self]
  · have hji' : ⟪b j, A.val (b i)⟫_ℝ = ⟪b j, B.val (b i)⟫_ℝ :=
      congrFun h ⟨(j, i), hji⟩
    have hA := A.property (b j) (b i)
    have hB := B.property (b j) (b i)
    have hcA := real_inner_comm (A.val (b j)) (b i)
    have hcB := real_inner_comm (B.val (b j)) (b i)
    linarith

/-- The dimension of the infinitesimal rotations is at most `k choose 2`. -/
theorem finrank_skewSubmodule_le [FiniteDimensional ℝ E] :
    finrank ℝ (skewSubmodule (E := E)) ≤ (finrank ℝ E).choose 2 := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (f := skewCoordinates (E := E)) skewCoordinates_injective
  rw [Module.finrank_pi] at h
  have hc : Fintype.card (UpperPair (finrank ℝ E)) = (finrank ℝ E).choose 2 := by
    simpa only [UpperPair, Fintype.card_subtype, Fintype.card_fin] using
      (Fintype.card_product_filter_lt (α := Fin (finrank ℝ E)))
  rwa [hc] at h

/-- Translation and rotation parameters have dimension at most
`(k+1) choose 2`. -/
theorem finrank_euclideanMotionParameters_le [FiniteDimensional ℝ E] :
    finrank ℝ (EuclideanMotionParameters E) ≤ (finrank ℝ E + 1).choose 2 := by
  rw [Module.finrank_prod]
  have h := finrank_skewSubmodule_le (E := E)
  have hc := Nat.choose_succ_succ (finrank ℝ E) 1
  norm_num only [Nat.choose_one_right, Nat.succ_eq_add_one, Nat.reduceAdd] at hc
  omega

/-- The derivative of an unoriented edge's squared length, up to its
irrelevant common factor two. -/
noncomputable def unorientedEdgeEquation (p u : V → E) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun a b => ⟪p a - p b, u a - u b⟫_ℝ, by
    intro a b
    have hp : p b - p a = -(p a - p b) := by abel
    have hu : u b - u a = -(u a - u b) := by abel
    dsimp only
    rw [hp, hu, inner_neg_neg]⟩

@[simp]
theorem unorientedEdgeEquation_mk (p u : V → E) (a b : V) :
    unorientedEdgeEquation p u s(a, b) = ⟪p a - p b, u a - u b⟫_ℝ := rfl

/-- One derivative constraint for each graph edge, with no duplicated
orientation coordinates. -/
noncomputable def unorientedMotionMap (G : SimpleGraph V) (p : V → E) :
    (V → E) →ₗ[ℝ] (G.edgeSet → ℝ) where
  toFun u e := unorientedEdgeEquation p u e.val
  map_add' u v := by
    funext e
    have h : ∀ x : Sym2 V,
        unorientedEdgeEquation p (u + v) x =
          unorientedEdgeEquation p u x + unorientedEdgeEquation p v x := by
      intro x
      induction x using Sym2.inductionOn with
      | hf a b =>
        simp only [unorientedEdgeEquation_mk, Pi.add_apply]
        have hs : u a + v a - (u b + v b) = (u a - u b) + (v a - v b) := by abel
        rw [hs, inner_add_right]
    exact h e.val
  map_smul' c u := by
    funext e
    have h : ∀ x : Sym2 V, unorientedEdgeEquation p (c • u) x =
        c • unorientedEdgeEquation p u x := by
      intro x
      induction x using Sym2.inductionOn with
      | hf a b => simp [← smul_sub, real_inner_smul_right]
    exact h e.val

@[simp]
theorem mem_ker_unorientedMotionMap (G : SimpleGraph V) (p u : V → E) :
    u ∈ LinearMap.ker (unorientedMotionMap G p) ↔ IsMotion G p u := by
  constructor
  · intro hu a b hab
    have h := congrFun (LinearMap.mem_ker.mp hu) ⟨s(a, b), hab⟩
    exact h
  · intro hu
    apply LinearMap.mem_ker.mpr
    funext e
    have h : ∀ x : Sym2 V, x ∈ G.edgeSet → unorientedEdgeEquation p u x = 0 := by
      intro x
      induction x using Sym2.inductionOn with
      | hf a b => exact hu a b
    exact h e.val e.property

/-- Rigidity identifies the kernel of the unoriented edge map with
translations and infinitesimal rotations. -/
theorem IsRigid.ker_unorientedMotionMap {G : SimpleGraph V} {p : V → E}
    (hp : IsRigid G p) :
    LinearMap.ker (unorientedMotionMap G p) = LinearMap.range (trivialMotionMap p) := by
  ext u
  rw [mem_ker_unorientedMotionMap, mem_range_trivialMotionMap]
  exact ⟨hp u, fun h => h.isMotion⟩

/-- The edge-count lower bound forced by infinitesimal rigidity. -/
theorem IsRigid.edge_count [Fintype V] [FiniteDimensional ℝ E]
    {G : SimpleGraph V} [Fintype G.edgeSet] {p : V → E} (hp : IsRigid G p) :
    finrank ℝ E * Fintype.card V ≤ Fintype.card G.edgeSet +
      (finrank ℝ E + 1).choose 2 := by
  have hrange : finrank ℝ (LinearMap.range (unorientedMotionMap G p)) ≤
      Fintype.card G.edgeSet := by
    simpa only [Module.finrank_pi] using
      Submodule.finrank_le (LinearMap.range (unorientedMotionMap G p))
  have hker : finrank ℝ (LinearMap.ker (unorientedMotionMap G p)) ≤
      (finrank ℝ E + 1).choose 2 := by
    rw [hp.ker_unorientedMotionMap]
    exact (trivialMotionMap p).finrank_range_le.trans finrank_euclideanMotionParameters_le
  have hdim := (unorientedMotionMap G p).finrank_range_add_finrank_ker
  have hpi : finrank ℝ (V → E) = Fintype.card V * finrank ℝ E := by
    simp [Module.finrank_pi_fintype]
  rw [hpi] at hdim
  rw [Nat.mul_comm (finrank ℝ E) (Fintype.card V)]
  omega

/-- Generic rigidity has the same unoriented edge-count consequence. -/
theorem GenericallyRigid.edge_count [Fintype V] [FiniteDimensional ℝ E]
    {G : SimpleGraph V} [Fintype G.edgeSet] (hG : GenericallyRigid G E) :
    finrank ℝ E * Fintype.card V ≤ Fintype.card G.edgeSet +
      (finrank ℝ E + 1).choose 2 := by
  obtain ⟨p, hp⟩ := hG
  exact hp.edge_count

end Cubical.Rigidity

end
end BundlePart20

section BundlePart21
/- Source: Cubical/Fogelsanger.lean -/
@[expose] public section





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

end
end BundlePart21

section BundlePart22
/- Source: Cubical/SimplicialFaces.lean -/





/-! # Faces, links, and incidence counting for finite simplicial families -/

@[expose] public section

namespace Cubical.Simplicial

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

/-- The faces with exactly `r` vertices in the complex generated by `s`. -/
def faces (s : Finset (Finset V)) (r : ℕ) : Finset (Finset V) :=
  s.biUnion (fun t => t.powersetCard r)

@[simp]
theorem mem_faces (s : Finset (Finset V)) (r : ℕ) (a : Finset V) :
    a ∈ faces s r ↔ a.card = r ∧ ∃ t ∈ s, a ⊆ t := by
  simp only [faces, Finset.mem_biUnion, Finset.mem_powersetCard]
  aesop

/-- The facet family of the link of `a`. No purity or topological condition
is imposed by this definition. -/
def link (s : Finset (Finset V)) (a : Finset V) : Finset (Finset V) :=
  (s.filter (a ⊆ ·)).image (· \ a)

@[simp]
theorem mem_link (s : Finset (Finset V)) (a t : Finset V) :
    t ∈ link s a ↔ Disjoint a t ∧ a ∪ t ∈ s := by
  constructor
  · intro ht
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hf, haf⟩ := Finset.mem_filter.mp hf
    refine ⟨Finset.disjoint_left.mpr (fun x hx hxa => (Finset.mem_sdiff.mp hxa).2 hx), ?_⟩
    simpa only [Finset.union_sdiff_of_subset haf] using hf
  · rintro ⟨hdisj, hmem⟩
    apply Finset.mem_image.mpr
    refine ⟨a ∪ t, Finset.mem_filter.mpr ⟨hmem, Finset.subset_union_left⟩, ?_⟩
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨ha | ht, hn⟩
      · exact (hn ha).elim
      · exact ht
    · intro ht
      exact ⟨Or.inr ht, fun ha => Finset.disjoint_left.mp hdisj ha ht⟩

@[simp]
theorem link_empty (s : Finset (Finset V)) : link s ∅ = s := by
  ext t
  simp

theorem link_link (s : Finset (Finset V)) {a b : Finset V}
    (hdisj : Disjoint a b) : link (link s a) b = link s (a ∪ b) := by
  ext t
  simp only [mem_link, Finset.disjoint_union_right, Finset.disjoint_union_left,
    hdisj, true_and, Finset.union_assoc]
  tauto

theorem Pure.link {n : ℕ} {s : Finset (Finset V)} (hpure : Pure n id s)
    (a : Finset V) : Pure (n - a.card) id (link s a) := by
  intro t ht
  obtain ⟨hdisj, hmem⟩ := (mem_link s a t).mp ht
  have hcard : (a ∪ t).card = n := hpure (a ∪ t) hmem
  rw [Finset.card_union_of_disjoint hdisj] at hcard
  change t.card = n - a.card
  omega

theorem faces_subset_vertices {s : Finset (Finset V)} {r : ℕ} {a : Finset V}
    (ha : a ∈ faces s r) : a ⊆ vertices id s := by
  obtain ⟨_, t, ht, hsub⟩ := (mem_faces s r a).mp ha
  intro v hv
  exact (mem_vertices id s v).mpr ⟨t, ht, hsub hv⟩

theorem faces_one (s : Finset (Finset V)) :
    faces s 1 = (vertices id s).image (fun v => {v}) := by
  ext a
  constructor
  · intro ha
    obtain ⟨hcard, t, ht, hsub⟩ := (mem_faces s 1 a).mp ha
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard
    exact Finset.mem_image.mpr ⟨v, (mem_vertices id s v).mpr
      ⟨t, ht, hsub (by simp)⟩, rfl⟩
  · intro ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨t, ht, hvt⟩ := (mem_vertices id s v).mp hv
    exact (mem_faces s 1 {v}).mpr ⟨by simp, t, ht, by simpa⟩

@[simp]
theorem faces_one_card (s : Finset (Finset V)) :
    (faces s 1).card = (vertices id s).card := by
  rw [faces_one, Finset.card_image_of_injective]
  exact fun _ _ h => Finset.singleton_injective h

theorem faces_top {n : ℕ} {s : Finset (Finset V)} (hpure : Pure n id s) :
    faces s n = s := by
  ext a
  constructor
  · intro ha
    obtain ⟨hcard, t, ht, hsub⟩ := (mem_faces s n a).mp ha
    have htcard : t.card = n := hpure t ht
    have heq : a = t := Finset.eq_of_subset_of_card_le hsub (by omega)
    exact heq ▸ ht
  · intro ha
    exact (mem_faces s n a).mpr ⟨hpure a ha, a, ha, Finset.Subset.rfl⟩

theorem faces_link_vertex {s : Finset (Finset V)} {v : V} {r : ℕ} {a : Finset V} :
    a ∈ faces (link s {v}) r ↔ v ∉ a ∧ insert v a ∈ faces s (r + 1) := by
  constructor
  · intro ha
    obtain ⟨hcard, t, ht, hat⟩ := (mem_faces (link s {v}) r a).mp ha
    obtain ⟨hdisj, hmem⟩ := (mem_link s {v} t).mp ht
    have hvt : v ∉ t := by simpa using hdisj
    have hva : v ∉ a := fun h => hvt (hat h)
    refine ⟨hva, (mem_faces s (r + 1) (insert v a)).mpr ⟨?_, {v} ∪ t, hmem, ?_⟩⟩
    · rw [Finset.card_insert_of_notMem hva, hcard]
    · exact Finset.insert_subset_iff.mpr ⟨by simp,
        hat.trans Finset.subset_union_right⟩
  · rintro ⟨hva, ha⟩
    obtain ⟨hcard, t, ht, hat⟩ := (mem_faces s (r + 1) (insert v a)).mp ha
    have hvt : v ∈ t := hat (by simp)
    refine (mem_faces (link s {v}) r a).mpr ⟨?_, t.erase v, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hva] at hcard
      omega
    · apply (mem_link s {v} (t.erase v)).mpr
      refine ⟨by simp, ?_⟩
      simpa only [Finset.singleton_union, Finset.insert_erase hvt] using ht
    · intro x hx
      exact Finset.mem_erase.mpr ⟨fun he => hva (he ▸ hx), hat (Finset.mem_insert_of_mem hx)⟩

theorem faces_link_vertex_image (s : Finset (Finset V)) (v : V) (r : ℕ) :
    (faces (link s {v}) r).image (insert v) = (faces s (r + 1)).filter (v ∈ ·) := by
  ext a
  constructor
  · intro ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_filter.mpr ⟨(faces_link_vertex.mp hb).2, by simp⟩
  · intro ha
    obtain ⟨ha, hva⟩ := Finset.mem_filter.mp ha
    refine Finset.mem_image.mpr ⟨a.erase v, ?_, Finset.insert_erase hva⟩
    apply faces_link_vertex.mpr
    exact ⟨Finset.notMem_erase _ _, by simpa only [Finset.insert_erase hva] using ha⟩

theorem faces_link_vertex_card (s : Finset (Finset V)) (v : V) (r : ℕ) :
    (faces (link s {v}) r).card = ((faces s (r + 1)).filter (v ∈ ·)).card := by
  rw [← faces_link_vertex_image]
  symm
  apply Finset.card_image_iff.mpr
  intro a ha b hb hab
  have hva := (faces_link_vertex.mp ha).1
  have hvb := (faces_link_vertex.mp hb).1
  have h := congrArg (fun t : Finset V => t.erase v) hab
  simpa only [Finset.erase_insert hva, Finset.erase_insert hvb] using h

/-- Count incidences between vertices and faces in the two directions. -/
theorem sum_link_faces (s : Finset (Finset V)) (r : ℕ) :
    (∑ v ∈ vertices id s, (faces (link s {v}) r).card) =
      (r + 1) * (faces s (r + 1)).card := by
  calc
    (∑ v ∈ vertices id s, (faces (link s {v}) r).card) =
        ∑ v ∈ vertices id s, ∑ a ∈ faces s (r + 1), if v ∈ a then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [faces_link_vertex_card, Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ a ∈ faces s (r + 1), ∑ v ∈ vertices id s, if v ∈ a then 1 else 0 :=
      Finset.sum_comm
    _ =
        ∑ a ∈ faces s (r + 1), a.card := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
      congr 1
      ext v
      simp only [Finset.mem_filter]
      exact ⟨And.right, fun hv => ⟨faces_subset_vertices ha hv, hv⟩⟩
    _ = (r + 1) * (faces s (r + 1)).card := by
      have heq : ∀ a ∈ faces s (r + 1), a.card = r + 1 := fun a ha => (mem_faces _ _ _).mp ha |>.1
      rw [Finset.sum_congr rfl heq]
      simp [Nat.mul_comm]

theorem sum_link_vertices (s : Finset (Finset V)) :
    (∑ v ∈ vertices id s, (vertices id (link s {v})).card) = 2 * (faces s 2).card := by
  simpa only [faces_one_card] using sum_link_faces s 1

/-- The circuit property for every link of dimension at least two. -/
def HasCircuitLinks (n : ℕ) (s : Finset (Finset V)) : Prop :=
  ∀ a : Finset V, (∃ t ∈ s, a ⊆ t) → a.card + 3 ≤ n → IsFacetCircuit id (link s a)

theorem HasCircuitLinks.circuit {n : ℕ} {s : Finset (Finset V)}
    (h : HasCircuitLinks n s) (hn : 3 ≤ n) (hne : s.Nonempty) : IsFacetCircuit id s := by
  obtain ⟨t, ht⟩ := hne
  simpa only [link_empty] using h ∅ ⟨t, ht, Finset.empty_subset _⟩ (by simpa using hn)

theorem HasCircuitLinks.link_vertex {n : ℕ} {s : Finset (Finset V)}
    (h : HasCircuitLinks n s) (v : V) : HasCircuitLinks (n - 1) (link s {v}) := by
  intro a ha hcard
  obtain ⟨t, ht, hat⟩ := ha
  obtain ⟨hdisj, hmem⟩ := (mem_link s {v} t).mp ht
  have hva : v ∉ a := by
    have hvt : v ∉ t := by simpa using hdisj
    exact fun hv => hvt (hat hv)
  have hdisja : Disjoint ({v} : Finset V) a := by simpa using hva
  rw [link_link s hdisja]
  apply h
  · exact ⟨{v} ∪ t, hmem, Finset.union_subset_union_right hat⟩
  · simp only [Finset.singleton_union, Finset.card_insert_of_notMem hva]
    omega

theorem link_vertex_nonempty {s : Finset (Finset V)} {v : V}
    (hv : v ∈ vertices id s) : (link s {v}).Nonempty := by
  obtain ⟨t, ht, hvt⟩ := (mem_vertices id s v).mp hv
  change v ∈ t at hvt
  refine ⟨t.erase v, (mem_link s {v} (t.erase v)).mpr ⟨by simp, ?_⟩⟩
  simpa only [Finset.singleton_union, Finset.insert_erase hvt] using ht

end Cubical.Simplicial

end
end BundlePart22

section BundlePart23
/- Source: Cubical/SimplicialFaceGraph.lean -/





/-! # The edge count of a simplicial family equals its number of two-element faces -/

@[expose] public section

namespace Cubical.Simplicial

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

theorem mem_vertices_link_vertex (s : Finset (Finset V)) (v w : V) :
    w ∈ vertices id (link s {v}) ↔ (oneSkeleton id s).Adj v w := by
  constructor
  · intro hw
    obtain ⟨t, ht, hwt⟩ := (mem_vertices id (link s {v}) w).mp hw
    obtain ⟨hdisj, hmem⟩ := (mem_link s {v} t).mp ht
    have hvt : v ∉ t := by simpa using hdisj
    refine ⟨fun h => hvt (h.symm ▸ hwt), {v} ∪ t, hmem, by simp, ?_⟩
    exact Finset.mem_union_right _ hwt
  · rintro ⟨hvw, t, ht, hvt, hwt⟩
    change v ∈ t at hvt
    change w ∈ t at hwt
    refine (mem_vertices id (link s {v}) w).mpr ⟨t.erase v, ?_, ?_⟩
    · apply (mem_link s {v} (t.erase v)).mpr
      refine ⟨by simp, ?_⟩
      simpa only [Finset.singleton_union, Finset.insert_erase hvt] using ht
    · exact Finset.mem_erase.mpr ⟨hvw.symm, hwt⟩

theorem supportGraph_degree (s : Finset (Finset V)) (v : {v // v ∈ vertices id s})
    [Fintype ((supportGraph id s).neighborSet v)] :
    (supportGraph id s).degree v = (vertices id (link s {v.val})).card := by
  classical
  have himage : ((supportGraph id s).neighborFinset v).image Subtype.val =
      vertices id (link s {v.val}) := by
    ext w
    constructor
    · intro hw
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
      exact (mem_vertices_link_vertex s v.val x.val).mpr
        ((supportGraph id s).mem_neighborFinset v x |>.mp hx)
    · intro hw
      have hadj := (mem_vertices_link_vertex s v.val w).mp hw
      have hwm := (oneSkeleton_adj_vertices hadj).2
      exact Finset.mem_image.mpr ⟨⟨w, hwm⟩,
        ((supportGraph id s).mem_neighborFinset v ⟨w, hwm⟩).mpr hadj, rfl⟩
  rw [← himage, Finset.card_image_of_injective _ Subtype.val_injective]
  exact ((supportGraph id s).card_neighborFinset_eq_degree v).symm

theorem supportGraph_edge_count_eq_faces (s : Finset (Finset V)) :
    Nat.card (supportGraph id s).edgeSet = (faces s 2).card := by
  classical
  have hsum := (supportGraph id s).sum_degrees_eq_twice_card_edges
  have hlink : (∑ v : {v // v ∈ vertices id s}, (supportGraph id s).degree v) =
      2 * (faces s 2).card := by
    simp_rw [supportGraph_degree]
    change (∑ v ∈ (vertices id s).attach, (vertices id (link s {v.val})).card) = _
    rw [Finset.sum_attach (vertices id s) (fun v => (vertices id (link s {v})).card)]
    exact sum_link_vertices s
  rw [hlink, ← SimpleGraph.card_edgeSet] at hsum
  rw [Nat.card_eq_fintype_card]
  omega

end Cubical.Simplicial

end
end BundlePart23

section BundlePart24
/- Source: Cubical/PseudomanifoldCircuit.lean -/





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

end
end BundlePart24

section BundlePart25
/- Source: Cubical/SimplicialRidgeCount.lean -/





/-! # Facet-ridge incidence for finite simplicial pseudomanifolds -/

@[expose] public section

namespace Cubical.Simplicial

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

theorem mem_simplexBoundary_iff {s t : Finset V} :
    t ∈ simplexBoundary s ↔ t ⊆ s ∧ t.card + 1 = s.card := by
  constructor
  · intro h
    exact ⟨simplexBoundary_subset h, simplexBoundary_card h⟩
  · rintro ⟨hsub, hcard⟩
    obtain ⟨v, hv, hvn⟩ := Finset.exists_mem_notMem_of_card_lt_card (by omega : t.card < s.card)
    have hsub' : t ⊆ s.erase v := by
      intro x hx
      exact Finset.mem_erase.mpr ⟨fun h => hvn (h ▸ hx), hsub hx⟩
    have hc := Finset.card_erase_add_one hv
    have heq : t = s.erase v := Finset.eq_of_subset_of_card_le hsub' (by omega)
    exact Finset.mem_image.mpr ⟨v, hv, heq.symm⟩

@[simp]
theorem simplexBoundary_card_eq (s : Finset V) : (simplexBoundary s).card = s.card := by
  exact Finset.card_image_iff.mpr s.erase_injOn

theorem simplexBoundary_subset_faces {n : ℕ} {s : Finset (Finset V)}
    (hpure : Pure n id s) {t : Finset V} (ht : t ∈ s) :
    simplexBoundary t ⊆ faces s (n - 1) := by
  intro r hr
  have hc := simplexBoundary_card hr
  have hct : t.card = n := hpure t ht
  exact (mem_faces s (n - 1) r).mpr
    ⟨by omega, t, ht, simplexBoundary_subset hr⟩

theorem RidgeDegreeTwo.ridge_incidence {n : ℕ} (hn : 0 < n)
    {s : Finset (Finset V)} (hpure : Pure n id s) (hdeg : RidgeDegreeTwo s) :
    n * s.card = 2 * (faces s (n - 1)).card := by
  have hleft : (∑ t ∈ s, ((faces s (n - 1)).filter
      (fun r => r ∈ simplexBoundary t)).card) = n * s.card := by
    have hterm : ∀ t ∈ s, ((faces s (n - 1)).filter
        (fun r => r ∈ simplexBoundary t)).card = n := by
      intro t ht
      have heq : (faces s (n - 1)).filter (fun r => r ∈ simplexBoundary t) =
          simplexBoundary t := by
        ext r
        simp only [Finset.mem_filter]
        exact ⟨And.right, fun hr => ⟨simplexBoundary_subset_faces hpure ht hr, hr⟩⟩
      rw [heq, simplexBoundary_card_eq]
      exact hpure t ht
    rw [Finset.sum_congr rfl hterm]
    simp [Nat.mul_comm]
  have hright : (∑ r ∈ faces s (n - 1), (s.filter
      (fun t => r ∈ simplexBoundary t)).card) = 2 * (faces s (n - 1)).card := by
    have hterm : ∀ r ∈ faces s (n - 1), (s.filter
        (fun t => r ∈ simplexBoundary t)).card = 2 := by
      intro r hr
      obtain ⟨hcr, t, ht, hsub⟩ := (mem_faces s (n - 1) r).mp hr
      have hct : t.card = n := hpure t ht
      have hrb : r ∈ simplexBoundary t := mem_simplexBoundary_iff.mpr ⟨hsub, by omega⟩
      have hpos : 0 < (s.filter (fun t => r ∈ simplexBoundary t)).card :=
        Finset.card_pos.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, hrb⟩⟩
      rcases hdeg r with hz | ht
      · omega
      · exact ht
    rw [Finset.sum_congr rfl hterm]
    simp [Nat.mul_comm]
  have hswap : (∑ t ∈ s, ((faces s (n - 1)).filter
      (fun r => r ∈ simplexBoundary t)).card) =
      ∑ r ∈ faces s (n - 1), (s.filter (fun t => r ∈ simplexBoundary t)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  exact hleft.symm.trans (hswap.trans hright)

end Cubical.Simplicial

end
end BundlePart25

section BundlePart26
/- Source: Cubical/SimplicialLowerBound.lean -/
@[expose] public section





/-! # The simplicial lower bound theorem from minimal-cycle rigidity

All face numbers count actual finite vertex subsets. The induction uses actual
vertex links, and every edge lower bound is supplied by the kernel-checked
Fogelsanger theorem. No lower bound is assumed in the complex hypotheses.
-/

namespace Cubical.Simplicial

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

theorem IsFacetCircuit.two_faces_lower_bound {n : ℕ} {s : Finset (Finset V)}
    (hs : IsFacetCircuit id s) (hn : 3 ≤ n) (hpure : Pure n id s) :
    n * (vertices id s).card ≤ (faces s 2).card + (n + 1).choose 2 := by
  classical
  have h := hs.edge_count hn hpure
  rw [← Nat.card_eq_fintype_card, supportGraph_edge_count_eq_faces] at h
  exact h

/-- The binomial arithmetic in the McMullen--Perles--Walkup induction. -/
theorem simplicial_mpw_step {n r N e F : ℕ} (hn : 0 < n) (hr : 2 ≤ r)
    (hedge : n * N ≤ e + (n + 1).choose 2)
    (hlink : 2 * (n - 1).choose (r - 2) * e ≤
      r * F + (r - 2) * n.choose (r - 1) * N) :
    n.choose (r - 1) * N ≤ F + (r - 1) * (n + 1).choose r := by
  let A := (n - 1).choose (r - 2)
  let B := n.choose (r - 1)
  let C := (n + 1).choose r
  let T := (n + 1).choose 2
  have hA : n * A = B * (r - 1) := by
    have h := Nat.add_one_mul_choose_eq (n - 1) (r - 2)
    have hn' : n - 1 + 1 = n := by omega
    have hr' : r - 2 + 1 = r - 1 := by omega
    simpa only [hn', hr'] using h
  have hB : (n + 1) * B = C * r := by
    have h := Nat.add_one_mul_choose_eq n (r - 1)
    have hr' : r - 1 + 1 = r := by omega
    simpa only [hr'] using h
  have hT : (n + 1) * n = T * 2 := by
    simpa only [Nat.choose_one_right] using Nat.add_one_mul_choose_eq n 1
  have hconst : 2 * A * T = r * ((r - 1) * C) := by
    calc
      2 * A * T = A * ((n + 1) * n) := by rw [hT]; ring
      _ = (n + 1) * (n * A) := by ring
      _ = (n + 1) * (B * (r - 1)) := by rw [hA]
      _ = ((n + 1) * B) * (r - 1) := by ring
      _ = (C * r) * (r - 1) := by rw [hB]
      _ = r * ((r - 1) * C) := by ring
  have hcoeff : r * (B * N) + (r - 2) * B * N = 2 * A * (n * N) := by
    have hrarith : r + (r - 2) = 2 * (r - 1) := by omega
    calc
      r * (B * N) + (r - 2) * B * N = (r + (r - 2)) * B * N := by ring
      _ = (2 * (r - 1)) * B * N := by rw [hrarith]
      _ = 2 * (B * (r - 1)) * N := by ring
      _ = 2 * (n * A) * N := by rw [← hA]
      _ = 2 * A * (n * N) := by ring
  have hfinal : r * (B * N) + (r - 2) * B * N ≤
      r * (F + (r - 1) * C) + (r - 2) * B * N := by
    calc
      r * (B * N) + (r - 2) * B * N = 2 * A * (n * N) := hcoeff
      _ ≤ 2 * A * (e + T) := Nat.mul_le_mul_left _ hedge
      _ = 2 * A * e + 2 * A * T := by ring
      _ ≤ (r * F + (r - 2) * B * N) + 2 * A * T := Nat.add_le_add_right hlink _
      _ = r * (F + (r - 1) * C) + (r - 2) * B * N := by rw [hconst]; ring
  have hmul : r * (B * N) ≤ r * (F + (r - 1) * C) :=
    Nat.le_of_add_le_add_right hfinal
  exact Nat.le_of_mul_le_mul_left hmul (by omega)

/-- Every lower-dimensional face-number bound for a pure finite simplicial
family whose links of dimension at least two are minimal mod-two cycles. -/
theorem simplicial_lower_bound {n : ℕ} (hn : 3 ≤ n)
    {s : Finset (Finset V)} (hne : s.Nonempty) (hpure : Pure n id s)
    (hlinks : HasCircuitLinks n s) {r : ℕ} (hr : 1 ≤ r) (hrn : r ≤ n - 1) :
    n.choose (r - 1) * (vertices id s).card ≤
      (faces s r).card + (r - 1) * (n + 1).choose r := by
  classical
  induction n using Nat.strong_induction_on generalizing s r with
  | h n ih =>
    by_cases hr1 : r = 1
    · subst r
      simp
    have hr2 : 2 ≤ r := by omega
    have hedge := (hlinks.circuit hn hne).two_faces_lower_bound hn hpure
    by_cases hr_eq : r = 2
    · subst r
      simpa using hedge
    have hr3 : 3 ≤ r := by omega
    have hn4 : 4 ≤ n := by omega
    have hlocal : ∀ v ∈ vertices id s,
        (n - 1).choose (r - 2) * (vertices id (link s {v})).card ≤
          (faces (link s {v}) (r - 1)).card +
            (r - 2) * n.choose (r - 1) := by
      intro v hv
      have hlpure : Pure (n - 1) id (link s {v}) := by simpa using hpure.link {v}
      have h := ih (n - 1) (by omega) (by omega : 3 ≤ n - 1)
        (link_vertex_nonempty hv) hlpure (hlinks.link_vertex v)
        (r := r - 1) (by omega) (by omega)
      have hr' : r - 1 - 1 = r - 2 := by omega
      have hn' : n - 1 + 1 = n := by omega
      simpa only [hr', hn'] using h
    have hsum := Finset.sum_le_sum hlocal
    have hsumlinks := sum_link_faces s (r - 1)
    have hr' : r - 1 + 1 = r := by omega
    rw [hr'] at hsumlinks
    have hlink : 2 * (n - 1).choose (r - 2) * (faces s 2).card ≤
        r * (faces s r).card + (r - 2) * n.choose (r - 1) * (vertices id s).card := by
      simpa only [← Finset.mul_sum, Finset.sum_add_distrib, sum_link_vertices,
        hsumlinks, Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_assoc,
        Nat.mul_comm, Nat.mul_left_comm] using hsum
    exact simplicial_mpw_step (by omega) hr2 hedge hlink

/-- The facet form of the simplicial lower bound theorem. -/
theorem simplicial_facet_lower_bound {n : ℕ} (hn : 3 ≤ n)
    {s : Finset (Finset V)} (hne : s.Nonempty) (hpure : Pure n id s)
    (hlinks : HasCircuitLinks n s) (hdeg : RidgeDegreeTwo s) :
    (n - 1) * (vertices id s).card ≤ s.card + (n - 2) * (n + 1) := by
  have hlower := simplicial_lower_bound hn hne hpure hlinks
    (r := n - 1) (by omega) le_rfl
  have hsub : n - 1 - 1 = n - 2 := by omega
  rw [hsub] at hlower
  have hchoose₁ : 2 * n.choose (n - 2) = n * (n - 1) := by
    rw [Nat.choose_symm (by omega : 2 ≤ n)]
    have h := Nat.add_one_mul_choose_eq (n - 1) 1
    have hn' : n - 1 + 1 = n := by omega
    simpa only [hn', Nat.choose_one_right, Nat.mul_comm] using h.symm
  have hchoose₂ : 2 * (n + 1).choose (n - 1) = n * (n + 1) := by
    have hidx : n - 1 = n + 1 - 2 := by omega
    rw [hidx, Nat.choose_symm (by omega : 2 ≤ n + 1)]
    have h := Nat.add_one_mul_choose_eq n 1
    simpa only [Nat.choose_one_right, Nat.mul_comm] using h.symm
  have hridges := hdeg.ridge_incidence (by omega : 0 < n) hpure
  have hmul := Nat.mul_le_mul_left 2 hlower
  have hrew : n * ((n - 1) * (vertices id s).card) ≤
      n * (s.card + (n - 2) * (n + 1)) := by
    calc
      n * ((n - 1) * (vertices id s).card) =
          (2 * n.choose (n - 2)) * (vertices id s).card := by rw [hchoose₁]; ring
      _ ≤ 2 * ((faces s (n - 1)).card + (n - 2) * (n + 1).choose (n - 1)) := by
        simpa only [Nat.mul_assoc] using hmul
      _ = 2 * (faces s (n - 1)).card +
          (n - 2) * (2 * (n + 1).choose (n - 1)) := by ring
      _ = n * s.card + (n - 2) * (n * (n + 1)) := by rw [← hridges, hchoose₂]
      _ = n * (s.card + (n - 2) * (n + 1)) := by ring
  exact Nat.le_of_mul_le_mul_left hrew (by omega)

end Cubical.Simplicial

end
end BundlePart26

section BundlePart27
/- Source: Cubical/SimplicialEmbedding.lean -/
@[expose] public section



/-! # Injective changes of the ambient vertex type -/

namespace Cubical.Simplicial

open scoped BigOperators

variable {V W I : Type*} [DecidableEq V] [DecidableEq W] [DecidableEq I]

noncomputable def mapChain (e : V ↪ W) : Chain V →ₗ[ZMod 2] Chain W :=
  Finsupp.lmapDomain (ZMod 2) (ZMod 2) (Finset.map e)

@[simp]
theorem mapChain_single (e : V ↪ W) (s : Finset V) (a : ZMod 2) :
    mapChain e (Finsupp.single s a) = Finsupp.single (s.map e) a := by
  simp [mapChain]

theorem mapChain_injective (e : V ↪ W) : Function.Injective (mapChain e) :=
  Finsupp.mapDomain_injective (Finset.map_injective e)

theorem mapChain_boundary_single (e : V ↪ W) (s : Finset V) (a : ZMod 2) :
    mapChain e (boundary (Finsupp.single s a)) =
      boundary (Finsupp.single (s.map e) a) := by
  simp only [boundary_single, map_sum, mapChain_single, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.map_erase]

theorem mapChain_boundary (e : V ↪ W) (c : Chain V) :
    mapChain e (boundary c) = boundary (mapChain e c) := by
  have heq : (mapChain e).comp boundary = boundary.comp (mapChain e) := by
    apply Finsupp.lhom_ext
    intro t a
    simpa only [LinearMap.comp_apply, mapChain_single] using mapChain_boundary_single e t a
  exact LinearMap.congr_fun heq c

theorem IsFacetCircuit.mapVertices {σ : I → Finset V} {s : Finset I}
    (h : IsFacetCircuit σ s) (e : V ↪ W) :
    IsFacetCircuit (fun i => (σ i).map e) s := by
  refine ⟨h.nonempty, ?_, ?_⟩
  · simp_rw [← mapChain_boundary_single]
    rw [← map_sum, h.sum_eq_zero, map_zero]
  · intro t hts htne htz
    apply h.minimal t hts htne
    apply mapChain_injective e
    simp only [map_sum, map_zero, mapChain_boundary_single]
    exact htz

def mapFamily (e : V ↪ W) (s : Finset (Finset V)) : Finset (Finset W) :=
  s.image (Finset.map e)

@[simp]
theorem mem_mapFamily (e : V ↪ W) (s : Finset (Finset V)) (t : Finset W) :
    t ∈ mapFamily e s ↔ ∃ a ∈ s, a.map e = t := Finset.mem_image

theorem IsFacetCircuit.mapFamily {s : Finset (Finset V)}
    (h : IsFacetCircuit id s) (e : V ↪ W) : IsFacetCircuit id (mapFamily e s) := by
  exact (h.mapVertices e).image (Finset.map_injective e).injOn

theorem Pure.mapFamily {n : ℕ} {s : Finset (Finset V)}
    (h : Pure n id s) (e : V ↪ W) : Pure n id (mapFamily e s) := by
  intro t ht
  obtain ⟨a, ha, rfl⟩ := (mem_mapFamily e s t).mp ht
  simpa using h a ha

@[simp]
theorem card_mapFamily (e : V ↪ W) (s : Finset (Finset V)) :
    (mapFamily e s).card = s.card :=
  Finset.card_image_of_injective _ (Finset.map_injective e)

theorem vertices_mapFamily (e : V ↪ W) (s : Finset (Finset V)) :
    vertices id (mapFamily e s) = (vertices id s).map e := by
  ext w
  simp only [mem_vertices, mem_mapFamily, Finset.mem_map, id_eq]
  aesop

theorem faces_mapFamily (e : V ↪ W) (s : Finset (Finset V)) (r : ℕ) :
    faces (mapFamily e s) r = mapFamily e (faces s r) := by
  simp only [faces, mapFamily, Finset.image_biUnion, Finset.biUnion_image,
    Finset.powersetCard_map]
  simp only [Finset.map_eq_image]
  rfl

@[simp]
theorem faces_mapFamily_card (e : V ↪ W) (s : Finset (Finset V)) (r : ℕ) :
    (faces (mapFamily e s) r).card = (faces s r).card := by
  rw [faces_mapFamily, card_mapFamily]

theorem link_mapFamily (e : V ↪ W) (s : Finset (Finset V)) (a : Finset V) :
    link (mapFamily e s) (a.map e) = mapFamily e (link s a) := by
  simp only [link, mapFamily, Finset.filter_image, Finset.map_subset_map,
    Finset.image_image, Function.comp_def, Finset.map_sdiff]

theorem HasCircuitLinks.mapFamily {n : ℕ} {s : Finset (Finset V)}
    (h : HasCircuitLinks n s) (e : V ↪ W) : HasCircuitLinks n (mapFamily e s) := by
  intro a ha hcard
  obtain ⟨t, ht, hat⟩ := ha
  obtain ⟨t', ht', rfl⟩ := (mem_mapFamily e s t).mp ht
  have hap : a ∈ (t'.map e).powersetCard a.card := Finset.mem_powersetCard.mpr ⟨hat, rfl⟩
  rw [Finset.powersetCard_map] at hap
  obtain ⟨a', ha', heq⟩ := Finset.mem_map.mp hap
  change a'.map e = a at heq
  subst a
  rw [link_mapFamily]
  apply IsFacetCircuit.mapFamily
  apply h a' ⟨t', ht', (Finset.mem_powersetCard.mp ha').1⟩
  simpa using hcard

/-- A recursive criterion for the all-links condition. This lets a geometric
development use its actual vertex figures repeatedly. -/
theorem HasCircuitLinks.of_vertex_links {n : ℕ} {s : Finset (Finset V)}
    (hs : IsFacetCircuit id s)
    (hvertex : ∀ v ∈ vertices id s, HasCircuitLinks (n - 1) (link s {v})) :
    HasCircuitLinks n s := by
  intro a ha hcard
  by_cases haempty : a = ∅
  · simpa [haempty] using hs
  obtain ⟨v, hva⟩ := Finset.nonempty_iff_ne_empty.mpr haempty
  obtain ⟨t, ht, hat⟩ := ha
  have hvt : v ∈ t := hat hva
  have hvs : v ∈ vertices id s := (mem_vertices id s v).mpr ⟨t, ht, hvt⟩
  have hface : ∃ f ∈ link s {v}, a.erase v ⊆ f := by
    refine ⟨t.erase v, (mem_link s {v} (t.erase v)).mpr ⟨by simp, ?_⟩, ?_⟩
    · simpa only [Finset.singleton_union, Finset.insert_erase hvt] using ht
    · exact Finset.erase_subset_erase v hat
  have hdim : (a.erase v).card + 3 ≤ n - 1 := by
    have hc := Finset.card_erase_add_one hva
    omega
  have h := hvertex v hvs (a.erase v) hface hdim
  rw [link_link s (by simp : Disjoint ({v} : Finset V) (a.erase v))] at h
  simpa only [Finset.singleton_union, Finset.insert_erase hva] using h

end Cubical.Simplicial

end
end BundlePart27

section BundlePart28
/- Source: Cubical/IndexedPseudomanifold.lean -/
@[expose] public section


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

end
end BundlePart28
