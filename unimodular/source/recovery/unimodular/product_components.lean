module

public import Mathlib.Combinatorics.Matroid.Circuit
public import Mathlib.Combinatorics.Matroid.Sum
public import Mathlib.Logic.Relation

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-! Connected components of an ordinary matroid, defined by circuit chains.

The relation is the standard circuit-generated equivalence, independently of
any representation, lattice splitting or fan conclusion. For a full-ground
matroid its restrictions to these components form its actual Mathlib
`disjointSigma`. No decomposition hypothesis is introduced.
-/

open Set
open scoped Matroid Function

namespace Unimodular.MatroidComponents

variable {E : Type*} (M : Matroid E)

def CircuitStep (a b : E) : Prop :=
  ∃ C : Set E, M.IsCircuit C ∧ a ∈ C ∧ b ∈ C

def componentSetoid : Setoid E := Relation.EqvGen.setoid (CircuitStep M)

abbrev Component := Quotient (componentSetoid M)

def component (a : E) : Component M := Quotient.mk _ a

def fiber (c : Component M) : Set E := {a | component M a = c}

@[simp] theorem mem_fiber (a : E) (c : Component M) :
    a ∈ fiber M c ↔ component M a = c := Iff.rfl

theorem component_surjective : Function.Surjective (component M) :=
  Quotient.mk_surjective

theorem fiber_nonempty (c : Component M) : (fiber M c).Nonempty := by
  obtain ⟨a, ha⟩ := component_surjective M c
  exact ⟨a, ha⟩

theorem component_eq_of_circuit {C : Set E} (hC : M.IsCircuit C)
    {a b : E} (ha : a ∈ C) (hb : b ∈ C) : component M a = component M b :=
  Quotient.sound (Relation.EqvGen.rel _ _ ⟨C, hC, ha, hb⟩)

theorem circuit_subset_fiber {C : Set E} (hC : M.IsCircuit C)
    {a : E} (ha : a ∈ C) : C ⊆ fiber M (component M a) := by
  intro b hb
  exact component_eq_of_circuit M hC hb ha

theorem fibers_pairwise_disjoint : Pairwise (Disjoint on fiber M) := by
  intro c d hcd
  apply Set.disjoint_left.mpr
  intro a ha hb
  exact hcd (ha.symm.trans hb)

theorem iUnion_fiber : (⋃ c : Component M, fiber M c) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro a
  exact Set.mem_iUnion.mpr ⟨component M a, rfl⟩

/-- Independence is exactly componentwise independence. This uses actual
minimal dependent sets, not a representation-specific surrogate. -/
theorem indep_iff_componentwise {I : Set E} (hIE : I ⊆ M.E) :
    M.Indep I ↔ ∀ c : Component M, M.Indep (I ∩ fiber M c) := by
  constructor
  · intro h c
    exact h.subset Set.inter_subset_left
  · intro h
    by_contra hn
    obtain ⟨C, hCI, hC⟩ := (show M.Dep I from ⟨hn, hIE⟩).exists_isCircuit_subset
    obtain ⟨a, ha⟩ := hC.nonempty
    exact hC.not_indep ((h (component M a)).subset
      (Set.subset_inter hCI (circuit_subset_fiber M hC ha)))

def restriction (c : Component M) : Matroid E := M ↾ fiber M c

theorem restrictions_disjoint : Pairwise (Disjoint on fun c => (restriction M c).E) := by
  simpa only [restriction, Matroid.restrict_ground_eq] using fibers_pairwise_disjoint M

def componentSum : Matroid E := Matroid.disjointSigma (restriction M) (restrictions_disjoint M)

/-- The usual matroid connected-component decomposition, as literal equality
of ordinary Mathlib matroids on their full ground-label type. -/
theorem eq_componentSum (hE : M.E = Set.univ) : M = componentSum M := by
  apply Matroid.ext_indep
  · simp only [componentSum, Matroid.disjointSigma_ground_eq, restriction,
      Matroid.restrict_ground_eq, iUnion_fiber, hE]
  intro I hI
  rw [componentSum, Matroid.disjointSigma_indep_iff]
  simp only [restriction, Matroid.restrict_ground_eq, Matroid.restrict_indep_iff]
  constructor
  · intro hi
    exact ⟨fun c => ⟨hi.subset Set.inter_subset_left, Set.inter_subset_right⟩,
      by rw [iUnion_fiber]; exact Set.subset_univ _⟩
  · rintro ⟨hi, _⟩
    exact (indep_iff_componentwise M hI).mpr (fun c => (hi c).1)

/-- Every global matroid basis cuts out a basis of each component. -/
theorem isBasis_inter_fiber (hE : M.E = Set.univ) {B : Set E}
    (hB : M.IsBase B) (c : Component M) : M.IsBasis (B ∩ fiber M c) (fiber M c) := by
  have hb : (componentSum M).IsBase B := by rwa [← eq_componentSum M hE]
  have hc := (Matroid.disjointSigma_isBase_iff.mp hb).1 c
  simp only [restriction, Matroid.restrict_ground_eq] at hc
  exact (Matroid.isBase_restrict_iff (by rw [hE]; exact Set.subset_univ _)).mp hc

/-- Any circuit-respecting partition is constant on the genuine connected
components. This makes the canonical nature of the component partition explicit. -/
theorem constant_on_component {J : Type*} (f : E → J)
    (hf : ∀ C : Set E, M.IsCircuit C → ∀ a ∈ C, ∀ b ∈ C, f a = f b)
    {a b : E} (hab : component M a = component M b) : f a = f b := by
  have h : Relation.EqvGen (CircuitStep M) a b := Quotient.exact hab
  clear hab
  induction h with
  | rel a b h =>
      obtain ⟨C, hC, ha, hb⟩ := h
      exact hf C hC a ha b hb
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ hab hbc => exact hab.trans hbc

theorem circuit_partition_factors_uniquely {J : Type*} (f : E → J)
    (hf : ∀ C : Set E, M.IsCircuit C → ∀ a ∈ C, ∀ b ∈ C, f a = f b) :
    ∃! g : Component M → J, ∀ a, g (component M a) = f a := by
  let g : Component M → J := Quotient.lift f (fun a b h =>
    constant_on_component M f hf (Quotient.sound h))
  refine ⟨g, fun a => rfl, ?_⟩
  intro h hh
  funext c
  obtain ⟨a, rfl⟩ := component_surjective M c
  exact hh a

end Unimodular.MatroidComponents

#print axioms Unimodular.MatroidComponents.indep_iff_componentwise
#print axioms Unimodular.MatroidComponents.eq_componentSum
#print axioms Unimodular.MatroidComponents.isBasis_inter_fiber
#print axioms Unimodular.MatroidComponents.circuit_partition_factors_uniquely
#check "UNIMODULAR_MATROID_COMPONENTS_EOF_V2"
