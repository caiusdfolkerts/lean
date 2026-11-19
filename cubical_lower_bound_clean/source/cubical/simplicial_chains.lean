module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic

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
