module

public import Continuation.CycleBounds.CycleDimension
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Pi

@[expose] public section

/-! # Actual active-equation directions from graph component indicators -/

noncomputable section
open scoped BigOperators
namespace Unimodular.CycleBounds
attribute [local instance] Classical.propDecidable

variable {V E N α : Type*} [Fintype V] [AddCommGroup N] [Module ℝ N]

/-- The genuine tangent space defined by vanishing on every active ray. -/
def activeDirections (v : E → N) (A : Set E) : Submodule ℝ (Module.Dual ℝ N) where
  carrier := {φ | ∀ e ∈ A, φ (v e) = 0}
  zero_mem' := by simp
  add_mem' := by intro φ ψ hφ hψ e he; simp [hφ e he, hψ e he]
  smul_mem' := by intro r φ hφ e he; simp [hφ e he]

/-- The component indicator is an actual linear functional on vertex coordinates. -/
def componentForm (c : V → α) (i : α) : (V → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ a, (if c a = i then (1 : ℝ) else 0) * x a
  map_add' := by intro x y; simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by intro r x; simp [Finset.mul_sum, mul_left_comm]

theorem componentForm_vertex (c : V → α) (i : α) (a : V) :
    componentForm c i (Pi.single a 1) = if i = c a then 1 else 0 := by
  classical
  change (∑ x, (if c x = i then (1 : ℝ) else 0) * ((Pi.single a 1 : V → ℝ) x)) = _
  rw [Finset.sum_eq_single a]
  · simp [Pi.single_apply, eq_comm]
  · intro x _ hxa
    simp [Pi.single_apply, hxa, hxa.symm]
  · simp

theorem componentForm_edge (c : V → α) (i : α) (a b : V) :
    componentForm c i (Pi.single a 1 - Pi.single b 1) =
      (if i = c a then 1 else 0) - (if i = c b then 1 else 0) := by
  rw [map_sub, componentForm_vertex, componentForm_vertex]

variable (v : E → N) (s t : E → V) (ι : N →ₗ[ℝ] (V → ℝ))
    (hι : ∀ e, ι (v e) = Pi.single (s e) 1 - Pi.single (t e) 1)
    (A : Set E) (c : V → α) (hc : ∀ e ∈ A, c (s e) = c (t e))

/-- Every component indicator annihilates the actual active rays. -/
def componentDirection (i : α) : activeDirections v A :=
  ⟨(componentForm c i).comp ι, by
    intro e he
    simp only [LinearMap.comp_apply, hι, componentForm_edge, hc e he, sub_self]⟩

theorem componentDirection_apply (i : α) (e : E) :
    (componentDirection v s t ι hι A c hc i).val (v e) =
      (if i = c (s e) then 1 else 0) - (if i = c (t e) then 1 else 0) := by
  simp only [componentDirection, LinearMap.comp_apply, hι, componentForm_edge]

theorem componentDirection_test (e : E) :
    IncidenceTest (componentDirection v s t ι hι A c hc) (c (s e)) (c (t e)) := by
  let ℓ : activeDirections v A →ₗ[ℝ] ℝ :=
    { toFun := fun φ ↦ φ.val (v e)
      map_add' := by intro φ ψ; rfl
      map_smul' := by intro r φ; rfl }
  exact ⟨ℓ, fun i ↦ componentDirection_apply v s t ι hι A c hc i e⟩

omit hι hc in
 theorem IncidenceTest.symm {W : Type*} [AddCommGroup W] [Module ℝ W]
    {f : α → W} {a b : α} (h : IncidenceTest f a b) : IncidenceTest f b a := by
  obtain ⟨ℓ, hℓ⟩ := h
  refine ⟨-ℓ, fun i ↦ ?_⟩
  simp only [LinearMap.neg_apply, hℓ, neg_sub]

/-- A graph walk provides all the actual incidence tests needed for the
 dimension bound. Its orientations are arbitrary. -/
theorem componentDirection_path (w : List V)
    (hpath : w.IsChain (fun a b ↦ ∃ e,
      (s e = a ∧ t e = b) ∨ (s e = b ∧ t e = a))) :
    (w.map c).IsChain (IncidenceTest (componentDirection v s t ι hι A c hc)) := by
  apply (List.isChain_map c).mpr
  apply hpath.imp
  intro a b hab
  obtain ⟨e, hor⟩ := hab
  rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact componentDirection_test v s t ι hι A c hc e
  · exact (componentDirection_test v s t ι hι A c hc e).symm

include hι hc in
/-- The q−1 count from a wall cycle is bounded by the dimension of the actual
 active-equation kernel. No graph-rank formula or supplied dimension is assumed. -/
theorem graph_cyclicCost_le_activeDimension [FiniteDimensional ℝ N]
    (h : α → ℝ) (w : List V) (hne : w ≠ [])
    (hnc : Noncrossing (w.map c))
    (hpath : w.IsChain (fun a b ↦ ∃ e,
      (s e = a ∧ t e = b) ∨ (s e = b ∧ t e = a))) :
    cyclicCost h (w.map c) ≤ Module.finrank ℝ (activeDirections v A) :=
  cyclicCost_le_finrank_of_incidence_path
    (componentDirection v s t ι hι A c hc) h (w.map c) hnc
    (componentDirection_path v s t ι hι A c hc w hpath)
    (by simpa using hne)

#print axioms graph_cyclicCost_le_activeDimension
end Unimodular.CycleBounds
