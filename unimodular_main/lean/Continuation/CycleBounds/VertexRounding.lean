module

public import Continuation.CycleBounds.BasisWallBound
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

/-! # Integral normalization by rounding graph vertex potentials

For an incidence configuration, subtracting the integer floor at every vertex
normalizes every edge at once. This proves the normalization directly for all
real parameters and identifies precisely the original integral active equations.
-/

noncomputable section
open scoped BigOperators Matroid
namespace Unimodular.CycleBounds
open SeriesParallel SeriesParallel.IncidenceGraph
attribute [local instance] Classical.propDecidable
variable {V E N : Type*} [Fintype V]

/-- The linear functional with specified values on actual graph vertex vectors. -/
def vertexFunctional (a : V → ℝ) : (V → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, a i * x i
  map_add' := by intro x y; simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by intro r x; simp [Finset.mul_sum, mul_left_comm]

@[simp] theorem vertexFunctional_vertex (a : V → ℝ) (i : V) :
    vertexFunctional a (vertex i) = a i := by
  classical
  change (∑ j, a j * ((Pi.single i 1 : V → ℝ) j)) = a i
  rw [Finset.sum_eq_single i]
  · simp [Pi.single_apply]
  · intro j _ hji
    simp [Pi.single_apply, hji, hji.symm]
  · simp

@[simp] theorem vertexFunctional_column (G : IncidenceGraph V E) (a : V → ℝ) (e : E) :
    vertexFunctional a (G.column e) = a (G.source e) - a (G.target e) := by
  rw [column, map_sub, vertexFunctional_vertex, vertexFunctional_vertex]

/-- Flooring vertex potentials gives a genuine integral value on every ray. -/
theorem fractional_difference (h : V → ℝ) (a b : V) :
    Int.fract (h a) - Int.fract (h b) =
      (h a - h b) - ((⌊h a⌋ - ⌊h b⌋ : ℤ) : ℝ) := by
  rw [Int.fract, Int.fract, Int.cast_sub]
  ring

/-- The ceiling coefficients change by precisely the integral vertex shift. -/
theorem ceil_fractional_difference (h : V → ℝ) (a b : V) :
    ⌈Int.fract (h a) - Int.fract (h b)⌉ = ⌈h a - h b⌉ - (⌊h a⌋ - ⌊h b⌋) := by
  rw [fractional_difference, Int.ceil_sub_intCast]

/-- The complete graph wall estimate for arbitrary real potentials. Its active
space is defined by integrality of the original pairings, exactly as in the
integral periodic hyperplane arrangement. -/
theorem graphic_basis_wall_bound_all_parameters [AddCommGroup N] [Module ℝ N]
    [FiniteDimensional ℝ N] (G : IncidenceGraph V E) (hK : ¬G.HasK4Minor)
    (v : E → N) (ι : N →ₗ[ℝ] (V → ℝ))
    (hι : ∀ e, ι (v e) = Pi.single (G.source e) 1 - Pi.single (G.target e) 1)
    (h : V → ℝ) (B : Finset E) (hB : G.cycleMatroid.Indep (B : Set E))
    (w : E) (hw : w ∈ G.edges) (hwB : w ∉ B)
    (hwspan : G.column w ∈ Submodule.span ℝ (G.column '' (B : Set E)))
    (hne : G.source w ≠ G.target w) (L : (V → ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀ e ∈ B, L (G.column e) = (⌈h (G.source e) - h (G.target e)⌉ : ℝ)) :
    (⌈h (G.source w) - h (G.target w)⌉ : ℝ) - L (G.column w) ≤
      (Module.finrank ℝ (activeDirections v
        {e | e ∈ G.edges ∧ ∃ z : ℤ, h (G.source e) - h (G.target e) = (z : ℝ)}) : ℝ) := by
  let f : V → ℝ := fun a ↦ Int.fract (h a)
  let P := vertexFunctional (fun a ↦ (⌊h a⌋ : ℝ))
  let L' := L - P
  have hfloor (e : E) : P (G.column e) = ((⌊h (G.source e)⌋ - ⌊h (G.target e)⌋ : ℤ) : ℝ) := by
    simp [P]
  have hceil (e : E) : (⌈f (G.source e) - f (G.target e)⌉ : ℝ) =
      (⌈h (G.source e) - h (G.target e)⌉ : ℝ) - P (G.column e) := by
    rw [hfloor]
    exact_mod_cast ceil_fractional_difference h (G.source e) (G.target e)
  have hL' (e : E) (he : e ∈ B) :
      L' (G.column e) = (⌈f (G.source e) - f (G.target e)⌉ : ℝ) := by
    rw [hceil]
    change L (G.column e) - P (G.column e) = _
    rw [hL e he]
  have hlo (e : E) : -1 < f (G.source e) - f (G.target e) := by
    have h₁ := Int.fract_nonneg (h (G.source e))
    have h₂ := Int.fract_lt_one (h (G.target e))
    dsimp only [f]
    linarith
  have hhi (e : E) : f (G.source e) - f (G.target e) < 1 := by
    have h₁ := Int.fract_lt_one (h (G.source e))
    have h₂ := Int.fract_nonneg (h (G.target e))
    dsimp only [f]
    linarith
  have hb := graphic_basis_wall_bound G hK v ι hι f B hB w hw hwB hwspan hne L' hL'
    (fun e _ ↦ hlo e) (fun e _ ↦ hhi e)
  have hactive : {e | e ∈ G.edges ∧ f (G.source e) = f (G.target e)} =
      {e | e ∈ G.edges ∧ ∃ z : ℤ, h (G.source e) - h (G.target e) = (z : ℝ)} := by
    ext e
    exact and_congr_right (fun _ ↦ Int.fract_eq_fract)
  rw [hactive, hceil] at hb
  change (⌈h (G.source w) - h (G.target w)⌉ : ℝ) - P (G.column w) -
    (L (G.column w) - P (G.column w)) ≤ _ at hb
  linarith

#print axioms graphic_basis_wall_bound_all_parameters
end Unimodular.CycleBounds
