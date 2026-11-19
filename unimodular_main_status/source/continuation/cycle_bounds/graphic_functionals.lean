module

public import Continuation.CycleBounds.VertexRounding
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

/-! # Wall interpolation in the original ambient vector space

An injective incidence presentation extends every covector to vertex coordinates.
The active direction space and the Cartier functional remain those of the original
ray configuration, independently of the chosen extension.
-/

noncomputable section
open scoped BigOperators Matroid
namespace Unimodular.CycleBounds
open SeriesParallel SeriesParallel.IncidenceGraph
attribute [local instance] Classical.propDecidable
variable {V E N : Type*} [Fintype V] [AddCommGroup N] [Module ℝ N]
    [FiniteDimensional ℝ N]

/-- The graph wall theorem expressed entirely in the original ray covectors. -/
theorem graphic_wall_bound_all_parameters (G : IncidenceGraph V E) (hK : ¬G.HasK4Minor)
    (v : E → N) (ι : N →ₗ[ℝ] (V → ℝ)) (hinj : Function.Injective ι)
    (hι : ∀ e, ι (v e) = Pi.single (G.source e) 1 - Pi.single (G.target e) 1)
    (θ ℓ : N →ₗ[ℝ] ℝ) (B : Finset E) (hBG : (B : Set E) ⊆ G.edges)
    (hB : LinearIndepOn ℝ v (B : Set E))
    (w : E) (hw : w ∈ G.edges) (hwB : w ∉ B) (hvw : v w ≠ 0)
    (hwspan : v w ∈ Submodule.span ℝ (v '' (B : Set E)))
    (hℓ : ∀ e ∈ B, ℓ (v e) = (⌈θ (v e)⌉ : ℝ)) :
    (⌈θ (v w)⌉ : ℝ) - ℓ (v w) ≤
      (Module.finrank ℝ (activeDirections v {e | e ∈ G.edges ∧ ∃ z : ℤ, θ (v e) = (z : ℝ)}) : ℝ) := by
  obtain ⟨ρ, hρ⟩ := ι.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinj)
  have hρ' (x : N) : ρ (ι x) = x := congrArg (fun f : N →ₗ[ℝ] N ↦ f x) hρ
  let H : (V → ℝ) →ₗ[ℝ] ℝ := θ.comp ρ
  let h : V → ℝ := fun a ↦ H (vertex a)
  let L : (V → ℝ) →ₗ[ℝ] ℝ := ℓ.comp ρ
  have hcol (e : E) : G.column e = ι (v e) := (hι e).symm
  have hθ (e : E) : h (G.source e) - h (G.target e) = θ (v e) := by
    rw [← map_sub H]
    change H (G.column e) = _
    rw [hcol]
    exact congrArg θ (hρ' (v e))
  have hL (e : E) : L (G.column e) = ℓ (v e) := by
    rw [hcol]
    exact congrArg ℓ (hρ' (v e))
  have hBM : G.cycleMatroid.Indep (B : Set E) := by
    apply (VectorMatroid.onSet_indep _ _ _).mpr
    refine ⟨hBG, ?_⟩
    have hh := hB.map_injOn ι hinj.injOn
    simpa only [Function.comp_def, ← hcol] using hh
  have hspan : G.column w ∈ Submodule.span ℝ (G.column '' (B : Set E)) := by
    have hh : ι (v w) ∈ (Submodule.span ℝ (v '' (B : Set E))).map ι :=
      ⟨v w, hwspan, rfl⟩
    rw [Submodule.map_span] at hh
    simpa only [Set.image_image, Function.comp_def, ← hcol] using hh
  have hne : G.source w ≠ G.target w := by
    intro heq
    have hz : ι (v w) = 0 := by rw [hι w, heq, sub_self]
    exact hvw (hinj (by simpa using hz))
  have hh := graphic_basis_wall_bound_all_parameters G hK v ι hι h B hBM w hw hwB hspan hne L
    (fun e he ↦ by rw [hL, hθ]; exact hℓ e he)
  have hactive : {e | e ∈ G.edges ∧ ∃ z : ℤ, h (G.source e) - h (G.target e) = (z : ℝ)} =
      {e | e ∈ G.edges ∧ ∃ z : ℤ, θ (v e) = (z : ℝ)} := by
    ext e
    simp only [Set.mem_setOf_eq, hθ]
  rwa [hθ w, hL w, hactive] at hh

#print axioms graphic_wall_bound_all_parameters
end Unimodular.CycleBounds
