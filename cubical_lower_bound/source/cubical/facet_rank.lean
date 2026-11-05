import cubical.bipartite_system
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Rank and nullity of a facet's normalized system

The edge equations are independent when, at every black vertex, the vectors
attached to its white neighbors are linearly independent.  We prove this by
solving the equations separately at each black vertex, with all white scalar
variables set to zero.
-/

namespace Cubical

open Module Matrix

variable {B W E : Type*} [Fintype B] [Fintype W] [Fintype E]

theorem bipartiteSystem_surjective (d : ℕ) (black : E → B) (white : E → W)
    (p : W → Fin d → ℝ)
    (hind : ∀ b, LinearIndependent ℝ
      (fun e : {e : E // black e = b} ↦ p (white e))) :
    Function.Surjective (bipartiteSystem d black white p) := by
  classical
  intro y
  have hs : ∀ b, ∃ u : Fin d → ℝ,
      (fun e : {e : E // black e = b} ↦ ∑ i, p (white e) i * u i) =
        (fun e : {e : E // black e = b} ↦ y e.val) := by
    intro b
    let M : Matrix {e : E // black e = b} (Fin d) ℝ :=
      fun e i ↦ p (white e) i
    have hM : LinearIndependent ℝ M.row := hind b
    exact hM.mulVec_surjective (fun e ↦ y e.val)
  choose u hu using hs
  refine ⟨(u, 0), ?_⟩
  funext e
  have h := congrFun (hu (black e)) ⟨e, rfl⟩
  simpa [bipartiteSystem] using h

theorem solutionSpace_finrank_add_edges (d : ℕ)
    (black : E → B) (white : E → W) (p : W → Fin d → ℝ)
    (hind : ∀ b, LinearIndependent ℝ
      (fun e : {e : E // black e = b} ↦ p (white e))) :
    finrank ℝ (solutionSpace d black white p) + Fintype.card E =
      d * Fintype.card B + Fintype.card W := by
  have hr := (bipartiteSystem d black white p).finrank_range_add_finrank_ker
  have hs := bipartiteSystem_surjective d black white p hind
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_pi,
    finrank_motion] at hr
  change finrank ℝ (LinearMap.ker (bipartiteSystem d black white p)) +
    Fintype.card E = d * Fintype.card B + Fintype.card W
  omega

/-- The facet dimension calculation in Proposition 3.
Here `k=d-1`, the facet has `s` vertices of each color and `k*s` edges. -/
theorem balanced_facet_dimension (k s : ℕ)
    (black : E → B) (white : E → W) (p : W → Fin (k + 1) → ℝ)
    (hind : ∀ b, LinearIndependent ℝ
      (fun e : {e : E // black e = b} ↦ p (white e)))
    (hb : Fintype.card B = s) (hw : Fintype.card W = s)
    (he : Fintype.card E = k * s) :
    finrank ℝ (solutionSpace (k + 1) black white p) = 2 * s := by
  have h := solutionSpace_finrank_add_edges (k + 1) black white p hind
  rw [hb, hw, he] at h
  nlinarith

end Cubical
