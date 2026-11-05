import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-!
# The normalized bipartite rigidity system

The variables are one `d`-vector at each black vertex and one scalar at each
white vertex.  An edge `e` imposes `p (white e) · u (black e) + s (white e) = 0`.
This file develops the linear algebra of that actual system.  No rigidity or
polytope property is included in its definition.
-/

namespace Cubical

open Module

variable {B W E : Type*} [Fintype B] [Fintype W] [Fintype E]

abbrev Motion (B W : Type*) (d : ℕ) := (B → Fin d → ℝ) × (W → ℝ)

/-- The linear operator whose kernel is system (1) of the manuscript. -/
def bipartiteSystem (d : ℕ) (black : E → B) (white : E → W)
    (p : W → Fin d → ℝ) : Motion B W d →ₗ[ℝ] (E → ℝ) where
  toFun m e := ∑ i, p (white e) i * m.1 (black e) i + m.2 (white e)
  map_add' x y := by
    funext e
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add,
      Finset.sum_add_distrib]
    ring
  map_smul' c x := by
    funext e
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    simp only [mul_add, Finset.mul_sum, mul_left_comm]

/-- The manuscript's solution space `M(P,p)`, for an arbitrary bipartite graph. -/
def solutionSpace (d : ℕ) (black : E → B) (white : E → W)
    (p : W → Fin d → ℝ) : Submodule ℝ (Motion B W d) :=
  LinearMap.ker (bipartiteSystem d black white p)

omit [Fintype B] [Fintype W] [Fintype E] in
theorem mem_solutionSpace_iff (d : ℕ) (black : E → B) (white : E → W)
    (p : W → Fin d → ℝ) (m : Motion B W d) :
    m ∈ solutionSpace d black white p ↔
      ∀ e, ∑ i, p (white e) i * m.1 (black e) i + m.2 (white e) = 0 := by
  change (bipartiteSystem d black white p) m = 0 ↔ _
  exact funext_iff

theorem finrank_motion (d : ℕ) :
    finrank ℝ (Motion B W d) = d * Fintype.card B + Fintype.card W := by
  simp [Motion, Module.finrank_prod, Module.finrank_pi_fintype, mul_comm]

/-- Rank-nullity gives the asymmetric edge bound once the nullity is bounded.
The hypothesis is deliberately explicit: this theorem does not assert that a
polytope supplies the nullity bound. -/
theorem edge_count_of_nullity_bound (d k : ℕ) (black : E → B) (white : E → W)
    (p : W → Fin d → ℝ)
    (h : finrank ℝ (solutionSpace d black white p) ≤ k) :
    d * Fintype.card B + Fintype.card W ≤ Fintype.card E + k := by
  have hr := (bipartiteSystem d black white p).finrank_range_add_finrank_ker
  have hle : finrank ℝ (LinearMap.range (bipartiteSystem d black white p)) ≤
      Fintype.card E := by
    simpa only [Module.finrank_pi] using
      (Submodule.finrank_le (LinearMap.range (bipartiteSystem d black white p)))
  rw [finrank_motion] at hr
  change finrank ℝ (LinearMap.ker (bipartiteSystem d black white p)) ≤ k at h
  omega

/-- An injective restriction to a space of dimension at most `k` supplies the
nullity bound required by `edge_count_of_nullity_bound`. -/
theorem edge_count_of_injective_restriction
    {V : Type*} [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V]
    (d k : ℕ) (black : E → B) (white : E → W) (p : W → Fin d → ℝ)
    (r : solutionSpace d black white p →ₗ[ℝ] V)
    (hr : Function.Injective r) (hk : finrank ℝ V ≤ k) :
    d * Fintype.card B + Fintype.card W ≤ Fintype.card E + k := by
  apply edge_count_of_nullity_bound d k black white p
  exact (LinearMap.finrank_le_finrank_of_injective hr).trans hk

end Cubical
