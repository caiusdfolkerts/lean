import cubical.rigidity_count

/-!
# Edge-count bounds for an explicit covering family of distance equations

The labels may repeat geometric edges. This lets a triangulated surface
be bounded by its original edges together with one diagonal per facet,
without replacing the actual graph by a numerical assumption.
-/

namespace Cubical.Rigidity

open Module
open scoped InnerProductSpace

variable {V L E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def labeledMotionMap (left right : L → V) (p : V → E) :
    (V → E) →ₗ[ℝ] (L → ℝ) where
  toFun u e := ⟪p (left e) - p (right e), u (left e) - u (right e)⟫_ℝ
  map_add' u v := by
    funext e
    simp only [Pi.add_apply]
    have h : (u (left e) + v (left e)) - (u (right e) + v (right e)) =
      (u (left e) - u (right e)) + (v (left e) - v (right e)) := by abel
    rw [h, inner_add_right]
  map_smul' c u := by funext e; simp [← smul_sub, real_inner_smul_right]

/-- Genuine rigidity bounds the number of vertices by the number of
explicit distance equations that cover every graph edge. -/
theorem IsRigid.edge_count_of_edge_cover [Fintype V] [Fintype L]
    [FiniteDimensional ℝ E] {G : SimpleGraph V} {p : V → E}
    (hp : IsRigid G p) (left right : L → V)
    (hcover : ∀ a b, G.Adj a b → ∃ e,
      (left e = a ∧ right e = b) ∨ (left e = b ∧ right e = a)) :
    finrank ℝ E * Fintype.card V ≤ Fintype.card L + (finrank ℝ E + 1).choose 2 := by
  have hker : LinearMap.ker (labeledMotionMap left right p) =
      LinearMap.range (trivialMotionMap p) := by
    ext u
    rw [mem_range_trivialMotionMap]
    constructor
    · intro hu
      apply hp u
      intro a b hab
      obtain ⟨e, he | he⟩ := hcover a b hab
      · have h := congrFun (LinearMap.mem_ker.mp hu) e
        simpa only [labeledMotionMap, LinearMap.coe_mk, AddHom.coe_mk, he.1, he.2, Pi.zero_apply] using h
      · have h := congrFun (LinearMap.mem_ker.mp hu) e
        change ⟪p (left e) - p (right e), u (left e) - u (right e)⟫_ℝ = 0 at h
        rw [he.1, he.2] at h
        have hp' : p b - p a = -(p a - p b) := by abel
        have hu' : u b - u a = -(u a - u b) := by abel
        rwa [hp', hu', inner_neg_neg] at h
    · rintro ⟨t, A, hA, hu⟩
      apply LinearMap.mem_ker.mpr
      funext e
      change ⟪p (left e) - p (right e), u (left e) - u (right e)⟫_ℝ = 0
      rw [hu, hu]
      have hs : t + A (p (left e)) - (t + A (p (right e))) =
          A (p (left e) - p (right e)) := by rw [map_sub]; abel
      rw [hs, hA.inner_self]
  have hrange : finrank ℝ (LinearMap.range (labeledMotionMap left right p)) ≤ Fintype.card L := by
    simpa only [Module.finrank_pi] using
      Submodule.finrank_le (LinearMap.range (labeledMotionMap left right p))
  have hnull : finrank ℝ (LinearMap.ker (labeledMotionMap left right p)) ≤
      (finrank ℝ E + 1).choose 2 := by
    rw [hker]
    exact (trivialMotionMap p).finrank_range_le.trans finrank_euclideanMotionParameters_le
  have hdim := (labeledMotionMap left right p).finrank_range_add_finrank_ker
  have hpi : finrank ℝ (V → E) = Fintype.card V * finrank ℝ E := by
    simp [Module.finrank_pi_fintype]
  rw [hpi] at hdim
  rw [Nat.mul_comm (finrank ℝ E) (Fintype.card V)]
  omega

end Cubical.Rigidity
