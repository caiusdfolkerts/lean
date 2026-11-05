module

public import paper_verification.toric009

@[expose] public section

/-!
# Positive-dimensional examples of the principal interfaces

The interval `[0,k]` is constructed from its two actual lattice generators.
Its affine span, complete primitive edge basis at each vertex, and exact
edge length are proved before applying the principal theorems. These
examples supplement the unrestricted main results.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.Examples

open Set LatticePolytope
open scoped BigOperators Classical Pointwise

def intervalRight (k : ℕ) : Lattice 1 := fun _ => (k : ℤ)

def latticeInterval (k : ℕ) (hk : 0 < k) : LatticePolytope 1 where
  generators := {0, intervalRight k}
  nonempty := by simp
  fullDimensional := by
    refine affineSpan_eq_top_of_scaled_axes _ ?_ (fun _ => (k : ℝ)) ?_ ?_
    · exact subset_convexHull ℝ _ ⟨0, by simp, map_zero (embed 1)⟩
    · intro i
      exact_mod_cast hk.ne'
    · intro i
      have he : (k : ℝ) • Pi.basisFun ℝ (Fin 1) i = embed 1 (intervalRight k) := by
        ext j
        have hij : i = j := Subsingleton.elim _ _
        simp [hij, intervalRight, embed, Pi.basisFun_apply]
      rw [he]
      exact subset_convexHull ℝ _ ⟨intervalRight k, by simp, rfl⟩

theorem latticeInterval_carrier (k : ℕ) (hk : 0 < k) :
    (latticeInterval k hk).carrier = segment ℝ (0 : Ambient 1) (embed 1 (intervalRight k)) := by
  simp only [LatticePolytope.carrier, latticeInterval, Finset.coe_insert,
    Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton, map_zero]
  exact convexHull_pair _ _

theorem intervalRight_real_ne_zero (k : ℕ) (hk : 0 < k) :
    embed 1 (intervalRight k) ≠ 0 := by
  intro h
  have hh := congrFun h (0 : Fin 1)
  have hpos : (0 : ℝ) < k := by exact_mod_cast hk
  change (k : ℝ) = 0 at hh
  linarith

theorem latticeInterval_left_edge (k : ℕ) (hk : 0 < k) :
    (latticeInterval k hk).IsEdge 0 (embed 1 (intervalRight k)) := by
  refine ⟨(intervalRight_real_ne_zero k hk).symm, ?_⟩
  rw [latticeInterval_carrier]

theorem latticeInterval_right_edge (k : ℕ) (hk : 0 < k) :
    (latticeInterval k hk).IsEdge (embed 1 (intervalRight k)) 0 := by
  refine ⟨intervalRight_real_ne_zero k hk, ?_⟩
  rw [latticeInterval_carrier, segment_symm ℝ (embed 1 (intervalRight k)) 0]

theorem latticeInterval_vertex_cases (k : ℕ) (hk : 0 < k)
    {v : Ambient 1} (hv : v ∈ (latticeInterval k hk).carrier.extremePoints ℝ) :
    v = 0 ∨ v = embed 1 (intervalRight k) := by
  obtain ⟨z, hz, rfl⟩ := (latticeInterval k hk).extreme_integral hv
  have hz' : z = 0 ∨ z = intervalRight k := by
    simpa only [latticeInterval, Finset.mem_insert, Finset.mem_singleton] using hz
  rcases hz' with rfl | rfl
  · exact Or.inl (map_zero (embed 1))
  · exact Or.inr rfl

theorem latticeInterval_edge_cases (k : ℕ) (hk : 0 < k)
    {v w : Ambient 1} (h : (latticeInterval k hk).IsEdge v w) :
    (v = 0 ∧ w = embed 1 (intervalRight k)) ∨
      (v = embed 1 (intervalRight k) ∧ w = 0) := by
  obtain ⟨hv, hw⟩ := (latticeInterval k hk).edge_endpoints_extreme h
  rcases latticeInterval_vertex_cases k hk hv with rfl | rfl <;>
    rcases latticeInterval_vertex_cases k hk hw with rfl | rfl
  · exact False.elim (h.1 rfl)
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact False.elim (h.1 rfl)

theorem latticeInterval_smooth (k : ℕ) (hk : 0 < k) :
    (latticeInterval k hk).Smooth := by
  intro v hv
  let b := Pi.basisFun ℤ (Fin 1)
  let c := b.map (LinearEquiv.neg ℤ)
  have hleft (i : Fin 1) : (0 : Lattice 1) + (k : ℤ) • b i = intervalRight k := by
    ext j
    have hij : i = j := Subsingleton.elim _ _
    simp [b, hij, intervalRight, Pi.basisFun_apply]
  have hright (i : Fin 1) : intervalRight k + (k : ℤ) • c i = 0 := by
    ext j
    have hij : i = j := Subsingleton.elim _ _
    simp [c, b, hij, intervalRight, Pi.basisFun_apply]
  rcases latticeInterval_vertex_cases k hk hv with rfl | rfl
  · refine ⟨0, b, fun _ => k, map_zero (embed 1), ?_, ?_⟩
    · intro i
      refine ⟨hk, ?_⟩
      rw [hleft]
      exact latticeInterval_left_edge k hk
    · intro w hw
      rcases latticeInterval_edge_cases k hk hw with ⟨_, hw⟩ | ⟨he, _⟩
      · exact ⟨0, by rw [hleft]; exact hw⟩
      · exact False.elim ((intervalRight_real_ne_zero k hk) he.symm)
  · refine ⟨intervalRight k, c, fun _ => k, rfl, ?_, ?_⟩
    · intro i
      refine ⟨hk, ?_⟩
      rw [hright, map_zero]
      exact latticeInterval_right_edge k hk
    · intro w hw
      rcases latticeInterval_edge_cases k hk hw with ⟨he, _⟩ | ⟨_, hw⟩
      · exact False.elim ((intervalRight_real_ne_zero k hk) he)
      · exact ⟨0, by rw [hright, map_zero]; exact hw⟩

theorem latticeInterval_edge_bound (k : ℕ) (hk : 0 < k) :
    (latticeInterval k hk).EdgesAtLeast k := by
  intro v w h
  rcases latticeInterval_edge_cases k hk h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨0, intervalRight k, map_zero (embed 1), rfl, ?_⟩
    simp [LatticePolytope.latticeLength, intervalRight, Finset.univ_unique]
  · refine ⟨intervalRight k, 0, rfl, map_zero (embed 1), ?_⟩
    simp [LatticePolytope.latticeLength, intervalRight, Finset.univ_unique]

/-- Theorem 1.1 applies to a concrete positive-dimensional polytope
for every positive length and every coefficient field. -/
theorem interval_idp_and_quadrics (k : ℕ) (hk : 0 < k)
    (K : Type*) [Field K] :
    (latticeInterval k hk).HasIDP ∧ (latticeInterval k hk).QuadraticallyGenerated K := by
  exact toric_theorem_1_1 K 1 (by decide) (latticeInterval k hk)
    (latticeInterval_smooth k hk)
    ((latticeInterval k hk).edgesAtLeast_mono (latticeInterval_edge_bound k hk) hk)

/-- The prescribed quotient-class result on this explicit interval family. -/
theorem interval_prescribed_parity (k : ℕ) (hk : 0 < k)
    (m : Lattice 1)
    (hm : embed 1 m ∈ interior ((latticeInterval k hk).minkowskiSum (latticeInterval k hk)))
    (α : ParityClass 1) :
    ∃ a b : Lattice 1,
      embed 1 a ∈ (latticeInterval k hk).carrier ∧
      embed 1 b ∈ (latticeInterval k hk).carrier ∧
      a + b = m ∧ parityClass 1 a = α := by
  have hbound := (latticeInterval k hk).edgesAtLeast_mono (latticeInterval_edge_bound k hk) hk
  exact toric_theorem_1_2_quotient_classes 1 _ _
    (latticeInterval_smooth k hk) (latticeInterval_smooth k hk) rfl hbound hbound m hm α

/-- The full adjoint set equality on all intervals of integral length at least two. -/
theorem interval_adjoint_equality (k : ℕ) (hk : 2 ≤ k) :
    let P := latticeInterval k (by omega)
    {m : Lattice 1 | embed 1 m ∈ P.carrier} +
        {m : Lattice 1 | embed 1 m ∈ interior P.carrier} =
      {m : Lattice 1 | embed 1 m ∈ interior (P.minkowskiSum P)} := by
  dsimp only
  have hpos : 0 < k := by omega
  have hbound := (latticeInterval k hpos).edgesAtLeast_mono (latticeInterval_edge_bound k hpos) hk
  exact toric_theorem_1_3_polytope_sets 1 _ _
    (latticeInterval_smooth k hpos) (latticeInterval_smooth k hpos) rfl hbound hbound

end PaperVerification.ToricGeometry.Examples
