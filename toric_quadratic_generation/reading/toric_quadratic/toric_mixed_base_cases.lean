module
public import PaperVerification.ToricStatements
public import Mathlib.Topology.Algebra.Group.Pointwise
@[expose] public section
/-!
# Dimension-zero mixed cases and the automatic inclusion

The mixed induction starts in the actual zero-dimensional lattice.
The reverse inclusion in adjoint multiplication is purely topological and is
proved without smoothness, positivity, or a common normal fan.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped Pointwise
open PaperVerification.ToricExchange

namespace LatticePolytope

/-- The carrier of any zero-dimensional lattice polytope is the whole
zero-dimensional real vector space. -/
theorem carrier_eq_univ_zero (P : LatticePolytope 0) : P.carrier = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨z, hz⟩ := P.nonempty
  have hmem : embed 0 z ∈ P.carrier :=
    subset_convexHull ℝ _ ⟨z, hz, rfl⟩
  simpa only [Subsingleton.elim (embed 0 z) x] using hmem

/-- The prescribed-parity base case retains all lattice targets and classes. -/
theorem mixed_parity_dimension_zero (P Q : LatticePolytope 0)
    (m c : Lattice 0) :
    ∃ a b : Lattice 0,
      embed 0 a ∈ P.carrier ∧ embed 0 b ∈ Q.carrier ∧
      a + b = m ∧ SameParity a c := by
  refine ⟨m, 0, ?_, ?_, add_zero m, ?_⟩
  · rw [P.carrier_eq_univ_zero]
    exact Set.mem_univ _
  · rw [Q.carrier_eq_univ_zero]
    exact Set.mem_univ _
  · refine ⟨0, ?_⟩
    exact Subsingleton.elim _ _

/-- Adding any carrier point to an interior point of the second polytope
always gives an interior point of the actual Minkowski sum. -/
theorem add_mem_interior_minkowskiSum {n : ℕ} (P Q : LatticePolytope n)
    (a b : Lattice n) (ha : embed n a ∈ P.carrier)
    (hb : embed n b ∈ interior Q.carrier) :
    embed n (a + b) ∈ interior (P.minkowskiSum Q) := by
  rw [map_add]
  exact subset_interior_add_right (Set.add_mem_add ha hb)

/-- The entire adjoint membership equivalence in dimension zero. -/
theorem mixed_adjoint_dimension_zero (P Q : LatticePolytope 0) (m : Lattice 0) :
    embed 0 m ∈ interior (P.minkowskiSum Q) ↔
      ∃ a b : Lattice 0, embed 0 a ∈ P.carrier ∧
        embed 0 b ∈ interior Q.carrier ∧ a + b = m := by
  constructor
  · intro _
    refine ⟨m, 0, ?_, ?_, add_zero m⟩
    · rw [P.carrier_eq_univ_zero]
      exact Set.mem_univ _
    · rw [Q.carrier_eq_univ_zero, interior_univ]
      exact Set.mem_univ _
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact P.add_mem_interior_minkowskiSum Q a b ha hb

end LatticePolytope

/-- The one-sided formulation used by the induction is equivalent to the
full equality in the principal adjoint statement. The omitted inclusion is
proved above for arbitrary polytopes. -/
theorem theorem1_3_iff_interior_decomposition :
    Theorem1_3PolytopeStatement ↔
      ∀ n : ℕ, ∀ P Q : LatticePolytope n,
        P.Smooth → Q.Smooth → P.SameNormalFan Q →
        P.EdgesAtLeast (n + 1) → Q.EdgesAtLeast (n + 1) →
        ∀ m : Lattice n, embed n m ∈ interior (P.minkowskiSum Q) →
          ∃ a b : Lattice n, embed n a ∈ P.carrier ∧
            embed n b ∈ interior Q.carrier ∧ a + b = m := by
  constructor
  · intro h n P Q hP hQ hfan hlenP hlenQ m hm
    exact (h n P Q hP hQ hfan hlenP hlenQ m).mp hm
  · intro h n P Q hP hQ hfan hlenP hlenQ m
    constructor
    · exact h n P Q hP hQ hfan hlenP hlenQ m
    · rintro ⟨a, b, ha, hb, rfl⟩
      exact P.add_mem_interior_minkowskiSum Q a b ha hb

end PaperVerification.ToricGeometry

