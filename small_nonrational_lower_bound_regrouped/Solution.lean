module

public import Consolidated.Seventeen
public import Consolidated.SixActualAssembly
public import Consolidated.RankFourTheorems
public import CompletedResidualCoverage
public import VerifiedTargets

@[expose] public section
noncomputable section
open Papers.RationalityTen

open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes
open scoped Classical

namespace SmallNonrationalBounds

/-- Theorem 2. Every real four-polytope with at most ten extreme vertices
has a rational realization of its ordinary face lattice. -/
theorem theoremTwo (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hn : P.vertices.card ≤ 10) : RationallyRealizable P :=
  PrincipalGeometryAssembly.theorem_two_of_inputs
    MatroidChecked.MatrixClassificationAssembly.nine_column_exceptional_matrix_density
    MatroidChecked.MatrixClassificationAssembly.eight_row_density_or_four_column_support
    (ActualResidualTargetAssembly.realizability_of_coverage
      Nonrational.TerminalVerification.targets_valid
      CompletedResidualCoverage.complete) P hP hn

/-- The upper bound is nonrationality of the entire face lattice, not only
irrationality of the displayed coordinates. The underlying proof establishes
`Real.sqrt 5 ∉ rationalSubfield` from the primality of five. -/
theorem seventeenVertexNonrational :
    ∃ P : ConvexPolytope 4,
      P.IsFullDim ∧ P.vertices.card = 17 ∧ ¬ RationallyRealizable P :=
  Papers.Nonrational.Seventeen.exists_seventeen_vertex_nonrational_polytope

/-- Every nonrational four-polytope has at least eleven vertices. -/
theorem nonrationalVertexLowerBound (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hnonrational : ¬ RationallyRealizable P) : 11 ≤ P.vertices.card := by
  by_contra h
  exact hnonrational (theoremTwo P hP (by omega))

/-- The paper's bounds on the least possible number of vertices, expressed
without introducing a separate convention for an infimum. -/
theorem vertexBounds :
    (∀ P : ConvexPolytope 4, P.IsFullDim → ¬ RationallyRealizable P →
      11 ≤ P.vertices.card) ∧
    ∃ P : ConvexPolytope 4,
      P.IsFullDim ∧ P.vertices.card = 17 ∧ ¬ RationallyRealizable P :=
  ⟨nonrationalVertexLowerBound, seventeenVertexNonrational⟩

/-- The minimum in the introduction exists and lies between eleven and
seventeen. Both its attainment and its defining minimality are explicit. -/
theorem minimumVertexBounds :
    ∃ N : ℕ,
      (∃ P : ConvexPolytope 4,
        P.IsFullDim ∧ P.vertices.card = N ∧ ¬ RationallyRealizable P) ∧
      (∀ P : ConvexPolytope 4,
        P.IsFullDim → ¬ RationallyRealizable P → N ≤ P.vertices.card) ∧
      11 ≤ N ∧ N ≤ 17 := by
  classical
  let S : ℕ → Prop := fun n => ∃ P : ConvexPolytope 4,
    P.IsFullDim ∧ P.vertices.card = n ∧ ¬ RationallyRealizable P
  have h17 : S 17 := seventeenVertexNonrational
  have hS : ∃ n, S n := ⟨17, h17⟩
  let N := Nat.find hS
  have hN : S N := Nat.find_spec hS
  refine ⟨N, hN, ?_, ?_, ?_⟩
  · intro P hP hnonrational
    exact Nat.find_min' hS ⟨P, hP, rfl, hnonrational⟩
  · obtain ⟨P, hP, hcard, hnonrational⟩ := hN
    simpa only [hcard] using nonrationalVertexLowerBound P hP hnonrational
  · exact Nat.find_min' hS h17

/-- Corollary 4. An eleven-vertex four-polytope with a simple vertex is
rationally realizable. -/
theorem corollaryFour (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hn : P.vertices.card = 11)
    (hsimple : ∃ v : VertexType P, IsSimpleVertex P v) : RationallyRealizable P :=
  PrincipalGeometryAssembly.corollary_four_of_theorem_two theoremTwo P hP hn hsimple

end SmallNonrationalBounds
