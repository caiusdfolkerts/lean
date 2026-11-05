module

public import Consolidated.Seventeen
public import Consolidated.SixActualAssembly
public import Consolidated.RankFourTheorems
public import Papers.DensityTheorems
public import Papers.GlobalEightRelationRowsClosed
public import Papers.PropositionNinePaper
public import Papers.RationalityTenMultiaffine
public import CompletedResidualCoverage
public import VerifiedTargets

/-!
# Small nonrational four-polytopes

The principal statements use actual convex polytopes, their extreme vertices,
and ordinary order isomorphisms of face lattices. Rational density means
approximation near every labelled realization of the combinatorial type.

The proofs below assemble the separately verified geometric and finite
results. The statement of each paper theorem is displayed directly.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace Papers.SmallNonrational

open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFacetSurplus
open Papers.PolytopeRelationBudget Papers.PolytopeMasterBudget
open Papers.RationalityTen
open Papers.RationalityTen.ChirotopeDensity

/-- Theorem 1. The field obstruction is exactly the golden quadratic field. -/
theorem theoremOne :
    ∃ P : ConvexPolytope 4, P.IsFullDim ∧ P.vertices.card = 17 ∧
      ∀ K : Subfield ℝ, RealizableOver P K ↔ Real.sqrt 5 ∈ K :=
  Papers.Nonrational.Seventeen.seventeen_vertex_field_theorem

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

/-- Theorem 3. Simple-vertex deletion is determined by the face lattice,
preserves all real realization fields, and preserves rational density. -/
theorem theoremThree (d : ℕ) (P : ConvexPolytope d) (v : VertexType P)
    (hP : P.IsFullDim) (hcard : d + 1 < P.vertices.card)
    (hs : IsSimpleVertex P v) :
    ∃ hne : (P.vertices.erase v.val).Nonempty,
      (deleteVertex P v.val hne).IsFullDim ∧
      (∀ (Q : ConvexPolytope d) (φ : FaceType P ≃o FaceType Q)
          (hneQ : (Q.vertices.erase (imageVertex φ v).val).Nonempty),
        CombinatoriallyEquivalent (deleteVertex P v.val hne)
          (deleteVertex Q (imageVertex φ v).val hneQ)) ∧
      realizationFields P = realizationFields (deleteVertex P v.val hne) ∧
      (RationallyDense P ↔ RationallyDense (deleteVertex P v.val hne)) :=
  paper_simple_vertex_deletion d P v hP hcard hs

/-- Corollary 4. An eleven-vertex four-polytope with a simple vertex is
rationally realizable. -/
theorem corollaryFour (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hn : P.vertices.card = 11)
    (hsimple : ∃ v : VertexType P, IsSimpleVertex P v) : RationallyRealizable P :=
  PrincipalGeometryAssembly.corollary_four_of_theorem_two theoremTwo P hP hn hsimple

/-- Proposition 7. A checked incidence deletion and height reconstruction,
including the polygon bound away from the chosen centre, gives density for
the entire combinatorial type. The label and relation counts are unrestricted. -/
theorem propositionSeven {n : ℕ} {B : FiniteProjection.Boundary n}
    (C : FiniteProjection.PaperCertifiedRelabelling B)
    (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (lab : Fin (n + 1) ≃ VertexType P)
    (hB : FiniteProjection.RealizesBoundary P lab B) : RationallyDense P :=
  C.toCertifiedRelabelling.rationallyDense hP lab hB

/-- Proposition 8(i). Density for every type with at most nine vertices. -/
theorem propositionEight_i (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hn : P.vertices.card ≤ 9) : RationallyDense P :=
  Papers.CheckedDensity.proposition_eight_i P hP hn

/-- Proposition 8(ii). Either small exceptional part suffices; there is no
bound on the total number of vertices or facets. -/
theorem propositionEight_ii (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hcount : (nonsimplicialFacets P).card ≤ 9 ∨
      (nonsimpleVertices P).card ≤ 9) : RationallyDense P :=
  Papers.CheckedDensity.proposition_eight_ii P hP hcount

/-- Proposition 8(iii). One realization with the paper's row budget gives
density near every realization, including those where local polygon ranks drop. -/
theorem propositionEight_iii (P : ConvexPolytope 4)
    (hadmit : ∃ Q : ConvexPolytope 4, Q.IsFullDim ∧
      CombinatoriallyEquivalent P Q ∧
      ∃ (n : ℕ) (e : Fin n ≃ Q.vertices),
        sharedRelationCount Q (actualPolygonRelationRank Q e) ≤ 8) :
    RationallyDense P :=
  proposition8iii_admitting_rows P hadmit

/-- Proposition 9. Every remaining ten-vertex type has the paper's exact
projection criterion or an ordinary face-order isomorphism with an explicit
Appendix B configuration. The earlier applicability conditions are geometric;
no labels, finite-catalogue membership or encoding are hypotheses here. -/
theorem propositionNine (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hn : P.vertices.card = 10)
    (hremaining : ¬ PaperResidualInterface.EarlierReductionsApply P) :
    Nonrational.TerminalVerification.SatisfiesPaperProjectionCriterion P ∨
      Nonrational.TerminalVerification.IsExplicitAppendixConfiguration P :=
  PaperResidualInterface.proposition_nine_of_not_removed
    CompletedResidualCoverage.complete P hP hn hremaining

/-- Lemma 11. Exact rank-four density, with rational entries and all minor
signs written out. Both real roots give the same exceptional matroid. -/
theorem lemmaEleven (p : Matrix (Fin 8) (Fin 4) ℝ)
    (hspan : Submodule.span ℝ (Set.range p) = ⊤)
    (t : ℝ) (ht : t ^ 2 + t - 1 = 0) :
    p ∈ closure {q : Matrix (Fin 8) (Fin 4) ℝ |
      (∀ i j, ∃ a : ℚ, (a : ℝ) = q i j) ∧
      ∀ b : Fin 4 → Fin 8,
        SignType.sign (Matrix.of (fun i j => q (b i) j)).det =
          SignType.sign (Matrix.of (fun i j => p (b i) j)).det} ↔
      ¬ ∃ σ : Equiv.Perm (Fin 8),
        (VectorBasisFamilies.vectorBases p).image (fun S => S.image σ) =
          VectorBasisFamilies.vectorBases
            (MatroidChecked.GoldenIdentification.goldenRows t) :=
  MatroidChecked.PaperRankFourTheorem.lemma11 p hspan t ht

/-- Lemma 12. Every zero in a nonzero multiaffine fibre is a limit of fully
rational zeros. The parameter has no degree bound and may vary in the limit. -/
theorem lemmaTwelve {n : ℕ} (p : MvPolynomial (Option (Fin n)) ℚ)
    (hdegree : ∀ i : Fin n, p.degreeOf (some i) ≤ 1)
    (x : Option (Fin n) → ℝ)
    (hzero : MultiaffineDensity.evalRat p x = 0)
    (hfiber : MultiaffineDensity.specializeParameter p (x none) ≠ 0) :
    x ∈ closure {q : Option (Fin n) → ℝ |
      (∀ i, ∃ a : ℚ, (a : ℝ) = q i) ∧ MultiaffineDensity.evalRat p q = 0} :=
  MultiaffineDensity.multiaffine_rational_zeros_dense p hdegree x hzero hfiber

end Papers.SmallNonrational
