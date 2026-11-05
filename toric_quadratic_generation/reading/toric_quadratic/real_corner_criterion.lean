module

public import ToricQuadratic.CornerCriterion
public import toric_quadratic.fan_basics

@[expose] public section

/-!
# The real corner-box criterion with intrinsic hypotheses

These are the two forms of Lemma 3.1 for an arbitrary real ample support.
The existing literal box-containment predicate is unchanged. Purity and
the integral projectivity witness needed by the underlying nef criterion
are consequences of the stated fan and real strict-support hypotheses.
-/

namespace ToricQuadratic

open PaperVerification.ToricGeometry

/-- A real ample support contains every corner box of side `side` exactly
when every contractible primitive relation satisfies the stated degree bound. -/
theorem real_corner_boxes_iff_contractible_degrees
    {n : ℕ} («Σ» : SmoothCompleteFan n)
    (a : Lattice n → ℝ) (ha : «Σ».IsStrictSupport a)
    (side : ℝ) (hside : 0 ≤ side) :
    «Σ».ContainsCornerBoxes a side ↔
      ∀ R : «Σ».PrimitiveRelation, R.IsCombinatoriallyContractible →
        side * R.fiberDimension ≤ R.degree a := by
  obtain ⟨A, hA⟩ := «Σ».exists_integral_strictSupport_of_real a ha
  exact «Σ».containsCornerBoxes_iff_contractible_degrees
    «Σ».isPure_of_complete A hA a side hside

/-- The same real corner-box condition is equivalent to the degree
inequalities on all extremal primitive relations. -/
theorem real_corner_boxes_iff_extremal_degrees
    {n : ℕ} («Σ» : SmoothCompleteFan n)
    (a : Lattice n → ℝ) (ha : «Σ».IsStrictSupport a)
    (side : ℝ) (hside : 0 ≤ side) :
    «Σ».ContainsCornerBoxes a side ↔
      ∀ R : «Σ».PrimitiveRelation, R.IsExtremal →
        side * R.fiberDimension ≤ R.degree a := by
  obtain ⟨A, hA⟩ := «Σ».exists_integral_strictSupport_of_real a ha
  exact «Σ».containsCornerBoxes_iff_extremal_degrees
    «Σ».isPure_of_complete A hA a side hside

end ToricQuadratic
