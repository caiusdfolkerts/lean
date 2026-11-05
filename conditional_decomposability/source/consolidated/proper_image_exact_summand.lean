module
public import consolidated_dev.minkowski_map_core

set_option Elab.async false

section BundlePart0
/- Source: Papers/ProperImageExactSummand.lean -/




@[expose] public section

/-!
# The proper-image summand with its exact affine dimension

The signed weak-summand theorem constructs a genuine polytope from the
parallel image. Positive rescaling makes it an ordinary Minkowski summand.
Both operations preserve affine dimension; this statement retains that
equality for the subsequent codimension arguments.
-/

noncomputable section
namespace Papers.ProperImageExactSummand

open Set Module
open Papers.PolytopeFourRegularTail Papers.ProperImageWeakSummand
open Papers.WeakSummandScaling Papers.Polytopes
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical Pointwise

variable {n : ℕ}

theorem nonconstant_of_nonhomothetic
    (P : ConvexPolytope n) (f : E n → E n)
    (hf : ¬IsHomothetyOnVertices P f) :
    ¬∃b:E n,∀x∈P.vertices,f x=b := by
  rintro ⟨b,hb⟩
  apply hf
  refine ⟨0,b,?_⟩
  intro x hx
  simpa only [zero_smul,zero_add] using hb x hx

theorem proper_image_actual_summand_exact_dimension
    (P : ConvexPolytope n) (hP : P.IsFullDim)
    (f : E n → E n) (hf : ParallelOnTail P P.vertices f)
    (hnonconstant : ¬∃b:E n,∀x∈P.vertices,f x=b)
    (hproper : finrank ℝ (vectorSpan ℝ (f '' (P.vertices : Set (E n))))<n)
    (hN : P.vertices.card<4*n-4) :
    ∃A B:ConvexPolytope n,
      A.dim=finrank ℝ (vectorSpan ℝ (f '' (P.vertices : Set (E n)))) ∧
      0<A.dim ∧ A.dim<n ∧ P.toSet=A.toSet+B.toSet := by
  obtain ⟨σ,hσ,c,ε,hε,A,B,hA,hdim,hsum⟩ :=
    proper_image_signed_weak_summand P hP f hf hnonconstant hproper hN
  refine ⟨scalePolytope A ε,B,?_,?_,?_,?_⟩
  · rw [scalePolytope_dim A ε hε.ne',hdim]
  · rw [scalePolytope_dim A ε hε.ne',hdim]
    exact nonconstant_image_dimension_pos P f hnonconstant
  · rwa [scalePolytope_dim A ε hε.ne',hdim]
  · rwa [scalePolytope_body]

end Papers.ProperImageExactSummand

end
end
end BundlePart0

