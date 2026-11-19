module
public import Papers.GPActualBoundaryExclusion
public import GPGeometry.PrismNine.Relations
public import GPGeometry.PrismNine.Boundary

@[expose] public section
noncomputable section
namespace Papers.RationalityTen.GPFiniteGeometry.Literal.PrismNine
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes
open Papers.RationalityTen.ChirotopeDensity
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Papers.RationalityTen.PureGP
open Papers.RationalityTen.SupportDeterminantStandalone
open Papers.RationalityTen.GPActualSupportSigns

/-- The prism boundary at terminal117 has no
actual realization. Its full boundary is the only combinatorial hypothesis;
all signs, rank facts and a nonzero anchor are derived internally.
 -/
theorem no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab boundary) : False := by
  let p := vertexCoordinates P lab
  let scale := (Papers.RationalityTen.SupportDeterminantStandalone.minor p (minorRows Papers.RationalityTen.PureGP.PrismNine.Initializer.anchor))⁻¹
  let assignment : Nat → Sign := fun i => realSign (scale * Papers.RationalityTen.SupportDeterminantStandalone.minor p (minorRows i))
  apply Papers.RationalityTen.PureGP.PrismNine.Initializer.support_sign_contradiction assignment
  · exact normalizedAssignment_anchor p minorRows Papers.RationalityTen.PureGP.PrismNine.Initializer.anchor
      (geometry.anchor_witness.actual_nonzero hB)
  · intro i hi
    exact (geometry.support_witness ⟨i, hi⟩).actual_holds hB scale
  · intro i hi
    exact (geometry.zero_witness ⟨i, hi⟩).actual_zero hP hB scale
  · intro i hi
    exact (allRelations ⟨i, hi⟩).allowed_scaled p scale

/-- Vertex relabelling preserves this boundary obstruction.
This universal transport also covers any other relabelling. -/
theorem no_actual_relabelled_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (σ : Equiv.Perm (Fin 10))
    (hB : RealizesBoundary P lab (boundary.relabel σ)) : False := by
  have h := hB.relabel σ.symm
  simp only [Boundary.relabel_symm, Equiv.symm_symm] at h
  exact no_actual_boundary P (σ.trans lab) hP h

end Papers.RationalityTen.GPFiniteGeometry.Literal.PrismNine
