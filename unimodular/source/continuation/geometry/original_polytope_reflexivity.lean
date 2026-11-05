module

public import Continuation.Geometry.OriginalPolytopeFaces

/-! # Reflexivity and full dimension in the original real space -/

@[expose] public section
noncomputable section
set_option autoImplicit false

open PaperVerification.OriginalLatticeCharts
open scoped Classical

universe u v

namespace Unimodular.OriginalSmoothReflexivePresentation

variable {N : Type u} [AddCommGroup N]
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : ℕ} {ι : N →+ V} (P : OriginalSmoothReflexivePresentation n ι)

/-- Interior is the ambient interior, not relative interior in a smaller
subspace. This derives full dimensionality in the original space. -/
theorem zero_mem_interior_carrier : (0 : V) ∈ interior P.carrier := by
  let b := P.coordinateBasis
  exact originalRayHull_zero_interior b P.lattice P.vertices
    (P.coordinatePresentation b).zero_mem_interior_carrier

/-- The full original real dual polar is a convex hull of finitely many
actual integral characters. Rank zero is covered by retaining zero. -/
theorem originalDualPolar_latticePolytope :
    ∃ W : Finset (N →+ ℤ), originalDualPolar P.carrier =
      convexHull ℝ (P.lattice.realCharacter '' (W : Set (N →+ ℤ))) := by
  let b := P.coordinateBasis
  apply PaperVerification.OriginalLatticeCharts.originalDualPolar_latticePolytope
    b P.lattice P.vertices (insert 0 (P.coordinatePresentation b).normals)
  have h := (P.coordinatePresentation b).realPolar_eq_convexHull_normals
  change coordinateDualPolar (convexHull ℝ (PaperVerification.ToricGeometry.embed n '' (P.coordinatePresentation b).vertices)) = _ at h
  simp only [Finset.coe_insert]
  exact h

/-- The intrinsic presentation supplies the ordinary original-space
reflexivity certificate: ambient interior and finite primal and dual lattice hulls. -/
theorem geometric_reflexivity :
    (0 : V) ∈ interior P.carrier ∧
    (∃ U : Finset N, P.carrier = convexHull ℝ (ι '' (U : Set N))) ∧
    (∃ W : Finset (N →+ ℤ), originalDualPolar P.carrier =
      convexHull ℝ (P.lattice.realCharacter '' (W : Set (N →+ ℤ)))) :=
  ⟨P.zero_mem_interior_carrier, ⟨P.vertices, rfl⟩, P.originalDualPolar_latticePolytope⟩

end Unimodular.OriginalSmoothReflexivePresentation
