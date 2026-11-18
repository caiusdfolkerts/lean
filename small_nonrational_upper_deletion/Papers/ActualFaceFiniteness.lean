module
public import Cubical.Polytope.FiguraAlVertice

@[expose] public section

/-! The finite type of genuine nonempty exposed faces, using facce_finite. -/

noncomputable section
namespace Papers.Polytopes
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical
variable {d : ℕ}

def ActualFaceType (P : ConvexPolytope d) :=
  {F : Set (E d) // P.IsFace F}

noncomputable instance actualFaceTypeFintype (P : ConvexPolytope d) :
    Fintype (ActualFaceType P) :=
  (facce_finite P).fintype

end Papers.Polytopes

