module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.Additive

/-! # An additive functor preserves the actual alternating coface complex -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  (F : C ⥤ D) [F.Additive] (X : CosimplicialObject C)

/-- The degree identities commute with the literal alternating
coface differentials because the functor preserves sums and signs. -/
def additiveAlternatingCofaceIso :
    AlgebraicTopology.AlternatingCofaceMapComplex.obj (X ⋙ F) ≅
      (F.mapHomologicalComplex (.up ℕ)).obj
        (AlgebraicTopology.AlternatingCofaceMapComplex.obj X) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (fun p q related => by
      change p+1 = q at related
      subst q
      simp [AlgebraicTopology.AlternatingCofaceMapComplex.obj,
        AlgebraicTopology.AlternatingCofaceMapComplex.objD, CochainComplex.of_d,
        F.map_sum, F.map_zsmul]
      rfl)

end ToricPower

end
