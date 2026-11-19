module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.Linear

/-!
# Small colimits and the linear single-degree functor

These instances package the existing degreewise colimit construction
uniformly in the indexing category. The single-degree functor retains
the original scalar action on its only nonzero component.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe w w' v u

section Colimits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {ι : Type*} (shape : ComplexShape ι)

instance homologicalComplex_hasSmallColimits [HasColimitsOfSize.{w,w'} C] :
    HasColimitsOfSize.{w,w'} (HomologicalComplex C shape) where
  has_colimits_of_shape J _ := inferInstance

instance single_preservesSmallColimits [HasZeroObject C] [DecidableEq ι] (q : ι) :
    PreservesColimitsOfSize.{w,w'} (HomologicalComplex.single C shape q) where
  preservesColimitsOfShape := by intros; infer_instance

end Colimits

section Linearity

variable (R : Type*) [Semiring R] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear R C] [HasZeroObject C]
  {ι : Type*} [DecidableEq ι] (shape : ComplexShape ι)

instance single_linear (q : ι) :
    (HomologicalComplex.single C shape q).Linear R where
  map_smul f r := by
    apply HomologicalComplex.to_single_hom_ext
    simp only [HomologicalComplex.single_map_f_self, HomologicalComplex.smul_f_apply,
      Linear.comp_smul, Linear.smul_comp]

end Linearity

end ToricPower

end
