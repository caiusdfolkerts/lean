module

public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Scalar linearity of the actual complex homology functor -/

@[expose] public noncomputable section

open CategoryTheory

namespace ToricPower

universe r u v w

variable (R : Type r) [Semiring R] (C : Type u) [Category.{v} C]
  [Preadditive C] [Linear R C] {I : Type w} (shape : ComplexShape I)

/-- Passing to the three adjacent terms of a complex preserves the
actual scalar action on chain maps. -/
instance shortComplexFunctor_linear (degree : I) :
    (HomologicalComplex.shortComplexFunctor C shape degree).Linear R where
  map_smul f r := by
    ext <;> rfl

/-- Complex homology has the scalar action already constructed by
Mathlib's homology of short complexes. -/
instance homologyFunctor_linear [CategoryWithHomology C] (degree : I) :
    (HomologicalComplex.homologyFunctor C shape degree).Linear R := by
  change (HomologicalComplex.shortComplexFunctor C shape degree ⋙
    ShortComplex.homologyFunctor C).Linear R
  infer_instance

end ToricPower

end
