module

public import ToricPower.InternalDualComplex
public import Mathlib.CategoryTheory.Monoidal.Linear

/-! # Scalar linearity of the actual internal dual functor -/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed Opposite

namespace ToricPower

universe u v w

variable (R : Type w) [CommRing R]
  (C : Type u) [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  [Preadditive C] [MonoidalPreadditive C] [Linear R C] [MonoidalLinear R C]

/-- Scalar multiplication transposes through internal Hom into the
unit with the same actual scalar. -/
instance internalDual_linear : (internalDual C).Linear R where
  map_smul {M N} f r := by
    change (pre (r • f.unop)).app (𝟙_ C) = r • (pre f.unop).app (𝟙_ C)
    apply uncurry_injective
    rw [uncurry_pre, uncurry_eq]
    simp only [MonoidalLinear.whiskerLeft_smul, Linear.smul_comp]
    rw [← uncurry_eq, uncurry_pre]
    simp

end ToricPower

end
