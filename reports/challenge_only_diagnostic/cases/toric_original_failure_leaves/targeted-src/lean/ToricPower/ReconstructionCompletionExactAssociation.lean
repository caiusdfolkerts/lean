module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-! # Exact paired factors before affine substitution

The exact affine factor is the direct image followed by the original
Hom functor. Associativity is checked with all functors abstract, so the
original reconstruction source can retain its literal parentheses.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe w v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {A : Type u₁} [Category.{v₁} A]
  {B : Type u₂} [Category.{v₂} B]
  {C : Type u₃} [Category.{v₃} C]
  {D : Type u₄} [Category.{v₄} D]
  {E : Type u₅} [Category.{v₅} E]
  {F : Type u₆} [Category.{v₆} F]
  (S : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) (T : D ⥤ E)

theorem reconstructionPaired_preservesFiniteLimits
    [PreservesFiniteLimits S] [PreservesFiniteLimits T]
    (pair : PreservesFiniteLimits (G ⋙ H)) :
    PreservesFiniteLimits ((S ⋙ G) ⋙ (H ⋙ T)) := by
  letI := pair
  change PreservesFiniteLimits ((S ⋙ (G ⋙ H)) ⋙ T)
  infer_instance

theorem reconstructionPaired_preservesFiniteColimits
    [PreservesFiniteColimits S] [PreservesFiniteColimits T]
    (pair : PreservesFiniteColimits (G ⋙ H)) :
    PreservesFiniteColimits ((S ⋙ G) ⋙ (H ⋙ T)) := by
  letI := pair
  change PreservesFiniteColimits ((S ⋙ (G ⋙ H)) ⋙ T)
  infer_instance

theorem reconstructionPairedDetector_preservesColimits (D' : E ⥤ F)
    [PreservesColimitsOfSize.{w,w} S] [PreservesColimitsOfSize.{w,w} T]
    [PreservesColimitsOfSize.{w,w} D']
    (pair : PreservesColimitsOfSize.{w,w} (G ⋙ H)) :
    PreservesColimitsOfSize.{w,w} (((S ⋙ G) ⋙ (H ⋙ T)) ⋙ D') := by
  letI := pair
  change PreservesColimitsOfSize.{w,w} (((S ⋙ (G ⋙ H)) ⋙ T) ⋙ D')
  infer_instance

theorem reconstructionTripleTarget_preservesColimits
    [PreservesColimitsOfSize.{w,w} S]
    (tail : PreservesColimitsOfSize.{w,w} (G ⋙ H ⋙ T)) :
    PreservesColimitsOfSize.{w,w} (((S ⋙ G) ⋙ H) ⋙ T) := by
  letI := tail
  change PreservesColimitsOfSize.{w,w} (S ⋙ (G ⋙ H ⋙ T))
  infer_instance

end ToricPower

end
