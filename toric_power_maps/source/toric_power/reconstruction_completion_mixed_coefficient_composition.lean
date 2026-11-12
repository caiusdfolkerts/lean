module

public import ToricPower.ReconstructionCompletionNativeCoefficientCondition

/-! # The original two scalar presentations in one coefficient functor

The Hom functor retains its original commutative-ring presentation and
the cellular functor retains its original ordinary complex-ring
presentation. Their composition is checked with both functors abstract,
before a geometric Hom diagram is inserted.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory

namespace ToricPower

variable (X : Scheme.{0}) {C : Type} [Category.{0} C]
  (H : QCoh X ⥤ (C ⥤ @ModuleCat.{0} ℂ Complex.commRing.toRing))
  (Φ : (C ⥤ ModuleCat.{0} ℂ) ⥤ CochainComplex (QCoh X) ℕ)

/-- The literal original composition, with both source scalar
presentations fixed before any concrete coefficient functor appears. -/
abbrev reconstructionMixedCoefficientComposition :
    QCoh X ⥤ CochainComplex (QCoh X) ℕ :=
  H ⋙ Φ

/-- Additivity of the same mixed-presentation composition, with the
entire target functor retained in its typed presentation. -/
theorem reconstructionMixedCoefficientComposition_additive [H.Additive] [Φ.Additive] :
    (reconstructionMixedCoefficientComposition X H Φ).Additive := by
  infer_instance

end ToricPower

end
