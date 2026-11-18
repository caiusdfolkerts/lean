module

public import ToricPower.ReconstructionCompletionMappedCondition
public import ToricPower.ReconstructionCompletionQuasicoherentOpenRange

/-! # The original named comparison on chart image opens

Both the affine-chart calculation and its image-open conclusion remain
the same named mapped comparison condition. The coefficient functor and
augmentation are abstract throughout this change of source scheme.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ToricPower

open FunctorTotal

section Single

variable {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
  [IsAffineHom j] [IsAffineHom j.opensRange.ι]
  [HasFiniteBiproducts (QCoh X)]
  (F : QCoh X ⥤ CochainComplex (QCoh X) ℕ) [F.Additive]
  (T : QCoh X ⥤ QCoh X) [T.Additive]
  (n width : ℕ) (retained : n < width)
  (τ : F ⟶ singleCoefficient T n)

/-- The original named comparison on the source chart gives the same
named comparison on its image open, for every unbounded input complex. -/
def reconstructionMappedOpenRangeCondition
    (localCondition : reconstructionMappedTopComparisonCondition U X
      (quasicoherentAffinePushforward j) F T n width retained τ) :
    reconstructionMappedTopComparisonCondition j.opensRange.toScheme X
      (quasicoherentAffinePushforward j.opensRange.ι) F T n width retained τ :=
  (reconstructionMappedTopComparisonCondition_iff j.opensRange.toScheme X
    (quasicoherentAffinePushforward j.opensRange.ι) F T n width retained τ).mpr
    (reconstructionQuasicoherentOpenRange_topComparison_quasiIso j F T n width retained τ
      ((reconstructionMappedTopComparisonCondition_iff U X
        (quasicoherentAffinePushforward j) F T n width retained τ).mp localCondition))

end Single

section Family

variable {I : Type*} (U : I → Scheme.{0}) (X : Scheme.{0})
  (j : ∀ i, U i ⟶ X)
  [∀ i, IsOpenImmersion (j i)] [∀ i, IsAffineHom (j i)]
  [∀ i, IsAffineHom (j i).opensRange.ι]
  [HasFiniteBiproducts (QCoh X)]
  (F : QCoh X ⥤ CochainComplex (QCoh X) ℕ) [F.Additive]
  (T : QCoh X ⥤ QCoh X) [T.Additive]
  (n width : ℕ) (retained : n < width)
  (τ : F ⟶ singleCoefficient T n)

/-- Whole-family chart-to-image transport, keeping the named comparison
condition and its original coefficient functors unchanged. -/
def reconstructionMappedOpenRangeFamilyCondition
    (localCondition : ∀ i, reconstructionMappedTopComparisonCondition (U i) X
      (quasicoherentAffinePushforward (j i)) F T n width retained τ) :
    ∀ i, reconstructionMappedTopComparisonCondition (j i).opensRange.toScheme X
      (quasicoherentAffinePushforward (j i).opensRange.ι) F T n width retained τ :=
  fun i => reconstructionMappedOpenRangeCondition (j i) F T n width retained τ
    (localCondition i)

end Family

end ToricPower

end
