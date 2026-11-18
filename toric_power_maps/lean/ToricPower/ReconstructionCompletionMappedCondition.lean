module

public import ToricPower.ReconstructionCompletionQuasicoherentComparison

/-! # The original mapped reconstruction condition

The whole natural comparison is retained by its original named map.
This predicate is fixed with all coefficient and input functors abstract,
before any Hom diagram, tensor functor, or affine chart is substituted.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ToricPower

open FunctorTotal

variable (U X : Scheme.{0}) [HasFiniteBiproducts (QCoh X)]
  (A : QCoh U ⥤ QCoh X) [A.Additive]
  (F : QCoh X ⥤ CochainComplex (QCoh X) ℕ) [F.Additive]
  (T : QCoh X ⥤ QCoh X) [T.Additive]
  (n width : ℕ) (retained : n < width)
  (τ : F ⟶ singleCoefficient T n)

/-- The original mapped-input top augmentation is a quasi-isomorphism
on every unbounded complex over the source scheme. -/
def reconstructionMappedTopComparisonCondition : Prop :=
  ∀ K : CochainComplex (QCoh U) ℤ,
    QuasiIso ((quasicoherentTopComparisonAfterMap X A F T n width retained τ).app K)

/-- The named mapped comparison and the original top comparison on
mapped input complexes express the same unrestricted condition. -/
theorem reconstructionMappedTopComparisonCondition_iff :
    reconstructionMappedTopComparisonCondition U X A F T n width retained τ ↔
      ∀ K : CochainComplex (QCoh U) ℤ,
        QuasiIso ((topComparison F T n width retained τ).app
          ((A.mapHomologicalComplex (.up ℤ)).obj K)) := by
  constructor
  · intro h K
    exact (quasicoherentAffineTopComparisonAfterMap_quasiIso_iff U X A F T
      n width retained τ K).mp (h K)
  · intro h K
    exact (quasicoherentAffineTopComparisonAfterMap_quasiIso_iff U X A F T
      n width retained τ K).mpr (h K)

end ToricPower

end
