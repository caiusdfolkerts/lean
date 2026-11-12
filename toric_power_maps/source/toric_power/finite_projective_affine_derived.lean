module

public import ToricPower.AffineBoundedSourceAssembly
public import ToricPower.AffineDerivedComparisonCriterion

/-!
# The full unbounded derived comparison for finite projective Čech models

A finite projective resolution, an exact chart-diagram functor, and
exact coefficient rows on genuine affine-open direct images give an
actual right-derived functor on all quasicoherent complexes. The
comparison is the original signed Hom augmentation, not a replacement
chosen after computing cohomology.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CochainComplex TopologicalSpace

namespace ToricPower

universe u v w

local instance finiteProjectiveAffineDerivedCategory (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} (QCoh X) := HasDerivedCategory.standard _

variable {X : Scheme.{u}} {I : Type v}
  (V : I → X.Opens) [∀ i, IsAffineHom (V i).ι]
  (hV : IsOpenCover V) (l : List I) (hl : ∀ i, i ∈ l)
  (R : Type u) [CommRing R]
  {C : Type w} [Category.{u} C] [Abelian C] [Linear R C]
  [HasDerivedCategory C] [HasDerivedCategory (ModuleCat.{u} R)]
  (S : QCoh X ⥤ C) [S.Additive]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  {Z : C} (P : ProjectiveResolution Z)
  [∀ i, PreservesFiniteLimits (quasicoherentOpenLocalization (V i).ι ⋙
    ordinaryProjectiveCoefficients R S (Z := Z))]
  [∀ i, PreservesFiniteColimits (quasicoherentOpenLocalization (V i).ι ⋙
    ordinaryProjectiveCoefficients R S (Z := Z))]

include hV hl

/-- This proves the full universal property after discharging the
finite support and all local ordinary coefficient rows. -/
theorem finiteProjectiveCoefficient_isRightDerivedFunctor
    (N : ℕ) (bound : ∀ m : ℕ, N < m → IsZero (P.complex.X m))
    (localRows : ∀ (i : I) (M : QCoh (V i).toScheme) (n : ℕ),
      (projectiveCoefficientComplex R P
        (S.obj ((quasicoherentAffinePushforward (V i).ι).obj M))).ExactAt (n+1)) :
    (projectiveCoefficientDerived R S P).IsRightDerivedFunctor
      (projectiveCoefficientDerivedUnit R S P)
      (HomologicalComplex.quasiIso (QCoh X) (.up ℤ)) := by
  apply affine_isRightDerivedFunctor_of_resolvedUnit V hV l hl
    (ordinaryProjectiveCoefficients R S (Z := Z))
    (projectiveCoefficientDerived R S P) (projectiveCoefficientDerivedUnit R S P)
  intro K
  letI := affineCoresolution_projectiveCoefficientUnit_quasiIso
    V S R P N bound localRows l K
  dsimp only [projectiveCoefficientDerivedUnit, NatTrans.comp_app,
    Functor.whiskerRight_app]
  infer_instance

/-- The concrete unbounded model agrees naturally with the already
constructed affine right-derived functor. -/
def finiteProjectiveAffineDerivedIso
    (N : ℕ) (bound : ∀ m : ℕ, N < m → IsZero (P.complex.X m))
    (localRows : ∀ (i : I) (M : QCoh (V i).toScheme) (n : ℕ),
      (projectiveCoefficientComplex R P
        (S.obj ((quasicoherentAffinePushforward (V i).ι).obj M))).ExactAt (n+1)) :
    projectiveCoefficientDerived R S P ≅
      affineConeDerivedStage V (ordinaryProjectiveCoefficients R S (Z := Z)) l := by
  letI := finiteProjectiveCoefficient_isRightDerivedFunctor V hV l hl R S P N bound localRows
  letI := affineConeDerivedStage_isRightDerivedFunctor V
    (ordinaryProjectiveCoefficients R S (Z := Z)) l hl hV
  exact Functor.rightDerivedUnique _ _ (projectiveCoefficientDerivedUnit R S P)
    (affineRightDerivedUnit V (ordinaryProjectiveCoefficients R S (Z := Z)) l)
    (HomologicalComplex.quasiIso (QCoh X) (.up ℤ))

end ToricPower

end
