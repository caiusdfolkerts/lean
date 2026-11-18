module

public import ToricPower.FiniteProjectiveAffineDerived
public import ToricPower.DiagramProjectiveCechDerived

/-!
# The unbounded finite Čech comparison for whole coefficient diagrams

Conservative evaluation proves the actual projective augmentation on
each resolved complex. Its right-derived universal property is then
established in the derived category of the entire coefficient diagram,
so every label arrow and coefficient morphism is retained.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CochainComplex TopologicalSpace

namespace ToricPower

universe u v w

local instance finiteDiagramAffineDerivedCategory (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} (QCoh X) := HasDerivedCategory.standard _

variable {X : Scheme.{u}} {I : Type v}
  (V : I → X.Opens) [∀ i, IsAffineHom (V i).ι]
  (hV : IsOpenCover V) (l : List I) (hl : ∀ i, i ∈ l)
  (R : Type u) [CommRing R]
  {C : Type w} [Category.{u} C] [Abelian C] [Linear R C]
  [HasDerivedCategory C]
  {L : Type u} [Category.{u} L] [HasDerivedCategory (L ⥤ ModuleCat.{u} R)]
  (S : QCoh X ⥤ L ⥤ C) [S.Additive]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  {Z : C} (P : ProjectiveResolution Z)
  [∀ i, PreservesFiniteLimits (quasicoherentOpenLocalization (V i).ι ⋙
    ordinaryDiagramProjectiveCoefficients R S (Z := Z))]
  [∀ i, PreservesFiniteColimits (quasicoherentOpenLocalization (V i).ι ⋙
    ordinaryDiagramProjectiveCoefficients R S (Z := Z))]

include hV hl

/-- Finite support and the proved local ordinary rows give the full
unbounded universal property, valued in the actual diagram category. -/
theorem finiteDiagramProjectiveCoefficient_isRightDerivedFunctor
    (N : ℕ) (bound : ∀ m : ℕ, N < m → IsZero (P.complex.X m))
    (localRows : ∀ (i : I) (M : QCoh (V i).toScheme) (c : L) (n : ℕ),
      (projectiveCoefficientComplex R P
        ((S.obj ((quasicoherentAffinePushforward (V i).ι).obj M)).obj c)).ExactAt (n+1)) :
    (diagramProjectiveCoefficientDerived R S P).IsRightDerivedFunctor
      (diagramProjectiveCoefficientDerivedUnit R S P)
      (HomologicalComplex.quasiIso (QCoh X) (.up ℤ)) := by
  apply affine_isRightDerivedFunctor_of_resolvedUnit V hV l hl
    (ordinaryDiagramProjectiveCoefficients R S (Z := Z))
    (diagramProjectiveCoefficientDerived R S P) (diagramProjectiveCoefficientDerivedUnit R S P)
  intro K
  haveI : QuasiIso ((diagramProjectiveCoefficientComplexUnit R S P).app
      ((affineConeCoresolution V l).obj K)) := by
    rw [HomologicalComplex.quasiIso_iff_evaluation]
    intro c
    exact affineCoresolution_projectiveCoefficientUnit_quasiIso
      V (S ⋙ (evaluation L C).obj c) R P N bound
      (fun i M n => localRows i M c n) l K
  dsimp only [diagramProjectiveCoefficientDerivedUnit, NatTrans.comp_app,
    Functor.whiskerRight_app]
  infer_instance

end ToricPower

end
