module

public import ToricPower.AffineHomotopyCoresolution
public import ToricPower.AffineConeHomotopySupport
public import ToricPower.CoresolutionDerivedUniversal

/-!
# Unbounded right derivation by a finite affine cover

The finite affine coresolution constructs the actual right derived
functor of an additive functor which is exact on affine-open direct
images. All complexes are unbounded. The covering hypothesis proves
that coaugmentation is a quasi-isomorphism; local contractibility and
orthogonality prove its iterated coherence up to chain homotopy.

The universal property is absolute: it remains true after arbitrary
postcomposition. Thus this construction can be used in a genuine
derived adjunction without assuming unbounded injective resolutions.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.Functor CochainComplex TopologicalSpace

namespace ToricPower

universe u v w z w' z'

local instance affineRightDerivedCategory (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} (QCoh X) := HasDerivedCategory.standard _

variable {X : Scheme.{u}} {I : Type v}
  (V : I → X.Opens) [∀ i, IsAffineHom (V i).ι]
  {D : Type w} [Category.{z} D] [Abelian D] [HasDerivedCategory D]
  (H : QCoh X ⥤ D) [H.Additive]
  [∀ i, PreservesFiniteLimits (quasicoherentOpenLocalization (V i).ι ⋙ H)]
  [∀ i, PreservesFiniteColimits (quasicoherentOpenLocalization (V i).ι ⋙ H)]
  (l : List I)

/-- The comparison induced by the literal finite coaugmentation. -/
def affineRightDerivedUnit :
    H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ affineConeDerivedStage V H l :=
  coresolutionDerivedUnit (affineConeCoresolution V l)
    (affineConeCoaugmentation V l) DerivedCategory.Q
    (H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (affineConeDerivedStage V H l) (affineConeDerivedStageFactors V H l)

variable (hl : ∀ i, i ∈ l) (hV : IsOpenCover V)

include hl hV

/-- The resolved functor satisfies the full right-derived universal
property on the actual unbounded quasicoherent derived category. -/
theorem affineConeDerivedStage_isRightDerivedFunctor :
    (affineConeDerivedStage V H l).IsRightDerivedFunctor
      (affineRightDerivedUnit V H l)
      (HomologicalComplex.quasiIso (QCoh X) (.up ℤ)) := by
  apply coresolution_isRightDerivedFunctor (affineConeCoresolution V l)
    (affineConeCoaugmentation V l) DerivedCategory.Q
    (HomologicalComplex.quasiIso (QCoh X) (.up ℤ))
    (fun K => by
      letI := affineConeCoaugmentation_quasiIso V l hl hV K
      infer_instance)
    (affineConeDerivedStageFactors V H l)
  intro K
  exact affineConeCoaugmentation_coherence V l
    (fun K i => openFiberStage_restrict_homotopy_isZero V l K i (hl i)) H K

/-- Arbitrary postcomposition preserves this right-derived universal
property; all local homotopy hypotheses have been proved. -/
theorem affineConeDerivedStage_isAbsoluteRightDerivedFunctor
    {E : Type w'} [Category.{z'} E] (T : DerivedCategory D ⥤ E) :
    (affineConeDerivedStage V H l ⋙ T).IsRightDerivedFunctor
      (whiskerRight (affineRightDerivedUnit V H l) T ≫
        (Functor.associator DerivedCategory.Q (affineConeDerivedStage V H l) T).hom)
      (HomologicalComplex.quasiIso (QCoh X) (.up ℤ)) := by
  apply coresolution_isAbsoluteRightDerivedFunctor (affineConeCoresolution V l)
    (affineConeCoaugmentation V l) DerivedCategory.Q
    (HomologicalComplex.quasiIso (QCoh X) (.up ℤ))
    (fun K => by
      letI := affineConeCoaugmentation_quasiIso V l hl hV K
      infer_instance)
    (affineConeDerivedStageFactors V H l)
  intro K
  exact affineConeCoaugmentation_coherence V l
    (fun K i => openFiberStage_restrict_homotopy_isZero V l K i (hl i)) H K

end ToricPower

end
