module

public import ToricPower.AffineRightDerivedResolved
public import ToricPower.DerivedOpenCoverDetection
public import ToricPower.DerivedHomPlusExt

/-!
# The affine right-derived comparison on actual injective resolutions

Contractibility on an actual open cover implies ordinary acyclicity,
proved by restriction of the actual homology sheaves. Every K-injective
complex is consequently right orthogonal to the locally contractible
complexes. The finite affine coresolution comparison is therefore an
isomorphism on every such complex, including the actual bounded-below
injective resolution of every quasicoherent sheaf.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CochainComplex TopologicalSpace

namespace ToricPower

universe u v w z

local instance affineInjectiveDerivedCategory (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} (QCoh X) := HasDerivedCategory.standard _

variable {X : Scheme.{u}} {I : Type v} (V : I → X.Opens)
  [∀ i, IsAffineHom (V i).ι] (hV : IsOpenCover V)

include hV

/-- Locally contractible complexes on a genuine cover are actually
acyclic. The proof detects the vanishing of every homology sheaf. -/
theorem affineCoverContractible_le_acyclic :
    affineCoverContractible V ≤ HomotopyCategory.subcategoryAcyclic (QCoh X) := by
  intro K hK
  change HomotopyCategory.subcategoryAcyclic (QCoh X)
    ((HomotopyCategory.quotient (QCoh X) (.up ℤ)).obj K.as)
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  apply IsZero.of_full_of_faithful_of_isZero (quasicoherentInclusion X)
  apply moduleSheaf_isZero_of_openCover V hV
  intro i
  let F := quasicoherentRestriction (V i).ι
  let FK := (F.mapHomologicalComplex (.up ℤ)).obj K.as
  have hFK : IsZero ((HomotopyCategory.quotient (QCoh (V i).toScheme) (.up ℤ)).obj FK) :=
    ((F.mapHomotopyCategoryFactors (.up ℤ)).app K.as).isZero_iff.mp (hK i)
  have hh : IsZero (FK.homology n) :=
    ((HomotopyCategory.homologyFunctorFactors (QCoh (V i).toScheme) (.up ℤ) n).app FK).isZero_iff.mp
      ((HomotopyCategory.homologyFunctor (QCoh (V i).toScheme) (.up ℤ) n).map_isZero hFK)
  have hFh : IsZero (F.obj (K.as.homology n)) :=
    ((K.as.sc n).mapHomologyIso F).isZero_iff.mp hh
  exact (quasicoherentInclusion (V i).toScheme).map_isZero hFh

/-- Actual K-injectivity discharges the resolved-object hypothesis of
the finite affine coresolution. -/
theorem kInjective_affineCover_rightOrthogonal (K : CochainComplex (QCoh X) ℤ)
    [K.IsKInjective] :
    (affineCoverContractible V).rightOrthogonal
      ((HomotopyCategory.quotient (QCoh X) (.up ℤ)).obj K) := by
  intro Z f hZ
  exact CochainComplex.IsKInjective.rightOrthogonal K f
    (affineCoverContractible_le_acyclic V hV Z hZ)

variable {D : Type w} [Category.{z} D] [Abelian D] [HasDerivedCategory D]
  (H : QCoh X ⥤ D) [H.Additive]
  [∀ i, PreservesFiniteLimits (quasicoherentOpenLocalization (V i).ι ⋙ H)]
  [∀ i, PreservesFiniteColimits (quasicoherentOpenLocalization (V i).ι ⋙ H)]
  (l : List I) (hl : ∀ i, i ∈ l)

include hl

/-- The actual affine right-derived unit is invertible on every actual
K-injective complex. -/
theorem affineRightDerivedUnit_isIso_of_isKInjective
    (K : CochainComplex (QCoh X) ℤ) [K.IsKInjective] :
    IsIso ((affineRightDerivedUnit V H l).app K) :=
  affineRightDerivedUnit_isIso V l hl H K
    (kInjective_affineCover_rightOrthogonal V hV K)

variable [EnoughInjectives (QCoh X)]

/-- On a single sheaf, the actual unbounded affine right-derived object
is computed by the actual bounded-below injective resolution. -/
def affineRightDerivedSingleModelIso (M : QCoh X) :
    (affineConeDerivedStage V H l).obj
        ((DerivedCategory.singleFunctor (QCoh X) 0).obj M) ≅
      DerivedCategory.Q.obj
        ((H.mapHomologicalComplex (.up ℤ)).obj (singleInjectiveCochain M)) := by
  letI := affineRightDerivedUnit_isIso_of_isKInjective V hV H l hl
    (singleInjectiveCochain M)
  exact (affineConeDerivedStage V H l).mapIso (singleInjectiveDerivedIso M) ≪≫
    (asIso ((affineRightDerivedUnit V H l).app (singleInjectiveCochain M))).symm

/-- The actual unbounded derived homology is therefore the homology of
literal termwise application to that actual injective resolution. -/
def affineRightDerivedSingleHomologyIso (M : QCoh X) (n : ℤ) :
    (DerivedCategory.homologyFunctor D n).obj
        ((affineConeDerivedStage V H l).obj
          ((DerivedCategory.singleFunctor (QCoh X) 0).obj M)) ≅
      ((H.mapHomologicalComplex (.up ℤ)).obj (singleInjectiveCochain M)).homology n :=
  (DerivedCategory.homologyFunctor D n).mapIso
      (affineRightDerivedSingleModelIso V hV H l hl M) ≪≫
    (DerivedCategory.homologyFunctorFactors D n).app _

end ToricPower
