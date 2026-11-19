module

public import ToricPower.AffineCoresolutionClosure
public import ToricPower.ShiftedConeOrthogonality
public import ToricPower.ProjectiveCochainBounds
public import ToricPower.ProjectiveCechDerivedComparison

/-!
# Finite projective comparisons on the unbounded affine coresolution

Exact ordinary Hom rows on actual affine-open direct images imply the
actual augmentation comparison on every finite affine coresolution,
including coresolutions of unbounded complexes. The proof uses the
bounded source, then the genuine finite cone filtration.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CochainComplex TopologicalSpace

namespace ToricPower

universe u v w r

variable {X : Scheme.{u}} {I : Type v}
  (V : I → X.Opens) [∀ i, IsAffineHom (V i).ι]
  {C : Type w} [Category.{u} C] [Abelian C]
  (S : QCoh X ⥤ C) [S.Additive]

/-- Local coefficient-row exactness gives the actual Hom comparison on
the entire finite coresolution, without bounds on its input. -/
theorem affineCoresolution_linearHomPrecomp_quasiIso
    (R : Type r) [CommRing R] [Linear R C]
    {K L : CochainComplex C ℤ} (ε : K ⟶ L) (d : ℤ)
    [(mappingCone ε).IsStrictlyGE d]
    (localRows : ∀ (i : I) (M : QCoh (V i).toScheme),
      RightHomExact (mappingCone ε)
        (S.obj ((quasicoherentAffinePushforward (V i).ι).obj M)))
    (l : List I) (E : CochainComplex (QCoh X) ℤ) :
    QuasiIso (linearHomComplexPrecomp R ε
      ((S.mapHomologicalComplex (.up ℤ)).obj ((affineConeCoresolution V l).obj E))) := by
  let P := shiftedHomotopyRightOrthogonal (mappingCone ε)
  let SP := P.inverseImage (S.mapHomotopyCategory (.up ℤ))
  have hlocal (i : I) (J : CochainComplex (QCoh (V i).toScheme) ℤ) :
      SP ((HomotopyCategory.quotient (QCoh X) (.up ℤ)).obj
        (((quasicoherentAffinePushforward (V i).ι).mapHomologicalComplex (.up ℤ)).obj J)) := by
    apply (P.prop_iff_of_iso ((S.mapHomotopyCategoryFactors (.up ℤ)).app
      (((quasicoherentAffinePushforward (V i).ι).mapHomologicalComplex (.up ℤ)).obj J))).mpr
    apply shiftedHomotopyRightOrthogonal_of_boundedSource (mappingCone ε) _ d
    exact fun q => localRows i (J.X q)
  have hE := affineConeCoresolution_mem V SP hlocal l E
  have hS : P ((HomotopyCategory.quotient C (.up ℤ)).obj
      ((S.mapHomologicalComplex (.up ℤ)).obj ((affineConeCoresolution V l).obj E))) :=
    (P.prop_iff_of_iso ((S.mapHomotopyCategoryFactors (.up ℤ)).app
      ((affineConeCoresolution V l).obj E))).mp hE
  exact linearHomComplexPrecomp_quasiIso_of_shiftedOrthogonal R ε _ hS

/-- The same statement for the original projective augmentation unit.
Both the source bound and the degree-zero augmentation condition are
discharged by the genuine finite projective resolution. -/
theorem affineCoresolution_projectiveCoefficientUnit_quasiIso
    (R : Type u) [CommRing R] [Linear R C]
    {Z : C} (P : ProjectiveResolution Z) (N : ℕ)
    (bound : ∀ m : ℕ, N < m → IsZero (P.complex.X m))
    (localRows : ∀ (i : I) (M : QCoh (V i).toScheme) (n : ℕ),
      (projectiveCoefficientComplex R P
        (S.obj ((quasicoherentAffinePushforward (V i).ι).obj M))).ExactAt (n+1))
    (l : List I) (E : CochainComplex (QCoh X) ℤ) :
    QuasiIso ((projectiveCoefficientComplexUnit R S P).app
      ((affineConeCoresolution V l).obj E)) := by
  letI := projectiveCochainAugmentation_cone_isStrictlyGE P N bound
  haveI : QuasiIso (linearHomComplexPrecomp R (projectiveCochainAugmentation P)
      ((S.mapHomologicalComplex (.up ℤ)).obj ((affineConeCoresolution V l).obj E))) := by
    apply affineCoresolution_linearHomPrecomp_quasiIso V S R
      (projectiveCochainAugmentation P) (-(N : ℤ)-1) _ l E
    intro i M
    apply rightHomExact_cone_of_single_precomp
    exact augmentation_single_precomp_bijective (projectiveCochain P) Z _
      (projectiveCochainAugmentation P)
      (projectiveCochain_augmentationHomExact R P _ (localRows i M))
  dsimp only [projectiveCoefficientComplexUnit]
  infer_instance

end ToricPower

end
