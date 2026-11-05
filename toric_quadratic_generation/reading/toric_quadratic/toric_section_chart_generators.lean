module

public import PaperVerification.ToricSectionProjectiveEmbedding
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.FiniteType

@[expose] public section

/-! # Actual affine coordinate generators as ratios of global sections -/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped Classical BaseSections

attribute [local instance] MvPolynomial.gradedAlgebra

namespace BaseSections

variable (k : Type u) [CommRing k] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))]

theorem scalarMap_finiteType [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    (U : X.Opens) (hU : IsAffineOpen U) :
    (scalarMap k X U).FiniteType := by
  let f := X ↘ Spec (CommRingCat.of k)
  have htop := f.finiteType_appLE (isAffineOpen_top _) hU
    (show U≤f ⁻¹ᵁ ⊤ by simp)
  have hc := RingHom.FiniteType.of_surjective
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    (ConcreteCategory.bijective_of_isIso _).2
  convert htop.comp hc using 1
  ext a
  simp only [scalarMap,RingHom.comp_apply,Scheme.Hom.appLE,
    CommRingCat.hom_comp,ConcreteCategory.comp_apply]
  rfl

theorem exists_finite_polynomial_generators
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ (ι : Type u) (_ : Fintype ι) (g : ι→Γ(X,U)),
      Function.Surjective (MvPolynomial.eval₂Hom (scalarMap k X U) g) := by
  letI : Algebra.FiniteType k Γ(X,U) := scalarMap_finiteType k U hU
  obtain ⟨g,F,hF⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial.mp
    (show Algebra.FiniteType k Γ(X,U) from inferInstance))
  refine ⟨g,inferInstance,(fun j=>F (MvPolynomial.X j)),?_⟩
  have he : MvPolynomial.eval₂Hom (scalarMap k X U)
      (fun j=>F (MvPolynomial.X j))=F.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      rw [MvPolynomial.eval₂Hom_C]
      change algebraMap k Γ(X,U) a = F (algebraMap k (MvPolynomial g k) a)
      exact (F.commutes a).symm
    · intro j
      simp
  rw [he]
  change Function.Surjective F
  exact hF

end BaseSections

namespace RationalCartierCocycle

variable (k : Type u) [CommRing k] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of k))]
    (C : RationalCartierCocycle X) {ι : Type u} (s : ι→Γ(C.sheaf,⊤))

def sectionProjectiveChartConstant (s : ι→Γ(C.sheaf,⊤)) (i : ι) :
    k→+*HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule ι k)
      (MvPolynomial.X i) :=
  (HomogeneousLocalization.fromZeroRingHom (MvPolynomial.homogeneousSubmodule ι k)
    (Submonoid.powers (MvPolynomial.X i))).comp (polynomialGradeZeroScalarMap k ι)

@[simp] theorem sectionProjectiveChartCoordinates_constant (i : ι) (a : k) :
    C.sectionProjectiveChartCoordinates k s i
        (C.sectionProjectiveChartConstant k s i a)=
      BaseSections.scalarMap k X (C.nonvanishingOpen (s i)) a := by
  change Localization.awayLift (C.sectionProjectiveChartRingMap k s i)
    (MvPolynomial.X i)
      (by rw [C.sectionProjectiveChartRingMap_self k s i]; exact isUnit_one)
      (algebraMap (MvPolynomial ι k) (Localization.Away (MvPolynomial.X i))
        (MvPolynomial.C a))=_
  simp only [Localization.awayLift,IsLocalization.Away.lift_eq,
    sectionProjectiveChartRingMap,MvPolynomial.eval₂Hom_C]

@[simp] theorem sectionProjectiveChartCoordinates_variable (i j : ι) :
    C.sectionProjectiveChartCoordinates k s i
      (HomogeneousLocalization.Away.isLocalizationElem
        (MvPolynomial.isHomogeneous_X k i) (MvPolynomial.isHomogeneous_X k j))=
      C.ratioSection (s j) (s i) := by
  exact C.sectionProjectiveChartRingMap_away_variable k s i j

/-- Every polynomial in actual generating ratios lifts to an actual
element of the homogeneous affine chart ring. -/
theorem sectionProjectiveChartCoordinates_surjective_of_polynomial_generators
    (i : ι) {κ : Type u} (j : κ→ι)
    (g : κ→Γ(X,C.nonvanishingOpen (s i)))
    (hpoly : Function.Surjective (MvPolynomial.eval₂Hom
      (BaseSections.scalarMap k X (C.nonvanishingOpen (s i))) g))
    (hgen : ∀ t,C.ratioSection (s (j t)) (s i)=g t) :
    Function.Surjective (C.sectionProjectiveChartCoordinates k s i) := by
  let F := MvPolynomial.eval₂Hom (C.sectionProjectiveChartConstant k s i)
    (fun t=>HomogeneousLocalization.Away.isLocalizationElem
      (MvPolynomial.isHomogeneous_X k i) (MvPolynomial.isHomogeneous_X k (j t)))
  have hcomp : (C.sectionProjectiveChartCoordinates k s i).comp F=
      MvPolynomial.eval₂Hom
        (BaseSections.scalarMap k X (C.nonvanishingOpen (s i))) g := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply,F,MvPolynomial.eval₂Hom_C,
        C.sectionProjectiveChartCoordinates_constant k s i a]
    · intro t
      simp only [RingHom.comp_apply,F,MvPolynomial.eval₂Hom_X',
        C.sectionProjectiveChartCoordinates_variable k s i (j t),hgen t]
  have hs : Function.Surjective ((C.sectionProjectiveChartCoordinates k s i).comp F) := by
    rw [hcomp]
    exact hpoly
  exact Function.Surjective.of_comp hs

end RationalCartierCocycle
end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.sectionProjectiveChartCoordinates_surjective_of_polynomial_generators
