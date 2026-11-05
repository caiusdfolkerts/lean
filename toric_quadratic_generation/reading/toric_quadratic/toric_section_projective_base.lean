module

public import PaperVerification.ToricSectionProjectiveMap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

@[expose] public section

/-! # The section morphism preserves the actual base structure map -/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [CommRing k] (ι : Type u)

def polynomialGradeZeroScalarMap :
    k→+*MvPolynomial.homogeneousSubmodule ι k 0 where
  toFun a := ⟨MvPolynomial.C a,MvPolynomial.isHomogeneous_C ι a⟩
  map_one' := Subtype.ext (MvPolynomial.C.map_one)
  map_mul' a b := Subtype.ext (MvPolynomial.C.map_mul a b)
  map_zero' := Subtype.ext (MvPolynomial.C.map_zero)
  map_add' a b := Subtype.ext (MvPolynomial.C.map_add a b)

/-- The literal structural morphism of polynomial projective space. -/
def polynomialProjectiveToSpec :
    Proj (MvPolynomial.homogeneousSubmodule ι k)⟶Spec (CommRingCat.of k) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule ι k) ≫
    Spec.map (CommRingCat.ofHom (polynomialGradeZeroScalarMap k ι))

instance polynomialProjectiveToSpec_isSeparated :
    IsSeparated (polynomialProjectiveToSpec k ι) := by
  unfold polynomialProjectiveToSpec
  infer_instance

namespace BaseSections

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]

theorem toSpec_scalarMap (U : X.Opens) :
    U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (scalarMap k X U)) =
      U.ι ≫ (X ↘ Spec (CommRingCat.of k)) := by
  unfold scalarMap
  rw [CommRingCat.ofHom_comp,CommRingCat.ofHom_comp,Spec.map_comp,
    Spec.map_comp,CommRingCat.ofHom_hom,CommRingCat.ofHom_hom,
    CommRingCat.ofHom_hom,← Category.assoc,
    Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top,Category.assoc,
    ← Scheme.toSpecΓ_naturality_assoc,toSpecΓ_SpecMap_ΓSpecIso_inv,
    Category.comp_id]

end BaseSections

namespace RationalCartierCocycle

variable {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of k))]
    (C : RationalCartierCocycle X) {ι : Type u} (s : ι→Γ(C.sheaf,⊤))

theorem sectionProjectiveChart_toSpec (i : ι) :
    C.sectionProjectiveChart k s i ≫ polynomialProjectiveToSpec k ι =
      (C.nonvanishingOpen (s i)).ι ≫ (X ↘ Spec (CommRingCat.of k)) := by
  let F := C.sectionProjectiveChartRingMap k s i
  have hunit : IsUnit (F (MvPolynomial.X i)) := by
    change IsUnit (C.sectionProjectiveChartRingMap k s i (MvPolynomial.X i))
    rw [C.sectionProjectiveChartRingMap_self k s i]
    exact isUnit_one
  let E := unitHomogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι k)
    F (MvPolynomial.X i) hunit
  have hscalar : E.comp
      ((HomogeneousLocalization.fromZeroRingHom
        (MvPolynomial.homogeneousSubmodule ι k) (Submonoid.powers (MvPolynomial.X i))).comp
          (polynomialGradeZeroScalarMap k ι))=
        BaseSections.scalarMap k X (C.nonvanishingOpen (s i)) := by
    ext a
    change Localization.awayLift F (MvPolynomial.X i) hunit
      (algebraMap (MvPolynomial ι k) (Localization.Away (MvPolynomial.X i))
        (MvPolynomial.C a))=_
    simp only [Localization.awayLift,IsLocalization.Away.lift_eq,
      F,sectionProjectiveChartRingMap,MvPolynomial.eval₂Hom_C]
  unfold sectionProjectiveChart polynomialProjectiveToSpec
  rw [Category.assoc,Category.assoc,Proj.awayι_toSpecZero_assoc,
    ← Spec.map_comp,← Spec.map_comp]
  change (C.nonvanishingOpen (s i)).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (E.comp
      ((HomogeneousLocalization.fromZeroRingHom
        (MvPolynomial.homogeneousSubmodule ι k) (Submonoid.powers (MvPolynomial.X i))).comp
          (polynomialGradeZeroScalarMap k ι))))=_
  rw [hscalar,BaseSections.toSpec_scalarMap]

theorem sectionProjectiveMap_toSpec
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) :
    C.sectionProjectiveMap k s hcover ≫ polynomialProjectiveToSpec k ι =
      (X ↘ Spec (CommRingCat.of k)) := by
  apply (X.openCoverOfIsOpenCover (fun i=>C.nonvanishingOpen (s i)) hcover).hom_ext
  intro i
  change (C.nonvanishingOpen (s i)).ι ≫
      (C.sectionProjectiveMap k s hcover ≫ polynomialProjectiveToSpec k ι) =
    (C.nonvanishingOpen (s i)).ι ≫ (X ↘ Spec (CommRingCat.of k))
  rw [← Category.assoc,C.sectionProjectiveMap_chart k s hcover i,
    C.sectionProjectiveChart_toSpec k s i]

/-- Properness follows from the genuine base-compatible map to the
separated projective target. -/
theorem sectionProjectiveMap_isProper
    [IsProper (X ↘ Spec (CommRingCat.of k))]
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) :
    IsProper (C.sectionProjectiveMap k s hcover) := by
  letI : IsProper
      (C.sectionProjectiveMap k s hcover ≫ polynomialProjectiveToSpec k ι) := by
    rw [C.sectionProjectiveMap_toSpec k s hcover]
    infer_instance
  exact IsProper.of_comp _ (polynomialProjectiveToSpec k ι)

end RationalCartierCocycle
end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.sectionProjectiveMap_isProper
