module

public import ToricPower.ProjectiveSectionsFromResolution

/-! # Actual single-coefficient comparison for projective sections -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CochainComplex

namespace ToricPower

universe v
variable (R : Type v) [CommRing R]
  {A C : Type*} [Category.{v} A] [Category.{v} C] [Abelian A] [Abelian C] [Linear R C]
  (S : A ⥤ C) [S.Additive] {Z : C} (P : ProjectiveResolution Z) (M : A)

/-- The full projective coefficient complex on a single object is
identified with the projective section complex of its actual image.
Both intervening single-complex comparisons are genuine canonical isomorphisms. -/
def projectiveCoefficientSingleIso :
    (projectiveCoefficientComplexFunctor R S P).obj ((singleFunctor A 0).obj M) ≅
      (projectiveCoefficientComplexFunctor R (𝟭 C) P).obj
        ((singleFunctor C 0).obj (S.obj M)) :=
  (linearHomComplexFunctor R (projectiveCochain P)).mapIso
    ((HomologicalComplex.singleMapHomologicalComplex S (.up ℤ) 0).app M ≪≫
      ((Functor.mapHomologicalComplexIdIso C (.up ℤ)).app
        ((singleFunctor C 0).obj (S.obj M))).symm)

theorem projectiveCoefficientSingle_acyclic
    (vanishes : ((projectiveCoefficientComplexFunctor R (𝟭 C) P).obj
      ((singleFunctor C 0).obj (S.obj M))).Acyclic) :
    ((projectiveCoefficientComplexFunctor R S P).obj ((singleFunctor A 0).obj M)).Acyclic := by
  intro q
  exact (exactAt_iff_of_quasiIsoAt (projectiveCoefficientSingleIso R S P M).hom q).mpr
    (vanishes q)

end ToricPower

end
