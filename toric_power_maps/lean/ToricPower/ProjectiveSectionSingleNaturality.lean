module

public import ToricPower.ProjectiveSectionSingleComparison

/-! # The actual augmentation on single coefficients

The canonical comparison on a single object agrees with its scalar
projective-section map under the canonical single-complex isomorphisms.
This retains the particular augmentation, not merely its source and target.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory CochainComplex Opposite

namespace ToricPower

universe v
variable (R : Type v) [CommRing R]
  {A C : Type*} [Category.{v} A] [Category.{v} C] [Abelian A] [Abelian C] [Linear R C]
  {Z : C} (P : ProjectiveResolution Z)

/-- Naturality of the literal projective augmentation before any
source coefficient functor is introduced. -/
theorem projectiveHomUnit_target_naturality
    {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    (linearHomFromSingleIso R Z K).inv ≫
        linearHomComplexPrecomp R (projectiveCochainAugmentation P) K ≫
        linearHomComplexMap R (projectiveCochain P) f =
      (((linearCoyoneda R C).obj (op Z)).mapHomologicalComplex (.up ℤ)).map f ≫
        (linearHomFromSingleIso R Z L).inv ≫
        linearHomComplexPrecomp R (projectiveCochainAugmentation P) L := by
  rw [← linearHomComplexPrecomp_naturality, ← Category.assoc,
    ← linearHomFromSingleIso_inv_naturality, Category.assoc]

variable (S : A ⥤ C) [S.Additive] (M : A)

/-- Transport of the actual unit on a single object to the actual
scalar section map on its image. -/
theorem projectiveCoefficientSingle_unit :
    (HomologicalComplex.singleMapHomologicalComplex
      (ordinaryProjectiveCoefficients R S (Z := Z)) (.up ℤ) 0).inv.app M ≫
        (projectiveCoefficientComplexUnit R S P).app ((singleFunctor A 0).obj M) ≫
        (projectiveCoefficientSingleIso R S P M).hom =
      scalarProjectiveSectionMap R P
        (𝟙 (((linearCoyoneda R C).obj (op Z)).obj (S.obj M))) := by
  let H := (linearCoyoneda R C).obj (op Z)
  let e := (HomologicalComplex.singleMapHomologicalComplex S (.up ℤ) 0).app M
  let i := (Functor.mapHomologicalComplexIdIso C (.up ℤ)).app
    ((singleFunctor C 0).obj (S.obj M))
  dsimp only [scalarProjectiveSectionMap,singleCoefficientSection,
    projectiveCoefficientComplexUnit,projectiveCoefficientSingleIso,
    Functor.mapIso_hom,Iso.trans_hom,Iso.symm_hom,linearHomComplexFunctor]
  simp only [CategoryTheory.Functor.map_id,Category.id_comp,Category.assoc]
  rw [projectiveHomUnit_target_naturality]
  rw [HomologicalComplex.singleMapHomologicalComplex_comp_inv_app]
  simp only [Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc]
  have cancellation : e.inv ≫ (e.hom ≫ i.inv) = i.inv := by simp
  erw [cancellation]
  have identity : i.inv = 𝟙 ((singleFunctor C 0).obj (S.obj M)) := rfl
  erw [identity]
  simp only [CategoryTheory.Functor.map_id,Category.id_comp,Category.comp_id]
  rfl

variable (E : A ⥤ ModuleCat.{v} R) [E.Additive]
  (a : E ⟶ ordinaryProjectiveCoefficients R S (Z := Z))

/-- Naturality in the chosen coefficient section, including the
single-complex transport and the literal signed augmentation. -/
theorem projectiveSingleSection_comparison :
    (NatTrans.mapHomologicalComplex a (.up ℤ)).app ((singleFunctor A 0).obj M) ≫
        (projectiveCoefficientComplexUnit R S P).app ((singleFunctor A 0).obj M) ≫
        (projectiveCoefficientSingleIso R S P M).hom =
      (HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).hom.app M ≫
        scalarProjectiveSectionMap R P (a.app M) := by
  rw [HomologicalComplex.natTransMapHomologicalComplex_app_single_obj]
  simp only [Category.assoc]
  rw [projectiveCoefficientSingle_unit]
  simp only [scalarProjectiveSectionMap,singleCoefficientSection,
    CategoryTheory.Functor.map_id,Category.id_comp,Category.assoc]

end ToricPower

end
