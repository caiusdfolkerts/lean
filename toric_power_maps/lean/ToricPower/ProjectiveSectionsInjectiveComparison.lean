module

public import ToricPower.ProjectiveCechDerivedComparison
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-! # Genuine projective sections compared through injective representatives -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex

namespace ToricPower

universe u v w
variable (R : Type v) [CommRing R]
  {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]

theorem linearHomComplexPrecomp_quasiIso_of_isKInjective
    {K L : CochainComplex C ℤ} (f : K ⟶ L) [QuasiIso f]
    (I : CochainComplex C ℤ) [I.IsKInjective] :
    QuasiIso (linearHomComplexPrecomp R f I) := by
  apply linearHomComplexPrecomp_quasiIso_of_homotopy_bijective
  intro n
  have localTarget : (HomotopyCategory.subcategoryAcyclic C).trW.isLocal
      ((HomotopyCategory.quotient C (.up ℤ)).obj (I⟦n⟧)) := by
    rw [ObjectProperty.isLocal_trW]
    exact CochainComplex.IsKInjective.rightOrthogonal _
  apply localTarget ((HomotopyCategory.quotient C (.up ℤ)).map f)
  rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).mpr (inferInstance : QuasiIso f)

variable {A : Type w} [Category.{v} A] [Abelian A]
  (S : A ⥤ C) [S.Additive] {Z : C} (P : ProjectiveResolution Z)

theorem projectiveCoefficientComplexUnit_quasiIso_of_isKInjective
    (I : CochainComplex A ℤ)
    [CochainComplex.IsKInjective ((S.mapHomologicalComplex (.up ℤ)).obj I)] :
    QuasiIso ((projectiveCoefficientComplexUnit R S P).app I) := by
  haveI : QuasiIso (projectiveCochainAugmentation P) := by
    unfold projectiveCochainAugmentation
    infer_instance
  haveI := linearHomComplexPrecomp_quasiIso_of_isKInjective R
    (projectiveCochainAugmentation P) ((S.mapHomologicalComplex (.up ℤ)).obj I)
  dsimp only [projectiveCoefficientComplexUnit]
  infer_instance

variable [HasDerivedCategory C] [PreservesFiniteLimits S] [PreservesFiniteColimits S]

/-- A comparison through an actual injective representative proves the
canonical projective-section map is a quasi-isomorphism. -/
theorem projectiveSectionMap_quasiIso_of_injective_comparison
    {K I : CochainComplex A ℤ} (f : K ⟶ I) [QuasiIso f]
    [CochainComplex.IsKInjective ((S.mapHomologicalComplex (.up ℤ)).obj I)]
    {V : CochainComplex (ModuleCat.{v} R) ℤ}
    (a : V ⟶ ((ordinaryProjectiveCoefficients R S (Z := Z)).mapHomologicalComplex (.up ℤ)).obj K)
    [QuasiIso (a ≫ ((ordinaryProjectiveCoefficients R S (Z := Z)).mapHomologicalComplex
      (.up ℤ)).map f)] :
    QuasiIso (a ≫ (projectiveCoefficientComplexUnit R S P).app K) := by
  haveI := projectiveCoefficientComplexUnit_quasiIso_of_isKInjective R S P I
  haveI := linearHomComplexMap_quasiIso R (projectiveCochain P)
    ((S.mapHomologicalComplex (.up ℤ)).map f)
  haveI : QuasiIso ((projectiveCoefficientComplexFunctor R S P).map f) := by
    change QuasiIso (linearHomComplexMap R (projectiveCochain P)
      ((S.mapHomologicalComplex (.up ℤ)).map f))
    infer_instance
  haveI : QuasiIso ((a ≫ (projectiveCoefficientComplexUnit R S P).app K) ≫
      (projectiveCoefficientComplexFunctor R S P).map f) := by
    rw [Category.assoc,← (projectiveCoefficientComplexUnit R S P).naturality f,
      ← Category.assoc]
    infer_instance
  exact quasiIso_of_comp_right _ ((projectiveCoefficientComplexFunctor R S P).map f)

end ToricPower

end
