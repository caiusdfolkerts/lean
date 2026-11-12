module

public import ToricPower.SerrePairingDerivedComplex
public import ToricPower.LinearHomComplexPrecomp

/-!
# Naturality of the linear derived-Hom comparison

The comparisons used in the Serre pairing intertwine literal source
and target composition. The zero-degree versions remove the canonical
zero shift explicitly, so their values are ordinary derived morphisms.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CochainComplex
open CochainComplex.HomComplex

namespace ToricPower

universe u v w r
variable (k : Type r) [Field k]
variable {A : Type u} [Category.{v} A] [Abelian A] [Linear k A]
variable [HasDerivedCategory.{w} A]

theorem homClassDerivedLinearEquivOfKInjective_precomp
    {E F J : CochainComplex A ℤ} [J.IsKInjective] (h : E ⟶ F)
    (n : ℤ) (z : CohomologyClass F J n) :
    homClassDerivedLinearEquivOfKInjective k E J n (homClassPrecomp k h J n z) =
      DerivedCategory.Q.map h ≫ homClassDerivedLinearEquivOfKInjective k F J n z := by
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective z
  simp only [homClassPrecomp_mk, homClassDerivedLinearEquivOfKInjective_mk,
    Cocycle.equivHomShift_symm_precomp, CategoryTheory.Functor.map_comp]

theorem homClassDerivedLinearEquivOfKInjective_postcomp
    {E J K : CochainComplex A ℤ} [J.IsKInjective] [K.IsKInjective] (h : J ⟶ K)
    (n : ℤ) (z : CohomologyClass E J n) :
    homClassDerivedLinearEquivOfKInjective k E K n (homClassPostcomp k E h n z) =
      homClassDerivedLinearEquivOfKInjective k E J n z ≫ DerivedCategory.Q.map (h⟦n⟧') := by
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective z
  simp only [homClassPostcomp_mk, homClassDerivedLinearEquivOfKInjective_mk,
    Cocycle.equivHomShift_symm_postcomp, CategoryTheory.Functor.map_comp]

theorem homClassDerivedLinearEquivOfKProjective_precomp
    {P Q E : CochainComplex A ℤ} [P.IsKProjective] [Q.IsKProjective] (h : P ⟶ Q)
    (n : ℤ) (z : CohomologyClass Q E n) :
    homClassDerivedLinearEquivOfKProjective k P E n (homClassPrecomp k h E n z) =
      DerivedCategory.Q.map h ≫ homClassDerivedLinearEquivOfKProjective k Q E n z := by
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective z
  simp only [homClassPrecomp_mk, homClassDerivedLinearEquivOfKProjective_mk,
    Cocycle.equivHomShift_symm_precomp, CategoryTheory.Functor.map_comp]

theorem homClassDerivedLinearEquivOfKProjective_postcomp
    {P E F : CochainComplex A ℤ} [P.IsKProjective] (h : E ⟶ F)
    (n : ℤ) (z : CohomologyClass P E n) :
    homClassDerivedLinearEquivOfKProjective k P F n (homClassPostcomp k P h n z) =
      homClassDerivedLinearEquivOfKProjective k P E n z ≫ DerivedCategory.Q.map (h⟦n⟧') := by
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective z
  simp only [homClassPostcomp_mk, homClassDerivedLinearEquivOfKProjective_mk,
    Cocycle.equivHomShift_symm_postcomp, CategoryTheory.Functor.map_comp]

omit [HasDerivedCategory.{w} A] in
theorem homologyLinearEquiv_precomp
    {E F : CochainComplex A ℤ} (h : E ⟶ F) (J : CochainComplex A ℤ)
    (n : ℤ) (x : (linearHomComplex k F J).homology n) :
    HomComplex.homologyLinearEquiv k E J n
        (HomologicalComplex.homologyMap (linearHomComplexPrecomp k h J) n x) =
      homClassPrecomp k h J n (HomComplex.homologyLinearEquiv k F J n x) :=
  congrArg (fun f : (linearHomComplex k F J).homology n ⟶
      ModuleCat.of k (CohomologyClass E J n) => f x)
    (linearHomComplexPrecompHomologyData k h J n).homologyMap_comm

omit [HasDerivedCategory.{w} A] in
theorem homologyLinearEquiv_postcomp
    (P : CochainComplex A ℤ) {E F : CochainComplex A ℤ} (h : E ⟶ F)
    (n : ℤ) (x : (linearHomComplex k P E).homology n) :
    HomComplex.homologyLinearEquiv k P F n
        (HomologicalComplex.homologyMap (linearHomComplexMap k P h) n x) =
      homClassPostcomp k P h n (HomComplex.homologyLinearEquiv k P E n x) :=
  congrArg (fun f : (linearHomComplex k P E).homology n ⟶
      ModuleCat.of k (CohomologyClass P F n) => f x)
    (linearHomComplexMapHomologyData k P h n).homologyMap_comm

end ToricPower

namespace ToricPower.SerrePairing

universe u v w
variable (k : Type u) [Field k]
variable {A : Type v} [Category.{u} A] [Abelian A] [Linear k A]
variable [HasDerivedCategory.{w} A]

theorem homClassDerivedZeroEquivOfKInjective_eq
    (E J : CochainComplex A ℤ) [J.IsKInjective] (z : CohomologyClass E J 0) :
    homClassDerivedZeroEquivOfKInjective k E J z =
      homClassDerivedLinearEquivOfKInjective k E J 0 z ≫
        DerivedCategory.Q.map ((shiftFunctorZero (CochainComplex A ℤ) ℤ).hom.app J) := by
  change (𝟙 _ ≫ _) ≫ _ = _
  rw [Category.id_comp]
  rfl

theorem homClassDerivedZeroEquivOfKProjective_eq
    (P E : CochainComplex A ℤ) [P.IsKProjective] (z : CohomologyClass P E 0) :
    homClassDerivedZeroEquivOfKProjective k P E z =
      homClassDerivedLinearEquivOfKProjective k P E 0 z ≫
        DerivedCategory.Q.map ((shiftFunctorZero (CochainComplex A ℤ) ℤ).hom.app E) := by
  change (𝟙 _ ≫ _) ≫ _ = _
  rw [Category.id_comp]
  rfl

theorem homClassDerivedZeroEquivOfKInjective_precomp
    {E F J : CochainComplex A ℤ} [J.IsKInjective] (h : E ⟶ F)
    (z : CohomologyClass F J 0) :
    homClassDerivedZeroEquivOfKInjective k E J (homClassPrecomp k h J 0 z) =
      DerivedCategory.Q.map h ≫ homClassDerivedZeroEquivOfKInjective k F J z := by
  rw [homClassDerivedZeroEquivOfKInjective_eq,
    homClassDerivedLinearEquivOfKInjective_precomp,
    homClassDerivedZeroEquivOfKInjective_eq, Category.assoc]

theorem homClassDerivedZeroEquivOfKProjective_postcomp
    {P E F : CochainComplex A ℤ} [P.IsKProjective] (h : E ⟶ F)
    (z : CohomologyClass P E 0) :
    homClassDerivedZeroEquivOfKProjective k P F (homClassPostcomp k P h 0 z) =
      homClassDerivedZeroEquivOfKProjective k P E z ≫ DerivedCategory.Q.map h := by
  rw [homClassDerivedZeroEquivOfKProjective_eq,
    homClassDerivedLinearEquivOfKProjective_postcomp,
    homClassDerivedZeroEquivOfKProjective_eq, Category.assoc, Category.assoc,
    ← CategoryTheory.Functor.map_comp, (shiftFunctorZero (CochainComplex A ℤ) ℤ).hom.naturality,
    CategoryTheory.Functor.map_comp]
  rfl

end ToricPower.SerrePairing

end
