module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-!
# Epimorphisms efface positive extension classes

No existence of projectives is needed. A right fraction for a morphism
from a degree-zero complex to a strictly negative complex has a numerator
whose degree-zero component vanishes. The degree-zero term of the
denominator therefore supplies the required epimorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open HomologicalComplex

namespace ToricPower

universe u v w w'

variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem exists_epi_killing_to_negative [HasDerivedCategory.{w'} C]
    {X : C} {L : CochainComplex C ℤ}
    (φ : DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj X) ⟶
      DerivedCategory.Q.obj L)
    (n : ℤ) (negative : n < 0) [L.IsStrictlyLE n] :
    ∃ (P : C) (p : P ⟶ X), Epi p ∧
      (DerivedCategory.singleFunctor C 0).map p ≫ φ = 0 := by
  obtain ⟨K, _, π, hπ, g, rfl⟩ :=
    DerivedCategory.right_fac_of_isStrictlyLE φ 0
  haveI : QuasiIso π := by
    rwa [DerivedCategory.isIso_Q_map_iff_quasiIso] at hπ
  let e := K.iCyclesIso 0 1 (by simp)
    ((K.isZero_of_isStrictlyLE 0 1 (by simp)).eq_of_tgt _ _)
  let p := e.inv ≫ K.homologyπ 0 ≫ homologyMap π 0 ≫
    (singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).hom
  haveI : Epi p := by dsimp [p]; infer_instance
  have hp : π.f 0 = p ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 X).inv := by
    rw [← cancel_epi e.hom]
    dsimp [p, e]
    rw [Category.assoc, Category.assoc, Category.assoc, iCyclesIso_hom_inv_id_assoc,
      homologyπ_naturality_assoc]
    dsimp [CochainComplex.singleFunctor, CochainComplex.singleFunctors]
    rw [homologyπ_singleObjHomologySelfIso_hom_assoc,
      ← singleObjCyclesSelfIso_inv_iCycles, Iso.hom_inv_id_assoc, ← cyclesMap_i]
  let s : (CochainComplex.singleFunctor C 0).obj (K.X 0) ⟶ K :=
    mkHomFromSingle (𝟙 _) (by
      rintro _ rfl
      exact (K.isZero_of_isStrictlyLE 0 1 (by simp)).eq_of_tgt _ _)
  have hsπ : s ≫ π = (CochainComplex.singleFunctor C 0).map p := by
    apply from_single_hom_ext
    dsimp [s]
    rw [mkHomFromSingle_f, Category.comp_id, hp]
    exact (single_map_f_self (ComplexShape.up ℤ) 0 p).symm
  have hsg : s ≫ g = 0 := by
    apply from_single_hom_ext
    exact (L.isZero_of_isStrictlyLE n 0 negative).eq_of_tgt _ _
  refine ⟨K.X 0, p, inferInstance, ?_⟩
  change DerivedCategory.Q.map ((CochainComplex.singleFunctor C 0).map p) ≫
    (inv (DerivedCategory.Q.map π) ≫ DerivedCategory.Q.map g) = 0
  rw [← hsπ, CategoryTheory.Functor.map_comp, Category.assoc,
    IsIso.hom_inv_id_assoc, ← CategoryTheory.Functor.map_comp, hsg,
    CategoryTheory.Functor.map_zero]

/-- Every individual positive Ext class is killed by an epimorphism onto
its source, in an arbitrary abelian category. -/
theorem exists_epi_effacing_ext [HasExt.{w} C] {X Y : C} {n : ℕ}
    (x : Ext.{w} X Y (n + 1)) :
    ∃ (P : C) (p : P ⟶ X), Epi p ∧
      (Ext.mk₀ p).comp x (zero_add (n + 1)) = 0 := by
  letI := HasDerivedCategory.standard C
  let e := ((DerivedCategory.singleFunctors C).shiftIso (n + 1) (-(n + 1)) 0
    (by lia)).app Y
  obtain ⟨P, p, hp, h⟩ := exists_epi_killing_to_negative (x.hom ≫ e.hom)
    (-(n + 1)) (by lia)
  refine ⟨P, p, hp, ?_⟩
  apply Ext.homEquiv.injective
  rw [← cancel_mono e.hom]
  simpa only [Ext.comp_hom, Ext.mk₀_hom, Ext.zero_hom, ShiftedHom.mk₀_comp,
    Category.assoc, zero_comp] using h

end ToricPower

end
