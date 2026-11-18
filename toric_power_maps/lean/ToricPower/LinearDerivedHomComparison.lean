module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-!
# Scalar-linear comparison with actual derived morphisms

Mathlib's Hom-cochain quotient comparison is upgraded to its literal
scalar-linear equivalence. Localization is used only when the source
is K-projective or the target is K-injective. The other complex may be
unbounded, and no dimension assumption is imposed.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CochainComplex
open CochainComplex.HomComplex

namespace ToricPower

universe u v w r
variable (R : Type r) [CommRing R]
variable {A : Type u} [Category.{v} A] [Abelian A] [Linear R A]

def homClassHomotopyLinearEquiv (K L : CochainComplex A ℤ) (n : ℤ) :
    CohomologyClass K L n ≃ₗ[R]
      ((HomotopyCategory.quotient A (.up ℤ)).obj K ⟶
        (HomotopyCategory.quotient A (.up ℤ)).obj (L⟦n⟧)) where
  toAddEquiv := CohomologyClass.homAddEquiv
  map_smul' a z := by
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective z
    change CohomologyClass.toHom (a • CohomologyClass.mk z) =
      a • CohomologyClass.toHom (CohomologyClass.mk z)
    rw [← CohomologyClass.mk_smul, CohomologyClass.toHom_mk,
      CohomologyClass.toHom_mk, Cocycle.equivHomShift_symm_smul,
      CategoryTheory.Functor.map_smul]

variable [HasDerivedCategory.{w} A]

def homotopyDerivedLinearEquivOfKInjective (K L : CochainComplex A ℤ) [L.IsKInjective] :
    ((HomotopyCategory.quotient A (.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient A (.up ℤ)).obj L) ≃ₗ[R]
      (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :=
  (LinearEquiv.ofBijective (DerivedCategory.Qh.mapLinearMap R)
    (CochainComplex.IsKInjective.Qh_map_bijective
      ((HomotopyCategory.quotient A (.up ℤ)).obj K) L)).trans
    (Linear.homCongr R ((DerivedCategory.quotientCompQhIso A).app K)
      ((DerivedCategory.quotientCompQhIso A).app L))

def homotopyDerivedLinearEquivOfKProjective (K L : CochainComplex A ℤ) [K.IsKProjective] :
    ((HomotopyCategory.quotient A (.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient A (.up ℤ)).obj L) ≃ₗ[R]
      (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :=
  (LinearEquiv.ofBijective (DerivedCategory.Qh.mapLinearMap R)
    (CochainComplex.IsKProjective.Qh_map_bijective K
      ((HomotopyCategory.quotient A (.up ℤ)).obj L))).trans
    (Linear.homCongr R ((DerivedCategory.quotientCompQhIso A).app K)
      ((DerivedCategory.quotientCompQhIso A).app L))

def homClassDerivedLinearEquivOfKInjective (K L : CochainComplex A ℤ) [L.IsKInjective]
    (n : ℤ) : CohomologyClass K L n ≃ₗ[R]
      (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (L⟦n⟧)) :=
  (homClassHomotopyLinearEquiv R K L n).trans
    (homotopyDerivedLinearEquivOfKInjective R K (L⟦n⟧))

def homClassDerivedLinearEquivOfKProjective (K L : CochainComplex A ℤ) [K.IsKProjective]
    (n : ℤ) : CohomologyClass K L n ≃ₗ[R]
      (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (L⟦n⟧)) :=
  (homClassHomotopyLinearEquiv R K L n).trans
    (homotopyDerivedLinearEquivOfKProjective R K (L⟦n⟧))

theorem homClassDerivedLinearEquivOfKInjective_mk
    (K L : CochainComplex A ℤ) [L.IsKInjective] (n : ℤ) (z : Cocycle K L n) :
    homClassDerivedLinearEquivOfKInjective R K L n (CohomologyClass.mk z) =
      DerivedCategory.Q.map (Cocycle.equivHomShift.symm z) := by
  change ((DerivedCategory.quotientCompQhIso A).inv.app K ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient A (.up ℤ)).map
      (Cocycle.equivHomShift.symm z))) ≫
      (DerivedCategory.quotientCompQhIso A).hom.app (L⟦n⟧) = _
  rw [Category.assoc, DerivedCategory.quotientCompQhIso_hom_naturality,
    Iso.inv_hom_id_app_assoc]

theorem homClassDerivedLinearEquivOfKProjective_mk
    (K L : CochainComplex A ℤ) [K.IsKProjective] (n : ℤ) (z : Cocycle K L n) :
    homClassDerivedLinearEquivOfKProjective R K L n (CohomologyClass.mk z) =
      DerivedCategory.Q.map (Cocycle.equivHomShift.symm z) := by
  change ((DerivedCategory.quotientCompQhIso A).inv.app K ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient A (.up ℤ)).map
      (Cocycle.equivHomShift.symm z))) ≫
      (DerivedCategory.quotientCompQhIso A).hom.app (L⟦n⟧) = _
  rw [Category.assoc, DerivedCategory.quotientCompQhIso_hom_naturality,
    Iso.inv_hom_id_app_assoc]

end ToricPower

end
