module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Shift.Adjunction

/-!
# The triangulated shift functor, with its necessary sign

The functor shifting by `n` commutes with the shift by `a` through the
ordinary interchange isomorphism multiplied by `(-1)^(n*a)`. The sign is
necessary for preservation of distinguished triangles. We construct the
full coherent commutation data and compare the resulting triangle functor
with Mathlib's signed shift on triangles.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Category CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated

namespace ToricPower

variable (C : Type*) [Category* C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]

@[simp, reassoc]
theorem shiftCommutation_hom_pair (a n : ℤ) (X : C) :
    (shiftFunctorComm C a n).hom.app X ≫ (shiftFunctorComm C n a).hom.app X = 𝟙 _ := by
  rw [← shiftFunctorComm_symm C a n]
  exact Iso.hom_inv_id_app _ _

/-- The ordinary interchange maps satisfy the full additive coherence. -/
theorem shiftCommutation_add (n a b : ℤ) (X : C) :
    (shiftFunctorComm C (a+b) n).hom.app X =
      (shiftFunctor C n).map ((shiftFunctorAdd C a b).hom.app X) ≫
        (shiftFunctorComm C b n).hom.app (X⟦a⟧) ≫
          (shiftFunctor C b).map ((shiftFunctorComm C a n).hom.app X) ≫
            (shiftFunctorAdd C a b).inv.app (X⟦n⟧) := by
  apply (cancel_epi ((shiftFunctorComm C n (a+b)).hom.app X)).mp
  rw [shiftCommutation_hom_pair]
  rw [← Category.assoc,
    shiftFunctorComm_hom_app_comp_shift_shiftFunctorAdd_hom_app]
  simp only [Category.assoc, shiftCommutation_hom_pair_assoc]
  rw [← Functor.map_comp_assoc, shiftCommutation_hom_pair]
  dsimp only [CategoryTheory.Functor.comp_obj]
  rw [(shiftFunctor C b).map_id ((X⟦n⟧)⟦a⟧), Category.id_comp,
    Iso.hom_inv_id_app]

/-- The signed interchange is an actual natural isomorphism. -/
def signedShiftCommutation (n a : ℤ) :
    shiftFunctor C a ⋙ shiftFunctor C n ≅
      shiftFunctor C n ⋙ shiftFunctor C a :=
  NatIso.ofComponents
    (fun X => (n*a).negOnePow • (shiftFunctorComm C a n).app X) (by
      intro X Y f
      change (shiftFunctor C n).map ((shiftFunctor C a).map f) ≫
          ((n*a).negOnePow • (shiftFunctorComm C a n).hom.app Y) =
        ((n*a).negOnePow • (shiftFunctorComm C a n).hom.app X) ≫
          (shiftFunctor C a).map ((shiftFunctor C n).map f)
      rw [Linear.comp_units_smul, Linear.units_smul_comp]
      exact congrArg ((n*a).negOnePow • ·) ((shiftFunctorComm C a n).hom.naturality f))

/-- All integer shifts commute with this functor with the Koszul sign. -/
def signedShiftFunctorCommShift (n : ℤ) : (shiftFunctor C n).CommShift ℤ where
  commShiftIso a := signedShiftCommutation C n a
  commShiftIso_zero := by
    ext X
    change (n*0).negOnePow • (shiftFunctorComm C 0 n).hom.app X = _
    simp only [mul_zero, Int.negOnePow_zero, one_smul]
    rw [shiftFunctorComm_eq C 0 n n (zero_add n)]
    simp [Functor.CommShift.isoZero_hom_app,
      shiftFunctorAdd'_zero_add_inv_app, shiftFunctorAdd'_add_zero_hom_app]
  commShiftIso_add a b := by
    ext X
    change (n*(a+b)).negOnePow • (shiftFunctorComm C (a+b) n).hom.app X = _
    rw [Functor.CommShift.isoAdd_hom_app]
    change _ = (shiftFunctor C n).map ((shiftFunctorAdd C a b).hom.app X) ≫
      ((n*b).negOnePow • (shiftFunctorComm C b n).hom.app (X⟦a⟧)) ≫
        (shiftFunctor C b).map ((n*a).negOnePow • (shiftFunctorComm C a n).hom.app X) ≫
          (shiftFunctorAdd C a b).inv.app (X⟦n⟧)
    simp only [Functor.map_units_smul, Linear.comp_units_smul,
      Linear.units_smul_comp, smul_smul, mul_add, Int.negOnePow_add]
    exact congrArg (((n*a).negOnePow * (n*b).negOnePow) • ·)
      (shiftCommutation_add C n a b X)

local instance signedShiftCommutationInstance (n : ℤ) : (shiftFunctor C n).CommShift ℤ :=
  signedShiftFunctorCommShift C n

/-- The usual triangle shift differs only by the middle object's sign. -/
def signedShiftTriangleIso (n : ℤ) (T : Triangle C) :
    (shiftFunctor C n).mapTriangle.obj T ≅ T⟦n⟧ :=
  Triangle.isoMk _ _ (Iso.refl _) (n.negOnePow • Iso.refl _) (Iso.refl _)
    (by simp [Linear.comp_units_smul, Linear.units_smul_comp])
    (by simp [Linear.comp_units_smul, Linear.units_smul_comp, smul_smul])
    (by
      simp only [Iso.refl_hom, CategoryTheory.Functor.map_id,
        Category.comp_id, Category.id_comp]
      change (shiftFunctor C n).map T.mor₃ ≫
          ((n*1).negOnePow • (shiftFunctorComm C 1 n).hom.app T.obj₁) = _
      simp [Linear.comp_units_smul, Linear.units_smul_comp])

variable [CategoryTheory.Limits.HasZeroObject C] [Pretriangulated C]

/-- The signed shift preserves every distinguished triangle. -/
theorem signedShiftFunctor_isTriangulated (n : ℤ) :
    (shiftFunctor C n).IsTriangulated where
  map_distinguished T hT :=
    isomorphic_distinguished _ (T.shift_distinguished hT n) _
      (signedShiftTriangleIso C n T)

end ToricPower

end
