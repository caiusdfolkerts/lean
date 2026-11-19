module

public import ToricPower.CategoricalFoundations

/-!
# A nonzero exact functor detects failure of classical generation

The objects killed by an actual triangulated functor form a thick subcategory.
Consequently a functor that kills a classical generator kills every object.
This uses the literal finite triangulated envelope, including retracts.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

namespace ToricPower

universe u v u' v'

section ZeroObjects

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The genuine zero objects, as an object property. -/
def zeroObjectProperty : ObjectProperty C := fun X => IsZero X

instance : (zeroObjectProperty C).IsStableUnderRetracts where
  of_retract {X Y} r hY := by
    apply (IsZero.iff_id_eq_zero X).mpr
    rw [← r.retract, hY.eq_of_tgt r.i 0, zero_comp]

instance : (zeroObjectProperty C).IsTriangulated where
  exists_zero := ⟨0, isZero_zero _, isZero_zero _⟩
  toIsStableUnderShift := ⟨fun n => ⟨fun X hX => (shiftFunctor C n).map_isZero hX⟩⟩
  toIsTriangulatedClosed₂ := ObjectProperty.IsTriangulatedClosed₂.mk'
    (fun T hT h₁ h₃ => T.isZero₂_of_isZero₁₃ hT h₁ h₃)

end ZeroObjects

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]

/-- If a triangulated functor kills a classical generator, it kills every
object. No faithfulness, fullness, or essential surjectivity is required. -/
theorem exactFunctor_isZero_of_generator (G : C)
    (hG : (ObjectProperty.singleton G).IsClassicalTriangulatedGenerator)
    (hFG : IsZero (F.obj G)) (X : C) : IsZero (F.obj X) := by
  let P := (zeroObjectProperty D).inverseImage F
  letI : P.IsStableUnderRetracts := inverseImage_stableUnderRetracts _ _
  have hle : (ObjectProperty.singleton G).triangEnvelope ≤ P := by
    apply ((ObjectProperty.singleton G).triangEnvelope_le_iff (Q := P)).mpr
    rw [ObjectProperty.singleton_le_iff]
    exact hFG
  apply hle X
  rw [hG]
  trivial

/-- An actual nonzero value of an exact functor is a witness that an object
annihilated by it does not classically generate. -/
theorem not_classicalGenerator_of_exactFunctor
    (G X : C) (hFG : IsZero (F.obj G)) (hFX : ¬ IsZero (F.obj X)) :
    ¬ (ObjectProperty.singleton G).IsClassicalTriangulatedGenerator := by
  intro hG
  exact hFX (exactFunctor_isZero_of_generator F G hG hFG X)

end ToricPower

end

