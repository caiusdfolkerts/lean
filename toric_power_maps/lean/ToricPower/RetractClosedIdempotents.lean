module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Retract

/-!
# Idempotents in a full subcategory closed under retracts

An ambient splitting belongs to the indicated full subcategory because
its image is an actual retract of the original object.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace ToricPower

universe u v
variable {D : Type u} [Category.{v} D] [IsIdempotentComplete D]

instance idempotentComplete_retractClosedFullSubcategory
    (P : ObjectProperty D) [P.IsStableUnderRetracts] :
    IsIdempotentComplete P.FullSubcategory where
  idempotents_split X e he := by
    have he' : e.hom ≫ e.hom = e.hom := congrArg (fun f => f.hom) he
    obtain ⟨Y, i, p, hi, hp⟩ := IsIdempotentComplete.idempotents_split X.obj e.hom he'
    let YP : P.FullSubcategory := ⟨Y, P.prop_of_retract ⟨i,p,hi⟩ X.property⟩
    refine ⟨YP, ObjectProperty.homMk i, ObjectProperty.homMk p, ?_, ?_⟩
    · apply P.ι.map_injective
      exact hi
    · apply P.ι.map_injective
      exact hp

end ToricPower

end
