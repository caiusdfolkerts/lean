module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # Finite source bounds after extension by zero -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]

/-- A nonnegative complex vanishing in degrees at least `width` has
precisely the required finite support after extension to integer degrees. -/
theorem finiteCochain_extend_isZero_outside (K : CochainComplex C ℕ) (width : ℕ)
    (outside : ∀ q : ℕ, width ≤ q → IsZero (K.X q))
    (p : ℤ) (notInside : ¬ (0 ≤ p ∧ p < (width : ℤ))) :
    IsZero ((K.extend ComplexShape.embeddingUpNat).X p) := by
  by_cases nonnegative : 0 ≤ p
  · have equality : ComplexShape.embeddingUpNat.f p.toNat = p := by
      exact Int.toNat_of_nonneg nonnegative
    exact (outside p.toNat (by omega)).of_iso
      (K.extendXIso ComplexShape.embeddingUpNat equality)
  · exact K.isZero_extend_X ComplexShape.embeddingUpNat p (fun q equality => by
      change (q : ℤ) = p at equality
      omega)

end ToricPower

end
