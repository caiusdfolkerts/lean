module

public import ToricPower.VectorScalarRetract
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Detecting arbitrary stalk complexes with a scalar test

A nonzero derived vector space contains a shifted scalar retract.
Applying the actual coefficient functor and its shift comparison turns
any nonzero scalar test into a nonzero test for that vector space. No
finite-dimensionality, degree bound, or tensor--Hom interchange is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u w v z
variable (k : Type u) [Field k] [HasDerivedCategory.{w} (ModuleCat.{u} k)]
  {D : Type v} [Category.{z} D] [Preadditive D] [HasShift D ℤ]
  [∀ q : ℤ, (shiftFunctor D q).Additive]
  (F : DerivedCategory (ModuleCat.{u} k) ⥤ D) [F.CommShift ℤ]

/-- The scalar retract transfers nonvanishing for any actual
shift-compatible coefficient functor. -/
theorem exists_nonzero_from_coefficient_shift
    (K : D)
    (f : F.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj
      (ModuleCat.of k k)) ⟶ K) (testNonzero : f ≠ 0)
    (E : DerivedCategory (ModuleCat.{u} k)) (nonzero : ¬ IsZero E) :
    ∃ n : ℤ, ∃ g : (F.obj E)⟦n⟧ ⟶ K, g ≠ 0 := by
  obtain ⟨n,⟨r⟩⟩ := nonzero_derived_vector_has_scalar_retract k E nonzero
  let q := (r.map F).trans (Retract.ofIso ((F.commShiftIso n).app E))
  refine ⟨n,q.r ≫ f,?_⟩
  intro zero
  apply testNonzero
  calc
    f = q.i ≫ (q.r ≫ f) := by rw [← Category.assoc,q.retract,Category.id_comp]
    _ = 0 := by rw [zero,comp_zero]

/-- Equivalently, the original coefficient source detects a shift of
the target, through the actual shift adjunction. -/
theorem exists_nonzero_from_coefficient
    (K : D)
    (f : F.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj
      (ModuleCat.of k k)) ⟶ K) (testNonzero : f ≠ 0)
    (E : DerivedCategory (ModuleCat.{u} k)) (nonzero : ¬ IsZero E) :
    ∃ n : ℤ, ∃ g : F.obj E ⟶ K⟦n⟧, g ≠ 0 := by
  obtain ⟨n,g,hg⟩ := exists_nonzero_from_coefficient_shift k F K f testNonzero E nonzero
  letI : (shiftEquiv D n).functor.Additive :=
    inferInstanceAs ((shiftFunctor D n).Additive)
  letI : (shiftEquiv D n).inverse.Additive :=
    inferInstanceAs ((shiftFunctor D (-n)).Additive)
  let adj := (shiftEquiv D n).toAdjunction
  refine ⟨-n,adj.homEquiv (F.obj E) K g,?_⟩
  intro zero
  apply hg
  apply (adj.homEquiv (F.obj E) K).injective
  exact zero.trans (adj.homAddEquiv_zero (F.obj E) K).symm

end ToricPower

end
