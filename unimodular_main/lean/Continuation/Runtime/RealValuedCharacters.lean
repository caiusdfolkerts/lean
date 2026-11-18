module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.HahnSeries.Summable
public import Mathlib.RingTheory.HahnSeries.Valuation
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Data.Real.Basic

/-!
# Real character weights as genuine valuative test points

A real additive weight on a lattice sends each character to a Hahn
monomial of precisely that weight. The Hahn field and its nonnegative
valuation ring therefore provide a valuative test point for every real
cocharacter, without a rational approximation argument. The map from the
character ring need not be injective and no injectivity is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.ToricCharacters

variable (k : Type*) [Field k]

/-- The actual valuation subring of the real-exponent Hahn field. -/
abbrev RealCharacterValuationRing :=
  (AddValuation.toValuation (HahnSeries.addVal ℝ k)).valuationSubring

/-- Membership is the ordinary nonnegativity of the leading exponent. -/
theorem mem_realCharacterValuationRing (x : HahnSeries ℝ k) :
    x ∈ RealCharacterValuationRing k ↔ 0 ≤ x.orderTop := by
  change 0 ≤ HahnSeries.addVal ℝ k x ↔ 0 ≤ x.orderTop
  rw [HahnSeries.addVal_apply]

/-- A nonzero Hahn monomial is in the valuation ring exactly when its
actual real exponent is nonnegative. -/
theorem single_mem_realCharacterValuationRing (w : ℝ) (c : k) (hc : c ≠ 0) :
    HahnSeries.single w c ∈ RealCharacterValuationRing k ↔ 0 ≤ w := by
  rw [mem_realCharacterValuationRing, HahnSeries.orderTop_single hc]
  exact WithTop.coe_le_coe

/-- The ground field embeds as constant series in the actual valuation
ring. This is the base-field map used in the valuative square. -/
def realCharacterConstant : k →+* RealCharacterValuationRing k :=
  (HahnSeries.C : k →+* HahnSeries ℝ k).codRestrict
    (RealCharacterValuationRing k).toSubring (fun c => by
      apply (mem_realCharacterValuationRing k _).mpr
      exact HahnSeries.orderTop_single_le)

instance realCharacterValuationRingAlgebra : Algebra k (RealCharacterValuationRing k) :=
  (realCharacterConstant k).toAlgebra

instance realCharacterValuationRingScalarTower :
    IsScalarTower k (RealCharacterValuationRing k) (HahnSeries ℝ k) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

variable {M : Type*} [AddCommMonoid M] (w : M →+ ℝ)

/-- Evaluate every original character at its Hahn monomial. -/
def realCharacterMonoidHom : Multiplicative M →* HahnSeries ℝ k where
  toFun m := HahnSeries.single (w m.toAdd) 1
  map_one' := by simp
  map_mul' m q := by
    change HahnSeries.single (w (m.toAdd + q.toAdd)) 1 =
      HahnSeries.single (w m.toAdd) 1 * HahnSeries.single (w q.toAdd) 1
    simp only [map_add, HahnSeries.single_mul_single, mul_one]

def realCharacterEvaluation : AddMonoidAlgebra k M →ₐ[k] HahnSeries ℝ k :=
  AddMonoidAlgebra.lift k (HahnSeries ℝ k) M (realCharacterMonoidHom k w)

@[simp] theorem realCharacterEvaluation_single (m : M) :
    realCharacterEvaluation k w (AddMonoidAlgebra.single m 1) =
      HahnSeries.single (w m) 1 := by
  simp [realCharacterEvaluation, realCharacterMonoidHom, AddMonoidAlgebra.lift_single]

/-- Regularity of an evaluated character records exactly the real
half-space inequality, with no rationality restriction on its weight. -/
theorem realCharacterEvaluation_mem_iff (m : M) :
    realCharacterEvaluation k w (AddMonoidAlgebra.single m 1) ∈
      RealCharacterValuationRing k ↔ 0 ≤ w m := by
  rw [realCharacterEvaluation_single]
  exact single_mem_realCharacterValuationRing k (w m) 1 one_ne_zero

variable (S : AddSubmonoid M) (hS : ∀ m ∈ S, 0 ≤ w m)

/-- Nonnegative weights give an actual semigroup homomorphism into the
valuation ring, not merely a condition on its fraction field. -/
def realMonoidCharacterHom : Multiplicative S →* RealCharacterValuationRing k where
  toFun m := ⟨HahnSeries.single (w m.toAdd.val) 1,
    (single_mem_realCharacterValuationRing k _ 1 one_ne_zero).mpr (hS _ m.toAdd.property)⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' m q := by
    apply Subtype.ext
    change HahnSeries.single (w (m.toAdd.val + q.toAdd.val)) 1 =
      HahnSeries.single (w m.toAdd.val) 1 * HahnSeries.single (w q.toAdd.val) 1
    simp only [map_add, HahnSeries.single_mul_single, mul_one]

def realMonoidCharacterEvaluation :
    AddMonoidAlgebra k S →ₐ[k] RealCharacterValuationRing k :=
  AddMonoidAlgebra.lift k (RealCharacterValuationRing k) S
    (realMonoidCharacterHom k w S hS)

@[simp] theorem realMonoidCharacterEvaluation_single (m : S) :
    (realMonoidCharacterEvaluation k w S hS (AddMonoidAlgebra.single m 1) : HahnSeries ℝ k) =
      HahnSeries.single (w m.val) 1 := by
  simp [realMonoidCharacterEvaluation, realMonoidCharacterHom, AddMonoidAlgebra.lift_single]

/-- The integral map has the same generic character values as the
original Hahn-field test point. -/
theorem realMonoidCharacterEvaluation_generic :
    (IsScalarTower.toAlgHom k (RealCharacterValuationRing k) (HahnSeries ℝ k)).comp
        (realMonoidCharacterEvaluation k w S hS) =
      (realCharacterEvaluation k w).comp (AddMonoidAlgebra.mapDomainAlgHom k k S.subtype) := by
  ext m
  simp [realMonoidCharacterEvaluation, realMonoidCharacterHom,
    realCharacterEvaluation, realCharacterMonoidHom, AddMonoidAlgebra.lift_single]

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.realCharacterEvaluation_mem_iff
#print axioms PaperVerification.ToricCharacters.realMonoidCharacterEvaluation_generic
