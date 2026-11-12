module

public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Algebra.Module.Pi

/-! # The actual scalar open/closed coefficient sequence

For a closed support predicate, open coefficients are the scalars which
vanish whenever the predicate holds. Closed coefficients are functions on
its PLift. The canonical quotient is the constant-function map.
-/

@[expose] public noncomputable section

namespace ToricPower.MorseCoefficients

universe u

variable (k : Type u) [CommRing k]

/-- Scalars supported on the complement of the closed predicate. -/
def openScalar (p : Prop) : Submodule k k where
  carrier := {a | p → a = 0}
  zero_mem' := fun _ => rfl
  add_mem' := by
    intro a b ha hb hp
    simp only [ha hp,hb hp,add_zero]
  smul_mem' := by
    intro a b hb hp
    simp only [hb hp,smul_zero]

/-- The genuine quotient to closed coefficients. -/
def closedScalarQuotient (p : Prop) : k →ₗ[k] (PLift p → k) where
  toFun a _ := a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem closedScalarQuotient_eq_zero_iff (p : Prop) (a : k) :
    closedScalarQuotient k p a = 0 ↔ p → a = 0 := by
  constructor
  · intro h hp
    exact congrFun h ⟨hp⟩
  · intro h
    funext hp
    exact h hp.down

theorem openScalar_range_eq_kernel (p : Prop) :
    LinearMap.range (openScalar k p).subtype =
      LinearMap.ker (closedScalarQuotient k p) := by
  apply SetLike.ext
  intro a
  constructor
  · rintro ⟨b,rfl⟩
    exact (closedScalarQuotient_eq_zero_iff k p b.val).mpr b.property
  · intro h
    exact ⟨⟨a,(closedScalarQuotient_eq_zero_iff k p a).mp h⟩,rfl⟩

theorem closedScalarQuotient_surjective (p : Prop) :
    Function.Surjective (closedScalarQuotient k p) := by
  classical
  intro f
  by_cases hp : p
  · refine ⟨f ⟨hp⟩,?_⟩
    funext h
    change f ⟨hp⟩ = f h
    congr 1
  · refine ⟨0,?_⟩
    funext h
    exact (hp h.down).elim

theorem openScalar_subtype_injective (p : Prop) :
    Function.Injective (openScalar k p).subtype :=
  Subtype.val_injective

/-- Face maps on the open coefficient submodule. -/
def openScalarMap {p q : Prop} (h : q → p) :
    openScalar k p →ₗ[k] openScalar k q where
  toFun a := ⟨a.val,fun hq => a.property (h hq)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Face maps on the closed coefficient quotient. -/
def closedScalarMap {p q : Prop} (h : q → p) :
    (PLift p → k) →ₗ[k] (PLift q → k) where
  toFun a hq := a ⟨h hq.down⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem openScalarMap_subtype {p q : Prop} (h : q → p) :
    (openScalar k q).subtype ∘ₗ openScalarMap k h =
      (openScalar k p).subtype := rfl

theorem closedScalarQuotient_naturality {p q : Prop} (h : q → p) :
    closedScalarMap k h ∘ₗ closedScalarQuotient k p =
      closedScalarQuotient k q := rfl

end ToricPower.MorseCoefficients

end
