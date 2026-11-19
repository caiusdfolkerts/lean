module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic

/-!
# The finite weight identities in Section 4.1

The two triangular families of normal weights are matched with an actual
rectangle by an explicit weight-preserving bijection. Repeated weights are
retained by the indexing equivalence; this is stronger than equality of the
underlying sets. The telescoping formula uses products in an arbitrary
commutative monoid and therefore introduces no division by a potentially zero
specialization.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace PaperVerification.AlternatingForms.BorelWeights

/-- Strictly ordered pairs of basis indices. -/
abbrev UpperPair (s : ℕ) := {p : Fin s × Fin s // p.1.val < p.2.val}

/-- The two normal-weight families have precisely the multiplicities of the
`s` by `s-1` rectangle. -/
def triangleRectangleEquiv (s : ℕ) :
    UpperPair s ⊕ UpperPair s ≃ Fin s × Fin (s-1) where
  toFun
    | Sum.inl p => (p.val.2, ⟨p.val.1.val, by have := p.property; have := p.val.2.isLt; omega⟩)
    | Sum.inr p => (p.val.1, ⟨p.val.2.val-1, by have := p.property; have := p.val.2.isLt; omega⟩)
  invFun p := if h : p.1.val ≤ p.2.val then
    Sum.inr ⟨(p.1, ⟨p.2.val+1, by have := p.2.isLt; omega⟩), by dsimp; omega⟩
    else
    Sum.inl ⟨(⟨p.2.val, by have := p.2.isLt; omega⟩,p.1), by dsimp; omega⟩
  left_inv := by
    rintro (⟨⟨i,j⟩,hij⟩|⟨⟨i,j⟩,hij⟩)
    · dsimp at hij
      dsimp
      rw [dif_neg (show ¬ j.val ≤ i.val by omega)]
    · dsimp at hij
      dsimp
      rw [dif_pos (show i.val ≤ j.val-1 by omega)]
      apply congrArg Sum.inr
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega
  right_inv := by
    rintro ⟨i,h⟩
    dsimp
    split_ifs with hih
    · apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega
    · rfl

/-- The triangular weights as written after reflection in Section 4.1. -/
def triangleWeight {s : ℕ} : UpperPair s ⊕ UpperPair s → ℕ
  | Sum.inl p => p.val.1.val+p.val.2.val
  | Sum.inr p => p.val.1.val+p.val.2.val-1

/-- The explicit bijection preserves the weight, including its multiplicity. -/
theorem triangleRectangleEquiv_weight {s : ℕ} (p : UpperPair s ⊕ UpperPair s) :
    (triangleRectangleEquiv s p).1.val+(triangleRectangleEquiv s p).2.val =
      triangleWeight p := by
  cases p with
  | inl p => simp only [triangleRectangleEquiv, Equiv.coe_fn_mk, triangleWeight]; omega
  | inr p =>
    simp only [triangleRectangleEquiv, Equiv.coe_fn_mk, triangleWeight]
    have := p.property
    omega

/-- Any multiplicative statistic of the normal weights agrees with the
rectangle statistic, in every size. -/
theorem triangular_weight_product {M : Type*} [CommMonoid M]
    (s : ℕ) (f : ℕ → M) :
    (∏ p : UpperPair s, f (p.val.1.val+p.val.2.val)) *
      (∏ p : UpperPair s, f (p.val.1.val+p.val.2.val-1)) =
      ∏ i : Fin s, ∏ h : Fin (s-1), f (i.val+h.val) := by
  have h := Equiv.prod_comp (triangleRectangleEquiv s)
    (fun p : Fin s × Fin (s-1) => f (p.1.val+p.2.val))
  simp only [triangleRectangleEquiv_weight, Fintype.prod_sum_type, triangleWeight,
    Fintype.prod_prod_type] at h
  exact h

/-- A denominator-free telescope for one row of tangent weights. -/
theorem telescope_row {M : Type*} [CommMonoid M] (f : ℕ → M) (a c : ℕ) :
    (∏ j ∈ Finset.range c, f (a+j+1))*f a =
      (∏ j ∈ Finset.range c, f (a+j))*f (a+c) := by
  induction c with
  | zero => simp
  | succ c ih =>
    simpa only [Finset.prod_range_succ, Nat.add_zero, Nat.add_assoc,
      Nat.succ_eq_add_one, mul_assoc, mul_comm, mul_left_comm] using
      congrArg (fun x => x*f (a+c+1)) ih

end PaperVerification.AlternatingForms.BorelWeights
