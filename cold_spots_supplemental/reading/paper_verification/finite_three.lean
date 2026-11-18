module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.NormNum

@[expose] public section
namespace PaperVerification.ColdSpots

open scoped BigOperators

theorem sum_zmod_three {M : Type*} [AddCommMonoid M] (f : ZMod 3 → M) :
    (∑ r, f r)=f 0+f 1+f 2 := by
  have h : (Finset.univ : Finset (ZMod 3))={0,1,2} := by decide
  have h0 : (0 : ZMod 3) ∉ ({1, 2} : Finset (ZMod 3)) := by decide
  have h1 : (1 : ZMod 3) ∉ ({2} : Finset (ZMod 3)) := by decide
  rw [h, Finset.sum_insert h0, Finset.sum_insert h1, Finset.sum_singleton, add_assoc]

theorem prod_zmod_three {M : Type*} [CommMonoid M] (f : ZMod 3 → M) :
    (∏ r, f r)=f 0*f 1*f 2 := by
  have h : (Finset.univ : Finset (ZMod 3))={0,1,2} := by decide
  have h0 : (0 : ZMod 3) ∉ ({1, 2} : Finset (ZMod 3)) := by decide
  have h1 : (1 : ZMod 3) ∉ ({2} : Finset (ZMod 3)) := by decide
  rw [h, Finset.prod_insert h0, Finset.prod_insert h1, Finset.prod_singleton, mul_assoc]

end PaperVerification.ColdSpots
