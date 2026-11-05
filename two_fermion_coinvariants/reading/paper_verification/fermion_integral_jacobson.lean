module

public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Group.Int.Units
public import Lean.Elab.Tactic.Omega

/-!
# The integral ground ring in universal coefficient descent

The integer Jacobson radical vanishes by the elementary unit criterion:
if x belongs to it, then 3x+1 must equal 1 or -1, forcing x=0.
Every nonzero prime ideal is maximal because the integers are a PID.
Together these prove the Jacobson-ring hypothesis used by the actual
universal coefficient construction.

-/

@[expose] public section
set_option autoImplicit false

namespace PaperVerification.Fermion

theorem integer_jacobson_bot : (⊥ : Ideal ℤ).jacobson = ⊥ := by
  apply le_antisymm
  · intro x hx
    have hu := Int.isUnit_iff.mp ((Ideal.mem_jacobson_bot.mp hx) 3)
    change x=0
    rcases hu with hu | hu <;> omega
  · exact bot_le

instance integers_isJacobson : IsJacobsonRing ℤ := by
  apply isJacobsonRing_iff_prime_eq.mpr
  intro P hP
  by_cases hzero : P=⊥
  · subst P
    exact integer_jacobson_bot
  · letI : P.IsPrime := hP
    letI : P.IsMaximal := IsPrime.to_maximal_ideal hzero
    exact Ideal.jacobson_eq_self_of_isMaximal

end PaperVerification.Fermion
