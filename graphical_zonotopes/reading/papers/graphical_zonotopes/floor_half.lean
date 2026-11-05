module

public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.NormNum

@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace GraphicalZonotopes
namespace FloorHalf
open Finset
open scoped BigOperators

/-- The exact carry identity behind every graphical Boolean slack. -/
theorem edge_boolean (m a b : ℤ) :
    (m+a+b+1)/2+m/2-(m+a)/2-(m+b)/2=0 ∨
    (m+a+b+1)/2+m/2-(m+a)/2-(m+b)/2=1 := by omega

theorem edge_boolean_of_mixed (m mu mv muv : ℤ) (h : muv+m-mu-mv=1) :
    muv/2+m/2-mu/2-mv/2=0 ∨ muv/2+m/2-mu/2-mv/2=1 := by omega

/-- Nonadjacent paired vertices have consecutive unrounded marginals, whose
rounding errors cancel exactly. -/
theorem twins_zero (m mu mv muv : ℤ) (hm : muv+m-mu-mv=0)
    (ht : mu+1=mv ∨ mv+1=mu) : muv/2+m/2-mu/2-mv/2=0 := by omega

/-- Four-variable quadratic-phase Möbius coefficient with arbitrary linear
part. This finite identity is later applied through an arbitrary four-clique
restriction; it is not used as a bounded replacement for a graph theorem. -/
def fourPhaseMobius (b : Fin 4 → Bool) : ℤ :=
  ∑ S : Finset (Fin 4),(-1 : ℤ)^(4-S.card)*
    (-1 : ℤ)^(S.card.choose 2+(S.filter (fun i => b i=false)).card)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem fourPhaseMobius_values :
    ∀ b : Fin 4 → Bool,fourPhaseMobius b=4 ∨ fourPhaseMobius b= -4 := by decide

end FloorHalf
end GraphicalZonotopes
