module

public import Papers.GraphicalZonotopes.FinitePowersetTransform
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H : Type*} [Fintype H] [DecidableEq H]

def exactlyOne (S : Finset H) : ℝ:=if S.card=1 then 1 else 0

def exactlyOneCoefficient (n : ℕ) : ℝ:=
  if n=0 then 0 else (n : ℝ)*(-1 : ℝ)^(n-1)

theorem exactlyOneCoefficient_step (n : ℕ) :
    exactlyOneCoefficient n+exactlyOneCoefficient (n+1)=(-1 : ℝ)^n := by
  cases n with
  | zero => norm_num [exactlyOneCoefficient]
  | succ n =>
    simp only [exactlyOneCoefficient,Nat.add_one_ne_zero,Nat.succ_ne_zero,
      ite_false,Nat.add_sub_cancel,Nat.succ_sub_one,Nat.cast_add,Nat.cast_one,
      Nat.cast_succ,pow_succ]
    ring

theorem real_alternating_powerset (S : Finset H) :
    (∑ T∈S.powerset,(-1 : ℝ)^T.card)=if S=∅ then 1 else 0 := by
  have hi:=sum_powerset_neg_one_pow_card (x:=S)
  exact_mod_cast hi

/-- The full finite multilinear expansion of the exactly-one indicator.
It includes the empty coefficient and every subset of the ambient type. -/
theorem zeta_exactlyOneCoefficient :
    zeta (fun S : Finset H => exactlyOneCoefficient S.card)=exactlyOne := by
  funext S
  by_cases hS : S=∅
  · subst S
    simp [zeta,exactlyOneCoefficient,exactlyOne]
  · obtain ⟨a,ha⟩:=nonempty_iff_ne_empty.mpr hS
    let T:=S.erase a
    have haT : a∉T:=notMem_erase a S
    have he : insert a T=S:=insert_erase ha
    rw [← he]
    change (∑ U∈(insert a T).powerset,exactlyOneCoefficient U.card)=_
    rw [sum_powerset_insert haT,← sum_add_distrib]
    have hs : (∑ U∈T.powerset,
        (exactlyOneCoefficient U.card+exactlyOneCoefficient (insert a U).card))=
        ∑ U∈T.powerset,(-1 : ℝ)^U.card := by
      apply sum_congr rfl
      intro U hU
      have haU : a∉U:=fun h => haT ((mem_powerset.mp hU) h)
      rw [card_insert_of_notMem haU,exactlyOneCoefficient_step]
    rw [hs,real_alternating_powerset]
    simp only [exactlyOne,card_insert_of_notMem haT]
    have hn : T.card+1=1 ↔ T=∅:=by rw [← card_eq_zero]; omega
    simp only [hn]

def absentCoefficient (a : H) (y : SetFunction H) : SetFunction H:=
  fun T => if a∈T then -y (T.erase a) else y T

/-- Multiplication by the Boolean factor `(1-x_a)` in actual subset
coordinates, derived by cancelling the two halves of the powerset sum. -/
theorem zeta_absentCoefficient (a : H) (y : SetFunction H) (S : Finset H) :
    zeta (absentCoefficient a y) S=if a∈S then 0 else zeta y S := by
  by_cases ha : a∈S
  · let T:=S.erase a
    have haT : a∉T:=notMem_erase a S
    have he : insert a T=S:=insert_erase ha
    rw [if_pos ha,← he]
    unfold zeta
    rw [sum_powerset_insert haT]
    have hfirst : (∑ U∈T.powerset,absentCoefficient a y U)=∑ U∈T.powerset,y U := by
      apply sum_congr rfl
      intro U hU
      have haU : a∉U:=fun h => haT ((mem_powerset.mp hU) h)
      exact if_neg haU
    have hsecond : (∑ U∈T.powerset,absentCoefficient a y (insert a U))=
        -(∑ U∈T.powerset,y U) := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro U hU
      have haU : a∉U:=fun h => haT ((mem_powerset.mp hU) h)
      simp only [absentCoefficient,mem_insert_self,ite_true,erase_insert haU]
    rw [hfirst,hsecond,add_neg_cancel]
  · rw [if_neg ha]
    apply sum_congr rfl
    intro U hU
    have haU : a∉U:=fun h => ha ((mem_powerset.mp hU) h)
    exact if_neg haU

theorem zeta_absent_exactlyOne (a : H) (S : Finset H) :
    zeta (absentCoefficient a (fun T => exactlyOneCoefficient T.card)) S=
      if a∈S then 0 else exactlyOne S := by
  rw [zeta_absentCoefficient,zeta_exactlyOneCoefficient]

end BooleanModule
end GraphicalZonotopes
