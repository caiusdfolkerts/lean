module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Card
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Equality in the three-plus-four finite fiber budget

Uncompiled draft. The conclusion records every individual fiber size,
the number of fibers, and saturation of the total vertex bound. There
is no geometric hypothesis hidden in this finite arithmetic lemma.
-/

namespace Papers.FiniteFiberSaturation

open scoped BigOperators

theorem finite_fiber_saturation {I : Type*} [Fintype I]
    (q0 : I) (s : I → ℕ) (d N : ℕ)
    (hcard : d + 1 ≤ Fintype.card I)
    (hzero : 3 ≤ s q0)
    (hother : ∀ q, q ≠ q0 → 4 ≤ s q)
    (hsum : (∑ q, s q) ≤ N)
    (hN : N ≤ 3 + 4 * d) :
    Fintype.card I = d + 1 ∧
      s q0 = 3 ∧
      (∀ q, q ≠ q0 → s q = 4) ∧
      (∑ q, s q) = N := by
  classical
  let S : Finset I := Finset.univ.erase q0
  have hS : S.card + 1 = Fintype.card I := by
    simpa [S] using Finset.card_erase_add_one
      (Finset.mem_univ q0)
  have hsplit : (∑ q ∈ S, s q) + s q0 = ∑ q, s q := by
    exact Finset.sum_erase_add Finset.univ s (Finset.mem_univ q0)
  have hlower : 4 * S.card ≤ ∑ q ∈ S, s q := by
    calc
      _ = ∑ _q ∈ S, (4 : ℕ) := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun q hq =>
        hother q (Finset.mem_erase.mp hq).1
  have hcount : Fintype.card I = d + 1 := by omega
  have hSsize : S.card = d := by omega
  have htotal : (∑ q, s q) = N := by omega
  have hzeroeq : s q0 = 3 := by omega
  have hSequal : (∑ q ∈ S, s q) = 4 * S.card := by omega
  refine ⟨hcount,hzeroeq,?_,htotal⟩
  intro q hq
  have hqS : q ∈ S := Finset.mem_erase.mpr ⟨hq,Finset.mem_univ q⟩
  have hrestcard : (S.erase q).card + 1 = S.card :=
    Finset.card_erase_add_one hqS
  have hrestsum :
      (∑ r ∈ S.erase q, s r) + s q = ∑ r ∈ S, s r :=
    Finset.sum_erase_add S s hqS
  have hrestlower : 4 * (S.erase q).card ≤ ∑ r ∈ S.erase q, s r := by
    calc
      _ = ∑ _r ∈ S.erase q, (4 : ℕ) := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun r hr =>
        hother r (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1
  have hqmin := hother q hq
  omega

theorem saturated_total_eq_three_add_four_mul {I : Type*} [Fintype I]
    (q0 : I) (s : I → ℕ) (d N : ℕ)
    (hcard : d + 1 ≤ Fintype.card I)
    (hzero : 3 ≤ s q0)
    (hother : ∀ q, q ≠ q0 → 4 ≤ s q)
    (hsum : (∑ q, s q) ≤ N)
    (hN : N ≤ 3 + 4 * d) :
    N = 3 + 4 * d := by
  classical
  obtain ⟨hc,hz,ho,ht⟩ :=
    finite_fiber_saturation q0 s d N hcard hzero hother hsum hN
  have hsplit := Finset.sum_erase_add Finset.univ s (Finset.mem_univ q0)
  have hsumOther :
      (∑ q ∈ Finset.univ.erase q0, s q) =
        4 * (Finset.univ.erase q0).card := by
    calc
      _ = ∑ _q ∈ Finset.univ.erase q0, (4 : ℕ) := by
        apply Finset.sum_congr rfl
        intro q hq
        exact ho q (Finset.mem_erase.mp hq).1
      _ = _ := by simp [Nat.mul_comm]
  have hcardOther := Finset.card_erase_add_one (Finset.mem_univ q0)
  simp only [Finset.card_univ] at hcardOther
  omega

theorem three_fiber_saturation {I : Type*} [Fintype I]
    (hcard : Fintype.card I = 3) (q0 : I) (s : I → ℕ)
    (a r e N : ℕ) (hr : 2 ≤ r) (ha : r + 1 ≤ a)
    (hsizes : ∀ q, a ≤ s q) (hlarge : 2 * r ≤ s q0)
    (hextra : 1 ≤ e) (hpartition : (∑ q, s q) + e = N)
    (hN : N ≤ 4 * r + 3) :
    a = r + 1 ∧ e = 1 ∧ s q0 = 2 * r ∧
      (∀ q, q ≠ q0 → s q = r + 1) ∧ N = 4 * r + 3 := by
  classical
  let S : Finset I := Finset.univ.erase q0
  have hS : S.card = 2 := by
    have hc := Finset.card_erase_add_one (Finset.mem_univ q0)
    simp only [Finset.card_univ] at hc
    change S.card + 1 = Fintype.card I at hc
    omega
  have hsplit : (∑ q ∈ S, s q) + s q0 = ∑ q, s q :=
    Finset.sum_erase_add Finset.univ s (Finset.mem_univ q0)
  have hotherlower : 2 * a ≤ ∑ q ∈ S, s q := by
    calc
      _ = ∑ _q ∈ S, a := by simp [hS,Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun q _ => hsizes q
  have haeq : a = r + 1 := by omega
  have heeq : e = 1 := by omega
  have hlargeeq : s q0 = 2 * r := by omega
  have hNeq : N = 4 * r + 3 := by omega
  have hothersum : (∑ q ∈ S, s q) = 2 * a := by omega
  refine ⟨haeq,heeq,hlargeeq,?_,hNeq⟩
  intro q hq
  have hqS : q ∈ S := Finset.mem_erase.mpr ⟨hq,Finset.mem_univ q⟩
  have hrestcard : (S.erase q).card = 1 := by
    have hc := Finset.card_erase_add_one hqS
    omega
  have hrestsum : (∑ v ∈ S.erase q, s v) + s q = ∑ v ∈ S, s v :=
    Finset.sum_erase_add S s hqS
  have hrestlower : a ≤ ∑ v ∈ S.erase q, s v := by
    calc
      _ = ∑ _v ∈ S.erase q, a := by simp [hrestcard]
      _ ≤ _ := Finset.sum_le_sum fun v _ => hsizes v
  have hqmin := hsizes q
  omega

end Papers.FiniteFiberSaturation
