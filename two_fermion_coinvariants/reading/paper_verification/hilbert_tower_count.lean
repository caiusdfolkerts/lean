module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Lean.Elab.Tactic.Omega

/-!
# The Hilbert series of homogeneous polynomial towers

This proves the coefficient-extraction identity for an arbitrary degree-indexed
basis with finite degree fibres. The inverse of `1-X^h` is the actual formal
power-series inverse with constant coefficient one, and its inverse property is
proved. The count retains all nonnegative tower exponents.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.HilbertTowerCount

variable {I : Type*}

abbrev Fibre (degree : I → ℕ) (d : ℕ) := {i // degree i = d}
abbrev Towers (degree : I → ℕ) (h d : ℕ) :=
  {a : ℕ × I // a.1 * h + degree a.2 = d}

theorem exponent_zero_of_lt (degree : I → ℕ) (h d : ℕ) (hd : d < h)
    (a : Towers degree h d) : a.val.1 = 0 := by
  obtain ⟨⟨j,i⟩,ha⟩ := a
  cases j with
  | zero => rfl
  | succ j => simp only [Nat.succ_mul] at ha; omega

def smallEquiv (degree : I → ℕ) (h d : ℕ) (hd : d < h) :
    Towers degree h d ≃ Fibre degree d where
  toFun a := ⟨a.val.2, by
    simpa only [exponent_zero_of_lt degree h d hd a, zero_mul, zero_add] using a.property⟩
  invFun i := ⟨(0,i.val), by simpa only [zero_mul, zero_add] using i.property⟩
  left_inv a := by
    apply Subtype.ext
    exact Prod.ext (exponent_zero_of_lt degree h d hd a).symm rfl
  right_inv i := rfl

def zeroSuccEquiv (degree : I → ℕ) (h d : ℕ) (hd : h ≤ d) :
    Towers degree h d ≃ Fibre degree d ⊕ Towers degree h (d-h) where
  toFun a := by
    obtain ⟨⟨j,i⟩,ha⟩ := a
    cases j with
    | zero => exact .inl ⟨i, by simpa only [zero_mul, zero_add] using ha⟩
    | succ j =>
      refine .inr ⟨(j,i), ?_⟩
      change j * h + degree i = d - h
      simp only [Nat.succ_mul] at ha
      omega
  invFun a := by
    cases a with
    | inl i => exact ⟨(0,i.val), by simpa only [zero_mul, zero_add] using i.property⟩
    | inr a =>
      refine ⟨(a.val.1 + 1,a.val.2), ?_⟩
      change (a.val.1 + 1) * h + degree a.val.2 = d
      have ha := a.property
      simp only [Nat.add_mul, one_mul]
      omega
  left_inv a := by
    obtain ⟨⟨j,i⟩,ha⟩ := a
    cases j <;> rfl
  right_inv a := by
    rcases a with ⟨i,hi⟩ | ⟨⟨j,i⟩,ha⟩ <;> rfl

theorem finite_towers (degree : I → ℕ) (h : ℕ) (hh : 0 < h)
    (hf : ∀ d, Finite (Fibre degree d)) (d : ℕ) : Finite (Towers degree h d) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    letI := hf d
    by_cases hd : h ≤ d
    · letI := ih (d-h) (by omega)
      exact Finite.of_equiv (Fibre degree d ⊕ Towers degree h (d-h))
        (zeroSuccEquiv degree h d hd).symm
    · exact Finite.of_equiv (Fibre degree d)
        (smallEquiv degree h d (Nat.lt_of_not_ge hd)).symm

theorem count_recurrence (degree : I → ℕ) (h : ℕ) (hh : 0 < h)
    (hf : ∀ d, Finite (Fibre degree d)) (d : ℕ) :
    Nat.card (Towers degree h d) = Nat.card (Fibre degree d) +
      if h ≤ d then Nat.card (Towers degree h (d-h)) else 0 := by
  letI := hf d
  letI := finite_towers degree h hh hf (d-h)
  by_cases hd : h ≤ d
  · rw [if_pos hd, Nat.card_congr (zeroSuccEquiv degree h d hd), Nat.card_sum]
  · rw [if_neg hd, add_zero]
    exact Nat.card_congr (smallEquiv degree h d (Nat.lt_of_not_ge hd))

def basisSeries (degree : I → ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun d => (Nat.card (Fibre degree d) : ℤ)

def towerSeries (degree : I → ℕ) (h : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun d => (Nat.card (Towers degree h d) : ℤ)

theorem denominator_mul_towerSeries (degree : I → ℕ) (h : ℕ) (hh : 0 < h)
    (hf : ∀ d, Finite (Fibre degree d)) :
    (1 - PowerSeries.X ^ h) * towerSeries degree h = basisSeries degree := by
  ext d
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul']
  have hc := congrArg (fun n : ℕ => (n : ℤ)) (count_recurrence degree h hh hf d)
  by_cases hd : h ≤ d
  · simp only [if_pos hd, Nat.cast_add] at hc
    simp only [if_pos hd, towerSeries, basisSeries, PowerSeries.coeff_mk]
    exact sub_eq_iff_eq_add.mpr hc
  · simp only [if_neg hd, add_zero] at hc
    simpa only [if_neg hd, sub_zero, towerSeries, basisSeries, PowerSeries.coeff_mk] using hc

def geometricInverse (h : ℕ) : PowerSeries ℤ :=
  PowerSeries.invOfUnit (1 - PowerSeries.X ^ h) 1

theorem geometricInverse_mul (h : ℕ) (hh : 0 < h) :
    geometricInverse h * (1 - PowerSeries.X ^ h) = 1 := by
  apply PowerSeries.invOfUnit_mul
  simp [Nat.ne_of_gt hh]

theorem mul_geometricInverse (h : ℕ) (hh : 0 < h) :
    (1 - PowerSeries.X ^ h) * geometricInverse h = 1 := by
  rw [mul_comm, geometricInverse_mul h hh]

/-- This is the exact meaning of division by `1-X^h` in the paper's Hilbert
series. The preceding two theorems establish the actual inverse property. -/
theorem towerSeries_eq (degree : I → ℕ) (h : ℕ) (hh : 0 < h)
    (hf : ∀ d, Finite (Fibre degree d)) :
    towerSeries degree h = basisSeries degree * geometricInverse h := by
  calc
    _ = (geometricInverse h * (1 - PowerSeries.X ^ h)) * towerSeries degree h := by
      rw [geometricInverse_mul h hh, one_mul]
    _ = geometricInverse h * ((1 - PowerSeries.X ^ h) * towerSeries degree h) := mul_assoc _ _ _
    _ = geometricInverse h * basisSeries degree := by
      rw [denominator_mul_towerSeries degree h hh hf]
    _ = _ := mul_comm _ _

end PaperVerification.HilbertTowerCount
