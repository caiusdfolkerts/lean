import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.Ideal.Operations

/-! # Linear-weight bounds and initial forms in polynomial domains -/

noncomputable section

namespace CommAlg.Weight

open Classical Finset
open scoped Pointwise

variable {V k : Type*} [DecidableEq V] [CommRing k]

def Bound (w : V → ℤ) (c : ℤ) (p : MvPolynomial V k) : Prop :=
  ∀ a, p.coeff a ≠ 0 → c ≤ Finsupp.weight w a

theorem bound_zero (w : V → ℤ) (c : ℤ) : Bound w c (0 : MvPolynomial V k) := by
  intro a ha
  simp at ha

theorem Bound.mono {w : V → ℤ} {c d : ℤ} {p : MvPolynomial V k}
    (hp : Bound w c p) (hd : d ≤ c) : Bound w d p := fun a ha => hd.trans (hp a ha)

theorem Bound.add {w : V → ℤ} {c : ℤ} {p q : MvPolynomial V k}
    (hp : Bound w c p) (hq : Bound w c q) : Bound w c (p + q) := by
  intro a ha
  by_cases hpa : p.coeff a = 0
  · apply hq a
    simpa only [MvPolynomial.coeff_add, hpa, zero_add] using ha
  · exact hp a hpa

theorem Bound.neg {w : V → ℤ} {c : ℤ} {p : MvPolynomial V k}
    (hp : Bound w c p) : Bound w c (-p) := by
  intro a ha
  exact hp a (by simpa using ha)

theorem Bound.mul {w : V → ℤ} {c d : ℤ} {p q : MvPolynomial V k}
    (hp : Bound w c p) (hq : Bound w d q) : Bound w (c + d) (p * q) := by
  intro a ha
  have hm := MvPolynomial.support_mul p q (MvPolynomial.mem_support_iff.mpr ha)
  obtain ⟨b, hb, e, he, rfl⟩ := Finset.mem_add.mp hm
  rw [map_add]
  exact add_le_add (hp b (MvPolynomial.mem_support_iff.mp hb))
    (hq e (MvPolynomial.mem_support_iff.mp he))

theorem bound_one (w : V → ℤ) : Bound w 0 (1 : MvPolynomial V k) := by
  intro a ha
  by_cases h : a = 0
  · subst a; simp
  · simp [MvPolynomial.coeff_one, h, Ne.symm h] at ha

theorem Bound.pow {w : V → ℤ} {c : ℤ} {p : MvPolynomial V k}
    (hp : Bound w c p) (n : ℕ) : Bound w ((n : ℤ) * c) (p ^ n) := by
  induction n with
  | zero => simpa using bound_one w
  | succ n ih =>
    simpa only [pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using ih.mul hp

theorem bound_sum {ι : Type*} (w : V → ℤ) (c : ℤ) (s : Finset ι)
    (f : ι → MvPolynomial V k) (hf : ∀ i ∈ s, Bound w c (f i)) :
    Bound w c (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using bound_zero w c
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem exists_minimum (w : V → ℤ) {p : MvPolynomial V k} (hp : p ≠ 0) :
    ∃ m : ℤ, Bound w m p ∧ ∃ a, p.coeff a ≠ 0 ∧ Finsupp.weight w a = m := by
  have hS := MvPolynomial.support_nonempty.mpr hp
  let m := p.support.inf' hS (Finsupp.weight w)
  obtain ⟨a, ha, he⟩ := Finset.exists_mem_eq_inf' hS (Finsupp.weight w)
  refine ⟨m, ?_, a, MvPolynomial.mem_support_iff.mp ha, he.symm⟩
  intro b hb
  exact Finset.inf'_le _ (MvPolynomial.mem_support_iff.mpr hb)

abbrev initial (w : V → ℤ) (m : ℤ) (p : MvPolynomial V k) : MvPolynomial V k :=
  MvPolynomial.weightedHomogeneousComponent w m p

theorem initial_ne_zero {w : V → ℤ} {m : ℤ} {p : MvPolynomial V k}
    (h : ∃ a, p.coeff a ≠ 0 ∧ Finsupp.weight w a = m) : initial w m p ≠ 0 := by
  obtain ⟨a, ha, haw⟩ := h
  intro he
  have hc := congrArg (fun q : MvPolynomial V k => q.coeff a) he
  apply ha
  simpa only [initial, MvPolynomial.coeff_weightedHomogeneousComponent, haw,
    ↓reduceIte, MvPolynomial.coeff_zero, Finsupp.zero_apply] using hc

/-- The lowest nonzero weighted homogeneous components multiply exactly. -/
theorem initial_mul {w : V → ℤ} {m n : ℤ} {p q : MvPolynomial V k}
    (hp : Bound w m p) (hq : Bound w n q) :
    initial w (m + n) (p * q) = initial w m p * initial w n q := by
  ext a
  rw [MvPolynomial.coeff_weightedHomogeneousComponent, MvPolynomial.coeff_mul,
    MvPolynomial.coeff_mul]
  by_cases haw : Finsupp.weight w a = m + n
  · rw [if_pos haw]
    apply Finset.sum_congr rfl
    rintro ⟨b, c⟩ hbc
    have hsum : b + c = a := Finset.mem_antidiagonal.mp hbc
    by_cases hb : p.coeff b = 0
    · simp [MvPolynomial.coeff_weightedHomogeneousComponent, hb]
    by_cases hc : q.coeff c = 0
    · simp [MvPolynomial.coeff_weightedHomogeneousComponent, hc]
    have hbw := hp b hb
    have hcw := hq c hc
    have hsumw : Finsupp.weight w b + Finsupp.weight w c = m + n := by
      rw [← map_add, hsum, haw]
    have hbm : Finsupp.weight w b = m := by omega
    have hcn : Finsupp.weight w c = n := by omega
    simp [MvPolynomial.coeff_weightedHomogeneousComponent, hbm, hcn]
  · rw [if_neg haw]
    symm
    apply Finset.sum_eq_zero
    rintro ⟨b, c⟩ hbc
    have hsum : b + c = a := Finset.mem_antidiagonal.mp hbc
    by_cases hbm : Finsupp.weight w b = m
    · have hcn : Finsupp.weight w c ≠ n := by
        intro hcn
        apply haw
        rw [← hsum, map_add, hbm, hcn]
      simp [MvPolynomial.coeff_weightedHomogeneousComponent, hcn]
    · simp [MvPolynomial.coeff_weightedHomogeneousComponent, hbm]

theorem minimum_mul [IsDomain k] {w : V → ℤ} {m n : ℤ} {p q : MvPolynomial V k}
    (hp : Bound w m p) (hq : Bound w n q)
    (hpm : ∃ a, p.coeff a ≠ 0 ∧ Finsupp.weight w a = m)
    (hqn : ∃ a, q.coeff a ≠ 0 ∧ Finsupp.weight w a = n) :
    ∃ a, (p * q).coeff a ≠ 0 ∧ Finsupp.weight w a = m + n := by
  have hn : initial w (m + n) (p * q) ≠ 0 := by
    rw [initial_mul hp hq]
    exact mul_ne_zero (initial_ne_zero hpm) (initial_ne_zero hqn)
  obtain ⟨a, ha⟩ := MvPolynomial.support_nonempty.mpr hn
  have hc := MvPolynomial.mem_support_iff.mp ha
  rw [MvPolynomial.coeff_weightedHomogeneousComponent] at hc
  split_ifs at hc with haw
  · exact ⟨a, hc, haw⟩
  · exact (hc rfl).elim

theorem minimum_pow [IsDomain k] {w : V → ℤ} {m : ℤ} {p : MvPolynomial V k}
    (hp : Bound w m p) (hpm : ∃ a, p.coeff a ≠ 0 ∧ Finsupp.weight w a = m) (n : ℕ) :
    ∃ a, (p ^ n).coeff a ≠ 0 ∧ Finsupp.weight w a = (n : ℤ) * m := by
  induction n with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨a, ha, haw⟩ := minimum_mul (hp.pow n) hp ih hpm
    exact ⟨a, by simpa only [pow_succ] using ha, by
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using haw⟩

end CommAlg.Weight
