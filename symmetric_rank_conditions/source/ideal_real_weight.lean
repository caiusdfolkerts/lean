module
public import ideal_integrality_foundation
public import Mathlib.Data.Real.Basic

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-!
# Real weighted filtrations and integral dependence

The weights are real numbers independent of the characteristic of the
coefficient domain.  All minima are over finite polynomial supports.
The least-weight initial form of a nonzero product is the product of its
least-weight forms; this prevents an integral equation from improving the
least weight.  No valuation theorem is assumed.
-/

noncomputable section
namespace CommAlg.RealWeight

open Classical Finset
open scoped Pointwise

variable {V k : Type*} [DecidableEq V] [CommRing k]

def Bound (w : V → ℝ) (c : ℝ) (p : MvPolynomial V k) : Prop :=
  ∀ a, p.coeff a ≠ 0 → c ≤ Finsupp.weight w a

theorem bound_zero (w : V → ℝ) (c : ℝ) : Bound w c (0 : MvPolynomial V k) := by
  intro a ha
  simp at ha

theorem Bound.mono {w : V → ℝ} {c d : ℝ} {p : MvPolynomial V k}
    (hp : Bound w c p) (hd : d ≤ c) : Bound w d p := fun a ha => hd.trans (hp a ha)

theorem Bound.add {w : V → ℝ} {c : ℝ} {p q : MvPolynomial V k}
    (hp : Bound w c p) (hq : Bound w c q) : Bound w c (p + q) := by
  intro a ha
  by_cases hpa : p.coeff a = 0
  · apply hq a
    simpa only [MvPolynomial.coeff_add, hpa, zero_add] using ha
  · exact hp a hpa

theorem Bound.neg {w : V → ℝ} {c : ℝ} {p : MvPolynomial V k}
    (hp : Bound w c p) : Bound w c (-p) := by
  intro a ha
  exact hp a (by simpa using ha)

theorem Bound.mul {w : V → ℝ} {c d : ℝ} {p q : MvPolynomial V k}
    (hp : Bound w c p) (hq : Bound w d q) : Bound w (c + d) (p * q) := by
  intro a ha
  have hm := MvPolynomial.support_mul p q (MvPolynomial.mem_support_iff.mpr ha)
  obtain ⟨b, hb, e, he, rfl⟩ := Finset.mem_add.mp hm
  rw [map_add]
  exact add_le_add (hp b (MvPolynomial.mem_support_iff.mp hb))
    (hq e (MvPolynomial.mem_support_iff.mp he))

theorem bound_one (w : V → ℝ) : Bound w 0 (1 : MvPolynomial V k) := by
  intro a ha
  by_cases h : a = 0
  · subst a; simp
  · simp [MvPolynomial.coeff_one, h, Ne.symm h] at ha

theorem Bound.pow {w : V → ℝ} {c : ℝ} {p : MvPolynomial V k}
    (hp : Bound w c p) (n : ℕ) : Bound w ((n : ℝ) * c) (p ^ n) := by
  induction n with
  | zero => simpa using bound_one w
  | succ n ih =>
    simpa only [pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using ih.mul hp

theorem bound_sum {ι : Type*} (w : V → ℝ) (c : ℝ) (s : Finset ι)
    (f : ι → MvPolynomial V k) (hf : ∀ i ∈ s, Bound w c (f i)) :
    Bound w c (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using bound_zero w c
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem exists_minimum (w : V → ℝ) {p : MvPolynomial V k} (hp : p ≠ 0) :
    ∃ m : ℝ, Bound w m p ∧ ∃ a, p.coeff a ≠ 0 ∧ Finsupp.weight w a = m := by
  have hS := MvPolynomial.support_nonempty.mpr hp
  let m := p.support.inf' hS (Finsupp.weight w)
  obtain ⟨a, ha, he⟩ := Finset.exists_mem_eq_inf' hS (Finsupp.weight w)
  refine ⟨m, ?_, a, MvPolynomial.mem_support_iff.mp ha, he.symm⟩
  intro b hb
  exact Finset.inf'_le _ (MvPolynomial.mem_support_iff.mpr hb)

abbrev initial (w : V → ℝ) (m : ℝ) (p : MvPolynomial V k) : MvPolynomial V k :=
  MvPolynomial.weightedHomogeneousComponent w m p

theorem initial_ne_zero {w : V → ℝ} {m : ℝ} {p : MvPolynomial V k}
    (h : ∃ a, p.coeff a ≠ 0 ∧ Finsupp.weight w a = m) : initial w m p ≠ 0 := by
  obtain ⟨a, ha, haw⟩ := h
  intro he
  have hc := congrArg (fun q : MvPolynomial V k => q.coeff a) he
  apply ha
  simpa only [initial, MvPolynomial.coeff_weightedHomogeneousComponent, haw,
    ↓reduceIte, MvPolynomial.coeff_zero, Finsupp.zero_apply] using hc

/-- The lowest nonzero weighted homogeneous components multiply exactly. -/
theorem initial_mul {w : V → ℝ} {m n : ℝ} {p q : MvPolynomial V k}
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
    have hbm : Finsupp.weight w b = m := by linarith
    have hcn : Finsupp.weight w c = n := by linarith
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

theorem minimum_mul [IsDomain k] {w : V → ℝ} {m n : ℝ} {p q : MvPolynomial V k}
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

theorem minimum_pow [IsDomain k] {w : V → ℝ} {m : ℝ} {p : MvPolynomial V k}
    (hp : Bound w m p) (hpm : ∃ a, p.coeff a ≠ 0 ∧ Finsupp.weight w a = m) (n : ℕ) :
    ∃ a, (p ^ n).coeff a ≠ 0 ∧ Finsupp.weight w a = (n : ℝ) * m := by
  induction n with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨a, ha, haw⟩ := minimum_mul (hp.pow n) hp ih hpm
    exact ⟨a, by simpa only [pow_succ] using ha, by
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using haw⟩

end CommAlg.RealWeight

namespace CommAlg.RealWeight

variable {R : Type*} [CommRing R]

variable {V k : Type*} [DecidableEq V] [CommRing k]

def cutIdeal (f : R →+* MvPolynomial V k) (w : V → ℝ)
    (h0 : ∀ x, Bound w 0 (f x)) (c : ℝ) : Ideal R where
  carrier := {x | Bound w c (f x)}
  zero_mem' := by simpa using bound_zero w c
  add_mem' hx hy := by simpa using hx.add hy
  smul_mem' r x hx := by
    change Bound w c (f (r * x))
    simpa only [smul_eq_mul, map_mul, zero_add] using (h0 r).mul hx

@[simp] theorem mem_cutIdeal (f : R →+* MvPolynomial V k) (w : V → ℝ)
    (h0 : ∀ x, Bound w 0 (f x)) (c : ℝ) (x : R) :
    x ∈ cutIdeal f w h0 c ↔ Bound w c (f x) := Iff.rfl

theorem bound_of_mem_pow (f : R →+* MvPolynomial V k) (w : V → ℝ)
    (h0 : ∀ x, Bound w 0 (f x)) (I : Ideal R) (c : ℝ)
    (hI : ∀ x ∈ I, Bound w c (f x)) (n : ℕ) {x : R} (hx : x ∈ I ^ n) :
    Bound w ((n : ℝ) * c) (f x) := by
  induction n generalizing x with
  | zero => simpa using h0 x
  | succ n ih =>
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on (C := fun y => Bound w ((↑(n + 1) : ℝ) * c) (f y)) hx ?_ ?_
    · intro a ha b hb
      have h := (ih ha).mul (hI b hb)
      simpa only [map_mul, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using h
    · intro a b ha hb
      simpa only [map_add] using ha.add hb

theorem bound_of_integral [IsDomain k] (f : R →+* MvPolynomial V k) (w : V → ℝ)
    (h0 : ∀ x, Bound w 0 (f x)) (I : Ideal R) (c : ℝ)
    (hI : ∀ x ∈ I, Bound w c (f x)) {x : R} (hx : IntegralOverIdeal I x) :
    Bound w c (f x) := by
  by_contra hn
  simp only [Bound, not_forall, not_le] at hn
  obtain ⟨a₀, ha₀, hbad⟩ := hn
  have hfx : f x ≠ 0 := by intro he; simp [he] at ha₀
  obtain ⟨m, hm, hmin⟩ := exists_minimum w hfx
  have hmc : m < c := (hm a₀ ha₀).trans_lt hbad
  obtain ⟨n, hn, b, hb, heq⟩ := hx
  obtain ⟨a, hap, haw⟩ := minimum_pow hm hmin n
  have hsum : Bound w ((n : ℝ) * m + (c - m))
      (∑ i ∈ Finset.range n, f (b i) * (f x) ^ i) := by
    apply bound_sum
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    have hbnd := (bound_of_mem_pow f w h0 I c hI (n - i) (hb i hin)).mul (hm.pow i)
    apply hbnd.mono
    have hni : ((n - i : ℕ) : ℝ) + i = n := by
      exact_mod_cast Nat.sub_add_cancel (Nat.le_of_lt hin)
    have hpos : (0 : ℝ) < ((n - i : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_pos_of_lt hin
    have hprod : (0 : ℝ) < ((n - i : ℕ) : ℝ) * (c - m) := mul_pos hpos (by linarith)
    have hone : (1 : ℝ) ≤ ((n - i : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.sub_pos_of_lt hin)
    have hprod1 : c - m ≤ ((n - i : ℕ) : ℝ) * (c - m) := by
      nlinarith
    rw [← hni]
    nlinarith
  have hsumcoeff : (∑ i ∈ Finset.range n, f (b i) * (f x) ^ i).coeff a = 0 := by
    by_contra hne
    have h := hsum a hne
    rw [haw] at h
    linarith
  have heq' : (f x) ^ n + ∑ i ∈ Finset.range n, f (b i) * (f x) ^ i = 0 := by
    simpa only [map_add, map_pow, map_sum, map_mul, map_zero] using congrArg f heq
  have hc := congrArg (fun p : MvPolynomial V k => p.coeff a) heq'
  apply hap
  simpa only [MvPolynomial.coeff_add, hsumcoeff, add_zero,
    MvPolynomial.coeff_zero, Finsupp.zero_apply] using hc

theorem cutIdeal_integrallyClosed [IsDomain k] (f : R →+* MvPolynomial V k) (w : V → ℝ)
    (h0 : ∀ x, Bound w 0 (f x)) (c : ℝ) : IsIntegrallyClosedIdeal (cutIdeal f w h0 c) := by
  intro x hx
  exact bound_of_integral f w h0 _ c (fun _ h => h) hx

/-- An arbitrary intersection of linear-weight cuts is integrally closed.
The coefficient ring may be any domain, in particular any field. -/
theorem integrallyClosed_of_weight_bounds [IsDomain k] {J : Type*}
    (f : R →+* MvPolynomial V k) (w : J → V → ℝ) (c : J → ℝ)
    (h0 : ∀ j x, Bound (w j) 0 (f x)) (I : Ideal R)
    (hmem : ∀ x, x ∈ I ↔ ∀ j, Bound (w j) (c j) (f x)) : IsIntegrallyClosedIdeal I := by
  intro x hx
  apply (hmem x).mpr
  intro j
  exact bound_of_integral f (w j) (h0 j) I (c j) (fun y hy => (hmem y).mp hy j) hx

end CommAlg.RealWeight
end
