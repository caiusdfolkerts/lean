module
public import Lean.Elab.Tactic.Omega
public import Lean.Elab.Tactic.NormCast
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Ext

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! Generic integer weights and ideal integral dependence.
These foundations are reused from the homological-shifts verification;
their mathematical source bodies are unchanged. The provenance manifest
records their earlier acceptance by the ordinary Lake build. -/

/- Recovered exact body: CommAlg.IntegralClosure.Weight -/
section
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
end -- source-file noncomputable section
end -- recovered component

/- Recovered exact body: CommAlg.IntegralClosure.Ideal -/
section
/-! # Integral closure of ideals cut out by integer linear weights

Mathlib's ring-integrality theory does not yet define integrality over an
ideal.  The definition here is the usual monic equation
`x^n + ∑_{i<n} c_i*x^i = 0`, with `c_i ∈ I^(n-i)`.
-/

noncomputable section

namespace CommAlg

open Classical Finset

variable {R : Type*} [CommRing R]

/-- The standard monic-equation definition of integrality over an ideal. -/
def IntegralOverIdeal (I : Ideal R) (x : R) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∃ c : ℕ → R,
    (∀ i < n, c i ∈ I ^ (n - i)) ∧ x ^ n + ∑ i ∈ Finset.range n, c i * x ^ i = 0

def IsIntegrallyClosedIdeal (I : Ideal R) : Prop :=
  ∀ x : R, IntegralOverIdeal I x → x ∈ I

theorem integralOverIdeal_of_mem {I : Ideal R} {x : R} (hx : x ∈ I) :
    IntegralOverIdeal I x := by
  refine ⟨1, by omega, fun _ => -x, ?_, ?_⟩
  · intro i hi
    have he : i = 0 := by omega
    simpa [he] using I.neg_mem hx
  · simp

namespace Weight

variable {V k : Type*} [DecidableEq V] [CommRing k]

def cutIdeal (f : R →+* MvPolynomial V k) (w : V → ℤ)
    (h0 : ∀ x, Bound w 0 (f x)) (c : ℤ) : Ideal R where
  carrier := {x | Bound w c (f x)}
  zero_mem' := by simpa using bound_zero w c
  add_mem' hx hy := by simpa using hx.add hy
  smul_mem' r x hx := by
    change Bound w c (f (r * x))
    simpa only [smul_eq_mul, map_mul, zero_add] using (h0 r).mul hx

@[simp] theorem mem_cutIdeal (f : R →+* MvPolynomial V k) (w : V → ℤ)
    (h0 : ∀ x, Bound w 0 (f x)) (c : ℤ) (x : R) :
    x ∈ cutIdeal f w h0 c ↔ Bound w c (f x) := Iff.rfl

theorem bound_of_mem_pow (f : R →+* MvPolynomial V k) (w : V → ℤ)
    (h0 : ∀ x, Bound w 0 (f x)) (I : Ideal R) (c : ℤ)
    (hI : ∀ x ∈ I, Bound w c (f x)) (n : ℕ) {x : R} (hx : x ∈ I ^ n) :
    Bound w ((n : ℤ) * c) (f x) := by
  induction n generalizing x with
  | zero => simpa using h0 x
  | succ n ih =>
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on (C := fun y => Bound w ((↑(n + 1) : ℤ) * c) (f y)) hx ?_ ?_
    · intro a ha b hb
      have h := (ih ha).mul (hI b hb)
      simpa only [map_mul, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using h
    · intro a b ha hb
      simpa only [map_add] using ha.add hb

theorem bound_of_integral [IsDomain k] (f : R →+* MvPolynomial V k) (w : V → ℤ)
    (h0 : ∀ x, Bound w 0 (f x)) (I : Ideal R) (c : ℤ)
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
  have hsum : Bound w ((n : ℤ) * m + 1)
      (∑ i ∈ Finset.range n, f (b i) * (f x) ^ i) := by
    apply bound_sum
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    have hbnd := (bound_of_mem_pow f w h0 I c hI (n - i) (hb i hin)).mul (hm.pow i)
    apply hbnd.mono
    have hni : ((n - i : ℕ) : ℤ) + i = n := by
      exact_mod_cast Nat.sub_add_cancel (Nat.le_of_lt hin)
    have hpos : (0 : ℤ) < ((n - i : ℕ) : ℤ) := by
      exact_mod_cast Nat.sub_pos_of_lt hin
    have hprod : (0 : ℤ) < ((n - i : ℕ) : ℤ) * (c - m) := mul_pos hpos (by omega)
    have hprod1 : (1 : ℤ) ≤ ((n - i : ℕ) : ℤ) * (c - m) := by omega
    rw [← hni]
    nlinarith
  have hsumcoeff : (∑ i ∈ Finset.range n, f (b i) * (f x) ^ i).coeff a = 0 := by
    by_contra hne
    have h := hsum a hne
    rw [haw] at h
    omega
  have heq' : (f x) ^ n + ∑ i ∈ Finset.range n, f (b i) * (f x) ^ i = 0 := by
    simpa only [map_add, map_pow, map_sum, map_mul, map_zero] using congrArg f heq
  have hc := congrArg (fun p : MvPolynomial V k => p.coeff a) heq'
  apply hap
  simpa only [MvPolynomial.coeff_add, hsumcoeff, add_zero,
    MvPolynomial.coeff_zero, Finsupp.zero_apply] using hc

theorem cutIdeal_integrallyClosed [IsDomain k] (f : R →+* MvPolynomial V k) (w : V → ℤ)
    (h0 : ∀ x, Bound w 0 (f x)) (c : ℤ) : IsIntegrallyClosedIdeal (cutIdeal f w h0 c) := by
  intro x hx
  exact bound_of_integral f w h0 _ c (fun _ h => h) hx

/-- An arbitrary intersection of linear-weight cuts is integrally closed.
The coefficient ring may be any domain, in particular any field. -/
theorem integrallyClosed_of_weight_bounds [IsDomain k] {J : Type*}
    (f : R →+* MvPolynomial V k) (w : J → V → ℤ) (c : J → ℤ)
    (h0 : ∀ j x, Bound (w j) 0 (f x)) (I : Ideal R)
    (hmem : ∀ x, x ∈ I ↔ ∀ j, Bound (w j) (c j) (f x)) : IsIntegrallyClosedIdeal I := by
  intro x hx
  apply (hmem x).mpr
  intro j
  exact bound_of_integral f (w j) (h0 j) I (c j) (fun y hy => (hmem y).mp hy j) hx

end Weight

end CommAlg
end -- source-file noncomputable section
end -- recovered component
