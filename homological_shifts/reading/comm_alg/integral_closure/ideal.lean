import CommAlg.IntegralClosure.Weight

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
