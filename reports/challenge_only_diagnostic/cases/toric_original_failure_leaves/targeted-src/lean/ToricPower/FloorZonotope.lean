module

public import ToricPower.ZonotopeFacets

@[expose] public section
noncomputable section

open Set Matrix
open scoped BigOperators Pointwise

namespace ToricPower

variable {n s : ℕ}

theorem rayRelation_dot_rayMap (A : Matrix (Fin s) (Fin n) ℤ)
    (h : Fin s → ℤ) (hh : h ∈ rayRelations A) (u : Fin n → ℤ) :
    ∑ i, h i * rayMap A u i = 0 := by
  change (∑ i, h i * ∑ j, A i j * u j) = 0
  calc
    _ = ∑ j, (∑ i, A i j * h i) * u j := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by simp [(mem_rayRelations A h).mp hh]

theorem circuit_bound_on_powerCoefficient (A : Matrix (Fin s) (Fin n) ℤ)
    (b : Fin s → ℤ) (ell : ℤ) (hell : 0 < ell) (u : Fin n → ℤ)
    (h : Fin s → ℤ) (hh : h ∈ rayRelations A) :
    ell * ((∑ i, h i * powerCoefficient A b ell u i) - cubeSupport h) ≤
      (∑ i, h i * b i) - cubeSupport h := by
  have hterm (i : Fin s) :
      ell * (h i * powerCoefficient A b ell u i) ≤
        h i * (b i + rayMap A u i) + (ell - 1) * max (-h i) 0 := by
    have hf := (Int.ediv_eq_iff_of_pos hell).mp
      (show (b i + rayMap A u i) / ell = powerCoefficient A b ell u i from rfl)
    by_cases hi : 0 ≤ h i
    · have hm := mul_le_mul_of_nonneg_left hf.1 hi
      rw [max_eq_right (neg_nonpos.mpr hi)]
      nlinarith [hm]
    · have hi' : h i ≤ 0 := by omega
      have hm := mul_le_mul_of_nonpos_left hf.2 hi'
      rw [max_eq_left (by omega : 0 ≤ -h i)]
      nlinarith [hm]
  have hs := Finset.sum_le_sum (fun i (_hi : i ∈ (Finset.univ : Finset (Fin s))) =>
    hterm i)
  have hz := rayRelation_dot_rayMap A h hh u
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, mul_add] at hs
  rw [hz, add_zero] at hs
  change ell * ((∑ i, h i * powerCoefficient A b ell u i) -
    ∑ i, max (-h i) 0) ≤ (∑ i, h i * b i) - ∑ i, max (-h i) 0
  nlinarith [hs]

/-- Every summand representative lies in the actual projected cube at precisely
the circuit threshold C_b used in Proposition 6.2. -/
theorem powerCoefficient_mem_zonotope (A : Matrix (Fin s) (Fin n) ℤ)
    (b : Fin s → ℤ) (ell : ℤ) (hell : (circuitBound A b : ℤ) ≤ ell)
    (u : Fin n → ℤ) :
    realDivisorClass A (powerCoefficient A b ell u) ∈ realZonotope A := by
  have hellpos : 0 < ell := lt_of_lt_of_le (by exact_mod_cast circuitBound_pos A b) hell
  rw [realDivisorClass_mem_zonotope_iff_circuits]
  intro h hh
  have hc := (mem_circuits A h).mp hh
  have hbound := circuit_bound_on_powerCoefficient A b ell hellpos u h hc.2.1
  have hstrict := circuitBound_strict A b hc
  have hlt : ell * ((∑ i, h i * powerCoefficient A b ell u i) - cubeSupport h) < ell :=
    lt_of_le_of_lt hbound (lt_of_lt_of_le hstrict hell)
  by_contra hn
  have hpos : 1 ≤ (∑ i, h i * powerCoefficient A b ell u i) - cubeSupport h := by omega
  nlinarith

end ToricPower

