import CommAlg.Polymatroid.PowerShiftSpanning

/-!
# The exact threshold is the least actual Rees generation bound

A coefficient of a minimal module monomial cannot be created by multiplying
module elements in which that coefficient is zero. This gives an intrinsic
obstruction to generation in any smaller Rees degrees.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V k : Type*} [Fintype V] [DecidableEq V] [CommRing k] [Nontrivial k]

theorem monomial_mem_powerShiftPiece_of_coeff (ρ : RankFunction V) (i s : ℕ)
    {f : MvPolynomial V k} (hf : f ∈ powerShiftPiece ρ i s) {a : Exponent V}
    (ha : f.coeff a ≠ 0) : MvPolynomial.monomial a (1 : k) ∈ powerShiftPiece ρ i s := by
  by_cases hs : s = 0
  · simp only [hs, powerShiftPiece_zero, Submodule.mem_bot] at hf
    simp [hf] at ha
  · rw [powerShiftPiece_pos ρ i (by omega)] at hf ⊢
    exact (mem_rankShiftIdeal_iff_coeff _ _ f).mp hf a (MvPolynomial.mem_support_iff.mpr ha)

theorem monomial_mem_rankIdeal_power_of_coeff (ρ : RankFunction V) (s : ℕ)
    {f : MvPolynomial V k} (hf : f ∈ (rankIdeal k ρ) ^ s) {a : Exponent V}
    (ha : f.coeff a ≠ 0) : MvPolynomial.monomial a (1 : k) ∈ (rankIdeal k ρ) ^ s := by
  rw [← rankIdeal_scale] at hf ⊢
  exact (monomial_mem_iff (rankBases (RankFunction.scale s ρ)) a).mpr
    ((mem_monomialIdeal_iff _ f).mp hf a (MvPolynomial.mem_support_iff.mpr ha))

def reesCoefficient (ρ : RankFunction V) (s : ℕ) (a : Exponent V)
    (p : reesAlgebra (rankIdeal k ρ)) : k := (p.val.coeff s).coeff a

@[simp] theorem reesCoefficient_zero (ρ : RankFunction V) (s : ℕ) (a : Exponent V) :
    reesCoefficient (k := k) ρ s a 0 = 0 := by simp [reesCoefficient]

@[simp] theorem reesCoefficient_add (ρ : RankFunction V) (s : ℕ) (a : Exponent V)
    (p q : reesAlgebra (rankIdeal k ρ)) :
    reesCoefficient ρ s a (p + q) = reesCoefficient ρ s a p + reesCoefficient ρ s a q := by
  simp [reesCoefficient]

theorem minimalShiftRees_coefficient_mul_zero (ρ : RankFunction V) (i s : ℕ)
    (a : Exponent V) (hmin : IsMinimalShiftReesMonomial (k := k) ρ i s a)
    (p : reesAlgebra (rankIdeal k ρ)) (hp : p ∈ shiftReesIdeal ρ i)
    (hz : reesCoefficient ρ s a p = 0) (r : reesAlgebra (rankIdeal k ρ)) :
    reesCoefficient ρ s a (r * p) = 0 := by
  change ((r.val * p.val).coeff s).coeff a = 0
  rw [Polynomial.coeff_mul, MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  rintro ⟨n, t⟩ hnt
  have hntEq : n + t = s := mem_antidiagonal.mp hnt
  rw [MvPolynomial.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨c, b⟩ hcb
  have hcbEq : c + b = a := mem_antidiagonal.mp hcb
  by_cases hr : (r.val.coeff n).coeff c = 0
  · simp [hr]
  by_cases hpb : (p.val.coeff t).coeff b = 0
  · simp [hpb]
  have hrMon := monomial_mem_rankIdeal_power_of_coeff ρ n (r.property n) hr
  have hpMon := monomial_mem_powerShiftPiece_of_coeff ρ i t (hp t) hpb
  have hba : b ≤ a := hcbEq ▸ le_add_left le_rfl
  have hquot : MvPolynomial.monomial (a - b) (1 : k) ∈ (rankIdeal k ρ) ^ (s - t) := by
    have haSub : a - b = c := by rw [← hcbEq, add_tsub_cancel_right]
    rw [haSub, show s - t = n by omega]
    exact hrMon
  obtain ⟨ht, hb⟩ := hmin.2 t b (by omega) hba hpMon hquot
  subst t
  subst b
  exact (hpb hz).elim

theorem coefficient_zero_on_span_bounded (ρ : RankFunction V) (i s q : ℕ)
    (a : Exponent V) (hmin : IsMinimalShiftReesMonomial (k := k) ρ i s a)
    (hqs : q < s) (p : reesAlgebra (rankIdeal k ρ))
    (hp : p ∈ Ideal.span (boundedShiftReesSet ρ i q)) :
    reesCoefficient ρ s a p = 0 := by
  have h : p ∈ shiftReesIdeal ρ i ∧ reesCoefficient ρ s a p = 0 := by
    induction hp using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨t, b, hb, ht, rfl⟩ := hp
      refine ⟨shiftReesMonomial_mem ρ i t b hb, ?_⟩
      have hst : s ≠ t := by omega
      simp [reesCoefficient, shiftReesMonomial, Polynomial.coeff_monomial, hst, Ne.symm hst]
    | zero => exact ⟨Ideal.zero_mem _, by simp⟩
    | add p r hp hr ihp ihr =>
      exact ⟨Ideal.add_mem _ ihp.1 ihr.1, by simp [ihp.2, ihr.2]⟩
    | smul r p hp ih =>
      exact ⟨Ideal.mul_mem_left _ r ih.1,
        minimalShiftRees_coefficient_mul_zero ρ i s a hmin p ih.1 ih.2 r⟩
  exact h.2

/-- No lower-degree monomial generating set can generate a minimal monomial
in a larger Rees degree. The obstruction is a literal polynomial coefficient. -/
theorem minimalShiftRees_notMem_span_bounded (ρ : RankFunction V) (i s q : ℕ)
    (a : Exponent V) (hmin : IsMinimalShiftReesMonomial (k := k) ρ i s a)
    (hqs : q < s) :
    shiftReesMonomial ρ i s a hmin.1 ∉ Ideal.span (boundedShiftReesSet ρ i q) := by
  intro hp
  have hz := coefficient_zero_on_span_bounded ρ i s q a hmin hqs _ hp
  simpa [reesCoefficient, shiftReesMonomial] using hz

/-- Theorem 4.4's exact least generation bound, stated as equality with an
actual ideal span in the ordinary Rees algebra. -/
theorem shiftReesIdeal_generation_bound_iff (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi0 : 0 < i) (hi : i ≤ eventualOffset ρ univ) (q : ℕ) :
    shiftReesIdeal (k := k) ρ i = Ideal.span (boundedShiftReesSet ρ i q) ↔
      globalPowerThreshold ρ i ≤ q := by
  constructor
  · intro he
    by_contra hq
    have hq' : q < globalPowerThreshold ρ i := by omega
    obtain ⟨a, ha⟩ := (minimalShiftRees_degree_iff (k := k) ρ hρ i hi0 hi
      (globalPowerThreshold ρ i)).mpr ⟨powerThreshold_le_global ρ i univ, le_rfl⟩
    have hp := shiftReesMonomial_mem ρ i (globalPowerThreshold ρ i) a ha.1
    rw [he] at hp
    exact minimalShiftRees_notMem_span_bounded ρ i _ q a ha hq' hp
  · intro hq
    apply le_antisymm
    · rw [shiftReesIdeal_generated_at_threshold ρ hρ i hi0 hi]
      apply Ideal.span_mono
      rintro p ⟨s, a, ha, hs, rfl⟩
      exact ⟨s, a, ha, hs.trans hq, rfl⟩
    · apply Ideal.span_le.mpr
      rintro p ⟨s, a, ha, _, rfl⟩
      exact shiftReesMonomial_mem ρ i s a ha

end CommAlg.Polymatroid
