import Characterizations.PrimePowers

/-! # The coordinate ideals in the intersection formula are actually prime -/
noncomputable section
namespace Characterizations
open Classical CommAlg CommAlg.Polymatroid MvPolynomial
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (k : Type*) [CommRing k] [IsDomain k]

theorem coordinatePrime_isPrime (U : Finset V) : (coordinatePrime k U).IsPrime := by
  refine ⟨?_, ?_⟩
  · intro ht
    have h : (1 : MvPolynomial V k) ∈ coordinatePrime k U := by rw [ht]; trivial
    have hb := coordinatePrime_weight k U h (0 : Exponent V) (by simp)
    simp [weight_subsetWeight, subsetSum] at hb
  · intro f g hfg
    by_contra hn
    push_neg at hn
    have hzero (p : MvPolynomial V k) (hp : p ∉ coordinatePrime k U) :
        ∃ a, p.coeff a ≠ 0 ∧ Finsupp.weight (subsetWeight U) a = 0 := by
      have hn : p ≠ 0 := fun he => hp (he ▸ (coordinatePrime k U).zero_mem)
      obtain ⟨m, hm, a, ha, he⟩ := Weight.exists_minimum (subsetWeight U) hn
      have hm0 : 0 ≤ m := he ▸ subsetWeight_nonnegative U p a ha
      have hm1 : m < 1 := by
        by_contra h
        apply hp
        have hb : Weight.Bound (subsetWeight U) (1 : ℤ) p := hm.mono (by omega)
        simpa only [pow_one] using (mem_coordinatePrime_pow_iff_weight k U 1 p).mpr hb
      exact ⟨a, ha, by omega⟩
    obtain ⟨a, ha, he⟩ := Weight.minimum_mul (subsetWeight_nonnegative U f)
      (subsetWeight_nonnegative U g) (hzero f hn.1) (hzero g hn.2)
    have hb := coordinatePrime_weight k U hfg a ha
    omega

end Characterizations
