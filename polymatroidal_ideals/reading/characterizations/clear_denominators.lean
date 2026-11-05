import Characterizations.RationalConvex
import Mathlib.Data.Rat.Lemmas

/-! # Exact denominator clearing for nonnegative rational convex combinations -/

noncomputable section
namespace Characterizations
universe u
open CommAlg.Polymatroid Finset
open scoped BigOperators

theorem nonnegative_rational_common_denominator {I : Type*} [Fintype I]
    (q : I → ℚ) (hq : ∀ i, 0 ≤ q i) :
    ∃ N : ℕ, 0 < N ∧ ∃ m : I → ℕ, ∀ i, (m i : ℚ) = (N : ℚ) * q i := by
  classical
  let N : ℕ := ∏ i, (q i).den
  have hN : 0 < N := Finset.prod_pos (fun i _ => (q i).den_pos)
  let m : I → ℕ := fun i => (q i).num.toNat * (N / (q i).den)
  refine ⟨N, hN, m, ?_⟩
  intro i
  have hdiv : (q i).den ∣ N := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have he : (q i).den * (N / (q i).den) = N := Nat.mul_div_cancel' hdiv
  have hnum : ((q i).num.toNat : ℚ) = ((q i).num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr (hq i))
  have hval : ((q i).num : ℚ) = q i * ((q i).den : ℚ) :=
    (div_eq_iff (show ((q i).den : ℚ) ≠ 0 by exact_mod_cast (q i).den_ne_zero)).mp
      (q i).num_div_den
  have he' : ((q i).den : ℚ) * (N / (q i).den : ℕ) = N := by exact_mod_cast he
  change ((q i).num.toNat * (N / (q i).den) : ℕ) = (N : ℚ) * q i
  rw [Nat.cast_mul, hnum, hval, mul_assoc, he', mul_comm]

variable {V : Type u} [Fintype V] [DecidableEq V]

theorem scaled_sum_of_mem_convexHull (B : Family V) (a : Exponent V)
    (ha : realExponent a ∈ convexHull ℝ (realExponent '' (B : Set (Exponent V)))) :
    ∃ (N : ℕ) (_ : 0 < N) (J : Type u) (_ : Fintype J)
      (p : J → Exponent V) (m : J → ℕ),
      (∀ j, p j ∈ B) ∧ (∑ j, m j = N) ∧ N • a = ∑ j, m j • p j := by
  classical
  obtain ⟨J, hJ, p, q, hp, hq, hsum, hcomb⟩ := rational_combination_of_mem_convexHull B a ha
  letI : Fintype J := hJ
  obtain ⟨N, hN, m, hm⟩ := nonnegative_rational_common_denominator q hq
  have hsum' : ∑ j, m j = N := by
    have h : (∑ j, (m j : ℚ)) = N := by
      simp_rw [hm]
      rw [← Finset.mul_sum, hsum, mul_one]
    exact_mod_cast h
  refine ⟨N, hN, J, hJ, p, m, hp, hsum', ?_⟩
  ext v
  have h : (N : ℚ) * (a v : ℚ) = ∑ j, (m j : ℚ) * (p j v : ℚ) := by
    simp_rw [hm, mul_assoc]
    rw [← Finset.mul_sum, hcomb]
  have hn : N * a v = ∑ j, m j * p j v := by exact_mod_cast h
  simpa only [Finsupp.smul_apply, Finsupp.finsetSum_apply, smul_eq_mul] using hn

end Characterizations
