module

public import Ellipsoid.RootMatchingBounds
public import Ellipsoid.Semiaxes

@[expose] public section

noncomputable section

open Polynomial Set
open scoped BigOperators

namespace EllipsoidVerification

theorem realRootCoefficients_eq_implies_perm {n : ℕ} {a b : Fin n → ℝ}
    (h : realRootCoefficients a = realRootCoefficients b) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, a i = b (σ i) := by
  have hp : realRootPolynomial a = realRootPolynomial b := by
    rw [← monicOfCoeff_realRootCoefficients a, ← monicOfCoeff_realRootCoefficients b, h]
  have hr := congrArg Polynomial.roots hp
  simp only [realRootPolynomial, Polynomial.roots_prod_X_sub_C_map] at hr
  have hr' : Finset.univ.val.map a = Finset.univ.val.map b := by
    apply Multiset.map_injective Complex.ofReal_injective
    simpa only [Multiset.map_map, Function.comp_def] using hr
  exact exists_perm_of_multiset_map_eq hr'

/-- Uniform root matching with the optimal exponent on every bounded real
root family. This controls multiplicities and imposes no separation of the
roots. The constants depend only on the degree and the root bound. -/
theorem uniform_real_root_holder {n : ℕ} (hn : 0 < n) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : Fin n → ℝ,
      ‖a‖ ≤ B → ‖b‖ ≤ B →
      ∃ σ : Equiv.Perm (Fin n), ∀ i,
        |a i - b (σ i)| ≤ C *
          ‖realRootCoefficients a - realRootCoefficients b‖ ^ (1 / (n : ℝ)) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Fin n → ℝ) B).exists_bound_of_continuousOn
    (continuous_realRootCoefficients n).continuousOn
  let R := max M 0
  have hR : 0 ≤ R := le_max_right _ _
  have hcoeff (a : Fin n → ℝ) (ha : ‖a‖ ≤ B) : ‖realRootCoefficients a‖ ≤ R :=
    (hM a (by simpa using ha)).trans (le_max_left _ _)
  let H : ℝ := n * (R + 1) ^ (n - 1)
  have hH : 0 < H := mul_pos (Nat.cast_pos.mpr hn) (pow_pos (by linarith) _)
  let C : ℝ := 2 * n * (2 * H) ^ (1 / (n : ℝ))
  have hC : 0 < C := mul_pos (by positivity)
    (Real.rpow_pos_of_pos (by positivity) _)
  refine ⟨C, hC, ?_⟩
  intro a b ha hb
  let δ : ℝ := ‖realRootCoefficients a - realRootCoefficients b‖
  by_cases hδ : δ = 0
  · obtain ⟨σ, hσ⟩ := realRootCoefficients_eq_implies_perm
      (sub_eq_zero.mp (norm_eq_zero.mp hδ))
    refine ⟨σ, fun i => ?_⟩
    rw [hσ i, sub_self, abs_zero]
    positivity
  have hδpos : 0 < δ := (norm_nonneg _).lt_of_ne (Ne.symm hδ)
  let ρ : ℝ := (2 * H * δ) ^ (1 / (n : ℝ))
  have hρ : 0 < ρ := Real.rpow_pos_of_pos (by positivity) _
  have hρpow : ρ ^ n = 2 * H * δ := by
    have hbase : 0 ≤ 2 * H * δ := by positivity
    simpa only [ρ, one_div] using Real.rpow_inv_natCast_pow hbase hn.ne'
  obtain ⟨σ, hσ⟩ := roots_match_of_coefficient_bound hn a b hR hρ.le
    (hcoeff a ha) (hcoeff b hb) (by
      change H * δ < ρ ^ n
      rw [hρpow]
      nlinarith [mul_pos hH hδpos])
  refine ⟨σ, fun i => (hσ i).trans_eq ?_⟩
  change 2 * n * (2 * H * δ) ^ (1 / (n : ℝ)) =
    (2 * n * (2 * H) ^ (1 / (n : ℝ))) * δ ^ (1 / (n : ℝ))
  rw [Real.mul_rpow (by positivity) hδpos.le]
  ring

end EllipsoidVerification
