module

public import Ellipsoid.RootMatchingTopology
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

noncomputable section

open Polynomial MeasureTheory Set Filter
open scoped BigOperators Topology

namespace EllipsoidVerification

def realRootPolynomial {n : ℕ} (a : Fin n → ℝ) : ℂ[X] :=
  ∏ i, (X - C (a i : ℂ))

def realRootCoefficients {n : ℕ} (a : Fin n → ℝ) : Fin n → ℂ :=
  fun i => (realRootPolynomial a).coeff i.val

theorem realRootPolynomial_monic {n : ℕ} (a : Fin n → ℝ) : (realRootPolynomial a).Monic :=
  monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _

theorem realRootPolynomial_natDegree {n : ℕ} (a : Fin n → ℝ) :
    (realRootPolynomial a).natDegree = n := by
  simp [realRootPolynomial, natDegree_prod_of_monic, monic_X_sub_C]

theorem monicOfCoeff_realRootCoefficients {n : ℕ} (a : Fin n → ℝ) :
    TauCeti.Polynomial.monicOfCoeff (realRootCoefficients a) = realRootPolynomial a :=
  TauCeti.Polynomial.monicOfCoeff_coeff (realRootPolynomial_monic a)
    (realRootPolynomial_natDegree a)

@[fun_prop] theorem continuous_realRootCoefficients (n : ℕ) :
    Continuous (realRootCoefficients (n := n)) := by
  apply continuous_pi
  intro i
  exact (TauCeti.Polynomial.continuous_coeff_prod_X_sub_C Finset.univ i.val).comp
    (continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j))

def rootHomotopy {n : ℕ} (c d : Fin n → ℂ) (t : Icc (0 : ℝ) 1) : ℂ[X] :=
  TauCeti.Polynomial.monicOfCoeff ((1 - (t : ℝ)) • c + (t : ℝ) • d)

theorem rootHomotopy_degree {n : ℕ} (c d : Fin n → ℂ) (t : Icc (0 : ℝ) 1) :
    (rootHomotopy c d t).degree = n := by
  unfold rootHomotopy
  rw [Polynomial.degree_eq_natDegree (TauCeti.Polynomial.monic_monicOfCoeff _).ne_zero]
  simp only [TauCeti.Polynomial.natDegree_monicOfCoeff]

@[fun_prop] theorem continuous_rootHomotopy_coeff {n : ℕ} (c d : Fin n → ℂ) (k : ℕ) :
    Continuous (fun t : Icc (0 : ℝ) 1 => (rootHomotopy c d t).coeff k) := by
  exact (TauCeti.Polynomial.continuous_coeff_monicOfCoeff k).comp (by fun_prop)

theorem root_norm_le_coefficient_norm_add_one {n : ℕ} (c : Fin n → ℂ)
    {z : ℂ} (hz : (TauCeti.Polynomial.monicOfCoeff c).IsRoot z) :
    ‖z‖ ≤ ‖c‖ + 1 := by
  have hm := TauCeti.Polynomial.monic_monicOfCoeff c
  have hroot := hz.norm_lt_cauchyBound hm.ne_zero
  have hbound : (TauCeti.Polynomial.monicOfCoeff c).cauchyBound ≤ ‖c‖₊ + 1 := by
    rw [Polynomial.cauchyBound, hm.leadingCoeff, nnnorm_one, div_one,
      TauCeti.Polynomial.natDegree_monicOfCoeff]
    refine add_le_add ?_ (le_refl 1)
    apply Finset.sup_le
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    rw [TauCeti.Polynomial.coeff_monicOfCoeff c ⟨k, hk'⟩]
    exact nnnorm_le_pi_nnnorm c ⟨k, hk'⟩
  exact_mod_cast hroot.le.trans hbound

theorem rootHomotopy_root_norm_le {n : ℕ} (c d : Fin n → ℂ) {M : ℝ}
    (hc : ‖c‖ ≤ M) (hd : ‖d‖ ≤ M) (t : Icc (0 : ℝ) 1)
    {z : ℂ} (hz : (rootHomotopy c d t).IsRoot z) : ‖z‖ ≤ M + 1 := by
  have ht0 : 0 ≤ (t : ℝ) := t.property.1
  have ht1 : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.property.2
  apply (root_norm_le_coefficient_norm_add_one _ hz).trans
  refine add_le_add ?_ (le_refl 1)
  calc
    ‖(1 - (t : ℝ)) • c + (t : ℝ) • d‖ ≤
        ‖(1 - (t : ℝ)) • c‖ + ‖(t : ℝ) • d‖ := norm_add_le _ _
    _ = (1 - (t : ℝ)) * ‖c‖ + (t : ℝ) * ‖d‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ht1, Real.norm_of_nonneg ht0]
    _ ≤ (1 - (t : ℝ)) * M + (t : ℝ) * M :=
      add_le_add (mul_le_mul_of_nonneg_left hc ht1) (mul_le_mul_of_nonneg_left hd ht0)
    _ = M := by ring

theorem eval_monicOfCoeff_sub_homotopy {n : ℕ} (c d : Fin n → ℂ)
    (t : Icc (0 : ℝ) 1) (z : ℂ) :
    (TauCeti.Polynomial.monicOfCoeff c).eval z - (rootHomotopy c d t).eval z =
      (t : ℝ) • ∑ i : Fin n, (c i - d i) * z ^ i.val := by
  simp only [rootHomotopy, TauCeti.Polynomial.eval_monicOfCoeff,
    Pi.add_apply, Pi.smul_apply, Complex.real_smul, add_sub_add_left_eq_sub,
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  push_cast
  ring

theorem rootHomotopy_initial_eval_bound {n : ℕ} (hn : 0 < n)
    (c d : Fin n → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hc : ‖c‖ ≤ M) (hd : ‖d‖ ≤ M) (t : Icc (0 : ℝ) 1)
    {z : ℂ} (hz : (rootHomotopy c d t).IsRoot z) :
    ‖(TauCeti.Polynomial.monicOfCoeff c).eval z‖ ≤
      n * (M + 1) ^ (n - 1) * ‖c - d‖ := by
  have hzB := rootHomotopy_root_norm_le c d hc hd t hz
  have hR : 1 ≤ M + 1 := by linarith
  have hval := eval_monicOfCoeff_sub_homotopy c d t z
  rw [hz, sub_zero] at hval
  rw [hval, norm_smul, Real.norm_of_nonneg t.property.1]
  have hs : ‖∑ i : Fin n, (c i - d i) * z ^ i.val‖ ≤
      ∑ i : Fin n, ‖c - d‖ * (M + 1) ^ (n - 1) := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    rw [norm_mul, norm_pow]
    have hi' : i.val ≤ n - 1 := by omega
    apply mul_le_mul (norm_le_pi_norm (c - d) i) ?_ (pow_nonneg (norm_nonneg z) _)
      (norm_nonneg (c - d))
    exact (pow_le_pow_left₀ (norm_nonneg z) hzB _).trans (pow_le_pow_right₀ hR hi')
  have hs' := mul_le_mul_of_nonneg_left hs t.property.1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs'
  apply hs'.trans
  have hnonneg : 0 ≤ (n : ℝ) * (‖c - d‖ * (M + 1) ^ (n - 1)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right t.property.2 hnonneg]

theorem rootHomotopy_root_near_initial {n : ℕ} (hn : 0 < n)
    (a : Fin n → ℝ) (c d : Fin n → ℂ)
    (hcP : TauCeti.Polynomial.monicOfCoeff c = realRootPolynomial a)
    {M ρ : ℝ} (hM : 0 ≤ M) (hρ : 0 ≤ ρ)
    (hc : ‖c‖ ≤ M) (hd : ‖d‖ ≤ M)
    (hsmall : n * (M + 1) ^ (n - 1) * ‖c - d‖ < ρ ^ n)
    (t : Icc (0 : ℝ) 1) {z : ℂ} (hz : z ∈ (rootHomotopy c d t).roots) :
    ∃ i, ‖z - (a i : ℂ)‖ < ρ := by
  have hroot := (Polynomial.mem_roots
    (TauCeti.Polynomial.monic_monicOfCoeff _).ne_zero).mp hz
  have heval := rootHomotopy_initial_eval_bound hn c d hM hc hd t hroot
  rw [hcP, realRootPolynomial, eval_prod] at heval
  simp only [eval_sub, eval_X, eval_C, norm_prod] at heval
  by_contra h
  push_neg at h
  have hprod := Finset.prod_le_prod₀ (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hρ)
    (fun i _ => h i)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod
  exact (not_lt_of_ge (hprod.trans heval)) hsmall

theorem roots_match_of_coefficient_bound {n : ℕ} (hn : 0 < n)
    (a b : Fin n → ℝ) {M ρ : ℝ} (hM : 0 ≤ M) (hρ : 0 ≤ ρ)
    (ha : ‖realRootCoefficients a‖ ≤ M) (hb : ‖realRootCoefficients b‖ ≤ M)
    (hsmall : n * (M + 1) ^ (n - 1) *
      ‖realRootCoefficients a - realRootCoefficients b‖ < ρ ^ n) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, |a i - b (σ i)| ≤ 2 * n * ρ := by
  apply exists_perm_dist_le_of_polynomial_homotopy a b
    (F := rootHomotopy (realRootCoefficients a) (realRootCoefficients b))
  · intro k hk
    exact continuous_rootHomotopy_coeff _ _ k
  · exact rootHomotopy_degree _ _
  · simp [rootHomotopy, monicOfCoeff_realRootCoefficients, realRootPolynomial]
  · simp [rootHomotopy, monicOfCoeff_realRootCoefficients, realRootPolynomial]
  · exact hρ
  · intro t z hz
    exact rootHomotopy_root_near_initial hn a _ _ (monicOfCoeff_realRootCoefficients a)
      hM hρ ha hb hsmall t hz

end EllipsoidVerification
