import Characterizations.TestNumbers
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Nat.Choose.Bounds

/-! # The fixed-degree logarithmic asymptotic in Corollary 5.5 -/

noncomputable section
namespace Characterizations
open Classical Finset Filter Asymptotics
variable (k : Type*) [CommSemiring k] [Nontrivial k]

theorem pattern_count_le_power {n d : ℕ} (hd : 1 ≤ d) :
    n * (n-1).choose 2 * (n-3).choose (d-1) ≤ n^(d+2) := by
  calc
    _ ≤ n * n^2 * n^(d-1) := by
      apply Nat.mul_le_mul
      · exact Nat.mul_le_mul_left n ((Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) 2))
      · exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) (d-1))
    _ = _ := by
      have hfirst : n*n^2=n^3 := by ring
      rw [hfirst,←pow_add]
      congr 1
      omega

theorem testNumber_log_upper {n d : ℕ} (hn : 4 ≤ n) (hd : 2 ≤ d) (hdn : d+2 ≤ n) :
    (orderTestNumber k n d : ℝ) ≤
      ((testProbability d)⁻¹ * (d+2) + ((testProbability d)⁻¹+1)/Real.log 2) * Real.log n := by
  let Q := n * (n-1).choose 2 * (n-3).choose (d-1)
  let p := testProbability d
  have hp : 0 < p := by dsimp [p,testProbability]; positivity
  have hQ : 0 < Q := by
    apply Nat.mul_pos
    · exact Nat.mul_pos (by omega) (Nat.choose_pos (by omega))
    · exact Nat.choose_pos (by omega)
  have hQpow : (Q:ℝ) ≤ (n:ℝ)^(d+2) := by exact_mod_cast pattern_count_le_power (n := n) (by omega : 1 ≤ d)
  have hlogQ : Real.log Q ≤ (d+2:ℝ)*Real.log n := by
    have hh := Real.log_le_log (show (0:ℝ)<Q by exact_mod_cast hQ) hQpow
    rw [Real.log_pow] at hh
    simpa using hh
  have hA : 0 ≤ p⁻¹ * (Real.log Q+1) := mul_nonneg (inv_nonneg.mpr hp.le)
    (by linarith [Real.log_natCast_nonneg Q])
  have hceil := Nat.ceil_lt_add_one hA
  have hN : (orderTestNumber k n d : ℝ) ≤ ⌈p⁻¹*(Real.log Q+1)⌉₊ := by
    exact_mod_cast orderTestNumber_logarithmic_upper k hn hd (by omega)
  have hN' : (orderTestNumber k n d : ℝ) ≤ p⁻¹*(Real.log Q+1)+1 := hN.trans hceil.le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num)
    (by exact_mod_cast (show 2 ≤ n by omega))
  have hbonus := mul_le_mul_of_nonneg_left hlogn
    (div_nonneg (by positivity : 0 ≤ p⁻¹+1) hlog2.le)
  rw [div_mul_cancel₀ _ hlog2.ne'] at hbonus
  have hmain := mul_le_mul_of_nonneg_left hlogQ (inv_nonneg.mpr hp.le)
  change (orderTestNumber k n d : ℝ) ≤ (p⁻¹*(d+2) + (p⁻¹+1)/Real.log 2)*Real.log n
  nlinarith

theorem log_le_testNumber {n d : ℕ} (hn : 4 ≤ n) (hd : 2 ≤ d) :
    Real.log n ≤ (2*Real.log 2)*(orderTestNumber k n d : ℝ) := by
  have hsig := orderTestNumber_signature_bound k hn hd
  have hpow : n-1 ≤ 2^(orderTestNumber k n d) :=
    hsig.trans (Nat.choose_le_two_pow _ _)
  have hn1 : (0:ℝ) < (n-1:ℕ) := by exact_mod_cast (show 0<n-1 by omega)
  have hlog := Real.log_le_log hn1 (show ((n-1:ℕ):ℝ) ≤ (2:ℝ)^(orderTestNumber k n d) by exact_mod_cast hpow)
  rw [Real.log_pow] at hlog
  have hsquare : (n:ℝ) ≤ (((n-1:ℕ):ℝ))^2 := by
    have hcast : ((n-1:ℕ):ℝ) = (n:ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
    rw [hcast]
    have hnR : (4:ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hlogn := Real.log_le_log (show (0:ℝ)<n by exact_mod_cast (show 0<n by omega)) hsquare
  rw [Real.log_pow] at hlogn
  norm_num at hlogn
  nlinarith

/-- For every fixed degree d≥2, the exact minimum number of tests has order
Θ(log n), with ordinary real natural logarithm and n tending to infinity. -/
theorem orderTestNumber_isTheta_log (d : ℕ) (hd : 2 ≤ d) :
    (fun n : ℕ => (orderTestNumber k n d : ℝ)) =Θ[atTop] (fun n : ℕ => Real.log n) := by
  constructor
  · apply IsBigO.of_bound ((testProbability d)⁻¹*(d+2) + ((testProbability d)⁻¹+1)/Real.log 2)
    filter_upwards [eventually_ge_atTop (max 4 (d+2))] with n hn
    have hh := testNumber_log_upper k (n := n) (d := d) (by omega) hd (by omega)
    simpa only [Real.norm_eq_abs,abs_of_nonneg (show (0:ℝ) ≤ (orderTestNumber k n d : ℝ) by positivity),
      abs_of_nonneg (Real.log_natCast_nonneg n)] using hh
  · apply IsBigO.of_bound (2*Real.log 2)
    filter_upwards [eventually_ge_atTop 4] with n hn
    have hh := log_le_testNumber k hn hd
    simpa only [Real.norm_eq_abs,abs_of_nonneg (show (0:ℝ) ≤ (orderTestNumber k n d : ℝ) by positivity),
      abs_of_nonneg (Real.log_natCast_nonneg n)] using hh

end Characterizations
