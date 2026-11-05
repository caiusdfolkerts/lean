module

public import Papers.GraphicalZonotopes.BookIntervalArithmetic

/-! # The closed formula for the optimal saturated-book hub degree

The integer-power exponent retains the paper's value (2^{-1}) when there
are three hubs.  The natural-number capacity difference is justified by
the proved monotonicity of clique capacity.
-/

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open BooleanModule

private theorem twice_choose_two_int (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℤ) * (n.choose 2 : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
  have h := Nat.add_one_mul_choose_eq (n - 1) 1
  have he : n - 1 + 1 = n := by omega
  have hnat : n * (n - 1) = n.choose 2 * 2 := by
    simpa only [he,Nat.choose_one_right] using h
  have hi : (n : ℤ) * ((n - 1 : ℕ) : ℤ) = (n.choose 2 : ℤ) * 2 := by
    exact_mod_cast hnat
  rw [Nat.cast_sub hn,Nat.cast_one] at hi
  nlinarith

theorem saturatedHubNeighbors_twice_formula {s : ℕ} (hs : 3 ≤ s) :
    (2 : ℤ) * (saturatedHubNeighbors s : ℤ) =
      ((s : ℤ)^2 + (s : ℤ) - 10) * (2 : ℤ)^(s - 3) + 4 := by
  have hmono := cliqueCapacity_pred_le (show 1 ≤ s by omega)
  have hu : (saturatedHubNeighbors s : ℤ) =
      (cliqueCapacity s : ℤ) - (cliqueCapacity (s - 1) : ℤ) + 1 := by
    rw [saturatedHubNeighbors,if_neg (by omega : s ≠ 2),Nat.cast_add,
      Nat.cast_sub hmono,Nat.cast_one]
  have hc := twice_choose_two_int s (by omega)
  have hp := twice_choose_two_int (s - 1) (by omega)
  rw [Nat.cast_sub (show 1 ≤ s by omega),Nat.cast_one] at hp
  have hcoef : 4 * (s.choose 2 : ℤ) - 2 * ((s - 1).choose 2 : ℤ) - 8 =
      (s : ℤ)^2 + (s : ℤ) - 10 := by nlinarith
  have hpow2 : (2 : ℤ)^(s - 2) = 2 * (2 : ℤ)^(s - 3) := by
    rw [show s - 2 = (s - 3) + 1 by omega,pow_add]
    norm_num <;> ring
  have hpow1 : (2 : ℤ)^(s - 1) = 4 * (2 : ℤ)^(s - 3) := by
    rw [show s - 1 = (s - 3) + 2 by omega,pow_add]
    norm_num <;> ring
  have hpow : (2 : ℤ)^s = 8 * (2 : ℤ)^(s - 3) := by
    calc
      (2 : ℤ)^s = (2 : ℤ)^((s - 3) + 3) := congrArg (fun n => (2 : ℤ)^n) (by omega)
      _ = _ := by rw [pow_add]; norm_num; ring
  calc
    (2 : ℤ) * (saturatedHubNeighbors s : ℤ) =
        (4 * (s.choose 2 : ℤ) - 2 * ((s - 1).choose 2 : ℤ) - 8) *
          (2 : ℤ)^(s - 3) + 4 := by
      rw [hu,cliqueCapacity_int_formula,cliqueCapacity_int_formula,
        show s - 1 - 2 = s - 3 by omega,hpow2,hpow1,hpow,
        Nat.cast_sub (show 1 ≤ s by omega),Nat.cast_one]
      ring
    _ = _ := by rw [hcoef]

/-- The numerical identity displayed in Theorem 7.12, including its
three-hub case with exponent (-1). -/
theorem saturatedHubNeighbors_closed_formula {s : ℕ} (hs : 3 ≤ s) :
    (saturatedHubNeighbors s : ℝ) =
      ((s : ℝ)^2 + (s : ℝ) - 10) * (2 : ℝ)^((s : ℤ) - 4) + 2 := by
  by_cases hs3 : s = 3
  · subst s
    norm_num [saturatedHubNeighbors,cliqueCapacity,Nat.choose]
  have hs4 : 4 ≤ s := by omega
  have hi := saturatedHubNeighbors_twice_formula hs
  have hr : (2 : ℝ) * (saturatedHubNeighbors s : ℝ) =
      ((s : ℝ)^2 + (s : ℝ) - 10) * (2 : ℝ)^(s - 3) + 4 := by
    exact_mod_cast hi
  have he : (s : ℤ) - 4 = ((s - 4 : ℕ) : ℤ) := by
    rw [Nat.cast_sub hs4]
    norm_num
  rw [he,zpow_natCast]
  have hp : (2 : ℝ)^(s - 3) = 2 * (2 : ℝ)^(s - 4) := by
    rw [show s - 3 = (s - 4) + 1 by omega,pow_add]
    norm_num <;> ring
  rw [hp] at hr
  nlinarith

end GraphicalZonotopes
