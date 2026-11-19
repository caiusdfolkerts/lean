module

public import mixed_volume.general.series_mixed_area
public import mixed_volume.general.rational_systems

/-! The first two exact moments of the full stochastic word series, together
with their finite rational resolvent formulas. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.AutomatonMoments

open VolumePolynomials AutomatonWords AutomatonZonoids AutomatonRecurrence Matrix
open scoped BigOperators

variable {s m : ℕ}

structure RationalData (s m : ℕ) where
  P : Fin s → Matrix (Fin m) (Fin m) ℚ
  P_nonneg : ∀ a j k, 0 ≤ P a j k
  P_sum : ∀ a j, ∑ k, P a j k = 1
  f : Fin m → ℚ
  f_nonneg : ∀ j, 0 ≤ f j
  f_le_one : ∀ j, f j ≤ 1
  stationary : Fin m → ℚ
  stationary_nonneg : ∀ j, 0 ≤ stationary j
  stationary_sum : ∑ j, stationary j = 1
  stationary_fixed : ∀ a, stationary ᵥ* P a = stationary

def RationalData.toReal (A : RationalData s m) : Data s m where
  P a j k := A.P a j k
  P_nonneg a j k := by exact_mod_cast A.P_nonneg a j k
  P_sum a j := by exact_mod_cast A.P_sum a j
  f j := A.f j
  f_nonneg j := by exact_mod_cast A.f_nonneg j
  f_le_one j := by exact_mod_cast A.f_le_one j
  stationary j := A.stationary j
  stationary_probability := by
    constructor
    · intro j
      change 0 ≤ (A.stationary j : ℝ)
      exact_mod_cast A.stationary_nonneg j
    · change (∑ j, (A.stationary j : ℝ)) = 1
      exact_mod_cast A.stationary_sum
  stationary_fixed a := by
    funext j
    have h := congrFun (A.stationary_fixed a) j
    change (∑ k, (A.stationary k : ℝ) * (A.P a k j : ℝ)) = (A.stationary j : ℝ)
    change (∑ k, A.stationary k * A.P a k j) = A.stationary j at h
    exact_mod_cast h

def massTerm (A : Data s m) (j : Fin m) (w : Word s) : ℝ :=
  A.weight w j * rho s ^ w.length

def firstTerm (A : Data s m) (j : Fin m) (w : Word s) : ℝ :=
  massTerm A j w * tag w

def mass (A : Data s m) (j : Fin m) : ℝ := ∑' w, massTerm A j w
def first (A : Data s m) (j : Fin m) : ℝ := ∑' w, firstTerm A j w

theorem massTerm_nonneg (A : Data s m) (hs : 0 < s) (j : Fin m) (w : Word s) :
    0 ≤ massTerm A j w := mul_nonneg (A.weight_pos w j).le (pow_nonneg (rho_pos hs).le _)

theorem mass_summable (A : Data s m) (hs : 0 < s) (j : Fin m) :
    Summable (massTerm A j) := by
  have h := state_summable A hs j
  change Summable (fun w => A.weight w j * rho s ^ w.length)
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (A.weight_pos _ j),
    generator_norm hs, massTerm] using h

theorem first_summable (A : Data s m) (hs : 0 < s) (j : Fin m) :
    Summable (firstTerm A j) := by
  apply (mass_summable A hs j).of_norm_bounded
  intro w
  rw [Real.norm_eq_abs, firstTerm, abs_mul,
    abs_of_nonneg (massTerm_nonneg A hs j w), abs_of_nonneg (tag_nonneg w)]
  exact mul_le_of_le_one_right (massTerm_nonneg A hs j w) (tag_lt_one w).le

theorem sum_states_tsum {ι κ : Type*} [Fintype ι] (c : ι → ℝ) (f : ι → κ → ℝ)
    (hf : ∀ i, Summable (f i)) :
    (∑' w, ∑ i, c i * f i w) = ∑ i, c i * ∑' w, f i w := by
  have h := (hasSum_sum (s := (Finset.univ : Finset ι))
    (fun i _ => ((hf i).mul_left (c i)).hasSum)).tsum_eq
  simpa only [tsum_mul_left] using h

@[simp] theorem massTerm_nil (A : Data s m) (j : Fin m) :
    massTerm A j [] = 1 + A.f j := by simp [massTerm]

@[simp] theorem firstTerm_nil (A : Data s m) (j : Fin m) :
    firstTerm A j [] = 0 := by simp [firstTerm]

theorem massTerm_cons (A : Data s m) (a : Fin s) (j : Fin m) (w : Word s) :
    massTerm A j (a :: w) = rho s * ∑ k, A.P a j k * massTerm A k w := by
  simp only [massTerm, A.weight_cons, List.length_cons, pow_succ,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem firstTerm_cons (A : Data s m) (a : Fin s) (j : Fin m) (w : Word s) :
    firstTerm A j (a :: w) = rho s / base s *
      ∑ k, A.P a j k * (((a.val : ℝ) + 1) * massTerm A k w + firstTerm A k w) := by
  simp only [firstTerm, massTerm_cons, tag_cons, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem mass_recurrence (A : Data s m) (hs : 0 < s) (j : Fin m) :
    mass A j = 1 + A.f j + rho s * ∑ a, ∑ k, A.P a j k * mass A k := by
  rw [mass, tsum_words _ (mass_summable A hs j), massTerm_nil, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [massTerm_cons]
  rw [tsum_mul_left, sum_states_tsum _ _ (mass_summable A hs)]
  rfl

theorem first_recurrence (A : Data s m) (hs : 0 < s) (j : Fin m) :
    first A j = rho s / base s *
      ∑ a, ∑ k, A.P a j k * (((a.val : ℝ) + 1) * mass A k + first A k) := by
  rw [first, tsum_words _ (first_summable A hs j), firstTerm_nil, zero_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [firstTerm_cons]
  rw [tsum_mul_left, sum_states_tsum _ _
    (fun k => ((mass_summable A hs k).mul_left ((a.val : ℝ) + 1)).add
      (first_summable A hs k))]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [Summable.tsum_add ((mass_summable A hs k).mul_left _)
    (first_summable A hs k), tsum_mul_left]
  rfl

def rhoQ (s : ℕ) : ℚ := 1 / (4 * s)
def baseQ (s : ℕ) : ℚ := s + 1

@[simp] theorem cast_rhoQ (s : ℕ) : (rhoQ s : ℝ) = rho s := by simp [rhoQ, rho]
@[simp] theorem cast_baseQ (s : ℕ) : (baseQ s : ℝ) = base s := by simp [baseQ, base]

def massMatrix (A : RationalData s m) : Matrix (Fin m) (Fin m) ℚ :=
  fun j k => rhoQ s * ∑ a, A.P a j k

def firstMatrix (A : RationalData s m) : Matrix (Fin m) (Fin m) ℚ :=
  fun j k => rhoQ s / baseQ s * ∑ a, A.P a j k

def massQ (A : RationalData s m) : Fin m → ℚ :=
  RationalSystems.rationalSolution (massMatrix A) (fun j => 1 + A.f j)

def firstSourceQ (A : RationalData s m) (j : Fin m) : ℚ :=
  rhoQ s / baseQ s * ∑ a, ∑ k, A.P a j k * ((a.val : ℚ) + 1) * massQ A k

def firstQ (A : RationalData s m) : Fin m → ℚ :=
  RationalSystems.rationalSolution (firstMatrix A) (firstSourceQ A)

theorem massMatrix_row (A : RationalData s m) (hs : 0 < s) (j : Fin m) :
    (∑ k, |(massMatrix A j k : ℝ)|) = 1 / 4 := by
  have hnonneg (k : Fin m) : 0 ≤ (massMatrix A j k : ℝ) := by
    simp only [massMatrix, Rat.cast_mul, cast_rhoQ, Rat.cast_sum]
    exact mul_nonneg (rho_pos hs).le (Finset.sum_nonneg fun a _ => by exact_mod_cast A.P_nonneg a j k)
  simp_rw [abs_of_nonneg (hnonneg _)]
  simp only [massMatrix, Rat.cast_mul, cast_rhoQ, Rat.cast_sum, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  have hsum (a : Fin s) : ∑ k, (A.P a j k : ℝ) = 1 := by exact_mod_cast A.P_sum a j
  simp_rw [hsum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [mul_comm]
  exact card_mul_rho hs

theorem firstMatrix_row (A : RationalData s m) (hs : 0 < s) (j : Fin m) :
    (∑ k, |(firstMatrix A j k : ℝ)|) ≤ 1 / 4 := by
  have heq (k : Fin m) : (firstMatrix A j k : ℝ) = (massMatrix A j k : ℝ) / base s := by
    simp only [firstMatrix, massMatrix, Rat.cast_mul, Rat.cast_div, cast_rhoQ, cast_baseQ,
      Rat.cast_sum]
    ring
  simp_rw [heq, abs_div, abs_of_pos (base_pos s)]
  rw [← Finset.sum_div, massMatrix_row A hs]
  apply (div_le_iff₀ (base_pos s)).2
  dsimp [base]
  nlinarith [Nat.cast_nonneg (α := ℝ) s]

theorem mass_eq_rational (A : RationalData s m) (hs : 0 < s) :
    mass A.toReal = RationalSystems.castVector (massQ A) := by
  apply RationalSystems.real_solution_is_rational (massMatrix A) (fun j => 1 + A.f j)
    (1 / 4) (by norm_num) (by norm_num) (fun j => (massMatrix_row A hs j).le)
  funext j
  rw [mass_recurrence A.toReal hs j]
  change 1 + (A.f j : ℝ) + rho s * (∑ a, ∑ k, (A.P a j k : ℝ) * mass A.toReal k) =
    ((1 + A.f j : ℚ) : ℝ) + ∑ k, (massMatrix A j k : ℝ) * mass A.toReal k
  simp only [Rat.cast_add, Rat.cast_one]
  congr 1
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [massMatrix, Rat.cast_mul, cast_rhoQ, Rat.cast_sum]
  rw [← Finset.sum_mul]
  ring

theorem first_eq_rational (A : RationalData s m) (hs : 0 < s) :
    first A.toReal = RationalSystems.castVector (firstQ A) := by
  apply RationalSystems.real_solution_is_rational (firstMatrix A) (firstSourceQ A)
    (1 / 4) (by norm_num) (by norm_num) (firstMatrix_row A hs)
  funext j
  rw [first_recurrence A.toReal hs j]
  simp only [mul_add, Finset.sum_add_distrib]
  change _ = (firstSourceQ A j : ℝ) + ∑ k, (firstMatrix A j k : ℝ) * first A.toReal k
  congr 1
  · simp only [firstSourceQ, Rat.cast_mul, Rat.cast_div, cast_rhoQ, cast_baseQ,
      Rat.cast_sum, Rat.cast_add, Rat.cast_natCast, Rat.cast_one]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro k _
    rw [congrFun (mass_eq_rational A hs) k]
    dsimp [RationalSystems.castVector, RationalData.toReal]
    ring
  · rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [firstMatrix, Rat.cast_mul, Rat.cast_div, cast_rhoQ, cast_baseQ, Rat.cast_sum,
      RationalData.toReal]
    rw [← Finset.sum_mul]
    ring

end MixedVolume.AutomatonMoments

end
