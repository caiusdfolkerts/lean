module

public import PaperVerification.FermionNewtonExpansion
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Tactic.LinearCombination

/-!
# Block elimination gives the Newton power-expansion recurrences

The three formulas used by `PowerExpansionPattern` are proved here from
literal matrix-vector equations. The suffix matrix is only required to be
injective; no polynomiality of its inverse coefficients is assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open scoped BigOperators Matrix

variable {L : Type*} [Field L] {n : ℕ}

def matrixPowerExpansion (S : Matrix (Fin n) (Fin n) L) (y : Fin n → L)
    (d : ℕ) : Fin n → L := S⁻¹ *ᵥ (fun i ↦ y i ^ d)

theorem matrixPowerExpansion_solves
    (S : Matrix (Fin n) (Fin n) L) (hS : S.det ≠ 0) (y : Fin n → L) (d : ℕ) :
    S *ᵥ matrixPowerExpansion S y d = fun i ↦ y i ^ d := by
  rw [matrixPowerExpansion, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv S (isUnit_iff_ne_zero.mpr hS), Matrix.one_mulVec]

theorem matrix_mulVec_injective_of_det_ne_zero
    (S : Matrix (Fin n) (Fin n) L) (hS : S.det ≠ 0) :
    Function.Injective (fun a ↦ S *ᵥ a) := by
  intro a b hab
  have h := congrArg (fun v ↦ S⁻¹ *ᵥ v) hab
  simpa only [Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul S (isUnit_iff_ne_zero.mpr hS), Matrix.one_mulVec] using h

theorem matrixPowerExpansion_one_of_first_column
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) L) (hS : S.det ≠ 0)
    (y : Fin (n + 1) → L) (hfirst : ∀ i, S i 0 = y i) (i : Fin (n + 1)) :
    matrixPowerExpansion S y 1 i = if i = 0 then 1 else 0 := by
  have he : matrixPowerExpansion S y 1 = Pi.single 0 1 := by
    apply matrix_mulVec_injective_of_det_ne_zero S hS
    dsimp only
    rw [matrixPowerExpansion_solves S hS y 1, Matrix.mulVec_single_one]
    funext k
    simp only [pow_one, Matrix.col_apply, hfirst]
  rw [he, Pi.single_apply]

section Extension

variable {E : Type*} [Field E]

theorem matrix_map_det {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (M : Matrix (Fin n) (Fin n) R) :
    (M.map f).det = f M.det := (f.map_det M).symm

theorem matrixPowerExpansion_map
    (f : L →+* E) (S : Matrix (Fin n) (Fin n) L) (hS : S.det ≠ 0)
    (y : Fin n → L) (d : ℕ) :
    matrixPowerExpansion (S.map f) (f ∘ y) d = f ∘ matrixPowerExpansion S y d := by
  have hSf : (S.map f).det ≠ 0 := by
    change (f.mapMatrix S).det ≠ 0
    rw [← f.map_det]
    exact (map_ne_zero f).mpr hS
  apply matrix_mulVec_injective_of_det_ne_zero (S.map f) hSf
  dsimp only
  rw [matrixPowerExpansion_solves (S.map f) hSf (f ∘ y) d]
  funext i
  rw [← RingHom.map_mulVec, matrixPowerExpansion_solves S hS y d]
  exact (map_pow f (y i) d).symm

theorem PowerExpansionPattern.map
    (height : Fin n → ℤ) (A : ℕ → Fin n → L) (h : PowerExpansionPattern height A)
    (f : L →+* E) : PowerExpansionPattern height (fun d i ↦ f (A d i)) := by
  constructor
  · intro d hd i hi
    dsimp only
    rw [h.1 d hd i hi, map_zero]
  · intro d hd i hi
    dsimp only
    rw [h.2 d hd i hi]
    split_ifs <;> simp

end Extension

/-- A first power column, an arbitrary first row, and the scaled suffix. -/
def adjoinPowerColumn (z : L) (y row scale : Fin n → L)
    (S : Matrix (Fin n) (Fin n) L) : Matrix (Fin (n + 1)) (Fin (n + 1)) L :=
  Fin.cases (Fin.cases z row)
    (fun k ↦ Fin.cases (y k) (fun i ↦ scale k * S k i))

@[simp] theorem adjoinPowerColumn_zero_zero (z : L) (y row scale : Fin n → L)
    (S : Matrix (Fin n) (Fin n) L) : adjoinPowerColumn z y row scale S 0 0 = z := rfl

@[simp] theorem adjoinPowerColumn_zero_succ (z : L) (y row scale : Fin n → L)
    (S : Matrix (Fin n) (Fin n) L) (i : Fin n) :
    adjoinPowerColumn z y row scale S 0 i.succ = row i := rfl

@[simp] theorem adjoinPowerColumn_succ_zero (z : L) (y row scale : Fin n → L)
    (S : Matrix (Fin n) (Fin n) L) (i : Fin n) :
    adjoinPowerColumn z y row scale S i.succ 0 = y i := rfl

@[simp] theorem adjoinPowerColumn_succ_succ (z : L) (y row scale : Fin n → L)
    (S : Matrix (Fin n) (Fin n) L) (k i : Fin n) :
    adjoinPowerColumn z y row scale S k.succ i.succ = scale k * S k i := rfl

theorem adjoinPowerColumn_mulVec_zero (z : L) (y row scale : Fin n → L)
    (S : Matrix (Fin n) (Fin n) L) (a : Fin (n + 1) → L) :
    (adjoinPowerColumn z y row scale S *ᵥ a) 0 = z * a 0 + row ⬝ᵥ (a ∘ Fin.succ) := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, adjoinPowerColumn_zero_zero,
    adjoinPowerColumn_zero_succ, Function.comp_apply]

theorem adjoinPowerColumn_mulVec_succ (z : L) (y row scale : Fin n → L)
    (S : Matrix (Fin n) (Fin n) L) (a : Fin (n + 1) → L) (k : Fin n) :
    (adjoinPowerColumn z y row scale S *ᵥ a) k.succ =
      y k * a 0 + scale k * (S *ᵥ (a ∘ Fin.succ)) k := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, adjoinPowerColumn_succ_zero,
    adjoinPowerColumn_succ_succ, Function.comp_apply, Finset.mul_sum, mul_assoc]

theorem expansion_first_coefficient_of_zero_row
    (z : L) (hz : z ≠ 0) (y scale : Fin n → L)
    (S : Matrix (Fin n) (Fin n) L) (a : Fin (n + 1) → L) (d : ℕ) (hd : 1 ≤ d)
    (h : adjoinPowerColumn z y 0 scale S *ᵥ a = fun i ↦ Fin.cases z y i ^ d) :
    a 0 = z ^ (d - 1) := by
  have h0 := congrFun h 0
  rw [adjoinPowerColumn_mulVec_zero] at h0
  simp only [zero_dotProduct, add_zero, Fin.cases_zero] at h0
  apply mul_left_cancel₀ hz
  rw [h0, ← pow_succ', Nat.sub_add_cancel hd]

theorem expansion_flat_suffix
    (z : L) (hz : z ≠ 0) (y : Fin n → L) (S : Matrix (Fin n) (Fin n) L)
    (hS : Function.Injective (fun a ↦ S *ᵥ a))
    (A : ℕ → Fin (n + 1) → L) (B : ℕ → Fin n → L)
    (hA : ∀ d, adjoinPowerColumn z y 0 1 S *ᵥ A d = fun i ↦ Fin.cases z y i ^ d)
    (hB : ∀ d, S *ᵥ B d = fun i ↦ y i ^ d)
    (d : ℕ) (hd : 2 ≤ d) (i : Fin n) :
    A d i.succ = B d i - z ^ (d - 1) * B 1 i := by
  have h0 := expansion_first_coefficient_of_zero_row z hz y 1 S (A d) d (by omega) (hA d)
  have he : A d ∘ Fin.succ = B d - z ^ (d - 1) • B 1 := by
    apply hS
    dsimp only
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hB d, hB 1]
    funext k
    have hk := congrFun (hA d) k.succ
    rw [adjoinPowerColumn_mulVec_succ, h0] at hk
    simp only [Pi.one_apply, one_mul, Fin.cases_succ, pow_one] at hk
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, pow_one]
    change (S *ᵥ (A d ∘ Fin.succ)) k = y k ^ d - z ^ (d - 1) * y k
    linear_combination hk
  exact congrFun he i

theorem expansion_down_suffix
    (z : L) (y row : Fin n → L) (hzy : ∀ i, y i ≠ z)
    (S : Matrix (Fin n) (Fin n) L) (hS : Function.Injective (fun a ↦ S *ᵥ a))
    (A : ℕ → Fin (n + 1) → L) (B : ℕ → Fin n → L)
    (hA : ∀ d, adjoinPowerColumn z y row (fun i ↦ (y i - z)⁻¹) S *ᵥ A d =
      fun i ↦ Fin.cases z y i ^ d)
    (hB : ∀ d, S *ᵥ B d = fun i ↦ y i ^ d)
    (d : ℕ) (i : Fin n) :
    A d i.succ = B (d + 1) i - z * B d i - A d 0 * B 2 i + z * A d 0 * B 1 i := by
  have he : A d ∘ Fin.succ = B (d + 1) - z • B d - A d 0 • B 2 + (z * A d 0) • B 1 := by
    apply hS
    dsimp only
    rw [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_sub,
      Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul,
      hB (d + 1), hB d, hB 2, hB 1]
    funext k
    have hk := congrFun (hA d) k.succ
    rw [adjoinPowerColumn_mulVec_succ] at hk
    simp only [Fin.cases_succ] at hk
    have hk' := congrArg (fun t : L ↦ (y k - z) * t) hk
    simp only [mul_add, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr (hzy k)), one_mul] at hk'
    change (S *ᵥ (A d ∘ Fin.succ)) k =
      y k ^ (d + 1) - z * y k ^ d - A d 0 * y k ^ 2 + (z * A d 0) * y k ^ 1
    rw [pow_succ]
    linear_combination hk'
  exact congrFun he i

theorem geometric_power_difference (y z : L) (d : ℕ) (hd : 1 ≤ d) :
    (y - z) * (∑ a ∈ Finset.range (d - 1), z ^ (d - 2 - a) * y ^ (a + 1)) =
      y ^ d - z ^ (d - 1) * y := by
  have h := congrArg (fun t : L ↦ y * t)
    ((Commute.all y z).mul_geom_sum₂ (d - 1))
  have he : y * ((y - z) * ∑ a ∈ Finset.range (d - 1),
      y ^ a * z ^ (d - 1 - 1 - a)) =
      (y - z) * ∑ a ∈ Finset.range (d - 1), z ^ (d - 2 - a) * y ^ (a + 1) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    have hs : d - 1 - 1 - a = d - 2 - a := by omega
    rw [hs, pow_succ]
    ring
  rw [he] at h
  calc
    _ = y * (y ^ (d - 1) - z ^ (d - 1)) := h
    _ = _ := by rw [mul_sub, ← pow_succ', Nat.sub_add_cancel hd]; ring

theorem expansion_up_suffix
    (z : L) (hz : z ≠ 0) (y : Fin n → L) (hzy : ∀ i, y i ≠ z)
    (S : Matrix (Fin n) (Fin n) L) (hS : Function.Injective (fun a ↦ S *ᵥ a))
    (A : ℕ → Fin (n + 1) → L) (B : ℕ → Fin n → L)
    (hA : ∀ d, adjoinPowerColumn z y 0 (fun i ↦ y i - z) S *ᵥ A d =
      fun i ↦ Fin.cases z y i ^ d)
    (hB : ∀ d, S *ᵥ B d = fun i ↦ y i ^ d)
    (d : ℕ) (hd : 2 ≤ d) (i : Fin n) :
    A d i.succ = ∑ a ∈ Finset.range (d - 1), z ^ (d - 2 - a) * B (a + 1) i := by
  have h0 := expansion_first_coefficient_of_zero_row z hz y (fun i ↦ y i - z) S
    (A d) d (by omega) (hA d)
  have he : A d ∘ Fin.succ = ∑ a ∈ Finset.range (d - 1), z ^ (d - 2 - a) • B (a + 1) := by
    apply hS
    dsimp only
    rw [Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hB]
    funext k
    have hk := congrFun (hA d) k.succ
    rw [adjoinPowerColumn_mulVec_succ, h0] at hk
    simp only [Fin.cases_succ] at hk
    apply mul_left_cancel₀ (sub_ne_zero.mpr (hzy k))
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    change (y k - z) * (S *ᵥ (A d ∘ Fin.succ)) k =
      (y k - z) * ∑ a ∈ Finset.range (d - 1), z ^ (d - 2 - a) * y k ^ (a + 1)
    rw [geometric_power_difference (y k) z d (by omega)]
    linear_combination hk
  simpa only [Function.comp_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun he i

end PaperVerification.Fermion.Newton
