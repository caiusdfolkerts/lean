module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Convert
public import Lean.Elab.Tactic.Omega

/-!
# The rectangular diagonal-difference map

This is a new reconstruction after the execution-environment loss. The source
is not a recovered or previously compiled file. Its proof identifies the kernel
by propagation along matrix diagonals and then uses rank-nullity.
-/

@[expose] public section
noncomputable section

namespace PaperVerification.AlternatingForms

open Matrix

variable {K : Type*} [Field K]

/-- A square matrix with one-based row and zero-based column, extended by zero. -/
def orbitSquarePad {t : ℕ} (P : Matrix (Fin (t + 1)) (Fin (t + 1)) K)
    (r c : ℕ) : K :=
  if hr : 0 < r ∧ r ≤ t + 1 then
    if hc : c ≤ t then P ⟨r - 1, by omega⟩ ⟨c, by omega⟩ else 0
  else 0

@[simp]
theorem orbitSquarePad_apply {t : ℕ}
    (P : Matrix (Fin (t + 1)) (Fin (t + 1)) K) (i j : Fin (t + 1)) :
    orbitSquarePad P (i.val + 1) j.val = P i j := by
  have hi : 0 < i.val + 1 ∧ i.val + 1 ≤ t + 1 := by have := i.isLt; omega
  have hj : j.val ≤ t := by have := j.isLt; omega
  simp [orbitSquarePad, hi, hj]

@[simp]
theorem orbitSquarePad_row_zero {t : ℕ}
    (P : Matrix (Fin (t + 1)) (Fin (t + 1)) K) (c : ℕ) :
    orbitSquarePad P 0 c = 0 := by simp [orbitSquarePad]

@[simp]
theorem orbitSquarePad_row_last {t : ℕ}
    (P : Matrix (Fin (t + 1)) (Fin (t + 1)) K) (c : ℕ) :
    orbitSquarePad P (t + 2) c = 0 := by simp [orbitSquarePad]

@[simp]
theorem orbitSquarePad_add {t : ℕ}
    (P Q : Matrix (Fin (t + 1)) (Fin (t + 1)) K) (r c : ℕ) :
    orbitSquarePad (P + Q) r c = orbitSquarePad P r c + orbitSquarePad Q r c := by
  unfold orbitSquarePad
  split_ifs <;> simp

@[simp]
theorem orbitSquarePad_smul {t : ℕ} (a : K)
    (P : Matrix (Fin (t + 1)) (Fin (t + 1)) K) (r c : ℕ) :
    orbitSquarePad (a • P) r c = a * orbitSquarePad P r c := by
  unfold orbitSquarePad
  split_ifs <;> simp [smul_eq_mul]

/-- Consecutive diagonal differences, including both zero boundary rows. -/
def orbitDifference (t : ℕ) :
    Matrix (Fin (t + 1)) (Fin (t + 1)) K →ₗ[K]
      Matrix (Fin t) (Fin (t + 2)) K where
  toFun P i j := orbitSquarePad P (j.val + 1) (i.val + 1) -
    orbitSquarePad P j.val i.val
  map_add' P Q := by
    ext i j
    change orbitSquarePad (P+Q) (j.val+1) (i.val+1)-orbitSquarePad (P+Q) j.val i.val =
      (orbitSquarePad P (j.val+1) (i.val+1)-orbitSquarePad P j.val i.val)+
        (orbitSquarePad Q (j.val+1) (i.val+1)-orbitSquarePad Q j.val i.val)
    simp only [orbitSquarePad_add]
    ring
  map_smul' a P := by
    ext i j
    change orbitSquarePad (a • P) (j.val+1) (i.val+1)-orbitSquarePad (a • P) j.val i.val =
      a * (orbitSquarePad P (j.val+1) (i.val+1)-orbitSquarePad P j.val i.val)
    simp only [orbitSquarePad_smul]
    ring

/-- A matrix in the kernel is determined by its upper-left entry. -/
theorem orbitDifference_zero_of_corner_zero (t : ℕ)
    (P : Matrix (Fin (t + 1)) (Fin (t + 1)) K)
    (hP : orbitDifference t P = 0) (h00 : P 0 0 = 0) : P = 0 := by
  have hentry (i : Fin t) (j : Fin (t + 2)) :
      orbitSquarePad P (j.val + 1) (i.val + 1) =
        orbitSquarePad P j.val i.val := by
    exact sub_eq_zero.mp (congrFun (congrFun hP i) j)
  have htop (c : ℕ) (hc : c < t) :
      P 0 ⟨c + 1, by omega⟩ = 0 := by
    have h := hentry ⟨c, hc⟩ 0
    simpa only [Fin.val_zero, zero_add, orbitSquarePad_row_zero,
      ← orbitSquarePad_apply P (0 : Fin (t + 1)) ⟨c + 1, by omega⟩] using h
  have hbottom (c : ℕ) (hc : c < t) :
      P (Fin.last t) ⟨c, by omega⟩ = 0 := by
    have h := hentry ⟨c, hc⟩ (Fin.last (t + 1))
    have h' : orbitSquarePad P (t + 1) c = 0 := by
      simpa only [Fin.val_last, orbitSquarePad_row_last] using h.symm
    simpa only [← orbitSquarePad_apply P (Fin.last t) ⟨c, by omega⟩,
      Fin.val_last] using h'
  have hstep (r c : ℕ) (hr : r + 1 < t + 1) (hc : c + 1 < t + 1) :
      P ⟨r + 1, hr⟩ ⟨c + 1, hc⟩ = P ⟨r, by omega⟩ ⟨c, by omega⟩ := by
    have h := hentry ⟨c, by omega⟩ ⟨r + 1, by omega⟩
    simpa only [← orbitSquarePad_apply P ⟨r + 1, hr⟩ ⟨c + 1, hc⟩,
      ← orbitSquarePad_apply P ⟨r, by omega⟩ ⟨c, by omega⟩] using h
  have hshift (r c d : ℕ) (hr : r + d < t + 1) (hc : c + d < t + 1) :
      P ⟨r + d, hr⟩ ⟨c + d, hc⟩ = P ⟨r, by omega⟩ ⟨c, by omega⟩ := by
    induction d with
    | zero => rfl
    | succ d ih =>
      calc
        P ⟨r + (d + 1), hr⟩ ⟨c + (d + 1), hc⟩ =
            P ⟨r + d, by omega⟩ ⟨c + d, by omega⟩ := by
          simpa only [Nat.add_assoc] using hstep (r + d) (c + d) (by omega) (by omega)
        _ = _ := ih (by omega) (by omega)
  ext i j
  change P i j = 0
  by_cases hij : i.val ≤ j.val
  · have h := hshift 0 (j.val - i.val) i.val (by have := i.isLt; omega)
      (by have := j.isLt; omega)
    have hred : P i j = P 0 ⟨j.val - i.val, by have := j.isLt; omega⟩ := by
      convert h using 1 <;> congr 1 <;> apply Fin.ext <;> simp only [Fin.val_mk, Fin.val_zero] <;> omega
    rw [hred]
    by_cases heq : i.val = j.val
    · simpa [heq] using h00
    · have ht := htop (j.val - i.val - 1) (by have := j.isLt; omega)
      convert ht using 1 <;> congr 1 <;> apply Fin.ext <;> simp only [Fin.val_mk] <;> omega
  · have h := hshift (i.val - j.val) 0 j.val (by have := i.isLt; omega)
      (by have := j.isLt; omega)
    have hred : P i j = P ⟨i.val - j.val, by have := i.isLt; omega⟩ 0 := by
      convert h using 1 <;> congr 1 <;> apply Fin.ext <;> simp only [Fin.val_mk, Fin.val_zero] <;> omega
    rw [hred]
    have h' := hshift (i.val - j.val) 0 (t - (i.val - j.val))
      (by have := i.isLt; omega) (by have := i.isLt; omega)
    have ht := hbottom (t - (i.val - j.val)) (by have := i.isLt; omega)
    have hred' :
        P (Fin.last t) ⟨t - (i.val - j.val), by have := i.isLt; omega⟩ =
          P ⟨i.val - j.val, by have := i.isLt; omega⟩ 0 := by
      convert h' using 1 <;> congr 1 <;> apply Fin.ext <;>
        simp only [Fin.val_mk, Fin.val_last, Fin.val_zero] <;> omega
    exact hred'.symm.trans ht

/-- All prescribed rectangular diagonal differences occur. -/
theorem orbitDifference_surjective (t : ℕ) :
    Function.Surjective (orbitDifference (K := K) t) := by
  let e : LinearMap.ker (orbitDifference (K := K) t) →ₗ[K] K :=
    { toFun P := P.val 0 0
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have he : Function.Injective e := by
    intro P Q h
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply orbitDifference_zero_of_corner_zero t (P.val - Q.val)
    · rw [map_sub, LinearMap.mem_ker.mp P.property, LinearMap.mem_ker.mp Q.property,
        sub_self]
    · exact sub_eq_zero.mpr h
  have hk : Module.finrank K (LinearMap.ker (orbitDifference (K := K) t)) ≤ 1 := by
    simpa using LinearMap.finrank_le_finrank_of_injective he
  have hd := (orbitDifference (K := K) t).finrank_range_add_finrank_ker
  have hsource :
      Module.finrank K (Matrix (Fin (t + 1)) (Fin (t + 1)) K) = (t + 1) * (t + 1) := by
    change Module.finrank K (Fin (t + 1) → Fin (t + 1) → K) = _
    simp [Module.finrank_pi_fintype]
  have htarget :
      Module.finrank K (Matrix (Fin t) (Fin (t + 2)) K) = t * (t + 2) := by
    change Module.finrank K (Fin t → Fin (t + 2) → K) = _
    simp [Module.finrank_pi_fintype]
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  have hle := Submodule.finrank_le (orbitDifference (K := K) t).range
  rw [hsource] at hd
  rw [htarget] at hle ⊢
  nlinarith

end PaperVerification.AlternatingForms
