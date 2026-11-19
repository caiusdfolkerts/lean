module

public import Recovery.Unimodular.PriorExtensions.SignedSumsPivot
public import Mathlib.Data.ZMod.Basic

set_option maxHeartbeats 0


@[expose] public section

/-! The integer-matrix step of the binary/ternary criterion for regularity.
Every square submatrix is included, with arbitrary size and selectors. The
proof uses unit elimination and induction, not a bound on matrix dimensions.
The argument includes all finite sizes and all row and column selectors. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators

namespace Unimodular.ModularTU

open SignedSums.Pivot

variable {I J I' J' : Type*}

/-- Equality of the zero patterns of all square minors modulo two and three,
written arithmetically so that unit multiplication can be cancelled directly. -/
def DivisibilityAgreement (A : Matrix I J ℤ) : Prop :=
  ∀ (k : ℕ) (f : Fin k → I) (g : Fin k → J),
    (2 : ℤ) ∣ (A.submatrix f g).det ↔ (3 : ℤ) ∣ (A.submatrix f g).det

/-- The same condition on the actual entrywise reductions of the matrix. -/
def ModularAgreement (A : Matrix I J ℤ) : Prop :=
  ∀ (k : ℕ) (f : Fin k → I) (g : Fin k → J),
    ((A.submatrix f g).map fun x => (x : ZMod 2)).det = 0 ↔
      ((A.submatrix f g).map fun x => (x : ZMod 3)).det = 0

theorem modularAgreement_iff_divisibilityAgreement (A : Matrix I J ℤ) :
    ModularAgreement A ↔ DivisibilityAgreement A := by
  unfold ModularAgreement DivisibilityAgreement
  simp only [← Int.cast_det, ZMod.intCast_zmod_eq_zero_iff_dvd]
  norm_num

theorem DivisibilityAgreement.submatrix {A : Matrix I J ℤ}
    (hA : DivisibilityAgreement A) (f : I' → I) (g : J' → J) :
    DivisibilityAgreement (A.submatrix f g) := by
  intro k a b
  simpa only [Matrix.submatrix_submatrix] using hA k (f ∘ a) (g ∘ b)

/-- Entries in {0,1,-1} and the modular condition already force every 2×2
minor to lie in {0,1,-1}: the only other possible values are 2 and -2. -/
theorem small_two_minor (A : Matrix I J ℤ)
    (hsmall : ∀ i j, SignedSums.Pivot.Small (A i j)) (hA : DivisibilityAgreement A)
    (f : Fin 2 → I) (g : Fin 2 → J) : SignedSums.Pivot.Small (A.submatrix f g).det := by
  have h := hA 2 f g
  simp only [Matrix.det_fin_two, Matrix.submatrix_apply] at h ⊢
  rcases hsmall (f 0) (g 0) with h00 | h00 | h00 <;>
    rcases hsmall (f 0) (g 1) with h01 | h01 | h01 <;>
    rcases hsmall (f 1) (g 0) with h10 | h10 | h10 <;>
    rcases hsmall (f 1) (g 1) with h11 | h11 | h11 <;>
    first
    | solve | norm_num [SignedSums.Pivot.Small, h00, h01, h10, h11]
    | exfalso
      norm_num [h00, h01, h10, h11] at h

/-- The determinant identity for an arbitrary minor after a unit pivot.
The selectors need not be injective. This is the same Laplace calculation
used in the checked `SignedSums.Pivot.tu_eliminate`, without a TU premise. -/
theorem det_bordered_elimination [DecidableEq I] (A : Matrix I J ℤ)
    (r : I) (c : J) (hp : Sign (A r c)) (k : ℕ)
    (f : Fin k → I) (g : Fin k → J) (hfr : ∀ i, f i ≠ r) :
    (A.submatrix (Fin.cons r f) (Fin.cons c g)).det =
      A r c * ((eliminate A r c).submatrix f g).det := by
  let f' : Fin (k + 1) → I := Fin.cons r f
  let g' : Fin (k + 1) → J := Fin.cons c g
  have hcol (i : Fin (k + 1)) (hi : i ≠ 0) :
      (eliminate A r c).submatrix f' g' i 0 = 0 := by
    induction i using Fin.cases with
    | zero => exact False.elim (hi rfl)
    | succ i => exact eliminate_pivot_column A r c (sign_square hp) (f i) (hfr i)
  have hmat : ((eliminate A r c).submatrix f' g').submatrix
      (0 : Fin (k + 1)).succAbove Fin.succ = (eliminate A r c).submatrix f g := by
    funext i j
    simp [Matrix.submatrix_apply, f', g']
  have hhead : (eliminate A r c).submatrix f' g' 0 0 = A r c := by
    simp [Matrix.submatrix_apply, f', g', eliminate]
  calc
    _ = ((eliminate A r c).submatrix f' g').det :=
      (eliminate_det_of_row A r c f' g' 0 (by rfl)).symm
    _ = _ := by
      rw [Matrix.det_succ_column_zero, Finset.sum_eq_single 0]
      · rw [hhead, hmat]
        simp
      · intro i _ hi
        rw [hcol i hi]
        simp
      · simp

/-- The actual smaller integer Schur matrix, formed by eliminating the
chosen unit column and deleting exactly its pivot row and pivot column. -/
def reduced {k : ℕ} (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ)
    (r c : Fin (k + 1)) : Matrix (Fin k) (Fin k) ℤ :=
  (eliminate A r c).submatrix r.succAbove c.succAbove

/-- Every reduced entry is a unit multiple of an actual 2×2 original minor. -/
theorem reduced_small {k : ℕ} (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ)
    (hsmall : ∀ i j, SignedSums.Pivot.Small (A i j)) (hA : DivisibilityAgreement A)
    (r c : Fin (k + 1)) (hp : Sign (A r c)) :
    ∀ i j, SignedSums.Pivot.Small (reduced A r c i j) := by
  intro i j
  have hminor := small_two_minor A hsmall hA
    (Fin.cons r (fun _ : Fin 1 => r.succAbove i))
    (Fin.cons c (fun _ : Fin 1 => c.succAbove j))
  have heq : (A.submatrix
      (Fin.cons r (fun _ : Fin 1 => r.succAbove i))
      (Fin.cons c (fun _ : Fin 1 => c.succAbove j))).det =
        A r c * reduced A r c i j := by
    rw [det_bordered_elimination A r c hp 1
      (fun _ => r.succAbove i) (fun _ => c.succAbove j)
      (fun _ => Fin.succAbove_ne r i), Matrix.det_fin_one]
    rfl
  rw [heq] at hminor
  exact small_cancel_sign hp hminor

/-- The modular zero pattern of every reduced minor follows from the
bordered original minor. Multiplication by 1 or -1 changes neither pattern. -/
theorem reduced_agreement {k : ℕ} (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ)
    (hA : DivisibilityAgreement A) (r c : Fin (k + 1)) (hp : Sign (A r c)) :
    DivisibilityAgreement (reduced A r c) := by
  intro d f g
  have h := hA (d + 1) (Fin.cons r (r.succAbove ∘ f)) (Fin.cons c (c.succAbove ∘ g))
  rw [det_bordered_elimination A r c hp d (r.succAbove ∘ f) (c.succAbove ∘ g)
    (fun i => Fin.succAbove_ne r (f i))] at h
  change ((2 : ℤ) ∣ A r c * ((reduced A r c).submatrix f g).det ↔
    (3 : ℤ) ∣ A r c * ((reduced A r c).submatrix f g).det) at h
  rcases hp with hp | hp <;> simpa [hp] using h

/-- The determinant of every finite square integer matrix satisfying the
hypotheses is 0, 1 or -1. The induction has no dimension restriction. -/
theorem det_small_of_divisibilityAgreement (k : ℕ)
    (A : Matrix (Fin k) (Fin k) ℤ) (hsmall : ∀ i j, SignedSums.Pivot.Small (A i j))
    (hA : DivisibilityAgreement A) : SignedSums.Pivot.Small A.det := by
  induction k with
  | zero => simp [Matrix.det_fin_zero, SignedSums.Pivot.Small]
  | succ k ih =>
      by_cases hz : ∀ i j, A i j = 0
      · have hzero : A = 0 := funext (fun i => funext (hz i))
        rw [hzero]
        simp [SignedSums.Pivot.Small]
      · push_neg at hz
        obtain ⟨r, c, hrc⟩ := hz
        have hp : Sign (A r c) := sign_of_small_ne_zero (hsmall r c) hrc
        have hdet := ih (reduced A r c) (reduced_small A hsmall hA r c hp)
          (reduced_agreement A hA r c hp)
        have hcol : ∀ i, i ≠ r → eliminate A r c i c = 0 :=
          fun i hi => eliminate_pivot_column A r c (sign_square hp) i hi
        have hhead : SignedSums.Pivot.Small (eliminate A r c r c) := by
          simpa only [eliminate, eq_self, ite_true] using hsmall r c
        have helim := small_det_of_pivot (eliminate A r c) r c hcol hhead hdet
        have heq : (eliminate A r c).det = A.det := by
          simpa only [Matrix.submatrix_id_id] using
            eliminate_det_of_row A r c (id : Fin (k + 1) → Fin (k + 1))
              (id : Fin (k + 1) → Fin (k + 1)) r rfl
        rw [← heq]
        exact helim

/-- Full total unimodularity, including arbitrary row and column types and
every finite minor. No finite row or column bound is supplied. -/
theorem isTotallyUnimodular_of_divisibilityAgreement (A : Matrix I J ℤ)
    (hsmall : ∀ i j, A i j = 0 ∨ A i j = 1 ∨ A i j = -1)
    (hA : DivisibilityAgreement A) : A.IsTotallyUnimodular := by
  apply tu_of_small_det
  intro k f g
  exact det_small_of_divisibilityAgreement k (A.submatrix f g)
    (fun i j => hsmall (f i) (g j)) (hA.submatrix f g)

/-- Literal GF(2)/GF(3) minor agreement is sufficient for an integer
0,1,-1 matrix to be totally unimodular. -/
theorem isTotallyUnimodular_of_modularAgreement (A : Matrix I J ℤ)
    (hsmall : ∀ i j, A i j = 0 ∨ A i j = 1 ∨ A i j = -1)
    (hA : ModularAgreement A) : A.IsTotallyUnimodular :=
  isTotallyUnimodular_of_divisibilityAgreement A hsmall
    ((modularAgreement_iff_divisibilityAgreement A).1 hA)

/-- The converse holds because 0, 1 and -1 have the same zero status in
both prime fields. This gives an exact criterion, not merely sufficient data. -/
theorem isTotallyUnimodular_iff_modularAgreement (A : Matrix I J ℤ) :
    A.IsTotallyUnimodular ↔
      (∀ i j, A i j = 0 ∨ A i j = 1 ∨ A i j = -1) ∧ ModularAgreement A := by
  constructor
  · intro hA
    refine ⟨small_entry hA, (modularAgreement_iff_divisibilityAgreement A).2 ?_⟩
    intro k f g
    rcases small_det hA k f g with hd | hd | hd <;> norm_num [hd]
  · rintro ⟨hs, hm⟩
    exact isTotallyUnimodular_of_modularAgreement A hs hm

end Unimodular.ModularTU

end
end

#print axioms Unimodular.ModularTU.isTotallyUnimodular_iff_modularAgreement
#check Unimodular.ModularTU.isTotallyUnimodular_iff_modularAgreement
