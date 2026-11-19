/- Integer unit elimination, ported from the recovered PivotTU485 source.
The source proof bodies through tu_eliminate are unchanged except namespace
qualifications. Additional lemmas make the arbitrary selected pivot explicit. -/
module
public import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
namespace Unimodular.SignedSums.Pivot

def Sign (a : ℤ) : Prop := a = 1 ∨ a = -1
def Small (a : ℤ) : Prop := a = 0 ∨ a = 1 ∨ a = -1

theorem sign_mul {a b : ℤ} (ha : Sign a) (hb : Sign b) : Sign (a * b) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    simp [Sign, ha, hb]

theorem sign_square {a : ℤ} (ha : Sign a) : a * a = 1 := by
  rcases ha with h | h <;> simp [h]

theorem sign_of_small_ne_zero {a : ℤ} (ha : Small a) (hne : a ≠ 0) : Sign a := by
  rcases ha with h | h | h
  · exact False.elim (hne h)
  · exact Or.inl h
  · exact Or.inr h

theorem small_mul {a b : ℤ} (ha : Small a) (hb : Small b) : Small (a * b) := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> norm_num [Small]

theorem small_of_sign (s : SignType) : Small (s.cast : ℤ) := by
  cases s <;> simp [Small]

theorem small_det {I J : Type*} {A : Matrix I J ℤ} (hA : A.IsTotallyUnimodular)
    (k : ℕ) (f : Fin k → I) (g : Fin k → J) : Small (A.submatrix f g).det := by
  obtain ⟨s, hs⟩ := (Matrix.isTotallyUnimodular_iff A).mp hA k f g
  rw [← hs]
  exact small_of_sign s

theorem tu_of_small_det {I J : Type*} {A : Matrix I J ℤ}
    (h : ∀ (k : ℕ) (f : Fin k → I) (g : Fin k → J), Small (A.submatrix f g).det) :
    A.IsTotallyUnimodular := by
  apply (Matrix.isTotallyUnimodular_iff A).mpr
  intro k f g
  rcases h k f g with he | he | he
  · exact ⟨0, by simpa using he.symm⟩
  · exact ⟨1, by simpa using he.symm⟩
  · exact ⟨-1, by simpa using he.symm⟩

theorem small_cancel_sign {a b : ℤ} (ha : Sign a) (hb : Small (a * b)) : Small b := by
  rcases ha with rfl | rfl
  · simpa using hb
  · rcases hb with h | h | h <;> unfold Small <;> omega

theorem small_prod {I : Type*} [DecidableEq I] (s : Finset I) (q : I → ℤ)
    (h : ∀ i ∈ s, Small (q i)) : Small (s.prod q) := by
  revert h
  induction s using Finset.induction_on with
  | empty => intro h; simp [Small]
  | @insert i s hi ih =>
      intro h
      rw [Finset.prod_insert hi]
      exact small_mul (h i (Finset.mem_insert_self i s))
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem tu_scale_rows {I J : Type*} {A : Matrix I J ℤ}
    (hA : A.IsTotallyUnimodular) (q : I → ℤ) (hq : ∀ i, Small (q i)) :
    Matrix.IsTotallyUnimodular (fun i j => q i * A i j) := by
  classical
  apply tu_of_small_det
  intro k f g
  change Small (Matrix.det (Matrix.of (fun i j => q (f i) * (A.submatrix f g) i j)))
  rw [Matrix.det_mul_column]
  exact small_mul (small_prod Finset.univ (fun i => q (f i)) (fun i _ => hq (f i)))
    (small_det hA k f g)

def eliminate {I J : Type*} [DecidableEq I] (A : Matrix I J ℤ) (r : I) (c : J) :
    Matrix I J ℤ :=
  fun i j => if i = r then A r j else A i j - A r c * A i c * A r j

theorem eliminate_pivot_column {I J : Type*} [DecidableEq I]
    (A : Matrix I J ℤ) (r : I) (c : J) (hp : A r c * A r c = 1)
    (i : I) (hi : i ≠ r) : eliminate A r c i c = 0 := by
  rw [eliminate, if_neg hi]
  calc
    A i c - A r c * A i c * A r c = A i c - (A r c * A r c) * A i c := by ring
    _ = 0 := by rw [hp]; ring

theorem eliminate_det_of_row {I J Z : Type*} [DecidableEq I] [DecidableEq Z] [Fintype Z]
    (A : Matrix I J ℤ) (r : I) (c : J) (f : Z → I) (g : Z → J)
    (x : Z) (hx : f x = r) :
    ((eliminate A r c).submatrix f g).det = (A.submatrix f g).det := by
  apply Matrix.det_eq_of_forall_row_eq_smul_add_const
    (B := A.submatrix f g) (fun i => if f i = r then 0 else -A r c * A (f i) c) x
  · simp [hx]
  · intro i j
    by_cases hi : f i = r <;>
      simp [Matrix.submatrix_apply, eliminate, hi, hx, sub_eq_add_neg] <;> ring

/-- Integer row elimination at a unit pivot preserves every square minor bound.
The proof also handles selectors with repetitions, using the established
Mathlib equivalence for total unimodularity. -/
theorem tu_eliminate {I J : Type*} [DecidableEq I]
    {A : Matrix I J ℤ} (hA : A.IsTotallyUnimodular) (r : I) (c : J)
    (hp : Sign (A r c)) : (eliminate A r c).IsTotallyUnimodular := by
  classical
  have hp2 := sign_square hp
  apply tu_of_small_det
  intro k f g
  by_cases hx : ∃ x, f x = r
  · obtain ⟨x, hx⟩ := hx
    rw [eliminate_det_of_row A r c f g x hx]
    exact small_det hA k f g
  · have hfr (i : Fin k) : f i ≠ r := fun he => hx ⟨i, he⟩
    let f' : Fin (k + 1) → I := Fin.cons r f
    let g' : Fin (k + 1) → J := Fin.cons c g
    have hlarge : Small (((eliminate A r c).submatrix f' g').det) := by
      rw [eliminate_det_of_row A r c f' g' 0 (by rfl)]
      exact small_det hA (k + 1) f' g'
    have hcol (i : Fin (k + 1)) (hi : i ≠ 0) :
        (eliminate A r c).submatrix f' g' i 0 = 0 := by
      induction i using Fin.cases with
      | zero => exact False.elim (hi rfl)
      | succ i => exact eliminate_pivot_column A r c hp2 (f i) (hfr i)
    have hmat : ((eliminate A r c).submatrix f' g').submatrix
        (0 : Fin (k + 1)).succAbove Fin.succ = (eliminate A r c).submatrix f g := by
      funext i j
      simp [Matrix.submatrix_apply, f', g']
    have hhead : (eliminate A r c).submatrix f' g' 0 0 = A r c := by
      simp [Matrix.submatrix_apply, f', g', eliminate]
    have hdet : ((eliminate A r c).submatrix f' g').det =
        A r c * ((eliminate A r c).submatrix f g).det := by
      rw [Matrix.det_succ_column_zero, Finset.sum_eq_single 0]
      · rw [hhead, hmat]
        simp
      · intro i _ hi
        rw [hcol i hi]
        simp
      · simp
    rw [hdet] at hlarge
    exact small_cancel_sign hp hlarge


theorem small_pow {a : ℤ} (ha : Small a) (n : ℕ) : Small (a ^ n) := by
  induction n with
  | zero => simp [Small]
  | succ n ih => rw [pow_succ]; exact small_mul ih ha

theorem small_entry {I J : Type*} {A : Matrix I J ℤ}
    (hA : A.IsTotallyUnimodular) (i : I) (j : J) : Small (A i j) := by
  obtain ⟨s, hs⟩ := hA.apply i j
  rw [← hs]
  exact small_of_sign s

/-- Laplace expansion at an arbitrary selected unit column. -/
theorem small_det_of_pivot {k : ℕ} (M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ)
    (i j : Fin (k + 1)) (hcol : ∀ r, r ≠ i → M r j = 0)
    (hp : Small (M i j))
    (hm : Small (M.submatrix i.succAbove j.succAbove).det) : Small M.det := by
  rw [Matrix.det_succ_column M j, Finset.sum_eq_single i]
  · exact small_mul (small_mul (small_pow (Or.inr (Or.inr rfl)) _) hp) hm
  · intro r _ hr
    rw [hcol r hr]
    simp
  · simp

end Unimodular.SignedSums.Pivot
#print axioms Unimodular.SignedSums.Pivot.tu_eliminate
#print axioms Unimodular.SignedSums.Pivot.small_det_of_pivot
